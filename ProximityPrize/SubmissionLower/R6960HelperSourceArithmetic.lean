import ProximityPrize.SubmissionLower.PortLow6
import ProximityPrize.SubmissionLower.UpperBranch5
import ProximityPrize.SubmissionLower.FrontCore82258Model
import Mathlib.Algebra.Order.Sub.Prod
import ProximityPrize.SubmissionLower.UpperBranch3
import ProximityPrize.SubmissionLower.HighCore82258Pairs

set_option Elab.async false

-- merged module PortLow7
section Merged_PortLow7
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_9_7
noncomputable section
open K1_13 (Shape chart ceilDiv mixed32)
open P0_9 (linearChart taylorLength physicalDegree )
def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
end
end P0_9_7
end
section
namespace P0_9_7_1
theorem sparse_bound : K1_13_7_1.c1 :=
  K1_13_7_1_1.of_children
    (K1_13_7_1_1_1.of_children
      (K1_13_7_1_1_1_1.of_children K1_13_7_1_1_1_1_1.proof K1_13_7_1_1_1_1_2.proof)
      (K1_13_7_1_1_1_2.of_children K1_13_7_1_1_1_2_1.proof K1_13_7_1_1_1_2_2.proof))
    K1_13_7_1_1_2.proof
theorem surface_sections : K1_13_7_1.c2 :=
  K1_13_7_1_2.of_children K1_13_7_1_2_1.proof
    (K1_13_7_1_2_2.of_children
      (K1_13_7_1_2_2_1.of_children K1_13_7_1_2_2_1_1.proof K1_13_7_1_2_2_1_2.proof)
      (K1_13_7_1_2_2_2.of_children K1_13_7_1_2_2_2_1.proof K1_13_7_1_2_2_2_2.proof))
end P0_9_7_1
end
section
namespace P0_9_7_1
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_1 K1_13_6 K1_13_7 K1_13_7_1
open K1_13_7_1 (topAt eval_topAt topAt_coeff topView_separant)
def derivativeBox (p : Shape) : Shape := ⟨p.b - 1, p.j - 3, p.t - 1⟩
theorem derivative_box (f : Row 4) {j : ℕ} (hj : 0 < j) :
    InBox (shape ((separant^[j]) f)) (derivativeBox (shape f).chamber) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  rw [Function.iterate_succ_apply]
  have h := derivative_in_box (separant f) k
  have hb : (shape (separant f)).b ≤ (shape f).b - 1 := by
    have hd := weightedTotalDegree_pderiv_le_sub (1 : Fin 4 → ℕ) 3 f
    simpa only [shape, weightedTotalDegree_one, Pi.one_apply, separant] using hd
  have hi : (shape (separant f)).j ≤ (shape f).j - 3 := by
    have hd := weightedTotalDegree_pderiv_le_sub (fun i : Fin 4 => i.val) 3 f
    have hthree : (3 : Fin 4).val = 3 := rfl
    simpa only [shape, indexDegree_eq, separant, hthree] using hd
  have ht : (shape (separant f)).t ≤ (shape f).t - 1 := by
    simpa only [Function.iterate_one] using derivative_degree f 1
  exact ⟨h.1.trans (hb.trans (Nat.sub_le_sub_right (le_max_left _ _) 1)),
    h.2.1.trans hi, h.2.2.trans ht⟩
end
end P0_9_7_1
end
section
namespace P0_9_7_2
noncomputable section
open Polynomial
open K1_13 (Geom Row Shape InBox shape mixed32)
open K1_13_6 (GeoJets toGeneric separant)
open K1_13_7_2 (evalTrajectory)
open P0_9 (taylorLength physicalDegree)
open P0_9_7 (fatChart )
structure FatTaylor (f : Row 4) where
  denom : Row 4
  numer : Fin taylorLength → Row 4
  test : Row 4
  denom_box : InBox (shape denom) (fatChart (shape f))
  numer_box : ∀ i, InBox (shape (numer i)) (fatChart (shape f))
  test_box : InBox (shape test) (fatChart (shape f))
  test_iff : ∀ (surface : Ideal GeoJets), surface.IsPrime → toGeneric f ∈ surface →
    toGeneric (separant f) ∉ surface →
    (toGeneric test ∈ surface ↔ toGeneric (P0_9_6.membershipTest f) ∈ surface)
  recovers : ∀ (L : Type) [Field L] [Algebra Geom L] (S : (Polynomial L)),
    S.natDegree ≤ physicalDegree → evalTrajectory f S = 0 →
    evalTrajectory (separant f) S ≠ 0 →
    evalTrajectory denom S ≠ 0 ∧ evalTrajectory test S = 0 ∧
      ∀ i, evalTrajectory (numer i) S = evalTrajectory denom S * C (S.coeff i.val)
end
end P0_9_7_2
end
section
namespace P0_9_7_2
noncomputable section
open K1_13 K1_13_6 K1_13_7 K1_13_7_2 K1_13_7_2_1 K1_13_7_2_1_2
open MvPolynomial UniqueFactorizationMonoid
open scoped Polynomial
open K1_13_7_2_1 (geometric_injective liftLower_ne_zero)
open K1_13_7_2_1 (local_length_one tangent_invariant)
open K1_13_7_2_1_2 (top top_rename_lower top_map top_derivative)
theorem local_generators (f : Row 4) (q : Row 3)
    (hq : Squarefree (genericRow q)) (surface : Ideal GeoJets)
    (h : LiftedSurface f q surface) : LocalGenerators f q surface h.minimal.isPrime := by
  let : surface.IsPrime := h.minimal.isPrime
  let A := Localization.AtPrime surface
  let l : GeoJets →+* A := algebraMap GeoJets A
  let J := intersectionIdeal f (liftLower q)
  let e : GeoJets ≃ₐ[GeoField] (Polynomial Lower) := top
  let F := e (toGeneric f)
  have hlower (u : Row 3) : e (toGeneric (liftLower u)) = Polynomial.C (genericRow u) := by
    change top (MvPolynomial.map genericCoeffs (MvPolynomial.rename Fin.castSucc u)) = _
    rw [MvPolynomial.map_rename, top_rename_lower]
    rfl
  have hlead : e (toGeneric (liftLower (K1_13_1.anchorLead f))) = Polynomial.C F.leadingCoeff := by
    rw [hlower]
    congr 1
    change MvPolynomial.map genericCoeffs (top f).leadingCoeff =
      (top (MvPolynomial.map genericCoeffs f)).leadingCoeff
    have hinj : Function.Injective genericCoeffs :=
      (algebraMap GenericField GeoField).injective.comp
        (IsFractionRing.injective (Polynomial Geom) GenericField)
    rw [top_map, Polynomial.leadingCoeff_map_of_injective (MvPolynomial.map_injective _ hinj)]
  have hsep : e (toGeneric (separant f)) = F.derivative := by
    change top (MvPolynomial.map genericCoeffs (MvPolynomial.pderiv 3 f)) =
      (top (MvPolynomial.map genericCoeffs f)).derivative
    rw [← MvPolynomial.pderiv_map, top_derivative]
  have hJ : J.map e.toRingHom = Ideal.span {F, Polynomial.C (genericRow q)} := by
    change (Ideal.span {toGeneric f, toGeneric (liftLower q)}).map e.toRingHom = _
    rw [Ideal.map_span, Set.image_pair]
    change Ideal.span {F, e (toGeneric (liftLower q))} = _
    rw [hlower]
  have hqrad : (Ideal.span ({genericRow q} : Set Lower)).IsRadical :=
    isRadical_iff_span_singleton.mp (isRadical_iff_squarefree_or_zero.mpr (Or.inl hq))
  have hrad : (J.map l).radical ≤ J.map l := by
    rw [← IsLocalization.map_radical surface.primeCompl A J]
    apply Ideal.map_le_iff_le_comap.mpr
    intro g hg
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hg
    have hn' : e g ^ n ∈ Ideal.span {F, Polynomial.C (genericRow q)} := by
      rw [← hJ, ← map_pow]
      exact Ideal.mem_map_of_mem e.toRingHom hn
    obtain ⟨k, hk⟩ := clear_monic_cut F (e g) hqrad hn'
    let u := toGeneric (liftLower (K1_13_1.anchorLead f)) ^ k * toGeneric (separant f)
    have hu : u ∉ surface := h.minimal.isPrime.mul_notMem
      (fun hm => h.leading (h.minimal.isPrime.mem_of_pow_mem _ hm)) h.regular
    have humem : u * g ∈ J := by
      have hc : (J.map e.toRingHom).comap e.toRingHom = J :=
        Ideal.comap_map_of_bijective e.toRingHom e.bijective
      rw [← hc, Ideal.mem_comap, hJ]
      change e (u * g) ∈ _
      simpa only [u, map_mul, map_pow, hlead, hsep, mul_assoc] using hk
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff surface.primeCompl A J g).mpr
      ⟨u, hu, humem⟩
  change J.map l = IsLocalRing.maximalIdeal A
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal surface A,
      ← IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes A surface J h.minimal]
  exact le_antisymm Ideal.le_radical hrad
end
end P0_9_7_2
end
section
namespace P0_9_7_2_3
noncomputable section
open Polynomial MvPolynomial
open K1_13 (Geom Row shape)
open K1_13_6 (GeoJets GeoField GenericField toGeneric genericCoeffs divisorIdeal)
open K1_13_6_3 (JetIdeal dimension geomConstants)
open K1_13_7_2_5 (wholeComponents properComponents)
open P0_9_7 (fatChart)
open P0_9_7_2 ( FatTaylor)
open scoped BigOperators
private theorem generic_degree_le (g : Row 4) : (toGeneric g).totalDegree ≤ g.totalDegree := by
  rw [toGeneric, MvPolynomial.totalDegree_eq, MvPolynomial.totalDegree_eq]
  exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
theorem generic_ne_zero {f : Row 4} (hf : Irreducible f) : toGeneric f ≠ 0 := by
  have hinj : Function.Injective genericCoeffs :=
    (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective (Polynomial Geom) GenericField)
  exact (map_ne_zero_iff (MvPolynomial.map genericCoeffs) (MvPolynomial.map_injective _ hinj)).mpr
    hf.ne_zero
theorem whole_dimension {f : Row 4} {component : JetIdeal} (hf : Irreducible f)
    (hZ : (Ideal.span {toGeneric f}).IsMinimalPrime component) : dimension component = 3 := by
  have h := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton
    (generic_ne_zero hf) hZ
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  change dimension component + 1 = 4 at h
  omega
theorem whole_sum {f : Row 4} (hf : Irreducible f) :
    ∑ component ∈ wholeComponents f, affineDegree component ≤ ((shape f).chamber.b : ℚ) := by
  have hn : toGeneric f ∉ (⊥ : JetIdeal) := fun h => generic_ne_zero hf ((Ideal.mem_bot).mp h)
  have hd : (toGeneric f).totalDegree ≤ (shape f).chamber.b :=
    (generic_degree_le f).trans (Nat.le_max_left _ _)
  simpa only [wholeComponents, bot_sup_eq, affineDegree_bot, mul_one] using (principalCut_sum_affineDegree_minimalPrimes_le (P := (⊥ : JetIdeal)) hn hd)
end
end P0_9_7_2_3
end
section
namespace P0_9_7_3
noncomputable section
open Polynomial K1_13 K1_13_7 K1_13_7_1 K1_13_7_5 K1_13_7_5_1 K1_13_7_5_3
open scoped BigOperators Pointwise
open K1_13_7_5_1 (lift_length_ge lift_length_finite)
open K1_13_7_5_3 (supported_anchor supported_lower supported_coordinate mixed_matches)
theorem common_section : K1_13_7_5_3.c1 :=
  K1_13_7_5_3_1.of_children K1_13_7_5_3_1_1.proof K1_13_7_5_3_1_2.proof
theorem sparse_length : K1_13_7_5_3.c3 :=
  K1_13_7_5_3_3.of_children K1_13_7_5_3_3_1.proof
    (K1_13_7_5_3_3_2.of_children K1_13_7_5_3_3_2_1.proof K1_13_7_5_3_3_2_2.proof)
    (K1_13_7_5_3_3_3.of_children K1_13_7_5_3_3_3_1.proof K1_13_7_5_3_3_3_2.proof)
    K1_13_7_5_3_3_4.proof
end
end P0_9_7_3
end
section
namespace P0_9_7_3
noncomputable section
open Polynomial Finset K1 K1_13 K1_13_7 K1_13_7_5 K1_13_7_1
open scoped BigOperators
open K1_13_7_5 (supported_sub supported_C supported_X exists_coordinate_cut jetPoint_injective chart_section eval_chart_section weighted_ceil)
theorem choose_linear_cut {f : Row 4} (ht : 0 < (shape f).t)
    {r : PrimeSpectrum Jets} {y : JetPoint} (h : r.asIdeal < jetPointIdeal y) :
    ∃ F : Jets, Supported (shape f).chamber F ∧ F ∉ r.asIdeal ∧
      r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y F = 0 := by
  obtain ⟨i, hi⟩ := exists_coordinate_cut h
  obtain ⟨hb, hj⟩ := shape_chamber f
  have hj' : 3 ≤ (shape f).chamber.j := by
    have htop : 0 < (shape f).chamber.t := ht
    omega
  have hb' : 1 ≤ (shape f).chamber.b := (by decide : 1 ≤ 3).trans (hj'.trans hb)
  exact ⟨MvPolynomial.X i - MvPolynomial.C (y i),
    supported_sub (supported_X hb' hj' ht i) (supported_C _ _), hi, h.le, by simp⟩
end
end P0_9_7_3
end
section
namespace P0_9_7_3_1
noncomputable section
open Polynomial MvPolynomial K1 K1_13 K1_13_1 K1_13_6 K1_13_7 K1_13_7_1 K1_13_7_5
open scoped BigOperators
open K1_13_7_5_2 (linearJet eval_linearJet separant_bound linearJet_bound denominator ordinary_eq_hasse)
open K1_13_7_5_2 (supported_of_fits eval_center)
open K1_13_7_5 (supported_C_mul)
local notation "W" => MvPolynomial.weightedTotalDegree
def numerator (L : ℕ) (f : Row 4) (n : ℕ) : Row 4 :=
  if hn : n < 4 then MvPolynomial.X ⟨n, hn⟩ * K1_13_7_5_2.denominator L f
  else
    MvPolynomial.C (Polynomial.C (↑n.factorial : Geom)⁻¹) *
      (separant f ^ (L - n) * linearJet f n)
theorem denominator_bound (L : ℕ) (w : Fin 4 → ℕ) {f : Row 4} {B : ℕ}
    (hf : W w f ≤ B) : W w (K1_13_7_5_2.denominator L f) ≤ L * (B - w 3) :=
  (weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _ (separant_bound w hf))
theorem numerator_bound {L n : ℕ} (hn : n ≤ L) (w : Fin 4 → ℕ) (Δ d₀ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) (hw : ∀ i, w i ≤ d₀)
    {f : Row 4} {B : ℕ} (hB : w 3 ≤ B) (hf : W w f ≤ B) :
    W w (numerator L f n) ≤ d₀ + L * (B - w 3 + Δ) := by
  unfold numerator
  split_ifs with hinit
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add ((weight_X_le w _).trans (hw _)) (denominator_bound L w hf)).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) _))
  · have hp := (weightedTotalDegree_pow_le w (separant f) (L - n)).trans
      (Nat.mul_le_mul_left _ (separant_bound w hf))
    apply (weight_const_mul_le _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _ ≤ (L - n) * (B - w 3) + (w 0 + n * (B - w 3 + Δ)) :=
        Nat.add_le_add hp (linearJet_bound w Δ hshift hB hf n)
      _ = w 0 + ((L - n) + n) * (B - w 3) + n * Δ := by ring
      _ ≤ _ := by
        rw [Nat.sub_add_cancel hn, Nat.mul_add]
        simpa only [Nat.add_assoc] using
          Nat.add_le_add (Nat.add_le_add_right (hw 0) _) (Nat.mul_le_mul_right Δ hn)
theorem coefficients_recover {L : ℕ} (hL : L < K1.p) {f : Row 4}
    (hf : (shape f).t = 1) (S : (Polynomial Geom)) (hon : atJet f S = 0) (hr : RegularAt f S) :
    evalGeneric S (toGeneric (K1_13_7_5_2.denominator L f)) ≠ 0 ∧
      ∀ i : Fin L, evalGeneric S (toGeneric (numerator L f i.val)) =
        evalGeneric S (toGeneric (K1_13_7_5_2.denominator L f)) * genericCoeffs (hasseDeriv i.val S) := by
  have hp : atJet (separant f) S ≠ 0 := hr
  have hden : atJet (K1_13_7_5_2.denominator L f) S = atJet (separant f) S ^ L :=
    map_pow (MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))) _ _
  constructor
  · rw [evalGeneric_toGeneric, hden]
    exact (map_ne_zero_iff _ genericCoeffs_injective).mpr (pow_ne_zero _ hp)
  · intro i
    rw [evalGeneric_toGeneric, evalGeneric_toGeneric, ← map_mul]
    apply congrArg genericCoeffs
    unfold numerator
    split_ifs with hinit
    · unfold atJet
      rw [map_mul, MvPolynomial.eval_X, mul_comm]
      rfl
    · let E := MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))
      change E (_ * (_ ^ _ * _)) = _
      rw [map_mul, map_mul, map_pow, MvPolynomial.eval_C]
      change _ * (atJet (separant f) S ^ (L - i.val) *
        atJet (linearJet f i.val) S) = _
      rw [eval_linearJet hf S hon hr, K1_13_7_5_2.ordinary_eq_hasse]
      have hinv : Polynomial.C (↑i.val.factorial : Geom)⁻¹ *
          Polynomial.C (↑i.val.factorial : Geom) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ (factorial_cast_ne_zero (i.isLt.trans hL)), map_one]
      have hpow : L - i.val + i.val = L := Nat.sub_add_cancel i.isLt.le
      calc
        _ = (Polynomial.C (↑i.val.factorial : Geom)⁻¹ * Polynomial.C (↑i.val.factorial : Geom)) *
            ((atJet (separant f) S ^ (L - i.val) * atJet (separant f) S ^ i.val) *
              hasseDeriv i.val S) := by ring
        _ = _ := by rw [hinv, one_mul, ← pow_add, hpow, hden]
private abbrev constants : Geom →+* GeometricX := genericCoeff.comp Polynomial.C
private abbrev center : GeometricX := genericCoeff Polynomial.X
private theorem eval_taylor {L : ℕ} (S : (Polynomial K)) (hS : S.natDegree < L) (x : K) :
    (∑ j : Fin L, (constantCoeff x - center) ^ j.val *
      genericCoeff (hasseDeriv j.val (extend S))) = constantCoeff (S.eval x) := by
  let P := (extend S).map constants
  let u := constantCoeff x - center
  have hcoeff (n : ℕ) : (Polynomial.taylor center P).coeff n =
      genericCoeff (hasseDeriv n (extend S)) := by
    rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, eval_center]
  have hd : (Polynomial.taylor center P).natDegree < L := by
    rw [Polynomial.natDegree_taylor]
    exact (Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le).trans_lt hS
  have hev : P.eval (constantCoeff x) = constantCoeff (S.eval x) := by
    change ((S.map embed).map constants).eval (constantCoeff x) = _
    rw [Polynomial.map_map]
    exact Polynomial.eval_map_apply K1_13_7_5.constantCoeff x
  calc
    _ = (Polynomial.taylor center P).eval u := by
      rw [Polynomial.eval_eq_sum_range' hd, ← Fin.sum_univ_eq_sum_range]
      simp only [hcoeff, u]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = P.eval (constantCoeff x) := Polynomial.taylor_eval_sub _ _ _
    _ = _ := hev
theorem values_of_coefficients {L : ℕ} {H : Shape} (D : GeoJets) (N : Fin L → GeoJets)
    (hD : GeoFits D H) (hN : ∀ j, GeoFits (N j) H) :
    ∃ C : ValueChart H, ∀ S : (Polynomial K), S.natDegree < L →
      (evalGeneric (extend S) D ≠ 0 ∧ ∀ j, evalGeneric (extend S) (N j) =
        evalGeneric (extend S) D * genericCoeffs (hasseDeriv j.val (extend S))) →
      C.recovers S := by
  let value (i : I) : Jets :=
    ∑ j : Fin L, MvPolynomial.C ((constantCoeff (node i) - center) ^ j.val) * N j
  have hvalue (i : I) : Supported H (value i) := by
    classical
    intro m hm
    unfold value at hm
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
    exact supported_C_mul (supported_of_fits (hN j)) _ m hj
  refine ⟨⟨D, value, supported_of_fits hD, hvalue⟩, ?_⟩
  intro S hS h
  refine ⟨h.1, fun i => ?_⟩
  let ev := evalGeneric (extend S)
  change ev (value i) = constantCoeff (S.eval (node i)) * ev D
  have hc (a : GeometricX) : ev (MvPolynomial.C a) = a := MvPolynomial.eval_C a
  have he (j : Fin L) : ev (N j) =
      ev D * genericCoeff (hasseDeriv j.val (extend S)) := h.2 j
  simp only [value, map_sum, map_mul, hc, he]
  calc
    _ = ev D * (∑ j : Fin L, (constantCoeff (node i) - center) ^ j.val *
        genericCoeff (hasseDeriv j.val (extend S))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => mul_left_comm _ _ _)
    _ = _ := by rw [eval_taylor S hS, mul_comm]
end
end P0_9_7_3_1
end
section
namespace P0_9_7_3_2
noncomputable section
open Polynomial MvPolynomial K1 K1_13 K1_13_6 K1_13_7 K1_13_7_1 K1_13_7_5
open K1_13_1 (indexDegree_eq)
open scoped BigOperators
open K1_13_7_1 (denominator denominator_bound topPartial_bound jet_bound ordinary_eq_hasse)
open K1_13_7_5_2 (supported_of_fits constants center eval_center)
open K1_13_7_5 (supported_C_mul)
local notation "W" => MvPolynomial.weightedTotalDegree
def coefficientNumerator (L : ℕ) (g : Row 4) (n : ℕ) : Row 4 :=
  if hn : n < 4 then MvPolynomial.X ⟨n, hn⟩ * denominator L g
  else
    MvPolynomial.C (Polynomial.C (↑n.factorial : Geom)⁻¹) *
      (separant g ^ (2 * (L - n)) * jetNumerator g n)
private theorem numerator_bound {L n : ℕ} (hn : n ≤ L) (w : Fin 4 → ℕ) (Δ d₀ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) (hw : ∀ i, w i ≤ d₀)
    {g : Row 4} {B : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) :
    W w (coefficientNumerator L g n) ≤ d₀ + 2 * L * (B - w 3) + L * Δ := by
  unfold coefficientNumerator
  split_ifs
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add ((weight_X_le w _).trans (hw _)) (denominator_bound L w hg)).trans
        (Nat.le_add_right _ _))
  · have hp := (weightedTotalDegree_pow_le w (separant g) (2 * (L - n))).trans
      (Nat.mul_le_mul_left _ ((topPartial_bound w g).trans (Nat.sub_le_sub_right hg _)))
    apply (weight_const_mul_le _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _ ≤ 2 * (L - n) * (B - w 3) + (w 0 + n * (2 * (B - w 3) + Δ)) :=
        Nat.add_le_add hp (jet_bound w Δ hshift hB hg n)
      _ = w 0 + 2 * (n + (L - n)) * (B - w 3) + n * Δ := by ring
      _ ≤ _ := by
        rw [Nat.add_sub_of_le hn]
        exact Nat.add_le_add (Nat.add_le_add_right (hw 0) _) (Nat.mul_le_mul_right Δ hn)
theorem coefficients_fit (L : ℕ) (g : Row 4) (p : Shape) (hB : InBox (shape g) p)
    (hp : Chamber p) (ht : 0 < p.t) :
    GeoFits (toGeneric (denominator L g)) (chart L p) ∧
      ∀ n ≤ L, GeoFits (toGeneric (coefficientNumerator L g n)) (chart L p) := by
  have hb : 1 ≤ p.b := by have := hp.1; have := hp.2; omega
  have hj : 3 ≤ p.j := by have := hp.2; omega
  have h₁ : W 1 g ≤ p.b := by simpa only [shape, weightedTotalDegree_one] using hB.1
  have h₂ : W Fin.val g ≤ p.j := by simpa only [shape, indexDegree_eq] using hB.2.1
  let w : Fin 4 → ℕ := Pi.single 3 1
  have h₃ : W w g ≤ p.t := by simpa only [w, shape, weightedTotalDegree_piSingle] using hB.2.2
  have hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + 1 := by
    intro i
    fin_cases i <;> decide
  have hw : ∀ i, w i ≤ 1 := by
    intro i
    fin_cases i <;> decide
  have hw3 : w 3 = 1 := by decide
  have fits (P : Row 4) (hb' : W 1 P ≤ 1 + 2 * L * (p.b - 1))
      (hj' : W Fin.val P ≤ 2 * L * (p.j - 3) + L + 3)
      (ht' : W w P ≤ 2 * L * (p.t - 1) + L + 1) :
      GeoFits (toGeneric P) (chart L p) := by
    apply toGeneric_fits
    refine ⟨?_, ?_, ?_⟩
    · change P.totalDegree ≤ max _ _
      exact (by simpa only [weightedTotalDegree_one] using hb' :
        P.totalDegree ≤ 1 + 2 * L * (p.b - 1)).trans (le_max_left _ _)
    · change indexDegree P ≤ _
      rwa [indexDegree_eq]
    · change P.degreeOf 3 ≤ min _ _
      apply le_min
      · simpa only [w, weightedTotalDegree_piSingle] using ht'
      · have h := (top_le_index P).trans hj'
        omega
  constructor
  · apply fits
    · exact (denominator_bound L _ h₁).trans (Nat.le_add_left _ _)
    · exact (denominator_bound L _ h₂).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    · have h := denominator_bound L w h₃
      rw [hw3] at h
      exact h.trans (by omega)
  · intro n hn
    apply fits
    · have h := numerator_bound hn 1 0 1 (fun _ => by simp) (fun _ => le_rfl) hb h₁
      change W 1 (coefficientNumerator L g n) ≤ 1 + 2 * L * (p.b - 1) + L * 0 at h
      simpa only [mul_zero, add_zero] using h
    · have h := numerator_bound hn Fin.val 1 3 (fun _ => by rfl)
        (fun j : Fin 4 => Nat.le_of_lt_succ j.isLt) hj h₂
      change W Fin.val (coefficientNumerator L g n) ≤ 3 + 2 * L * (p.j - 3) + L * 1 at h
      simpa only [mul_one, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
    · have hwle : w 3 ≤ p.t := hw3.symm ▸ ht
      have h := numerator_bound hn w 1 1 hshift hw hwle h₃
      simpa only [hw3, mul_one, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
theorem coefficients_recover (L : ℕ) (g : Row 4) (S : (Polynomial Geom))
    (hg : atJet g S = 0) (hr : RegularAt g S) :
    evalGeneric S (toGeneric (denominator L g)) ≠ 0 ∧
      ∀ n ≤ L, n < K1.p →
        evalGeneric S (toGeneric (coefficientNumerator L g n)) =
          evalGeneric S (toGeneric (denominator L g)) * genericCoeffs (hasseDeriv n S) := by
  have hp : atJet (separant g) S ≠ 0 := hr
  have hden : atJet (denominator L g) S = atJet (separant g) S ^ (2 * L) :=
    map_pow (MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))) _ _
  constructor
  · rw [evalGeneric_toGeneric]
    apply (map_ne_zero_iff _ genericCoeffs_injective).mpr
    rw [hden]
    exact pow_ne_zero _ hp
  · intro n hn hc
    rw [evalGeneric_toGeneric, evalGeneric_toGeneric, ← map_mul]
    apply congrArg genericCoeffs
    unfold coefficientNumerator
    split_ifs
    · unfold atJet
      rw [map_mul, MvPolynomial.eval_X, mul_comm]
      rfl
    · let E := MvPolynomial.eval (jet S : Fin 4 → (Polynomial Geom))
      change E (_ * (_ ^ _ * _)) = _
      rw [map_mul, map_mul, map_pow, MvPolynomial.eval_C]
      change _ * (atJet (separant g) S ^ (2 * (L - n)) * atJet (jetNumerator g n) S) = _
      rw [eval_jetNumerator _ _ hg, ordinary_eq_hasse]
      have hinv : Polynomial.C (↑n.factorial : Geom)⁻¹ * Polynomial.C (↑n.factorial : Geom) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ (factorial_cast_ne_zero hc), map_one]
      have hpow : 2 * (L - n) + 2 * n = 2 * L := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hn]
      calc
        _ = (Polynomial.C (↑n.factorial : Geom)⁻¹ * Polynomial.C (↑n.factorial : Geom)) *
            ((atJet (separant g) S ^ (2 * (L - n)) * atJet (separant g) S ^ (2 * n)) *
              hasseDeriv n S) := by ring
        _ = _ := by rw [hinv, one_mul, ← pow_add, hpow, hden]
end
end P0_9_7_3_2
end

end Merged_PortLow7

-- merged module GoldBranch6N6
section Merged_GoldBranch6N6
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_6_6
noncomputable section
open Polynomial
open P3 (K)
open P3_6 ( physicalDegree primaryBox  taylorLength TrueWeightLE)
open K1_13 (Geom Row Shape shape extend InBox OnFactor OrderAt chart mixed32)
open K1_13_6 (HighChart toGeneric markIdeal separant jetNumerator divisorIdeal cycleLength)
def membershipTest (g : Row 4) : Row 4 := jetNumerator g taylorLength
def nextTest (g : Row 4) : Row 4 := jetNumerator g (taylorLength + 1)
end
end P3_6_6
end
section
namespace P3_6_6
noncomputable section
open Polynomial
open P3 (K)
open P3_6 (physicalPrice primaryBox surfaceNumerator32 taylorLength)
open K1_13 (Row Shape Geom extend atJet shape ceilDiv)
open K1_13_6 (Pieces toGeneric
  separant jetNumerator HighMark divisorIdeal cycleLength eval_jetNumerator)
open K1_13_6_1 (mem_markIdeal mark_curve)
open scoped BigOperators
end
end P3_6_6
end
section
namespace P3_6_6_2
noncomputable section
open Polynomial
open P3 (K)
open P3_6 (physicalDegree primaryBox taylorLength)
open P3_6_6 (membershipTest nextTest)
open K1_13 (Row Shape Geom shape extend chart liftedChart mixed32)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength CanonicalChart
  Invariant separant divisorIdeal partialFlow)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint Box4 Box5 graphBox)
open scoped BigOperators
structure Branch (f Q : Row 4) (l : ℕ) where
  surface : Ideal GeoJets
  r : ℕ
  base : (intersectionIdeal f Q).IsMinimalPrime surface
  high : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface base.isPrime
  chart : CanonicalChart f surface r
  invariant : Invariant ((separant^[r]) f) surface
  proper : toGeneric (membershipTest ((separant^[r]) f)) ∉ surface
  curve : Ideal GeoJets
  divisor : (divisorIdeal surface (membershipTest ((separant^[r]) f))).IsMinimalPrime curve
  regularCurve : toGeneric (separant ((separant^[r]) f)) ∉ curve
  terminal :
    cycleLength (divisorIdeal surface (membershipTest ((separant^[r]) f))) curve
      divisor.isPrime ≠ 1 ∨ toGeneric (nextTest ((separant^[r]) f)) ∉ curve
namespace Branch
variable {f Q : Row 4} {l : ℕ} (b : Branch f Q l)
def g : Row 4 := (separant^[b.r]) f
def sigma : GeoJets := toGeneric (separant b.g)
def graph : GeoJets5 :=
  MvPolynomial.rename Fin.castSucc (toGeneric (partialFlow b.g)) +
    MvPolynomial.C (4 : GeoField) * MvPolynomial.rename Fin.castSucc b.sigma *
      MvPolynomial.X (Fin.last 4)
abbrev Local := Localization.Away b.sigma
def localMap : GeoJets →+* b.Local := algebraMap GeoJets b.Local
def onGraph : GeoJets5 →+* b.Local :=
  MvPolynomial.eval₂Hom (b.localMap.comp MvPolynomial.C)
    (Fin.lastCases
      (b.localMap (MvPolynomial.C (-(4 : GeoField)⁻¹) * toGeneric (partialFlow b.g)) *
        IsLocalization.Away.invSelf b.sigma)
      (fun i => b.localMap (MvPolynomial.X i)))
end Branch
end
end P3_6_6_2
end
section
namespace P3_6_6_2
noncomputable section
open Polynomial
open P3_6 (physicalDegree)
open K1_13 (Geom Row Shape shape InBox atJet jet indexDegree)
open K1_13_1 (indexDegree_eq)
open K1_13_6 (GeoJets GenericField GeoField genericCoeffs toGeneric separant)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint)
open scoped BigOperators
namespace Branch
variable {f Q : Row 4} {l : ℕ}
end Branch
end
end P3_6_6_2
end
section
namespace P3_6_6_2
noncomputable section
open Polynomial MvPolynomial
open P3 (K)
open P3_6 (physicalDegree  taylorLength)
open K1_13 (Row Shape Geom InBox embed extend shape chart atJet jet)
open K1_13_6 (GeoJets GeoField GenericField genericCoeffs evalGeneric toGeneric
  separant jetNumerator eval_jetNumerator)
open K1_13_6_2_1 (jet_fits oldBox_of_fits three_weights separant_pow_bound jet_bound)
open K1_13_7_1 (Chamber GeoFits shape_chamber weight_X_le weight_const_mul_le)
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
private abbrev TaylorIndex := Fin taylorLength
private structure TaylorChart where
  denom : GeoJets
  numerator : TaylorIndex → GeoJets
end
end P3_6_6_2
end
section
namespace P3_6_6_2_1
noncomputable section
open Polynomial MvPolynomial
open P3_6_6_2 (Branch )
open K1_13 (Geom Row Shape InBox shape indexDegree liftedChart)
open K1_13_1 (indexDegree_eq)
open K1_13_6 (GeoJets GeoField genericCoeffs toGeneric separant partialFlow jetNumerator)
open K1_13_6_2 (GeoJets5 Box5 graphBox)
open K1_13_6_2_2 (lift4 generic5 rawGraph numerator denominator padded)
open K1_13_6_2_2_2 (Chart incl S invS S_mul_invS negQuarter q constants W
  graphMap graphMap_lift graphMap_X_last)
open scoped BigOperators
open K1_13_6_2_2_2 (compare_numerators)
open K1_13_6_2_2_1 (support_bounds topWeight fifthWeight box_of_weights)
variable {f Q : Row 4} {l : ℕ}
@[simp] theorem onGraph_C (b : Branch f Q l) (a : GeoField) :
    b.onGraph (MvPolynomial.C a) = b.localMap (MvPolynomial.C a) := by
  simp [Branch.onGraph]
private def toBranch (b : Branch f Q l) : Chart b.g →+* b.Local :=
  IsLocalization.Away.lift (separant b.g)
    (g := b.localMap.comp (MvPolynomial.map genericCoeffs))
    (IsLocalization.Away.algebraMap_isUnit b.sigma)
@[simp] private theorem toBranch_incl (b : Branch f Q l) (P : Row 4) :
    toBranch b (incl b.g P) = b.localMap (toGeneric P) :=
  IsLocalization.Away.lift_eq _ _ _
local notation "wtDegree" => MvPolynomial.weightedTotalDegree
end
end P3_6_6_2_1
end
section
namespace P3_6_6_2_3
noncomputable section
open P3_6 (primaryBox taylorLength)
open P3_6_6_2 (Branch)
open K1_13 (Shape liftedChart)
open K1_13_6 (GeoJets)
open K1_13_6_2 (GeoJets5 graphBox)
open K1_13_6_2_4 (Boxes)
end
end P3_6_6_2_3
end
section
namespace P3_6_6_2_3
noncomputable section
open P3_6_6_2 (Branch)
open K1_13_6 (GeoJets)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (oldEmbedding)
end
end P3_6_6_2_3
end
section
namespace P3_6_6_2_3_2
noncomputable section
open P3_6_6 (membershipTest)
open P3_6_6_2 (Branch)
open K1_13_6 (GeoField GeoJets toGeneric partialFlow divisorIdeal cycleLength)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_3 (localWeight weight_cast weight_pos)
open K1_13_6_2_4 (OfDim LengthAt sectionIdeal oldEmbedding)
open K1_13_6_2_4_5 (four_ne_zero)
open K1_13_6_2_4_5 (length_le_of_surjection dim_after_proper_cut)
local notation "memberDiv" b => divisorIdeal (Branch.surface b) (membershipTest (Branch.g b))
end
end P3_6_6_2_3_2
end
section
set_option autoImplicit false
namespace P3_6_6_3
noncomputable section
open K1_13 (Row)
open K1_13_6 (toGeneric divisorIdeal cycleLength)
open K1_13_6_3 (CoeffIdeal JetIdeal)
open P3_6_6 (membershipTest nextTest)
end
end P3_6_6_3
end
section
set_option autoImplicit false
namespace P3_6_6_3
noncomputable section
open K1_13 K1_13_6
open K1_13_6_3 (JetIdeal)
open K1_13_6_3_1
attribute [local instance] MvPolynomial.algebraMvPolynomial
open P0_9_6_3 (flat_sepToGeo map_eq_maximal_of_length_one step_in_sep sep_sq_dvd_jet nonvanishing_of_simple_cut stable_of_simple_cut)
end
end P3_6_6_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1600
namespace P3_6_6_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_5 K1_13_6_3_5_3 MvPolynomial
open scoped Polynomial WithZero
attribute [local instance] MvPolynomial.gradedAlgebra
open K1_13_6_3_5_3 (tupleHeight_le_of_inclusion finsum_weighted cone_eval_jets jet_zero_nonzero)
end
end P3_6_6_3_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace P3_6_6_3_2
noncomputable section
open MvPolynomial K1_13_6 K1_13_6_3 K1_13_6_3_5
attribute [local instance] MvPolynomial.gradedAlgebra
end
end P3_6_6_3_2
end

end Merged_GoldBranch6N6

-- merged module GoldBranch6N7
section Merged_GoldBranch6N7
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_6_7
noncomputable section
open K1_13 (Shape chart ceilDiv mixed32 Row)
open K1_13_7 (LowerPoint pointIdeal pairIdeal tripleIdeal localColength)
open P3_6 (commonBox resultantBox fatOrder divisorOrder isolatedOrder taylorLength
  linearChart incidenceGap physicalDegree)
def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
end
end P3_6_7
end
section
namespace P3_6_7_2
noncomputable section
open Polynomial
open K1_13 (Geom Row Shape InBox shape mixed32 atJet)
open K1_13_6 (GeoJets toGeneric separant cycleLength intersectionIdeal Invariant)
open K1_13_7 (LowerCaps genericRow)
open K1_13_7_2 (evalTrajectory LiftedSurface lowerFlow liftLower)
open P3_6 (taylorLength physicalDegree)
open P3_6_7 (fatChart )
structure FatTaylor (f : Row 4) where
  denom : Row 4
  numer : Fin taylorLength → Row 4
  test : Row 4
  denom_box : InBox (shape denom) (fatChart (shape f))
  numer_box : ∀ i, InBox (shape (numer i)) (fatChart (shape f))
  test_box : InBox (shape test) (fatChart (shape f))
  test_iff : ∀ (surface : Ideal GeoJets), surface.IsPrime → toGeneric f ∈ surface →
    toGeneric (separant f) ∉ surface →
    (toGeneric test ∈ surface ↔ toGeneric (P3_6_6.membershipTest f) ∈ surface)
  recovers : ∀ (L : Type) [Field L] [Algebra Geom L] (S : (Polynomial L)),
    S.natDegree ≤ physicalDegree → evalTrajectory f S = 0 →
    evalTrajectory (separant f) S ≠ 0 →
    evalTrajectory denom S ≠ 0 ∧ evalTrajectory test S = 0 ∧
      ∀ i, evalTrajectory (numer i) S = evalTrajectory denom S * C (S.coeff i.val)
end
end P3_6_7_2
end
section
namespace P3_6_7_2
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_6
open K1_13_7_2_2 (stride raw topLinear denominator numerator hasseNumerator)
open K1_13_7_1 (weight_const_mul_le top_le_index shape_chamber Chamber)
open K1_13_1 (indexDegree_eq)
open K1_13_7_2_2 (raw_false raw_true_compare)
open K1_13_7_2_2 (raw_bound sep_pow_bound)
open K1_13_7_2_2 (specializes topLinear_regular)
local notation "W" => MvPolynomial.weightedTotalDegree
end
end P3_6_7_2
end
section
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
namespace P3_6_7_2_2
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_6_3 K1_13_7
open K1_13_7_2_4 K1_13_7_2_4_2
open P3_6 (physicalDegree )
open K1_13_7_2_4_2 (intDerivation coeffDeriv coeffDeriv_zero_of_shift zero_of_stationary_eval rowTrajectory rowTrajectory_stationary eval_chartTrajectory)
open K1_13_7_2_4 (sum_monomial_eq_of_coeffs)
open K1_13_7_2_4 (trajectory_at_component component_ne_zero)
end
end P3_6_7_2_2
end
section
set_option autoImplicit false
namespace P3_6_7_2_3
noncomputable section
open Polynomial MvPolynomial
open K1_13 (Geom Row)
open K1_13_6 (GeoField GeoJets toGeneric separant)
open K1_13_6_3 (JetIdeal dimension geomConstants genericArgument)
open P3_6 (taylorLength)
open P3_6_7_2 ( FatTaylor)
end
end P3_6_7_2_3
end
section
namespace P3_6_7_3
noncomputable section
open Polynomial MvPolynomial K1 K1_13 K1_13_6 K1_13_7 K1_13_7_1 K1_13_7_5
open K1_13_1 (indexDegree_eq)
open P3_6 (physicalDegree)
section
open K1_13_7_5_2 (denominator)
open P0_9_7_3_1 (numerator numerator_bound denominator_bound coefficients_recover)
local notation "W" => MvPolynomial.weightedTotalDegree
end
section
open K1_13_7_1 (denominator)
open P0_9_7_3_2 (coefficientNumerator coefficients_fit coefficients_recover)
end
end
end P3_6_7_3
end

end Merged_GoldBranch6N7

-- merged module LowerBase
section Merged_LowerBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_6
noncomputable section
open Polynomial
open P1 (I K k node agreement)
open K1_13 (Geom embed extend Row Shape shape InBox atJet OnFactor OrderAt indexDegree
  chart liftedChart mixed32 ceilDiv)
open scoped BigOperators
inductive Bank where
  | primary
  | secondary
  deriving DecidableEq
structure FatEquations where
  common : Row 3
  residual : Row 3
  common_ne : common ≠ 0
  residual_ne : residual ≠ 0
  common_total : common.totalDegree ≤ 3284
  common_index : indexDegree common ≤ 1120
  residual_total : residual.totalDegree ≤ 409200000
  residual_index : indexDegree residual ≤ 129000000
end
end P1_6
end
section
namespace P1_6
noncomputable section
open Polynomial
open P1 (K I k node AnchorModel AnchoredFamily)
open K1_13 (Geom embed extend atJet PoleData)
open scoped BigOperators
end
end P1_6
end

end Merged_LowerBase

-- merged module UpperBranch8
section Merged_UpperBranch8
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_8
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P1 (K I node agreement)
open K1_14_6 (occupancy)
open P0_10 (incidence_arithmetic)
end
end P1_7_8
end
section
set_option autoImplicit false
namespace P1_7_8
noncomputable section
open Polynomial Finset
open P1 (K I Words AnchorModel AnchoredFamily p node agreement blockLength)
open P1_7 (Reduced AdjacentChart regularRoot degreeAt quotientOrder singularDegree)
open K1_14 (L FX Seeds Equation SeedBound liftPoly atMark seedEmbedding)
open K1_14_4 (seedDegree)
open K1_14_6 (Biform)
open K1_14_6_1 (Dx flatten cleared separant markEval)
open scoped BigOperators
structure Input where
  words : Words
  deleted : Finset I
  model : AnchorModel words deleted
  labels : Finset K
  family : AnchoredFamily model labels
  shift_out : model.shift ∉ labels
  block : (Polynomial L)
  chart : AdjacentChart model family block
  marks : Finset K
  marks_sub : marks ⊆ labels
  f : Equation
  regular : ∀ γ ∈ marks, regularRoot f (model.label γ) (family.scalar γ)
  reduced : Reduced f
  sheets : 3 ≤ f.natDegree
  seed_pos : 0 < seedDegree f
  v : ℕ
  seed_bound : SeedBound f v
  lo : ℕ
  hi : ℕ
  lower : lo ≤ model.overhead.toNat
  upper : model.overhead.toNat ≤ hi
  positive : 0 < model.overhead.toNat
  quotient_pos : 0 < quotientOrder model.overhead.toNat
  agreement_gap : degreeAt hi < agreement
  factorial_guard : degreeAt hi + 1 < p
  separant_guard : singularDegree f.natDegree v < p
  flat_guard : f.natDegree * degreeAt hi + v < p
abbrev Input.w (J : Input) : ℕ := J.model.overhead.toNat
abbrev Input.ell (J : Input) : ℕ := quotientOrder J.w
abbrev Input.e (J : Input) : ℕ := J.f.natDegree
def Input.secondBlock (J : Input) : (Polynomial L) := J.block.map (frobenius L p)
def Input.blockProduct (J : Input) : (Polynomial L) := J.block * J.secondBlock
abbrev SeedConstants := MvPolynomial (Fin 2) L
def residueData (_J : Input) (i : Fin 2) (g : (Polynomial K)) : (Polynomial SeedConstants) :=
  ((liftPoly g).map (if i = 0 then RingHom.id L else frobenius L p)).map MvPolynomial.C
def blockAt (J : Input) (i : Fin 2) : (Polynomial L) :=
  if i = 0 then J.block else J.secondBlock
def residueDenominator (J : Input) (i : Fin 2) : (Polynomial SeedConstants) :=
  residueData J i (J.model.factor * J.model.A₀) +
    C (MvPolynomial.X i) * residueData J i (J.model.factor * J.model.A₁)
def evalSeedConstants (z : K) : SeedConstants →+* L :=
  MvPolynomial.eval ![algebraMap K L z, (algebraMap K L z)^p]
structure ResidueLift (J : Input) where
  denominator : SeedConstants
  numerator : (Polynomial SeedConstants)
  denominator_ne : denominator ≠ 0
  denominator_degree : denominator.totalDegree ≤ 2 * J.w
  numerator_degree : ∀ j, (numerator.coeff j).totalDegree ≤ 2 * J.w
  numerator_width : numerator.natDegree < 2 * J.w
  congruences : ∀ i : Fin 2, (blockAt J i).map MvPolynomial.C ∣
    residueDenominator J i * numerator +
      C (MvPolynomial.X i * denominator) * residueData J i J.model.Q
  unit_at_marks : ∀ γ ∈ J.labels, evalSeedConstants (J.model.label γ) denominator ≠ 0
def constantAbscissa : L →+* FX :=
  (algebraMap (Polynomial L) FX).comp Polynomial.C
def liftSeeds : SeedConstants →+* Seeds := MvPolynomial.map constantAbscissa
def seedBiform : SeedConstants →+* Biform :=
  (MvPolynomial.rename (R := FX) (some : Fin 2 → Option (Fin 2))).toRingHom.comp liftSeeds
def center : FX := algebraMap (Polynomial L) FX Polynomial.X
def liftTaylor (P : (Polynomial SeedConstants)) (i : ℕ) : Biform :=
  (Polynomial.taylor (MvPolynomial.C center) (P.map seedBiform)).coeff i
def inverseBlockCoeff (J : Input) (i : ℕ) : FX :=
  (i.factorial : FX)⁻¹ *
    (Dx^[i]) ((algebraMap (Polynomial L) FX J.blockProduct)⁻¹)
def ordinateTaylorNum (f : Equation) (r : ℕ) : ℕ → Biform
  | 0 => separant (flatten f) ^ (2*r-1) * MvPolynomial.X none
  | i + 1 => MvPolynomial.C (((i+1).factorial : FX)⁻¹) *
      (separant (flatten f) ^ ((2*r-1)-(2*i+1)) * cleared (flatten f) i)
def quotientNumerator (J : Input) (B : ResidueLift J) (r : ℕ) : Biform :=
  ∑ i ∈ range (r+1), MvPolynomial.C (inverseBlockCoeff J (r-i)) *
    (seedBiform B.denominator * ordinateTaylorNum J.f r i -
      separant (flatten J.f) ^ (2*r-1) * liftTaylor B.numerator i)
def quotientDenominator (J : Input) (B : ResidueLift J) (r : ℕ) : Biform :=
  seedBiform B.denominator * separant (flatten J.f) ^ (2*r-1)
def cutoff (J : Input) (B : ResidueLift J) : Equation :=
  MvPolynomial.optionEquivLeft FX (Fin 2) (quotientNumerator J B (J.ell+1))
abbrev SeedField := FractionRing Seeds
def generic (q : Equation) : (Polynomial SeedField) := q.map (algebraMap Seeds SeedField)
def rootOn (J : Input) (q : Equation) (γ : K) : Prop :=
  atMark q (J.model.label γ) (J.family.scalar γ) = 0
structure Factors (J : Input) (B : ResidueLift J) where
  proper : Equation
  count : ℕ
  flat : Fin count → Equation
  product : J.f = proper * ∏ j, flat j
  cutoff_at_marks : ∀ γ ∈ J.marks, rootOn J (cutoff J B) γ
  proper_coprime : IsCoprime (generic proper) (generic (cutoff J B))
  flat_reduced : ∀ j, Reduced (flat j)
  flat_irred : ∀ j, Irreducible (generic (flat j))
  flat_cutoff : ∀ j, generic (flat j) ∣ generic (cutoff J B)
  sheets : count ≤ J.e
  degree_each : ∀ j, (flat j).natDegree ≤ J.e
  seed_sum : ∑ j, seedDegree (flat j) ≤ J.v
structure ProperCurve (J : Input) (B : ResidueLift J) (D : Factors J B) where
  prime : Ideal Equation
  isPrime : prime.IsPrime
  onProper : D.proper ∈ prime
  onCutoff : cutoff J B ∈ prime
  marks : Finset K
  sub : marks ⊆ J.marks
  liesOn : ∀ γ ∈ marks, prime ≤ RingHom.ker
    (eval₂RingHom (K1_14.graphEval (J.model.label γ)) (K1_14.atX (J.family.scalar γ)))
  persistent : Finset I
  hits : ∀ γ ∈ marks, ∀ x ∈ persistent, (J.family.scalar γ).eval (node x) = J.model.word x
  fiber : ℕ
  tangent : ℕ
  seed : ℕ
  positive_seed : 0 < seed
  sections : ∀ x ∉ persistent,
    let r := J.ell - persistent.card
    (marks.filter fun γ => (J.family.scalar γ).eval (node x) = J.model.word x).card ≤
      (1 + (J.e-3)*r)*fiber + r*tangent + (r*J.v + 2*J.w)*seed
def cutVelocity (J : Input) : ℕ := quotientOrder J.lo + 1
def cutOrdinate (J : Input) : ℕ := 1 + cutVelocity J * (J.e-1)
def cutSeed (J : Input) : ℕ := cutVelocity J * J.v + 2*J.hi
structure ProperCover (J : Input) (B : ResidueLift J) (D : Factors J B) where
  count : ℕ
  curves : Fin count → ProperCurve J B D
  covers : ∀ γ ∈ J.marks, rootOn J D.proper γ → ∃ j, γ ∈ (curves j).marks
  fiber : ∑ j, (curves j).fiber ≤ J.v*cutSeed J + J.v^2*cutVelocity J
  tangent : ∑ j, (curves j).tangent ≤ 2*J.e*J.v*cutSeed J + J.v^2*cutOrdinate J
  seed : ∑ j, (curves j).seed ≤
    J.e*cutSeed J + J.v*((2*J.e-2)*cutVelocity J + cutOrdinate J)
abbrev SeedClosure := AlgebraicClosure SeedField
def intoSeedClosure : Seeds →+* SeedClosure :=
  (algebraMap SeedField SeedClosure).comp (algebraMap Seeds SeedField)
def genericPoint (y : SeedClosure) : Biform →+* SeedClosure :=
  (eval₂RingHom intoSeedClosure y).comp (MvPolynomial.optionEquivLeft FX (Fin 2)).toRingHom
def liftConstantSeeds : SeedConstants →+* SeedClosure :=
  intoSeedClosure.comp liftSeeds
def reconstructed (J : Input) (B : ResidueLift J) (y : SeedClosure) : (Polynomial SeedClosure) :=
  let ζ := intoSeedClosure (MvPolynomial.C center)
  let ev := genericPoint y
  C ((liftConstantSeeds B.denominator)⁻¹) * B.numerator.map liftConstantSeeds +
    J.blockProduct.map (liftConstantSeeds.comp MvPolynomial.C) *
      ∑ j ∈ range (J.ell+1),
        C (ev (quotientNumerator J B j) / ev (quotientDenominator J B j)) *
          (Polynomial.X - C ζ)^j
def genericRoots (q : Equation) : Finset SeedClosure := by
  classical
  exact (q.map intoSeedClosure).roots.toFinset
structure DifferentialProduct (J : Input) (B : ResidueLift J) (q : Equation) where
  numerator : Polynomial (Polynomial Seeds)
  denominator : Seeds
  denominator_ne : denominator ≠ 0
  leading : numerator.coeff q.natDegree = C denominator
  abscissa_width : ∀ j, (numerator.coeff j).natDegree ≤ q.natDegree * degreeAt J.hi
  numerator_constant : ∀ i j m, Dx (((numerator.coeff i).coeff j).coeff m) = 0
  denominator_constant : ∀ m, Dx (denominator.coeff m) = 0
  identity :
    numerator.map (Polynomial.mapRingHom intoSeedClosure) =
      C (C (intoSeedClosure denominator)) *
        ∏ y ∈ genericRoots q,
          (Polynomial.X - C (reconstructed J B y))
end
end P1_7_8
end
section
set_option autoImplicit false
namespace P1_7_8
noncomputable section
open P1 (agreement blockLength)
open P1_7 (degreeAt quotientOrder     ceilRatio )
end
end P1_7_8
end
section
set_option autoImplicit false
namespace P1_7_8_3
noncomputable section
open P1 (K I node)
open P1_7_8 (Input ResidueLift Factors)
open K1_14 (FX Equation Seeds atX graphEval seedEmbedding)
open K1_14_6_1 (Dx partialX flatten)
open Polynomial (eval₂RingHom)
abbrev JetRing := Polynomial Equation
instance jetCommRing : CommRing JetRing := @AddMonoidAlgebra.commRing Equation ℕ inferInstance _
abbrev Degree := ℕ × ℕ × ℕ
def nefDegree (h t s : ℕ) : Degree := (h + 2*t, t, s)
abbrev CoxVar := Fin 2 ⊕ (Fin 2 ⊕ Fin 3)
abbrev Cox := MvPolynomial CoxVar FX
def coxWeight : CoxVar → Degree
  | .inl _ => (1, 0, 0)
  | .inr (.inl i) => (2*i.val, 1, 0)
  | .inr (.inr _) => (0, 0, 1)
def ordinate : JetRing := Polynomial.C Polynomial.X
def seedVar (i : Fin 2) : JetRing :=
  Polynomial.C (Polynomial.C (MvPolynomial.X i))
def affineCoord : CoxVar → JetRing
  | .inl i => if i = 0 then 1 else ordinate
  | .inr (.inl i) => if i = 0 then 1 else Polynomial.X
  | .inr (.inr i) => if hi : i.val < 2 then seedVar ⟨i.val, hi⟩ else 1
def dehom : Cox →ₐ[FX] JetRing := MvPolynomial.aeval affineCoord
structure RelativeSection (Q : Ideal JetRing) (d : Degree) where
  order : ℕ
  finiteChart : Cox
  inverseChart : Cox
  finite_degree :
    finiteChart.IsWeightedHomogeneous coxWeight (d + order • (1, 0, 0))
  inverse_degree :
    inverseChart.IsWeightedHomogeneous coxWeight (d + order • (1, 0, 0))
  glue : ordinate ^ order * dehom finiteChart - dehom inverseChart ∈ Q
def RelativeSection.affine {Q : Ideal JetRing} {d : Degree}
    (S : RelativeSection Q d) : JetRing :=
  dehom S.finiteChart
def gradedPiece (Q : Ideal JetRing) (d : Degree) : Submodule FX (JetRing ⧸ Q) :=
  (MvPolynomial.weightedHomogeneousSubmodule FX coxWeight d).map
    (((Ideal.Quotient.mkₐ FX Q).comp dehom).toLinearMap)
structure CurveProbe (Q : Ideal JetRing) where
  fiber : ℕ
  tangent : ℕ
  seed : ℕ
  offset : ℤ
  threshold : ℕ
  hilbert : ∀ h t s, threshold ≤ h → threshold ≤ t → threshold ≤ s →
    (Module.finrank FX (gradedPiece Q (nefDegree h t s)) : ℤ) =
      (h*fiber + t*tangent + s*seed : ℕ) + offset
def markRoot (J : Input) (γ : K) : Equation →+* FX :=
  eval₂RingHom (graphEval (J.model.label γ)) (atX (J.family.scalar γ))
def markPoint (J : Input) (γ : K) : JetRing →ₐ[FX] FX where
  toRingHom := eval₂RingHom (markRoot J γ) (Dx (atX (J.family.scalar γ)))
  commutes' a := by
    change (eval₂RingHom (markRoot J γ) (Dx (atX (J.family.scalar γ))))
      (Polynomial.C (Polynomial.C (MvPolynomial.C a))) = a
    simp [markRoot, graphEval]
def tangentEquation (f : Equation) : JetRing :=
  Polynomial.C (MvPolynomial.optionEquivLeft FX (Fin 2) (partialX (flatten f))) +
    Polynomial.X * Polynomial.C f.derivative
def rootIdeal {J : Input} {B : ResidueLift J} (D : Factors J B) : Ideal JetRing :=
  Ideal.span {Polynomial.C D.proper}
def residueInJet {J : Input} (B : ResidueLift J) : JetRing :=
  Polynomial.C (Polynomial.C (P1_7_8.liftSeeds B.denominator))
def openFactor (J : Input) (B : ResidueLift J) : JetRing :=
  residueInJet B * Polynomial.C J.f.derivative
def saturate (Q : Ideal JetRing) (g : JetRing) : Ideal JetRing where
  carrier := {f | ∃ n : ℕ, g^n * f ∈ Q}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro f h ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m+n, ?_⟩
    rw [mul_add, pow_add]
    have hf : g^m * g^n * f = g^n * (g^m * f) := by ring
    have hh : g^m * g^n * h = g^m * (g^n * h) := by ring
    rw [hf, hh]
    exact Q.add_mem (Q.mul_mem_left _ hm) (Q.mul_mem_left _ hn)
  smul_mem' := by
    rintro a f ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change g^n * (a * f) ∈ Q
    rw [show g^n * (a*f) = a * (g^n*f) by ring]
    exact Q.mul_mem_left _ hn
def graphIdeal (J : Input) (B : ResidueLift J) (D : Factors J B) : Ideal JetRing :=
  saturate (Ideal.span {Polynomial.C D.proper, tangentEquation J.f}) (openFactor J B)
structure TangentSection (J : Input) {B : ResidueLift J} (D : Factors J B) where
  section_ : RelativeSection (rootIdeal D) (J.e, 1, J.v)
  affine_eq : section_.affine = tangentEquation J.f
def jetDegree (J : Input) (r : ℕ) : Degree :=
  nefDegree (1 + (J.e-3)*r) r (r*J.v + 2*J.w)
def jetDenominator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  residueInJet B * Polynomial.C J.f.derivative ^ (r-1)
def oldDenominator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  Polynomial.C
    (MvPolynomial.optionEquivLeft FX (Fin 2) (P1_7_8.quotientDenominator J B r))
def oldNumerator (J : Input) (B : ResidueLift J) (r : ℕ) : JetRing :=
  Polynomial.C
    (MvPolynomial.optionEquivLeft FX (Fin 2) (P1_7_8.quotientNumerator J B r))
structure TaylorSections (J : Input) (B : ResidueLift J) (D : Factors J B) (r : ℕ) where
  denominator : RelativeSection (graphIdeal J B D) (jetDegree J r)
  numerator : Fin (r+1) → RelativeSection (graphIdeal J B D) (jetDegree J r)
  den_eq : denominator.affine = jetDenominator J B r
  agrees : ∀ j : Fin (r+1),
    oldDenominator J B j.val * (numerator j).affine -
      oldNumerator J B j.val * denominator.affine ∈ graphIdeal J B D
structure CurveMarks (J : Input) (B : ResidueLift J) (D : Factors J B) where
  prime : Ideal JetRing
  isPrime : prime.IsPrime
  onGraph : graphIdeal J B D ≤ prime
  onCutoff : Polynomial.C (P1_7_8.cutoff J B) ∈ prime
  regular : openFactor J B ∉ prime
  marks : Finset K
  sub : marks ⊆ J.marks
  liesOn : ∀ γ ∈ marks, prime ≤ RingHom.ker (markPoint J γ).toRingHom
structure CurveSlice (J : Input) (B : ResidueLift J) (D : Factors J B)
    extends CurveMarks J B D where
  probe : CurveProbe prime
  positive_seed : 0 < probe.seed
open scoped BigOperators
structure MixedCover (J : Input) (B : ResidueLift J) (D : Factors J B) where
  count : ℕ
  curves : Fin count → CurveSlice J B D
  covers : ∀ γ ∈ J.marks, P1_7_8.rootOn J D.proper γ → ∃ j, γ ∈ (curves j).marks
  fiber : ∑ j, (curves j).probe.fiber ≤
    J.v*P1_7_8.cutSeed J + J.v^2*P1_7_8.cutVelocity J
  tangent : ∑ j, (curves j).probe.tangent ≤
    2*J.e*J.v*P1_7_8.cutSeed J + J.v^2*P1_7_8.cutOrdinate J
  seed : ∑ j, (curves j).probe.seed ≤
    J.e*P1_7_8.cutSeed J + J.v*((2*J.e-2)*P1_7_8.cutVelocity J + P1_7_8.cutOrdinate J)
structure NodeSections {J : Input} {B : ResidueLift J} {D : Factors J B}
    (C : CurveMarks J B D) where
  persistent : Finset I
  hits : ∀ γ ∈ C.marks, ∀ x ∈ persistent,
    (J.family.scalar γ).eval (node x) = J.model.word x
  cuts : ∀ x ∉ persistent,
    ∃ S : RelativeSection C.prime (jetDegree J (J.ell - persistent.card)),
      S.affine ∉ C.prime ∧
      ∀ γ ∈ C.marks, (J.family.scalar γ).eval (node x) = J.model.word x →
        markPoint J γ S.affine = 0
end
end P1_7_8_3
end

end Merged_UpperBranch8

-- merged module UpperBranch4
section Merged_UpperBranch4
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_4
noncomputable section
open Polynomial
open P1 (HighBand K p agreement blockLength AnchorModel AnchoredFamily)
open P1_7 (Stage stages terminal fullCutoff degreeAt  fees )
open K1_14 (Shape Jet Seeds FX Banks atX jetAt seedHasse graphEval)
open K1_14_2 (Ambient ODE OnJet)
open K1_14_2_2 (Active Fits FixedPart ODECaps fixedOn mass sectionDegree weight dot)
open K1_14_2_2_4 (pairCap residualShape highCap highScale)
open scoped BigOperators Classical
abbrev Mass := Fin 4 → ℚ
def massQ (S : Finset (Ideal Ambient)) : Mass := fun k => mass S k
def dotQ (a c : Mass) : ℚ := ∑ k, a k * c k
def capMin (a c : Mass) : Mass := fun k => min (a k) (c k)
def pairMinSeed (s t : Shape) : ℕ := min s.U t.U
def pairMinOrdinate (s t : Shape) : ℕ := min s.B t.B
def sharedBound (s t : Shape) (x z r m : ℕ) (square : Bool) (k : Fin 4) : ℚ :=
  let n := m + 1 - r
  let d := if square || (k == 3) then n^2 else n
  (highCap x z k : ℚ) / highScale r k +
    (pairCap (residualShape s x z) (residualShape t x z) k : ℚ) / d
def cornerBound (s t : Shape) (r m : ℕ) (square : Bool) (k : Fin 4) : ℚ :=
  let xs := [0, pairMinSeed s t]
  let zMax := pairMinOrdinate s t
  let zs := [0, zMax, min zMax (s.B-s.J), min zMax (t.B-t.J)]
  (xs.flatMap fun x => zs.map fun z => sharedBound s t x z r m square k).foldl max 0
def pairedCap (s t : Shape) (reserve : ℕ) (square : Bool) : Mass :=
  fun k =>
    let m := reserve+1
    (List.range m).foldl
      (fun a r => min a (cornerBound s t (r+1) m square k))
      (cornerBound s t 1 m square k)
def PairedMass : Prop :=
  ∀ (s t : Shape) (r : ℕ) (square : Bool) (P Q : Jet),
    0 < r → r < p → s.B < p → t.B < p → s.U < p → t.U < p →
    s.J ≤ s.B → t.J ≤ t.B → P ≠ 0 → Q ≠ 0 →
    K1_14_3.RowCaps P s → K1_14_3.RowCaps Q t → K1_14_3.NoMovingCommon P Q →
    ∀ (A : FixedPart P s) (B : FixedPart Q t) (S : Finset (Ideal Ambient)),
    (square = true → ∀ I ∈ S, K1_14_2_2.dual I) →
    (∀ I ∈ S, Active I ∧ K1_14_2_2R.chainCompatible P Q I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧
      K1_14_2_2.orderOn I P (r+1) ∧ K1_14_2_2.orderOn I Q (r+1)) →
    ∀ k, massQ S k ≤ pairedCap s t r square k
def stageAt (b : HighBand) (i : ℕ) : Stage :=
  ((stages b)[i]?).getD ⟨0, terminal b, terminal b⟩
theorem stage_mem {b : HighBand} {i : ℕ} (hi : i < (stages b).length) :
    stageAt b i ∈ stages b := by
  rw [stageAt, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi
def introIndices : HighBand → List ℕ
  | .h2370 | .h2390 | .h2420 | .h2440 => List.range' 1 11
  | .h2410 => List.range' 1 9 ++ [11]
  | .h2460 | .h2480 | .h2500 | .h2520 | .h2530 | .h2540 |
    .h2550 | .h2560 | .h2570 | .h2585 | .h2590 | .h2600 | .h2601 | .h2611 |
    .h2621 | .h2640 | .h2670 | .h2700 | .h2750 | .h2800 | .h2900 | .h2950 |
    .h2980 | .h3000 | .h3050 | .h3100 | .h3200 | .h3400 | .h3555 => List.range' 1 8
  | _ => []
def stopIndex : HighBand → ℕ
  | .h4000 => 2
  | .h4800 => 1
  | _ => 0
def degreeVector (s : Shape) : Fin 3 → ℕ := ![s.B, s.J, s.U]
def introWeight (s : Shape) (k : Fin 4) : Fin 3 → ℕ :=
  ![![s.J, s.B-s.J, 0], ![0, s.U, s.J], ![s.U, 0, s.B], ![0, 0, s.U]] k
def introJump (cap old : Fin 3 → ℕ) (s : Shape) (k : Fin 4) : ℕ :=
  ∑ j, (max (old j) (introWeight s k j) - old j) * cap j
def introAccount (b : HighBand) (k : Fin 4) :
    List ℕ → (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℕ
  | [], cap, old =>
    introJump cap old (stageAt b 0).moving.shape k +
      (![cap 0, cap 2, 2*cap 0*cap 2, cap 2 * cap 2] : Fin 4 → ℕ) k
  | i :: is, cap, old =>
    let s := stageAt b i
    let c := s.free.shape
    introJump cap old c k + introAccount b k is
      (fun j => min (cap j) (degreeVector c j / (s.reserve+1)))
      (fun j => max (old j) (introWeight c k j))
def initialCap (b : HighBand) (k : Fin 4) : ℕ :=
  let s := stageAt b 0
  if (introIndices b).isEmpty then
    (cornerBound s.free.shape s.moving.shape 1 1 false k).floor.toNat
  else introAccount b k (introIndices b) (degreeVector s.free.shape) (fun _ => 0)
def initialE (b : HighBand) : ℕ :=
  if (introIndices b).isEmpty then
    let s := stageAt b 0
    s.free.shape.U * s.moving.shape.U + (pairMinSeed s.free.shape s.moving.shape)^2
  else initialCap b 3
def stageCap (b : HighBand) (i : ℕ) (square : Bool) : Mass :=
  let s := stageAt b i
  pairedCap s.free.shape s.moving.shape s.reserve square
def history (b : HighBand) : ℕ → Mass
  | 0 => fun k => initialCap b k
  | i+1 => capMin (history b i) (stageCap b (i+1) (decide (stopIndex b ≤ i+1)))
def envelope (s : Stage) : Shape :=
  let a := s.free.shape
  let b := s.moving.shape
  let j := max a.J b.J
  ⟨0, max (a.B-a.J) (b.B-b.J) + j, j, max a.U b.U⟩
def running (v : ℕ → Mass) : ℕ → Mass
  | 0 => fun _ => 0
  | i+1 => fun k => max (running v i k) (v i k)
def weightedBill (n : ℕ) (v : ℕ → Mass) (hist : ℕ → Mass) : ℚ :=
  ∑ i ∈ Finset.range n, dotQ (fun k => running v (i+1) k - running v i k) (hist i)
def OnParent {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop := OnJet I (M.label γ) (F.scalar γ)
structure ODEGuard (B J : ℕ) : Prop where
  bmin : 2 ≤ B
  jpos : 0 < J
  jb : J ≤ B
  small : B < p
structure InitialCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (b : HighBand) (freeFixed movingFixed : ODE) where
  parents : Finset (Ideal Ambient)
  active : ∀ I ∈ parents, Active I
  height_two : ∀ I ∈ parents, I.height = 2
  mass_bound : Fits parents (initialCap b)
  seed : K1_14_3.SeedCover
  seed_le : seed.curve.totalDegree ≤ initialCap b 2
  seed_points : seed.points.card ≤ initialE b
  ordinates : Finset FX
  ordinate_le : ordinates.card ≤ initialCap b 0
  content : Seeds
  content_ne : content ≠ 0
  content_le : content.totalDegree ≤ (stageAt b 0).free.shape.U + (stageAt b 0).moving.shape.U
  covers : ∀ γ ∈ Γ, seed.Covers (M.label γ) ∨ atX (F.scalar γ) ∈ ordinates ∨
    graphEval (M.label γ) content = 0 ∨ K1_14_2.fixedAt freeFixed (F.scalar γ) = 0 ∨
    K1_14_2.fixedAt movingFixed (F.scalar γ) = 0 ∨ ∃ I ∈ parents, OnParent F I γ
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
namespace P1_7_4
noncomputable section
open P1 (HighBand)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass)
open scoped BigOperators Classical
theorem massQ_mono {S T : Finset (Ideal Ambient)} (h : S ⊆ T) (k : Fin 4) :
    massQ S k ≤ massQ T k := by
  exact (Nat.cast_le (α := ℚ)).mpr (K1_14_2_2.mass_mono h k)
theorem massQ_nonneg (S : Finset (Ideal Ambient)) (k : Fin 4) : 0 ≤ massQ S k :=
  Nat.cast_nonneg _
theorem massQ_split {S T : Finset (Ideal Ambient)} (h : T ⊆ S) (k : Fin 4) :
    massQ (S \ T) k + massQ T k = massQ S k := by
  unfold massQ
  exact_mod_cast (Finset.sum_sdiff h :
    mass (S \ T) k + mass T k = mass S k)
theorem dotQ_nonneg {v c : Mass} (hv : ∀ k, 0 ≤ v k) (hc : ∀ k, 0 ≤ c k) :
    0 ≤ dotQ v c :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hv k) (hc k)
theorem dotQ_mono_mass {v c d : Mass} (hv : ∀ k, 0 ≤ v k) (h : ∀ k, c k ≤ d k) :
    dotQ v c ≤ dotQ v d :=
  Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (hv k)
theorem dotQ_mono_weight {v w c : Mass} (hc : ∀ k, 0 ≤ c k) (h : ∀ k, v k ≤ w k) :
    dotQ v c ≤ dotQ w c :=
  Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (h k) (hc k)
theorem dotQ_scale_add (a h : ℚ) (v w x : Mass) :
    a * dotQ v x + h * dotQ w x = dotQ (fun k => a*v k + h*w k) x := by
  simp only [dotQ, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring
private theorem running_nonneg (v : ℕ → Mass) (i : ℕ) (k : Fin 4) :
    0 ≤ running v i k := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact ih.trans (le_max_left _ _)
private theorem jump_nonneg (v : ℕ → Mass) (i : ℕ) (k : Fin 4) :
    0 ≤ running v (i+1) k - running v i k :=
  sub_nonneg.mpr (le_max_left _ _)
private theorem running_succ_dot (v : ℕ → Mass) (i : ℕ) (c : Mass) :
    dotQ (running v (i+1)) c = dotQ (running v i) c +
      dotQ (fun k => running v (i+1) k - running v i k) c := by
  unfold dotQ
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring
private theorem pay_one (v : ℕ → Mass) (hist : ℕ → Mass) (i : ℕ)
    {S T U : Finset (Ideal Ambient)} (hT : T ⊆ S) (hU : U ⊆ S \ T)
    (hcap : ∀ k, massQ S k ≤ hist i k) :
    dotQ (v i) (massQ U) + dotQ (running v (i+1)) (massQ T) ≤
      dotQ (running v i) (massQ S) +
        dotQ (fun k => running v (i+1) k - running v i k) (hist i) := by
  have hleft : dotQ (v i) (massQ U) ≤ dotQ (running v (i+1)) (massQ (S \ T)) :=
    (dotQ_mono_weight (massQ_nonneg U) (fun k => le_max_right _ _)).trans
      (dotQ_mono_mass (running_nonneg v (i+1)) (massQ_mono hU))
  have hsplit :
      dotQ (running v (i+1)) (massQ (S \ T)) + dotQ (running v (i+1)) (massQ T) =
        dotQ (running v (i+1)) (massQ S) := by
    unfold dotQ
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_add, massQ_split hT]
  calc
    _ ≤ _ := add_le_add hleft le_rfl
    _ = _ := hsplit
    _ = _ := running_succ_dot v i _
    _ ≤ _ := add_le_add le_rfl (dotQ_mono_mass (jump_nonneg v i) hcap)
/-- Unspent weight on the final components is available for their terminal count. -/
theorem bill_bound_with_final (n : ℕ) (v hist : ℕ → Mass)
    (live lost : ℕ → Finset (Ideal Ambient))
    (next : ∀ i < n, live (i+1) ⊆ live i)
    (fail : ∀ i < n, lost i ⊆ live i \ live (i+1))
    (cap : ∀ i < n, ∀ k, massQ (live i) k ≤ hist i k) :
    (∑ i ∈ Finset.range n, dotQ (v i) (massQ (lost i))) +
      dotQ (running v n) (massQ (live n)) ≤ weightedBill n v hist := by
  induction n with
  | zero => simp [running, dotQ, weightedBill]
  | succ n ih =>
    have old := ih (fun i hi => next i (by omega)) (fun i hi => fail i (by omega))
      (fun i hi => cap i (by omega))
    have step := pay_one v hist n (next n (by omega)) (fail n (by omega)) (cap n (by omega))
    unfold weightedBill at old ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

theorem final_credit_nonneg (n : ℕ) (v : ℕ → Mass) (S : Finset (Ideal Ambient)) :
    0 ≤ dotQ (running v n) (massQ S) :=
  dotQ_nonneg (running_nonneg v n) (massQ_nonneg S)

theorem bill_bound (n : ℕ) (v hist : ℕ → Mass)
    (live lost : ℕ → Finset (Ideal Ambient))
    (next : ∀ i < n, live (i+1) ⊆ live i)
    (fail : ∀ i < n, lost i ⊆ live i \ live (i+1))
    (cap : ∀ i < n, ∀ k, massQ (live i) k ≤ hist i k) :
    (∑ i ∈ Finset.range n, dotQ (v i) (massQ (lost i))) ≤ weightedBill n v hist := by
  have h := bill_bound_with_final n v hist live lost next fail cap
  exact (le_add_of_nonneg_right (dotQ_nonneg (running_nonneg v n) (massQ_nonneg _))).trans h
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
namespace P1_7_4
noncomputable section
open Polynomial
open P1 (HighBand AnchorModel AnchoredFamily K p agreement)
open P1_7 (Stage    stages terminal fullCutoff buffered )
open K1_14 (Shape Banks Jet Equation jetAt seedHasse seedEmbedding)
open K1_14_2 (Ambient OnJet jetMarkHom toJet eval_toJet CoordinateRing SeedField
  JetSeedSection JetYSection ODE)
open K1_14_2_2 (Active dual orderOn FixedPart ODECaps fixedOn RowCaps CutCover
  sectionDegree weight dot joinCuts joinCuts_cost sum_dot emptyCut mass)
open K1_14_2_2_3
open K1_14_2_2_7
open K1_14_2_2_3 (specialize_shiftedWord shift_word)
open K1_14_2_2_7 (seed_value_eq)
open K1_14_2_2_5 (parent_caps)
open scoped BigOperators Classical
abbrev StageIndex (b : HighBand) := Fin (stages b).length
def pairAt {b h rows} (pairs : P1_7.Pairs b h rows) (i : StageIndex b) :
    P1_7.BufferedPair h rows (stageAt b i) :=
  pairs _ (stage_mem i.isLt)
structure FixedRows {b h rows} (pairs : P1_7.Pairs b h rows) (i : StageIndex b) where
  free : FixedPart (pairAt pairs i).free (stageAt b i).free.shape
  moving : FixedPart (pairAt pairs i).moving (stageAt b i).moving.shape
theorem rank_equation (S : Finset (Ideal Ambient))
    (hS : ∀ I ∈ S, Active I ∧ ¬ dual I) {B J : ℕ}
    (hord : mass S 1 ≤ J) (hmix : mass S 2 ≤ B) :
    ∃ G : ODE, ODECaps G B J ∧ ∀ I ∈ S, fixedOn G I := by
  have hchoose (I : Ideal Ambient) :
      ∃ G : ODE, I ∈ S → ODECaps G (sectionDegree I 2) (sectionDegree I 1) ∧ fixedOn G I := by
    by_cases hI : I ∈ S
    · obtain ⟨G, hg⟩ := parent_caps K1_14_2_2_5_1.proof K1_14_2_2_5_2.proof
        (hS I hI).1 (hS I hI).2
      exact ⟨G, fun _ => hg⟩
    · exact ⟨1, fun h => (hI h).elim⟩
  choose G hG using hchoose
  have hp := K1_14_2_2_5.product_caps S G (fun I => sectionDegree I 2)
    (fun I => sectionDegree I 1) (fun I hI => (hG I hI).1)
  exact ⟨∏ I ∈ S, G I, ⟨hp.1, hp.2.1.trans hord, fun j i h => (hp.2.2 j i h).trans hmix⟩,
    fun I hI => K1_14_2_2_5.product_fixedOn hI G (hG I hI).2⟩
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace P1_7_4
noncomputable section
open Polynomial
open P1 (HighBand AnchorModel AnchoredFamily K p)
open K1_14 (Seeds graphEval)
open K1_14_2 (Ambient OnJet SeedField RootSeedSection)
open K1_14_2_2 (CutCover CurveGeometry)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength
  yLength)
open K1_14_2_3 (on_root on_seed moving_graph_count seed_graph_count equal_image_degree union_card_le)
open scoped BigOperators Classical
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1500000
namespace P1_7_4
noncomputable section
open Polynomial
open P1 (HighBand K p AnchorModel AnchoredFamily)
open P1_7 ( stages terminal   PrefixBooks PrefixInventory fees)
open K1_14 (Jet Banks seedHasse jetAt atX graphEval)
open K1_14_2 (Ambient ODE fixedAt)
open K1_14_2_2 (FixedPart ODECaps fixedOn dual)
open K1_14_3 (SeedCover Surface RowCaps NoMovingCommon)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open scoped BigOperators Classical
def c2 : Prop := PairedMass
end
end P1_7_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace P1_7_4_2
noncomputable section
open P1 (p)
open P1_7_4 (massQ sharedBound)
open K1_14 (Jet Shape)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 K1_14_2_2_4 Polynomial
open scoped Classical
open K1_14_2_2_4 (cancel_fixed)
open K1_14_2_2_4_1 (factor_caps)
private theorem cancellation : K1_14_2_2_4.c3 :=
  K1_14_2_2_4_3.of_children K1_14_2_2_4_3_1.proof K1_14_2_2_4_3_2.proof
theorem sections : K1_14_2_2_4.c5 :=
  K1_14_2_2_4_5.of_children K1_14_2_2_4_5_1.proof K1_14_2_2_4_5_2.proof
    K1_14_2_2_4_5_3.proof K1_14_2_2_4_5_4.proof K1_14_2_2_4_5_5.proof
private theorem scaled_le_div {d m c : ℕ} (hd : 0 < d) (h : d * m ≤ c) :
    (m : ℚ) ≤ (c : ℚ) / (d : ℚ) := by
  apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℚ) < (d : ℚ))).mpr
  rw [mul_comm]
  exact_mod_cast h
private theorem paired_stage {s t : Shape} {P Q : Jet} {A : FixedPart P s} {B : FixedPart Q t}
    (G : P0_10R_2.SharedGcd A B) (S : Finset (Ideal Ambient)) (square : Bool)
    (m r : ℕ) (k : Fin 4) (hr : 0 < r) (hrm : r ≤ m)
    (hx : seedDegree G.ordinary < p) (hz : G.ordinary.natDegree < p)
    (hdual : square = true → ∀ I ∈ S, dual I)
    (hpass : ∀ I ∈ S, Active I ∧ K1_14_2_2R.chainCompatible P Q I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧ orderOn I P m ∧ orderOn I Q m) :
    massQ S k ≤ sharedBound s t (seedDegree G.ordinary) G.ordinary.natDegree r m square k := by
  let x := seedDegree G.ordinary
  let z := G.ordinary.natDegree
  let n := m + 1 - r
  let d := if square || (k == 3) then n^2 else n
  have hn : 0 < n := by dsimp [n]; omega
  have hd : 0 < d := by
    unfold d
    split
    · exact Nat.pow_pos hn
    · exact hn
  have hg : 0 < highScale r k := by
    fin_cases k <;> first | exact hr | exact Nat.pow_pos hr
  have hh : highScale r k * mass (S.filter (HighOn G.ordinary r)) k ≤ highCap x z k := by
    apply K1_14_2_2R.high_graph_mass K1_14_2_2_4_4.proof sections G.ordinary P Q
      _ r G.ordinary_ne hz hr
    · refine ⟨fixedIncl A.equation * G.left, G.left_factor.trans ?_⟩
      ring
    · refine ⟨fixedIncl B.equation * G.right, G.right_factor.trans ?_⟩
      ring
    intro I hI
    obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hI
    exact ⟨(hpass I hm).1, (hpass I hm).2.1, hf⟩
  have hl : d * mass (S.filter fun I => ¬ HighOn G.ordinary r I) k ≤
      pairCap (residualShape s x z) (residualShape t x z) k := by
    apply sections G.left G.right _ _ _ k d G.left_ne G.right_ne G.relativelyPrime
      (min_le_right _ _) (min_le_right _ _) G.left_caps G.right_caps hd
    intro I hI
    obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hI
    obtain ⟨ha, _, hA, hB, hP, hQ⟩ := hpass I hm
    rw [G.left_factor] at hP
    rw [G.right_factor] at hQ
    have hlP := cancellation G.ordinary G.left I m r G.ordinary_ne hx hz ha hr hrm hf
      (cancel_fixed ha.prime _ _ m hA hP)
    have hlQ := cancellation G.ordinary G.right I m r G.ordinary_ne hx hz ha hr hrm hf
      (cancel_fixed ha.prime _ _ m hB hQ)
    have hlen := K1_14_2_2_4_4.proof G.left G.right I ha n hn hlP hlQ
    refine ⟨ha, fun hdegree => ?_⟩
    by_cases hIdual : dual I
    · rw [ite_eq_left hIdual] at hlen
      apply le_trans _ hlen
      apply Nat.cast_le.mpr
      unfold d
      split
      · exact le_rfl
      · simpa only [pow_two, mul_one] using Nat.mul_le_mul_left n (show 1 ≤ n by omega)
    · have hs : square = false := Bool.eq_false_iff.mpr fun he => hIdual (hdual he I hm)
      have hk : k ≠ 3 := fun he => hIdual (show 0 < sectionDegree I 3 by
        rw [← he]
        exact Nat.pos_of_ne_zero hdegree)
      simpa [d, hs, hk, hIdual] using hlen
  have hadd : mass (S.filter (HighOn G.ordinary r)) k +
      mass (S.filter fun I => ¬ HighOn G.ordinary r I) k = mass S k :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  change (mass S k : ℚ) ≤ (highCap x z k : ℚ) / highScale r k +
    (pairCap (residualShape s x z) (residualShape t x z) k : ℚ) / d
  rw [← hadd, Nat.cast_add]
  exact add_le_add (scaled_le_div hg hh) (scaled_le_div hd hl)
theorem paired_thresholds (s t : Shape) (m : ℕ) (square : Bool) (P Q : Jet)
    (hsB : s.B < p) (hsU : s.U < p) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hPs : RowCaps P s) (hQt : RowCaps Q t) (hno : K1_14_3.NoMovingCommon P Q)
    (A : FixedPart P s) (B : FixedPart Q t) (S : Finset (Ideal Ambient))
    (hdual : square = true → ∀ I ∈ S, dual I)
    (hpass : ∀ I ∈ S, Active I ∧ K1_14_2_2R.chainCompatible P Q I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧ orderOn I P m ∧ orderOn I Q m) :
    ∃ x ≤ P1_7_4.pairMinSeed s t, ∃ z ≤ P1_7_4.pairMinOrdinate s t,
      ∀ r, 0 < r → r ≤ m → ∀ k, massQ S k ≤ sharedBound s t x z r m square k := by
  obtain ⟨G⟩ := P0_10R_2.sharedGcd A B hP hQ hPs hQt hno
  obtain ⟨hU, hB, _⟩ := factor_caps hQ G.ordinary_ne hQt G.right_factor
  refine ⟨seedDegree G.ordinary, le_min G.seed_le hU, G.ordinary.natDegree,
    le_min G.ordinate_le hB, ?_⟩
  intro r hr hrm k
  exact paired_stage G S square m r k hr hrm (G.seed_le.trans_lt hsU)
    (G.ordinate_le.trans_lt hsB) hdual hpass
end
end P1_7_4_2
end
section
set_option maxHeartbeats 1000000
namespace P1_7_4_2
noncomputable section
open P1_7_4 (pairMinSeed pairMinOrdinate cornerBound sharedBound)
open K1_14 (Shape)
open K1_14_2_2_4 (highCap highScale pairCap residualShape)
private theorem at_endpoints {F : ℕ → ℚ} {l x u : ℕ} {a b c M : ℚ}
    (hl : l ≤ x) (hu : x ≤ u) (ha : 0 ≤ a)
    (hF : ∀ y, l ≤ y → y ≤ u → F y = a * (y : ℚ)^2 + b * (y : ℚ) + c)
    (hL : F l ≤ M) (hU : F u ≤ M) : F x ≤ M := by
  have hl' : (l : ℚ) ≤ x := by exact_mod_cast hl
  have hu' : (x : ℚ) ≤ u := by exact_mod_cast hu
  have hchord := mul_nonneg ha (mul_nonneg (sub_nonneg.mpr hl') (sub_nonneg.mpr hu'))
  rw [hF x hl hu]
  rw [hF l le_rfl (hl.trans hu)] at hL
  rw [hF u (hl.trans hu) le_rfl] at hU
  by_cases hs : 0 ≤ a * ((l : ℚ) + u) + b
  · have h := mul_nonneg hs (sub_nonneg.mpr hu')
    linarith only [hU, hchord, h]
  · have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) (sub_nonneg.mpr hl')
    linarith only [hL, hchord, h]
private def sectionBound (s t : Shape) (a b : ℚ) (k : Fin 4) (x z : ℕ) : ℚ :=
  a * (highCap x z k : ℚ) + b * (pairCap (residualShape s x z) (residualShape t x z) k : ℚ)
private theorem cast_trapezoid (B C J E : ℕ) (hJ : J ≤ B) :
    ((B * E + C * J - J * E : ℕ) : ℚ) =
      (B : ℚ) * E + (C : ℚ) * J - (J : ℚ) * E := by
  have h := (Nat.mul_le_mul_right E hJ).trans (Nat.le_add_right (B * E) (C * J))
  simp only [Nat.cast_sub h, Nat.cast_add, Nat.cast_mul]
private theorem seed_endpoints (s t : Shape) {a b M : ℚ} (hb : 0 ≤ b)
    {x z : ℕ} (hz : z ≤ pairMinOrdinate s t) (hsJ : s.J ≤ s.B) (htJ : t.J ≤ t.B)
    (h0 : sectionBound s t a b 0 0 0 ≤ M)
    (hZ : sectionBound s t a b 0 0 (pairMinOrdinate s t) ≤ M)
    (hC : sectionBound s t a b 0 0 (min (s.B-s.J) (t.B-t.J)) ≤ M) :
    sectionBound s t a b 0 x z ≤ M := by
  let C := min (s.B-s.J) (t.B-t.J)
  let limit := pairMinOrdinate s t
  let F (y : ℕ) := sectionBound s t a b 0 0 y
  have hcS : C ≤ s.B-s.J := min_le_left _ _
  have hcT : C ≤ t.B-t.J := min_le_right _ _
  change F z ≤ M
  by_cases hlow : z ≤ C
  · refine at_endpoints (F := F) (l := 0) (u := C) (a := 0)
      (b := a - b * ((s.J : ℚ) + t.J))
      (c := b * ((s.B : ℚ) * t.J + (t.B : ℚ) * s.J - (s.J : ℚ) * t.J))
      (Nat.zero_le z) hlow le_rfl ?_ h0 hC
    intro y _ hy
    have hsj : s.J ≤ s.B-y := by omega
    have htj : t.J ≤ t.B-y := by omega
    change a * (y : ℚ) + b * (((s.B-y) * min t.J (t.B-y) +
      (t.B-y) * min s.J (s.B-y) - min s.J (s.B-y) * min t.J (t.B-y) : ℕ) : ℚ) = _
    rw [min_eq_left hsj, min_eq_left htj, cast_trapezoid _ _ _ _ hsj,
      Nat.cast_sub (show y ≤ s.B by omega), Nat.cast_sub (show y ≤ t.B by omega)]
    ring
  · refine at_endpoints (F := F) (l := C) (u := limit) (a := b)
      (b := a - b * ((s.B : ℚ) + t.B)) (c := b * (s.B : ℚ) * t.B)
      (by omega) hz hb ?_ hC hZ
    intro y hy hyZ
    have hyS := hyZ.trans (min_le_left s.B t.B)
    have hyT := hyZ.trans (min_le_right s.B t.B)
    change a * (y : ℚ) + b * (((s.B-y) * min t.J (t.B-y) +
      (t.B-y) * min s.J (s.B-y) - min s.J (s.B-y) * min t.J (t.B-y) : ℕ) : ℚ) = _
    rw [cast_trapezoid _ _ _ _ (min_le_right _ _)]
    rcases min_choice (s.B-s.J) (t.B-t.J) with hc | hc
    · have hj : s.B-y ≤ s.J := by change min (s.B-s.J) (t.B-t.J) ≤ y at hy; omega
      rw [min_eq_right hj, Nat.cast_sub hyS, Nat.cast_sub hyT]
      ring
    · have hj : t.B-y ≤ t.J := by change min (s.B-s.J) (t.B-t.J) ≤ y at hy; omega
      rw [min_eq_right hj, Nat.cast_sub hyS, Nat.cast_sub hyT]
      ring
private theorem ordinate_endpoints (s t : Shape) {a b M : ℚ} (hb : 0 ≤ b)
    {x z : ℕ} (hx : x ≤ pairMinSeed s t) (hsJ : s.J ≤ s.B) (htJ : t.J ≤ t.B)
    (h0 : sectionBound s t a b 1 0 0 ≤ M)
    (hX : sectionBound s t a b 1 (pairMinSeed s t) 0 ≤ M) :
    sectionBound s t a b 1 x z ≤ M := by
  have hmono : sectionBound s t a b 1 x z ≤ sectionBound s t a b 1 x 0 := by
    change a * (x : ℚ) + b * (((s.U-x) * min t.J (t.B-z) +
      (t.U-x) * min s.J (s.B-z) : ℕ) : ℚ) ≤ a * (x : ℚ) +
      b * (((s.U-x) * min t.J (t.B-0) + (t.U-x) * min s.J (s.B-0) : ℕ) : ℚ)
    simp only [Nat.sub_zero, min_eq_left hsJ, min_eq_left htJ]
    apply add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hb)
    exact_mod_cast Nat.add_le_add (Nat.mul_le_mul_left _ (min_le_left _ _))
      (Nat.mul_le_mul_left _ (min_le_left _ _))
  apply hmono.trans
  refine at_endpoints (F := fun y => sectionBound s t a b 1 y 0)
    (l := 0) (u := pairMinSeed s t) (a := 0)
    (b := a - b * ((t.J : ℚ) + s.J)) (c := b * ((s.U : ℚ) * t.J + (t.U : ℚ) * s.J))
    (Nat.zero_le x) hx le_rfl ?_ h0 hX
  intro y _ hy
  change a * (y : ℚ) + b * (((s.U-y) * min t.J (t.B-0) +
    (t.U-y) * min s.J (s.B-0) : ℕ) : ℚ) = _
  simp only [Nat.sub_zero, min_eq_left hsJ, min_eq_left htJ, Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub (hy.trans (min_le_left s.U t.U)),
    Nat.cast_sub (hy.trans (min_le_right s.U t.U))]
  ring
private theorem mixed_endpoints (s t : Shape) {a b M : ℚ} {x z : ℕ}
    (hx : x ≤ pairMinSeed s t) (hz : z ≤ pairMinOrdinate s t)
    (hC : ∀ y, (y = 0 ∨ y = pairMinSeed s t) → ∀ w,
      (w = 0 ∨ w = pairMinOrdinate s t) → sectionBound s t a b 2 y w ≤ M) :
    sectionBound s t a b 2 x z ≤ M := by
  have hform (y w : ℕ) (hy : y ≤ pairMinSeed s t) (hw : w ≤ pairMinOrdinate s t) :
      sectionBound s t a b 2 y w =
        a * (2 * (y : ℚ) * (w : ℚ)) +
          b * (((s.U : ℚ)-y) * ((t.B : ℚ)-w) + ((t.U : ℚ)-y) * ((s.B : ℚ)-w)) := by
    change a * ((2*y*w : ℕ) : ℚ) +
      b * (((s.U-y) * (t.B-w) + (t.U-y) * (s.B-w) : ℕ) : ℚ) = _
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_sub (hy.trans (min_le_left s.U t.U)),
      Nat.cast_sub (hy.trans (min_le_right s.U t.U)),
      Nat.cast_sub (hw.trans (min_le_left s.B t.B)),
      Nat.cast_sub (hw.trans (min_le_right s.B t.B))]
  have hxCorner (y : ℕ) (hy : y = 0 ∨ y = pairMinSeed s t) :
      sectionBound s t a b 2 y z ≤ M := by
    have hy' : y ≤ pairMinSeed s t := hy.elim (fun h => h ▸ Nat.zero_le _) (fun h => h ▸ le_rfl)
    refine at_endpoints (F := sectionBound s t a b 2 y)
      (l := 0) (u := pairMinOrdinate s t) (a := 0)
      (b := 2 * a * y - b * (((s.U : ℚ)-y) + ((t.U : ℚ)-y)))
      (c := b * (((s.U : ℚ)-y) * t.B + ((t.U : ℚ)-y) * s.B))
      (Nat.zero_le z) hz le_rfl ?_ (hC y hy 0 (Or.inl rfl)) (hC y hy _ (Or.inr rfl))
    intro w _ hw
    rw [hform y w hy' hw]
    ring
  refine at_endpoints (F := fun y => sectionBound s t a b 2 y z)
    (l := 0) (u := pairMinSeed s t) (a := 0)
    (b := 2 * a * z - b * (((t.B : ℚ)-z) + ((s.B : ℚ)-z)))
    (c := b * ((s.U : ℚ) * ((t.B : ℚ)-z) + (t.U : ℚ) * ((s.B : ℚ)-z)))
    (Nat.zero_le x) hx le_rfl ?_ (hxCorner 0 (Or.inl rfl)) (hxCorner _ (Or.inr rfl))
  intro y _ hy
  rw [hform y z hy hz]
  ring
private theorem jet_endpoints (s t : Shape) {a b M : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {x z : ℕ} (hx : x ≤ pairMinSeed s t)
    (h0 : sectionBound s t a b 3 0 0 ≤ M)
    (hX : sectionBound s t a b 3 (pairMinSeed s t) 0 ≤ M) :
    sectionBound s t a b 3 x z ≤ M := by
  change sectionBound s t a b 3 x 0 ≤ M
  refine at_endpoints (F := fun y => sectionBound s t a b 3 y 0)
    (l := 0) (u := pairMinSeed s t) (a := a+b)
    (b := -b * ((s.U : ℚ) + t.U)) (c := b * (s.U : ℚ) * t.U)
    (Nat.zero_le x) hx (add_nonneg ha hb) ?_ h0 hX
  intro y _ hy
  change a * ((y*y : ℕ) : ℚ) + b * (((s.U-y) * (t.U-y) : ℕ) : ℚ) = _
  simp only [Nat.cast_mul, Nat.cast_sub (hy.trans (min_le_left s.U t.U)),
    Nat.cast_sub (hy.trans (min_le_right s.U t.U))]
  ring
private theorem foldMax_ge {w : ℚ} (L : List ℚ) (init : ℚ)
    (h : w ≤ init ∨ w ∈ L) : w ≤ L.foldl max init := by
  induction L generalizing init with
  | nil => exact h.resolve_right List.not_mem_nil
  | cons v L ih =>
    apply ih
    rcases h with h | h
    · exact Or.inl (h.trans (le_max_left _ _))
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl (le_max_right _ _)
      · exact Or.inr h
private def ordinateCorners (s t : Shape) : List ℕ :=
  [0, pairMinOrdinate s t, min (pairMinOrdinate s t) (s.B-s.J),
    min (pairMinOrdinate s t) (t.B-t.J)]
private theorem first_break_mem (s t : Shape) :
    min (s.B-s.J) (t.B-t.J) ∈ ordinateCorners s t := by
  let c := min (s.B-s.J) (t.B-t.J)
  have hc : c ≤ pairMinOrdinate s t :=
    le_min ((min_le_left _ _).trans (Nat.sub_le ..)) ((min_le_right _ _).trans (Nat.sub_le ..))
  rcases min_choice (s.B-s.J) (t.B-t.J) with h | h
  · have he := min_eq_right (show s.B-s.J ≤ pairMinOrdinate s t from h ▸ hc)
    simp [ordinateCorners, h, he]
  · have he := min_eq_right (show t.B-t.J ≤ pairMinOrdinate s t from h ▸ hc)
    simp [ordinateCorners, h, he]
theorem shared_le_corner (s t : Shape) {x z r m : ℕ} (square : Bool) (k : Fin 4)
    (hx : x ≤ pairMinSeed s t) (hz : z ≤ pairMinOrdinate s t)
    (hsJ : s.J ≤ s.B) (htJ : t.J ≤ t.B) :
    sharedBound s t x z r m square k ≤ cornerBound s t r m square k := by
  let a : ℚ := (highScale r k : ℚ)⁻¹
  let n := m + 1 - r
  let d := if square || (k == 3) then n^2 else n
  let b : ℚ := (d : ℚ)⁻¹
  have ha : 0 ≤ a := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hb : 0 ≤ b := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hEq (y w : ℕ) : sharedBound s t y w r m square k = sectionBound s t a b k y w := by
    simp only [sharedBound, sectionBound, a, b, d, n, div_eq_mul_inv, mul_comm]
  have hcorner (y w : ℕ) (hy : y = 0 ∨ y = pairMinSeed s t) (hw : w ∈ ordinateCorners s t) :
      sectionBound s t a b k y w ≤ cornerBound s t r m square k := by
    rw [← hEq]
    apply foldMax_ge
    refine Or.inr (List.mem_flatMap.mpr ⟨y, ?_, List.mem_map.mpr ⟨w, hw, rfl⟩⟩)
    exact hy.elim (fun h => by simp [h]) (fun h => by simp [h])
  rw [hEq]
  have h0 : 0 ∈ ordinateCorners s t := by simp [ordinateCorners]
  have hZ : pairMinOrdinate s t ∈ ordinateCorners s t := by simp [ordinateCorners]
  fin_cases k
  · exact seed_endpoints s t hb hz hsJ htJ (hcorner 0 0 (Or.inl rfl) h0)
      (hcorner 0 _ (Or.inl rfl) hZ) (hcorner 0 _ (Or.inl rfl) (first_break_mem s t))
  · exact ordinate_endpoints s t hb hx hsJ htJ (hcorner 0 0 (Or.inl rfl) h0)
      (hcorner _ 0 (Or.inr rfl) h0)
  · exact mixed_endpoints s t hx hz (fun y hy w hw =>
      hcorner y w hy (hw.elim (fun h => h ▸ h0) (fun h => h ▸ hZ)))
  · exact jet_endpoints s t ha hb hx (hcorner 0 0 (Or.inl rfl) h0)
      (hcorner _ 0 (Or.inr rfl) h0)
end
end P1_7_4_2
end
section
namespace P1_7_4_2
open P1_7_4 (pairedCap cornerBound)
private theorem le_foldMin (v : ℚ) (f : ℕ → ℚ) (L : List ℕ) (init : ℚ)
    (hi : v ≤ init) (h : ∀ j ∈ L, v ≤ f j) :
    v ≤ L.foldl (fun a j => min a (f j)) init := by
  induction L generalizing init with
  | nil => exact hi
  | cons j L ih =>
    exact ih _ (le_min hi (h j (List.mem_cons_self ..)))
      (fun i hii => h i (List.mem_cons_of_mem _ hii))
theorem proof : P1_7_4.c2 := by
  intro s t r square P Q _ _ hsB _ hsU _ hsJ htJ hP hQ hPs hQt hno A B S hdual hpass k
  let m := r + 1
  obtain ⟨x, hx, z, hz, ht⟩ :=
    paired_thresholds s t m square P Q hsB hsU hP hQ hPs hQt hno A B S hdual hpass
  have bound (j : ℕ) (hj : j < m) :
      P1_7_4.massQ S k ≤ cornerBound s t (j+1) m square k :=
    (ht (j+1) (Nat.succ_pos _) hj k).trans (shared_le_corner s t square k hx hz hsJ htJ)
  change _ ≤ pairedCap s t r square k
  unfold pairedCap
  exact le_foldMin _ _ _ _ (bound 0 (Nat.succ_pos _))
    (fun j hj => bound j (List.mem_range.mp hj))
end P1_7_4_2
end
section
namespace P1_7_4_1
noncomputable section
open P1 (HighBand K p AnchorModel AnchoredFamily)
open P1_7_4 (stageAt introIndices initialCap OnParent)
open K1_14 (Jet Shape Seeds FX graphEval seedHasse)
open K1_14_2 (Ambient CoordinateRing ODE OnJet fixedAt)
open K1_14_2_2 (Fits RowCaps)
open K1_14_2_2_2 (FiniteSections residualBudget afterGcd ordinaryBudget)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open scoped BigOperators
def SectionGeometry (S : Finset (Ideal Ambient)) : Prop :=
  ∀ I ∈ S, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ I.height = 2 ∧ FiniteSections I
structure AffineCover {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (b : HighBand) (G H : ODE) where
  components : Finset (Ideal Ambient)
  geometry : SectionGeometry components
  fits : Fits components (initialCap b)
  content : Seeds
  content_ne : content ≠ 0
  content_le : content.totalDegree ≤ (stageAt b 0).free.shape.U + (stageAt b 0).moving.shape.U
  covers : ∀ γ ∈ Γ, graphEval (M.label γ) content = 0 ∨
    fixedAt G (F.scalar γ) = 0 ∨ fixedAt H (F.scalar γ) = 0 ∨
      ∃ I ∈ components, OnParent F I γ
def factorDegree (D : Jet) : Fin 3 → ℕ :=
  ![jetDegree D, D.natDegree, seedDegree D]
def factorMass (D : Finset Jet) (j : Fin 3) : ℕ :=
  ∑ f ∈ D, factorDegree f j
def IntroHasse : Prop :=
  ∀ (s : Shape) (P : Jet), RowCaps P s →
    ∀ j a, RowCaps (seedHasse j a P) s
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
namespace P1_7_4_1
noncomputable section
open P1 (K p HighBand AnchorModel AnchoredFamily)
open P1_7_4 (stageAt initialCap initialE  InitialCover OnParent)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (SeedCover joinCovers joinCovers_degree joinCovers_points joinCovers_covers)
open scoped BigOperators Classical
open P0_10R_1 (section_bound seed_projection component_height ordinary_cover)
theorem proper_cover {P Q : Jet} (hp : ProperPair P Q) {s t : Shape}
    (hs : s.J ≤ s.B) (ht : t.J ≤ t.B) (hP : RowCaps P s) (hQ : RowCaps Q t) :
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧ Fits S (residualBudget s t) ∧
      ∀ z R, jetAt P z R = 0 → jetAt Q z R = 0 → ∃ I ∈ S, OnJet I z R := by
  obtain ⟨S, hS, hcover⟩ := K1_14_2_2_2_3.proof _ _ hp
  obtain ⟨hfinite, hfits⟩ := section_bound _ _ hp s t hs ht hP hQ S hS
  refine ⟨S, ?_, hfits, hcover⟩
  intro I hI
  obtain ⟨hprime, hdim, hrow, hcut⟩ := hS I hI
  exact ⟨hprime, hdim, component_height hp hprime hdim hrow hcut, hfinite I hI⟩
theorem ordinary_component_cover (f : Equation) (hi : Irreducible f)
    (hd : 0 < f.natDegree) (hp : f.natDegree < p) :
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧
      Fits S (ordinaryBudget (ordinarySeedDegree f) f.natDegree) ∧
      ∀ z R, atMark f z R = 0 → ∃ I ∈ S, OnJet I z R := by
  obtain ⟨S, hS, hf, hc⟩ := ordinary_cover f hi hd hp
  exact ⟨S, fun I hI => ⟨(hS I hI).1, (hS I hI).2.1, (hS I hI).2.2.1,
    (hS I hI).2.2.2.1⟩, hf, hc⟩
theorem collect {α : Type*} (D : Finset α)
    (budget : α → Fin 4 → ℕ) (T : α → K → (Polynomial K) → Prop)
    (h : ∀ d ∈ D, ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧ Fits S (budget d) ∧
      ∀ z R, T d z R → ∃ I ∈ S, OnJet I z R) :
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧ Fits S (fun k => ∑ d ∈ D, budget d k) ∧
      ∀ d ∈ D, ∀ z R, T d z R → ∃ I ∈ S, OnJet I z R := by
  classical
  let C (d : α) := if hd : d ∈ D then Classical.choose (h d hd) else ∅
  have hC (d : α) (hd : d ∈ D) :
      SectionGeometry (C d) ∧ Fits (C d) (budget d) ∧
      ∀ z R, T d z R → ∃ I ∈ C d, OnJet I z R := by
    simpa only [C, dite_eq_left hd] using Classical.choose_spec (h d hd)
  refine ⟨D.biUnion C, ?_, ?_, ?_⟩
  · intro I hI
    obtain ⟨d, hd, hi⟩ := Finset.mem_biUnion.mp hI
    exact (hC d hd).1 I hi
  · intro k
    exact (sum_biUnion_le D C (fun I => sectionDegree I k)).trans
      (Finset.sum_le_sum fun d hd => (hC d hd).2.1 k)
  · intro d hd z R hr
    obtain ⟨I, hI, hone⟩ := (hC d hd).2.2 z R hr
    exact ⟨I, Finset.mem_biUnion.mpr ⟨d, hd, hI⟩, hone⟩
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
namespace P1_7_4_1
noncomputable section
open P1 (K p)
open P1_7_4 (degreeVector)
open K1_14 K1_14_2 K1_14_2_2 K1_14_3_2 Polynomial UniqueFactorizationMonoid
open K1_14_2_2_2_1 (extractSeed rowCaps_iff jetDegree seedDegree seedDegree_le
  jetDegree_mul seedDegree_mul seedDegree_seed jetDegree_C)
open K1_14_2_1_1 (view exists_view_degree_pos view_seedHasse view_degree_le OtherSeed)
open K1_14_3_2_1 (seedToJet markEval_fixed markEval_seed)
open K1_14_3 (fixedEmbedding)
open scoped BigOperators Classical
open K1_14_2_2_2_1 (seedContent_cap divisor_caps)
open K1_14_2_2_2_1 (exists_fixedIncl)
open K1_14_2_1_1 (dvd_pow_of_dvd_hasse derivative_not_dvd)
structure Stripped {P : Jet} {s : Shape} (A : FixedPart P s) where
  content : Seeds
  row : Jet
  content_ne : content ≠ 0
  content_le : content.totalDegree ≤ s.U
  row_ne : row ≠ 0
  row_dvd : row ∣ P
  row_caps : RowCaps row s
  residual_eq : A.residual = C (C content) * row
  primitive : ∀ b : Seeds, C (C b) ∣ row → IsUnit b
  no_fixed : ∀ g : ODE, Irreducible (fixedIncl g) → ¬ fixedIncl g ∣ row
  covers : ∀ z S, jetAt P z S = 0 →
    graphEval z content = 0 ∨ fixedAt A.equation S = 0 ∨ jetAt row z S = 0
theorem strip {P : Jet} {s : Shape} (hP : P ≠ 0) (hc : RowCaps P s) (A : FixedPart P s) :
    Nonempty (Stripped A) := by
  have hr : A.residual ≠ 0 := fun hz => hP (by rw [A.factorization, hz, mul_zero])
  have hd : A.residual ∣ P := ⟨_, A.factorization.trans (mul_comm _ _)⟩
  obtain ⟨a, R, he, hprim⟩ := extractSeed A.residual hr
  have hm : (C (C a) * R : Jet) ≠ 0 := he ▸ hr
  have hR := (show R ∣ A.residual from ⟨_, he.trans (mul_comm _ _)⟩)
  refine ⟨⟨a, R, by simpa using left_ne_zero_of_mul hm,
    seedContent_cap hP hc ((show C (C a) ∣ A.residual from ⟨R, he⟩).trans hd),
    right_ne_zero_of_mul hm, hR.trans hd, divisor_caps hP hc (hR.trans hd),
    he, hprim, fun g hg hgR => A.stripped g hg (hgR.trans hR), ?_⟩⟩
  intro z S h
  have H := congrArg (markEval z S) (A.factorization.trans (congrArg (fixedIncl A.equation * ·) he))
  change markEval z S P = 0 at h
  rw [h, map_mul, map_mul] at H
  change 0 = markEval z S (fixedEmbedding A.equation) *
    (markEval z S (seedToJet a) * markEval z S R) at H
  rw [markEval_fixed, markEval_seed, eq_comm, mul_eq_zero, mul_eq_zero] at H
  rcases H with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
theorem factorDegree_add {P Q : Jet} (hP : P ≠ 0) (hQ : Q ≠ 0) (j : Fin 3) :
    factorDegree (P * Q) j = factorDegree P j + factorDegree Q j := by
  fin_cases j
  · exact jetDegree_mul hP hQ
  · exact natDegree_mul hP hQ
  · exact seedDegree_mul hP hQ
private theorem factorDegree_one (j : Fin 3) : factorDegree 1 j = 0 := by
  fin_cases j
  · exact jetDegree_C (1 : Equation) |>.trans natDegree_one
  · exact natDegree_one
  · exact seedDegree_seed (1 : Seeds) |>.trans MvPolynomial.totalDegree_one
theorem factorDegree_pow {P : Jet} (hP : P ≠ 0) (r : ℕ) (j : Fin 3) :
    factorDegree (P ^ r) j = r * factorDegree P j := by
  induction r with
  | zero => simp [factorDegree_one]
  | succ r ih =>
    rw [pow_succ, factorDegree_add (pow_ne_zero _ hP) hP, ih, Nat.succ_mul]
theorem factorDegree_prod {S : Finset Jet} {f : Jet → Jet} (hf : ∀ d ∈ S, f d ≠ 0) (j : Fin 3) :
    factorDegree (∏ d ∈ S, f d) j = ∑ d ∈ S, factorDegree (f d) j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [factorDegree_one]
  | insert d S hd ih =>
    have hS : ∀ e ∈ S, f e ≠ 0 := fun e he => hf e (Finset.mem_insert_of_mem he)
    rw [Finset.prod_insert hd, Finset.sum_insert hd,
      factorDegree_add (hf d (Finset.mem_insert_self _ _)) (Finset.prod_ne_zero_iff.mpr hS), ih hS]
theorem factorDegree_dvd {P Q : Jet} (hQ : Q ≠ 0) (hd : P ∣ Q) (j : Fin 3) :
    factorDegree P j ≤ factorDegree Q j := by
  obtain ⟨T, rfl⟩ := hd
  rw [factorDegree_add (left_ne_zero_of_mul hQ) (right_ne_zero_of_mul hQ)]
  exact Nat.le_add_right _ _
theorem caps_iff (P : Jet) (s : Shape) :
    RowCaps P s ↔ ∀ j, factorDegree P j ≤ degreeVector s j := by
  rw [rowCaps_iff]
  constructor
  · rintro ⟨hB, hJ, hU⟩ j
    fin_cases j <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2⟩
def ownShape (P : Jet) : Shape :=
  ⟨0, factorDegree P 0, factorDegree P 1, factorDegree P 2⟩
theorem own_caps (P : Jet) : RowCaps P (ownShape P) := by
  apply (caps_iff _ _).mpr
  intro j
  fin_cases j <;> exact le_rfl
theorem own_J_le_B {P : Jet} (hP : P ≠ 0) : (ownShape P).J ≤ (ownShape P).B := by
  have hc : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree ≠ 0 := by
    rw [coeff_natDegree, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP)
  exact (Nat.le_add_left _ _).trans ((own_caps P) _ _ hc).1
theorem factorMass_mono {D E : Finset Jet} (h : D ⊆ E) (j : Fin 3) :
    factorMass D j ≤ factorMass E j :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)
structure IntroFactors (P : Jet) (D : Finset Jet) : Prop where
  factors : ∀ f ∈ D, Irreducible f ∧ f ∣ P ∧ UsesSeed f ∧
    f ∉ Set.range seedToJet ∧ f ∉ Set.range fixedEmbedding
  pairwise : (D : Set Jet).Pairwise IsRelPrime
theorem IntroFactors.mono {P : Jet} {D E : Finset Jet} (h : IntroFactors P E) (he : D ⊆ E) :
    IntroFactors P D :=
  ⟨fun f hf => h.factors f (he hf), h.pairwise.mono he⟩
theorem initial_factors {P : Jet} {s : Shape} {A : FixedPart P s} (R : Stripped A) :
    ∃ D : Finset Jet, IntroFactors P D ∧ (∀ j, factorMass D j ≤ degreeVector s j) ∧
      ∀ z S, jetAt R.row z S = 0 → ∃ f ∈ D, jetAt f z S = 0 := by
  classical
  let _ : StrongNormalizationMonoid Jet := UniqueFactorizationMonoid.strongNormalizationMonoid
  let N := normalizedFactors R.row
  let D := N.toFinset
  have hmem (f : Jet) (hf : f ∈ D) : f ∈ N := Multiset.mem_toFinset.mp hf
  have hirr (f : Jet) (hf : f ∈ D) : Irreducible f :=
    irreducible_of_normalized_factor f (hmem f hf)
  have hdvd (f : Jet) (hf : f ∈ D) : f ∣ R.row := dvd_of_mem_normalizedFactors (hmem f hf)
  have hprod : (∏ f ∈ D, f) ∣ R.row :=
    (Multiset.toFinset_prod_dvd_prod N).trans (prod_normalizedFactors R.row_ne).dvd
  refine ⟨D, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro f hf
    have hfix : f ∉ Set.range fixedEmbedding := by
      rintro ⟨g, rfl⟩
      exact R.no_fixed g (hirr _ hf) (hdvd _ hf)
    have hseed : f ∉ Set.range seedToJet := by
      rintro ⟨a, rfl⟩
      exact (hirr _ hf).not_isUnit (isUnit_C.mpr (isUnit_C.mpr (R.primitive a (hdvd _ hf))))
    exact ⟨hirr f hf, (hdvd f hf).trans R.row_dvd,
      by_contra (fun h => hfix (by
        obtain ⟨g, hg⟩ := exists_fixedIncl f h
        exact ⟨g, hg.symm⟩)), hseed, hfix⟩
  · intro f hf g hg hne
    exact (hirr f hf).isRelPrime_iff_not_dvd.mpr fun hd =>
      hne (normalizedFactors_eq_of_dvd R.row f (hmem _ hf) g (hmem _ hg) hd)
  · intro j
    calc
      _ = factorDegree (∏ f ∈ D, id f) j :=
        (factorDegree_prod (f := id) (fun f hf => (hirr f hf).ne_zero) j).symm
      _ ≤ factorDegree R.row j := factorDegree_dvd R.row_ne hprod j
      _ ≤ _ := (caps_iff _ _).mp R.row_caps j
  · intro z S hz
    change markEval z S R.row = 0 at hz
    have hm := map_dvd (markEval z S) (prod_normalizedFactors R.row_ne).symm.dvd
    change markEval z S R.row ∣ markEval z S N.prod at hm
    rw [hz, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hm
    obtain ⟨f, hf, he⟩ := hm
    exact ⟨f, Multiset.mem_toFinset.mpr hf, he⟩
theorem hasse_power {D R : Jet} {s : Shape} (hi : Irreducible D) (hseed : UsesSeed D)
    (hR : R ≠ 0) (hcap : RowCaps R s) (hsmall : s.U < p) {e : ℕ}
    (hall : ∀ i a, a ≤ e → D ∣ seedHasse i a R) : D^(e+1) ∣ R := by
  obtain ⟨i, hpos⟩ := exists_view_degree_pos D hseed
  have hD : D ∣ R := by
    apply (map_dvd_iff (view i)).mp
    simpa only [view_seedHasse, hasseDeriv_zero'] using
      (map_dvd_iff (view i)).mpr (hall i 0 (Nat.zero_le _))
  have hbound : (view i D).natDegree < p :=
    ((natDegree_le_of_dvd ((map_dvd_iff (view i)).mpr hD)
      ((view i).map_ne_zero_iff.mpr hR)).trans
        (view_degree_le i R s.U ((seedDegree_le _ _).mp ((rowCaps_iff _ _).mp hcap).2.2))).trans_lt hsmall
  let : CharP FX p := charP_of_injective_ringHom seedEmbedding.injective p
  let : CharP OtherSeed p := charP_of_injective_ringHom (MvPolynomial.C_injective (Fin 1) FX) p
  have hirr : Irreducible (view i D) := (MulEquiv.irreducible_iff (view i)).mpr hi
  have hprime : Prime (view i D) := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  apply (map_dvd_iff (view i)).mp
  rw [map_pow]
  apply dvd_pow_of_dvd_hasse hprime (derivative_not_dvd _ hpos hbound)
  intro a ha
  rw [← view_seedHasse]
  exact (map_dvd_iff (view i)).mpr (hall i a (Nat.le_of_lt_succ ha))
theorem retained_mass {P R : Jet} {D : Finset Jet} (hD : IntroFactors P D)
    {s : Shape} (hR : R ≠ 0) (hcap : RowCaps R s) (hsmall : s.U < p)
    (e : ℕ) (hall : ∀ f ∈ D, ∀ i a, a ≤ e → f ∣ seedHasse i a R) (j : Fin 3) :
    factorMass D j ≤ degreeVector s j / (e+1) := by
  have hprod : (∏ f ∈ D, f^(e+1)) ∣ R := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro f hf g hg hne
      exact (hD.pairwise hf hg hne).pow_left.pow_right
    · intro f hf
      exact hasse_power (hD.factors f hf).1 (hD.factors f hf).2.2.1 hR hcap hsmall (hall f hf)
  apply (Nat.le_div_iff_mul_le (Nat.succ_pos e)).mpr
  rw [Nat.mul_comm, factorMass, Finset.mul_sum]
  calc
    _ = factorDegree (∏ f ∈ D, f^(e+1)) j := by
      rw [factorDegree_prod (fun f hf => pow_ne_zero _ (hD.factors f hf).1.ne_zero)]
      exact Finset.sum_congr rfl fun f hf =>
        (factorDegree_pow (hD.factors f hf).1.ne_zero _ j).symm
    _ ≤ factorDegree R j := factorDegree_dvd hR hprod j
    _ ≤ _ := (caps_iff _ _).mp hcap j
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace P1_7_4_1
noncomputable section
open P1_7_4 (introWeight introJump)
open K1_14 (Jet Shape)
open K1_14_2_2_2 (residualBudget ordinaryBudget)
open scoped BigOperators Classical
def factorTariff (s : Shape) (k : Fin 4) (f : Jet) : ℕ :=
  ∑ j, introWeight s k j * factorDegree f j
def weightedDegree (w : Fin 3 → ℕ) (D : Finset Jet) : ℕ :=
  ∑ j, w j * factorMass D j
theorem weighted_factors (w : Fin 3 → ℕ) (D : Finset Jet) :
    weightedDegree w D = ∑ f ∈ D, ∑ j, w j * factorDegree f j := by
  unfold weightedDegree factorMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
theorem residual_tariff (f : Jet) (s : Shape) (hs : s.J ≤ s.B) (k : Fin 4) :
    residualBudget (ownShape f) s k = factorTariff s k f := by
  fin_cases k
  · simp only [residualBudget, factorTariff, Fin.sum_univ_three, introWeight, ownShape]
    change factorDegree f 0*s.J + s.B*factorDegree f 1 - factorDegree f 1*s.J =
      s.J*factorDegree f 0 + (s.B-s.J)*factorDegree f 1 + 0*factorDegree f 2
    have hm := Nat.mul_le_mul_right (factorDegree f 1) hs
    rw [Nat.mul_comm (factorDegree f 1) s.J, Nat.add_sub_assoc hm, ← Nat.sub_mul]
    ring
  · change _ = ∑ j, introWeight s 1 j * factorDegree f j
    rw [Fin.sum_univ_three]
    change factorDegree f 2*s.J + s.U*factorDegree f 1 =
      0*factorDegree f 0 + s.U*factorDegree f 1 + s.J*factorDegree f 2
    ring
  · change _ = ∑ j, introWeight s 2 j * factorDegree f j
    rw [Fin.sum_univ_three]
    change factorDegree f 2*s.B + s.U*factorDegree f 0 =
      s.U*factorDegree f 0 + 0*factorDegree f 1 + s.B*factorDegree f 2
    ring
  · change _ = ∑ j, introWeight s 3 j * factorDegree f j
    rw [Fin.sum_univ_three]
    change factorDegree f 2*s.U = 0*factorDegree f 0 + 0*factorDegree f 1 + s.U*factorDegree f 2
    ring
theorem tariff_step {D T : Finset Jet} (hT : T ⊆ D) (cap old : Fin 3 → ℕ)
    (s : Shape) (k : Fin 4) (hcap : ∀ j, factorMass D j ≤ cap j) :
    (∑ f ∈ D \ T, factorTariff s k f) +
      weightedDegree (fun j => max (old j) (introWeight s k j)) T ≤
      weightedDegree old D + introJump cap old s k := by
  classical
  let w := fun j => max (old j) (introWeight s k j)
  have hadd (j : Fin 3) : old j + (w j-old j) = w j :=
    Nat.add_sub_of_le (le_max_left _ _)
  calc
    _ ≤ weightedDegree w (D \ T) + weightedDegree w T := by
      apply Nat.add_le_add_right
      rw [weighted_factors]
      exact Finset.sum_le_sum fun f _ =>
        Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (le_max_right _ _)
    _ = weightedDegree w D := by
      simp only [weighted_factors]
      exact Finset.sum_sdiff hT
    _ = weightedDegree old D + ∑ j, (w j-old j) * factorMass D j := by
      unfold weightedDegree
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [← Nat.add_mul, hadd]
    _ ≤ _ := Nat.add_le_add_left
      (Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ (hcap j)) _
theorem ordinary_charge (D : Finset Jet) (cap : Fin 3 → ℕ)
    (hcap : ∀ j, factorMass D j ≤ cap j) (k : Fin 4) :
    (∑ f ∈ D, ordinaryBudget (factorDegree f 2) (factorDegree f 0) k) ≤
      ordinaryBudget (cap 2) (cap 0) k := by
  fin_cases k
  · exact hcap 0
  · exact hcap 2
  · change (∑ f ∈ D, 2 * factorDegree f 2 * factorDegree f 0) ≤ 2 * cap 2 * cap 0
    calc
      _ ≤ ∑ f ∈ D, 2 * factorDegree f 2 * cap 0 := by
        exact Finset.sum_le_sum fun f hf => Nat.mul_le_mul_left _
          ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans (hcap 0))
      _ = (2 * factorMass D 2) * cap 0 := by rw [factorMass, Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hcap 2))
  · change (∑ f ∈ D, factorDegree f 2 * factorDegree f 2) ≤ cap 2 * cap 2
    calc
      _ ≤ ∑ f ∈ D, factorDegree f 2 * cap 2 := by
        exact Finset.sum_le_sum fun f hf => Nat.mul_le_mul_left _
          ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans (hcap 2))
      _ = factorMass D 2 * cap 2 := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ (hcap 2)
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1400000
namespace P1_7_4_1
noncomputable section
open P1 (K p HighBand AnchorModel AnchoredFamily)
open P1_7_4 (stageAt introIndices initialCap  introAccount introJump introWeight degreeVector)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (NoMovingCommon)
open K1_14_2_2_2_1 (jetDegree_C seedDegree_C)
open scoped BigOperators Classical
open K1_14_3_2_1 (ordinary_factor)
theorem irreducible_cut {f C : Jet} (hf : Irreducible f) (hd : ¬ f ∣ C) :
    ProperPair f C :=
  ⟨hf.ne_zero, fun h => hd (h ▸ dvd_zero _), fun _ hD hDf hDC =>
    hd ((hD.associated_of_dvd hf hDf).dvd'.trans hDC)⟩
theorem terminal_piece {P Q : Jet} {t : Shape} {D : Finset Jet}
    (hD : IntroFactors P D) (hnc : NoMovingCommon P Q)
    (hQc : RowCaps Q t) (hJB : t.J ≤ t.B) (hB : t.B < p) (hQ : Q ≠ 0)
    (f : Jet) (hf : f ∈ D) :
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧
      Fits S (fun k => factorTariff t k f + ordinaryBudget (factorDegree f 2) (factorDegree f 0) k) ∧
      ∀ z R, (jetAt f z R = 0 ∧ jetAt Q z R = 0) → ∃ I ∈ S, OnJet I z R := by
  obtain ⟨hi, hPf, _, hs, hfix⟩ := hD.factors f hf
  by_cases hd : f ∣ Q
  · have hv : f.natDegree = 0 := by
      by_contra h
      exact hfix (hnc f hi hPf hd (Nat.pos_of_ne_zero h))
    obtain ⟨hc, hirr, hpos⟩ := ordinary_factor hi hv hs
    have hdegrees : factorDegree f 0 = (f.coeff 0).natDegree ∧
        factorDegree f 2 = ordinarySeedDegree (f.coeff 0) :=
      ⟨(congrArg K1_14_2_2_2_1.jetDegree hc).symm.trans (jetDegree_C _),
       (congrArg K1_14_2_2_2_1.seedDegree hc).symm.trans (seedDegree_C _)⟩
    have hsmall : (f.coeff 0).natDegree < p := by
      rw [← hdegrees.1]
      exact ((factorDegree_dvd hQ hd 0).trans ((caps_iff _ _).mp hQc 0)).trans_lt hB
    obtain ⟨S, hG, hF, hC⟩ := ordinary_component_cover _ hirr hpos hsmall
    refine ⟨S, hG, fun k => (hF k).trans ?_, fun z R h => hC z R ?_⟩
    · rw [hdegrees.1, hdegrees.2]
      exact Nat.le_add_left _ _
    · have hz := h.1
      rw [← hc] at hz
      simpa [jetAt, atMark] using hz
  · obtain ⟨S, hG, hF, hC⟩ :=
      proper_cover (irreducible_cut hi hd) (own_J_le_B hi.ne_zero) hJB (own_caps f) hQc
    refine ⟨S, hG, fun k => (hF k).trans ?_, fun z R h => hC z R h.1 h.2⟩
    rw [residual_tariff f t hJB]
    exact Nat.le_add_right _ _
end
end P1_7_4_1
end
section
set_option backward.isDefEq.respectTransparency false
namespace P1_7_4_1
def c2 : Prop := IntroHasse
end P1_7_4_1
end
section
namespace P1_7_4_1_1
open K1_14 (Shape)
open K1_14_2_2_2 (afterGcd residualBudget ordinaryBudget)
open K1_14_2_2_4 (highCap highScale pairCap residualShape)
open P1_7_4 (sharedBound stageAt initialCap)
end P1_7_4_1_1
end
section
set_option backward.isDefEq.respectTransparency false
namespace P1_7_4_1_2
open K1_14 (FX Seeds Jet seedHasse)
open K1_14_1_3 (translation seedCoeff mapCoeffs mapCoeffs_coeff)
private theorem seedCoeff_totalDegree (i : Fin 2) (r : ℕ) (P : Seeds) :
    (seedCoeff i r P).totalDegree ≤ P.totalDegree := by
  classical
  let g : Fin 2 → MvPolynomial (Option (Fin 2)) FX :=
    fun j => MvPolynomial.X (some j) + if j = i then MvPolynomial.X none else 0
  let f : Seeds →ₐ[FX] MvPolynomial (Option (Fin 2)) FX := MvPolynomial.aeval g
  have htrans : translation i = (MvPolynomial.optionEquivLeft FX (Fin 2)).toAlgHom.comp f := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = i <;> simp [translation, f, g, hj]
  have hg (j : Fin 2) : (g j).totalDegree ≤ 1 := by
    by_cases hj : j = i
    · simpa [g, hj] using (MvPolynomial.totalDegree_add
        (MvPolynomial.X (some j) : MvPolynomial (Option (Fin 2)) FX)
        (MvPolynomial.X none))
    · simp [g, hj]
  have hf : (f P).totalDegree ≤ P.totalDegree := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro m hm
    change (MvPolynomial.aeval g (MvPolynomial.monomial m (P.coeff m))).totalDegree ≤ _
    rw [MvPolynomial.aeval_monomial]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    refine le_trans (Finset.sum_le_sum (fun j _ => ?_)) (MvPolynomial.le_totalDegree hm)
    exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m j) (hg j))
  change ((translation i P).coeff r).totalDegree ≤ _
  rw [htrans]
  exact (MvPolynomial.totalDegree_coeff_optionEquivLeft_le FX (Fin 2) (f P) r).trans hf
private theorem seedHasse_coeff (i : Fin 2) (r : ℕ) (P : Jet) (j k : ℕ) :
    ((seedHasse i r P).coeff j).coeff k = seedCoeff i r ((P.coeff j).coeff k) := by
  change ((mapCoeffs (mapCoeffs (seedCoeff i r)) P).coeff j).coeff k = _
  rw [mapCoeffs_coeff, mapCoeffs_coeff]
theorem proof : P1_7_4_1.c2 := by
  intro s P hP i r j k hc
  rw [seedHasse_coeff] at hc ⊢
  have hsource : (P.coeff j).coeff k ≠ 0 := by
    intro hz
    exact hc (by rw [hz, map_zero])
  obtain ⟨hB, hJ, hU⟩ := hP j k hsource
  exact ⟨hB, hJ, (seedCoeff_totalDegree i r _).trans hU⟩
end P1_7_4_1_2
end
section
namespace P1_7_4_3
noncomputable section
open Polynomial Finset
open P1 (K I node agreement)
open K1_13 (Row extend embed)
open K1_13_5 (RegularAt)
open K1_13_5_3
open K1_14_3_6 (totalCap topCap)
def mix (b j : ℕ) (a v : ℚ) : ℚ := (↑(b-j : ℕ) : ℚ) * v + j * a
theorem mix_eq {b j : ℕ} (h : j ≤ b) (a v : ℚ) :
    mix b j a v = (b : ℚ) * v + j * (a-v) := by
  unfold mix
  rw [Nat.cast_sub h]
  ring
theorem cast_mixed {b j a v : ℕ} (h : j ≤ b) (hv : v ≤ a) :
    (MvPolynomial.cappedDegreeMixedVolume b j a v : ℚ) = mix b j a v := by
  rw [MvPolynomial.cappedDegreeMixedVolume_eq h hv, mix]
  push_cast
  rfl
end
end P1_7_4_3
end
section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace P1_7_4_3
noncomputable section
open Polynomial PolynomialDifferential
open P1 (K I node p agreement)
open K1_13 (Row Geom extend embed atJet)
open K1_13_5 (RegularAt)
open K1_13_5_3
open K1_14 (seedEmbedding)
open K1_14_3_6 (power totalCap topCap)
open scoped BigOperators
open K1_14_3_6_2 (specialization_flatten eval_at_center)
private theorem solution_taylor {f : Row 2} {S : (Polynomial K)} {d : ℕ}
    (hd : d < p) (hS : RegularAt 1 f (extend S)) :
    MvPolynomial.aeval (marked (extend S)) (initialJetSeparant center (chart f)) ≠ 0 ∧
    ∀ j ≤ d, rationalTaylorCoefficient center (chart f) (marked (extend S)) j =
      (Polynomial.taylor center (S.map seedEmbedding)).coeff j := by
  let P := (extend S).map constants
  have hsol : differentialSpecialization (chart f) P = 0 := by
    change differentialSpecialization (chart f) ((extend S).map constants) = 0
    rw [chart, ← map_differentialSpecialization, K1_14_3_6_2.specialization_flatten, hS.1, Polynomial.map_zero]
  have hsf : differentialSpecialization (PolynomialDifferential.separant (flatten f) 1) (extend S) ≠ 0 := by
    change differentialSpecialization
      (MvPolynomial.pderiv (some 1) ((MvPolynomial.optionEquivRight Geom (Fin 2)).symm f)) _ ≠ 0
    rw [← MvPolynomial.optionEquivRight_symm_pderiv]
    exact (K1_14_3_6_2.specialization_flatten (MvPolynomial.pderiv 1 f) _).substr hS.2
  have hsep : jetEvaluation (PolynomialDifferential.separant (chart f) (Fin.last 1))
      center (marked (extend S)) ≠ 0 := by
    change jetEvaluation (PolynomialDifferential.separant (chart f) 1) center (marked (extend S)) ≠ 0
    rw [marked, ← eval_differentialSpecialization, chart, ← map_separant,
      ← map_differentialSpecialization, K1_14_3_6_2.eval_at_center]
    exact fun he => hsf (toCenter_inj (he.trans (map_zero _).symm))
  refine ⟨by rwa [aeval_initialJetSeparant], ?_⟩
  have hcharG : CharP Geom p := charP_of_injective_ringHom embed.injective p
  have : CharP CenterField p := charP_of_injective_ringHom constants.injective p
  have hP : P = S.map seedEmbedding := by
    change (extend S).map constants = _
    rw [Polynomial.map_map]
    rfl
  intro j hj
  rw [← hP]
  refine rationalTaylorCoefficient_eq_solution center (chart f) P hsol hsep j (fun i hi ht => ?_)
  rw [Nat.choose_one_right]
  intro hz
  exact (not_le_of_gt ((ht.trans hj).trans_lt hd))
    (Nat.le_of_dvd (by omega : 0 < i) ((CharP.cast_eq_zero_iff CenterField p i).mp hz))
private theorem short_numerator_bound (f : Row 2) {B J t : ℕ} (hJ : 0 < J)
    (hB : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J) (j : Fin (t+1)) :
    commonTaylorNumerator center (chart f) (power t) j ∈
      MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 (totalCap t B) (topCap t B J) := by
  let Q := chart f
  let N := commonTaylorNumerator center Q (power t) j
  have hτ : TaylorExponentSufficient 1 (t+1) (power t) :=
    taylorExponentSufficient_firstOrder_tight t
  have htot : N.totalDegree ≤ totalCap t B :=
    (totalDegree_commonTaylorNumerator_le center Q (hτ j)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right ((chart_degree f).trans hB) 1)) 1)
  exact mem_capped _ htot (le_min
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans htot)
    ((degreeOf_commonTaylorNumerator_firstOrder_le center Q J (t+1) (power t) hτ
      ((chart_top f).trans hj) j).trans (Nat.add_le_add_left (Nat.le_of_lt_succ j.isLt) _)))
private theorem short_denominator_bound (f : Row 2) {B J t : ℕ}
    (hB : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J) :
    initialJetSeparant center (chart f) ^ power t ∈
      MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 (totalCap t B) (topCap t B J) := by
  let Q := chart f
  let D := initialJetSeparant center Q ^ power t
  have hD₀ : D.totalDegree ≤ totalCap t B :=
    (MvPolynomial.totalDegree_pow _ _).trans ((Nat.mul_le_mul_left _
      ((totalDegree_initialJetSeparant_le center Q).trans
        (Nat.sub_le_sub_right ((chart_degree f).trans hB) 1))).trans (Nat.le_add_left _ _))
  have hD₁ : D.degreeOf 1 ≤ power t * (J-1) :=
    (MvPolynomial.degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left _
      ((degreeOf_initialJetSeparant_le center Q).trans
        (Nat.sub_le_sub_right ((chart_top f).trans hj) 1)))
  exact mem_capped D hD₀ (le_min
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans hD₀) (hD₁.trans (Nat.le_add_right _ _)))
theorem short_cut (f : Row 2) {d t B J : ℕ} (hd : d < p) (ht : t ≤ d)
    (hJ : 0 < J) (hB : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J)
    (sites : Finset I) (hs : d ≤ sites.card + t) (w : I → K) (i : I) :
    ∃ cut : MvPolynomial (Fin 2) CenterField,
      cut ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 (totalCap t B) (topCap t B J) ∧
      ∀ S : (Polynomial K), S.natDegree ≤ d → RegularAt 1 f (extend S) →
        (∀ j ∈ sites, S.eval (node j) = w j) →
        (MvPolynomial.aeval (marked (extend S)) cut = 0 ↔ S.eval (node i) = w i) := by
  classical
  obtain ⟨c, a, ha⟩ := P1_7_3.interpolation_weights sites d t hs w (node i)
  let Q := chart f
  let D := initialJetSeparant center Q ^ power t
  let N (j : Fin (t+1)) := commonTaylorNumerator center Q (power t) j
  let cut := MvPolynomial.C (c - seedEmbedding (w i)) * D + ∑ j, MvPolynomial.C (a j) * N j
  have hτ : TaylorExponentSufficient 1 (t+1) (power t) :=
    taylorExponentSufficient_firstOrder_tight t
  refine ⟨cut, ?_, ?_⟩
  · dsimp only [cut]
    apply Submodule.add_mem
    · rw [← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (short_denominator_bound f hB hj)
    · apply Submodule.sum_mem
      intro j _
      rw [← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (short_numerator_bound f hJ hB hj j)
  · intro S hS hreg hnodes
    obtain ⟨hsep, hcoef⟩ := solution_taylor hd hreg
    have hval := ha (S.map seedEmbedding) (Polynomial.natDegree_map_le.trans hS)
      (fun j hj => by rw [Polynomial.eval_map_apply, hnodes j hj])
    change (S.map seedEmbedding).eval (seedEmbedding (node i)) = _ at hval
    rw [Polynomial.eval_map_apply] at hval
    let x := marked (extend S)
    have he (j : Fin (t+1)) : MvPolynomial.aeval x (N j) =
        MvPolynomial.aeval x D * (Polynomial.taylor center (S.map seedEmbedding)).coeff j := by
      dsimp only [N, D]
      rw [aeval_commonTaylorNumerator center Q x (hτ j) hsep, map_pow,
        hcoef _ ((Nat.le_of_lt_succ j.isLt).trans ht)]
    have hdne : MvPolynomial.aeval x D ≠ 0 := by
      dsimp only [D]
      rw [map_pow]
      exact pow_ne_zero _ hsep
    have hc : MvPolynomial.aeval x cut =
        MvPolynomial.aeval x D * (seedEmbedding (S.eval (node i)) - seedEmbedding (w i)) := by
      dsimp only [cut]
      rw [hval, map_add, map_mul, map_sum, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply,
        mul_sub, mul_add, Finset.mul_sum]
      simp only [map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, he]
      have hsum : (∑ j : Fin (t+1), a j *
          (MvPolynomial.aeval x D * (Polynomial.taylor center (S.map seedEmbedding)).coeff j)) =
          ∑ j : Fin (t+1), MvPolynomial.aeval x D *
            (a j * (Polynomial.taylor center (S.map seedEmbedding)).coeff j) :=
        Finset.sum_congr rfl fun _ _ => by ring
      rw [hsum]
      ring
    change MvPolynomial.aeval x cut = 0 ↔ _
    rw [hc, mul_eq_zero, or_iff_right hdne, sub_eq_zero, seedEmbedding.injective.eq_iff]
end
end P1_7_4_3
end
section
namespace P1_7_4_3
noncomputable section
open Polynomial Finset
open P1 (K I node p agreement blockLength HighBand AnchorModel AnchoredFamily)
open P1_7 (degreeAt )
open P1_7_4 (ODEGuard )
open K1_13 (Geom Row extend embed)
open K1_13_5 (RegularAt)
open K1_14_2 (ODE fixedAt)
open K1_14_2_2 (ODECaps)
open K1_14_2_5 (clear_equation factor_cover)
open K1_14_3_6 (totalCap topCap)
open scoped BigOperators
end
end P1_7_4_3
end

end Merged_UpperBranch4

-- merged module R6960PowerLayers
section Merged_R6960PowerLayers
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
namespace Lower6960.PowerLayers
open K1_14 (Shape Jet Equation Seeds FX triangle)
open K1_14_3 (RowCaps)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (jetDegree seedDegree jetDegree_le seedDegree_le jetDegree_mul seedDegree_mul)
open P1_7_4_1 (factorDegree factorDegree_pow factorDegree_add)
open Polynomial Finset
open scoped BigOperators Classical
open K1_14_2_1_2 (seed_finrank)
theorem forced_power {h N W U : ℕ} (hh : 0<h) (hw : W<N) {G P R : Jet}
    (irr : Irreducible G) (slope : 0<G.natDegree) (seeded : UsesSeed G)
    (np : P≠0) (div : G∣P) (small : U<K1.p)
    (caps : ∀ j i, ((P.coeff j).coeff i).totalDegree≤U)
    (shifts : ∀ (i : Fin 2) a, W+2*h*a≤N-1 → G∣K1_14.seedHasse i a R) :
    G^(1+(N-1-W)/(2*h))∣R := by
  apply K1_14_2_1_1.proof G P R U _ irr slope seeded np div small caps
  intro i a ha
  apply shifts i a
  have le : a≤(N-1-W)/(2*h) := by omega
  have := (Nat.le_div_iff_mul_le (by omega : 0<2*h)).mp le
  rw [Nat.mul_comm a] at this
  omega
def positions (s : Shape) (h W : ℕ) (F : Jet) : Finset (ℕ×ℕ) :=
  ((range (s.B+1)).product (range (s.J+1))).filter fun a =>
    a.1+a.2+jetDegree F≤s.B ∧ a.2+F.natDegree≤s.J ∧
    (a.1+a.2+F.leadingCoeff.natDegree+F.natDegree)*(131071-h) ≤ W+(a.2+F.natDegree)
theorem quotient_rank (s : Shape) (h W : ℕ) (V : Submodule FX Jet) (F : Jet)
    (nf : F≠0) (dvd : ∀ R∈V,F∣R) (caps : ∀ R∈V,RowCaps R s)
    (lead : ∀ R∈V,R≠0 →
      (R.leadingCoeff.natDegree+R.natDegree)*(131071-h)≤W+R.natDegree) :
    Module.finrank FX V≤(positions s h W F).card*triangle (s.U-seedDegree F) := by
  classical
  let U := V.comap (Algebra.lmul FX Jet F)
  let mulF : U →ₗ[FX] V := (((Algebra.lmul FX Jet F).comp U.subtype).codRestrict V
    (fun Q=>Q.property))
  have eqv : Function.Bijective mulF := by
    constructor
    · intro x y he
      exact Subtype.ext (mul_left_cancel₀ nf (congrArg Subtype.val he))
    · intro x
      obtain ⟨y,hy⟩:=dvd x x.property
      exact ⟨⟨y,by change F*y∈V; rw [←hy]; exact x.property⟩, Subtype.ext hy.symm⟩
  have cdeg (Q : U) : seedDegree (Q : Jet)≤s.U-seedDegree F := by
    by_cases zero : (Q : Jet)=0
    · simp [zero,seedDegree]
    have hp : seedDegree (F*(Q : Jet))≤s.U := by
      apply (seedDegree_le ..).2
      intro j i
      by_cases z : (((F*(Q : Jet)).coeff j).coeff i)=0
      · simp [z]
      exact (caps _ Q.property j i z).2.2
    rw [seedDegree_mul nf zero] at hp
    omega
  let T := MvPolynomial.restrictTotalDegree (Fin 2) FX (s.U-seedDegree F)
  let S := positions s h W F
  let coord (a : S) : U →ₗ[FX] Seeds :=
    (((lcoeff Seeds a.val.1).restrictScalars FX).comp
      ((lcoeff Equation a.val.2).restrictScalars FX)).comp U.subtype
  let proj : U →ₗ[FX] (S→T) := LinearMap.pi fun a => (coord a).codRestrict T (fun Q =>
    (MvPolynomial.mem_restrictTotalDegree ..).2 ((seedDegree_le ..).1 (cdeg Q) a.val.2 a.val.1))
  have hz : ∀ Q : U, proj Q=0 → Q=0 := by
    intro Q z
    apply Subtype.ext
    by_contra bad
    have nq : (Q : Jet)≠0 := bad
    let j := (Q : Jet).natDegree
    let i := (Q : Jet).leadingCoeff.natDegree
    have coeff : (((Q : Jet).coeff j).coeff i)≠0 := by
      dsimp only [i,j]
      rw [coeff_natDegree,coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nq)
    have jq := (jetDegree_le (Q : Jet) _).1 le_rfl j i coeff
    have total : jetDegree (F*(Q : Jet))≤s.B := (jetDegree_le ..).2 (fun v y ne=>(caps _ Q.property v y ne).1)
    rw [jetDegree_mul nf nq] at total
    have nd : (F*(Q : Jet)).natDegree≤s.J := by
      let R := F*(Q : Jet)
      have hn : R≠0 := mul_ne_zero nf nq
      apply (caps R Q.property R.natDegree R.leadingCoeff.natDegree ?_).2.1
      rw [coeff_natDegree,coeff_natDegree]; exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    have l := lead (F*(Q:Jet)) Q.property (mul_ne_zero nf nq)
    rw [natDegree_mul nf nq] at nd l
    rw [leadingCoeff_mul,natDegree_mul (leadingCoeff_ne_zero.mpr nf) (leadingCoeff_ne_zero.mpr nq)] at l
    have mem : (i,j)∈S := by
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by dsimp [j]; omega)⟩,?_,?_,?_⟩
      · omega
      · dsimp [j]; omega
      · dsimp [i,j]; linarith
    have witness := congrArg (fun f : S→T => ((f ⟨(i,j),mem⟩ : T) : Seeds)) z
    exact coeff witness
  have inj : Function.Injective proj := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub,hxy]
    ext a
    exact sub_self _
  let eq := LinearEquiv.ofBijective mulF eqv
  rw [←eq.finrank_eq]
  calc _ ≤ Module.finrank FX (S→T) := LinearMap.finrank_le_finrank_of_injective inj
       _ = _ := by
          let : Module.Free FX T := Module.Free.of_basis (MvPolynomial.basisRestrictSupport FX _)
          rw [Module.finrank_pi_fintype FX (M:=fun _ : S=>T)]
          simp [T,S,seed_finrank]
def eligiblePositions (s : Shape) (h W slope trim : ℕ) : Finset (ℕ×ℕ) :=
  ((range (s.B+1)).product (range (s.J+1))).filter fun a =>
    a.2≤a.1 ∧ slope≤a.2 ∧ a.1+trim≤s.B ∧ a.1*(131071-h)≤W+a.2
theorem layer_rank (s : Shape) (h W k slope extra u : ℕ) (V : Submodule FX Jet)
    (G : Jet) (g : G≠0) (sg : slope≤G.natDegree) (ug : u≤seedDegree G)
    (bg : G.natDegree+extra≤jetDegree G)
    (dvd : ∀ R∈V,G^k∣R) (caps : ∀ R∈V,RowCaps R s)
    (lead : ∀ R∈V,R≠0 →
      (R.leadingCoeff.natDegree+R.natDegree)*(131071-h)≤W+R.natDegree) :
    Module.finrank FX V ≤ (eligiblePositions s h W (k*slope) (k*extra)).card *
      (if k*u≤s.U then triangle (s.U-k*u) else 0) := by
  classical
  let F:=G^k
  have nf : F≠0 := pow_ne_zero k g
  have ds : F.natDegree=k*G.natDegree := natDegree_pow G k
  have du : seedDegree F=k*seedDegree G := factorDegree_pow g k 2
  have db : jetDegree F=k*jetDegree G := factorDegree_pow g k 0
  have sfit : k*slope≤F.natDegree := ds ▸ Nat.mul_le_mul_left _ sg
  have bfit : F.natDegree+k*extra≤jetDegree F := by
    rw [ds,db,←Nat.mul_add]; exact Nat.mul_le_mul_left _ bg
  have ufit : k*u≤seedDegree F := du ▸ Nat.mul_le_mul_left _ ug
  by_cases zero : s.U<k*u
  · rw [ite_eq_right (Nat.not_le.mpr zero),Nat.mul_zero]
    have sub : V=⊥ := by
      apply bot_unique
      intro R hr
      change R=0
      by_contra nr
      obtain ⟨Q,hq⟩:=dvd R hr
      have qn : Q≠0 := right_ne_zero_of_mul (hq ▸ nr)
      have cap : seedDegree R≤s.U := (seedDegree_le ..).2 (by
        intro j i
        by_cases hz : ((R.coeff j).coeff i)=0
        · simp [hz]
        exact (caps R hr j i hz).2.2)
      change R=F*Q at hq
      rw [hq,seedDegree_mul nf qn] at cap
      omega
    rw [sub,finrank_bot]
  · rw [ite_eq_left (Nat.le_of_not_gt zero)]
    have rank:=quotient_rank s h W V F nf dvd caps lead
    have card : (positions s h W F).card ≤ (eligiblePositions s h W (k*slope) (k*extra)).card := by
      apply card_le_card_of_injOn (fun a:ℕ×ℕ=>(a.1+a.2+F.natDegree,a.2+F.natDegree))
      · intro a ha
        obtain ⟨_,ht,hj,hw⟩:=mem_filter.mp ha
        apply mem_filter.mpr
        dsimp only
        refine ⟨mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,
          by omega, by omega, by omega, ?_⟩
        exact (Nat.mul_le_mul_right _ (by omega)).trans hw
      · rintro ⟨i,j⟩ _ ⟨i',j'⟩ _ he
        simp only [Prod.mk.injEq,Nat.add_left_inj] at he
        obtain ⟨ha,rfl⟩:=he
        simp_all
    have tri : triangle (s.U-seedDegree F)≤triangle (s.U-k*u) := by
      unfold triangle
      apply Nat.div_le_div_right
      have := Nat.sub_le_sub_left ufit s.U
      exact Nat.mul_le_mul (by omega) (by omega)
    exact rank.trans (Nat.mul_le_mul card tri)
def layerCost (s : Shape) (h N W slope extra u : ℕ) : ℕ :=
  let k:=1+(N-1-W)/(2*h)
  (eligiblePositions s h W (k*slope) (k*extra)).card *
    (if k*u≤s.U then triangle (s.U-k*u) else 0)
theorem no_common_power (s : Shape) (h N slope extra u : ℕ)
    (rows : ℕ→Submodule FX Jet) (G : Jet) (nz : G≠0)
    (sg : slope≤G.natDegree) (ug : u≤seedDegree G) (bg : G.natDegree+extra≤jetDegree G)
    (caps : ∀ W<N, ∀ R∈rows W, RowCaps R s)
    (lead : ∀ W<N, ∀ R∈rows W, R≠0 →
      (R.leadingCoeff.natDegree+R.natDegree)*(131071-h)≤W+R.natDegree)
    (supply : (∑ W∈range N,layerCost s h N W slope extra u) <
      ∑ W∈range N,Module.finrank FX (rows W)) :
    ¬ (∀ W<N, ∀ R∈rows W,G^(1+(N-1-W)/(2*h))∣R) := by
  intro power
  apply (Nat.not_lt_of_ge (Finset.sum_le_sum (s:=range N) (fun W mem =>
    layer_rank s h W _ slope extra u (rows W) G nz sg ug bg (power W (mem_range.mp mem))
      (caps W (mem_range.mp mem)) (lead W (mem_range.mp mem))))) supply
theorem avoiding_row (s : Shape) (h N slope extra u : ℕ) (hh : 0<h)
    (rows : ℕ→Submodule FX Jet) (G P : Jet) (irr : Irreducible G)
    (gs : 0<G.natDegree) (seeded : UsesSeed G) (np : P≠0) (gp : G∣P)
    (small : s.U<K1.p) (pc : ∀ j i,((P.coeff j).coeff i).totalDegree≤s.U)
    (sg : slope≤G.natDegree) (ug : u≤seedDegree G) (bg : G.natDegree+extra≤jetDegree G)
    (caps : ∀ W<N, ∀ R∈rows W, RowCaps R s)
    (lead : ∀ W<N, ∀ R∈rows W, R≠0 →
      (R.leadingCoeff.natDegree+R.natDegree)*(131071-h)≤W+R.natDegree)
    (shift : ∀ W<N,∀ R∈rows W,∀ i a, W+2*h*a≤N-1 → K1_14.seedHasse i a R∈rows (N-1))
    (supply : (∑ W∈range N,layerCost s h N W slope extra u) <
      ∑ W∈range N,Module.finrank FX (rows W)) :
    ∃ Q∈rows (N-1), ¬ G∣Q := by
  by_contra! shared
  apply no_common_power s h N slope extra u rows G irr.ne_zero sg ug bg caps lead supply
  intro W hw R hr
  exact forced_power hh hw irr gs seeded np gp small pc
    (fun i a hsp => shared _ (shift W hw R hr i a hsp))
def net {ι : Type*} (T : Finset ι) (weight : ι→ℕ) (a b : ι→ℤ)
    (c d : ℤ) (x : ℕ) : ℤ :=
  (∑ i∈T, (weight i : ℤ)*max 0 (a i+b i*(x:ℤ)))-(c+d*(x:ℤ))
private theorem clip_second (x y : ℤ) :
    2*max 0 (x+y) ≤ max 0 x + max 0 (x+2*y) := by
  by_cases h : 0≤x+y
  · rw [max_eq_right h]
    have h1 := le_max_right 0 x
    have h2 := le_max_right 0 (x+2*y)
    omega
  · rw [max_eq_left (by omega : x+y≤0)]
    have h1 := le_max_left 0 x
    have h2 := le_max_left 0 (x+2*y)
    omega
theorem net_convex {ι : Type*} (T : Finset ι) (weight : ι→ℕ) (a b : ι→ℤ)
    (c d : ℤ) (x : ℕ) :
    2*net T weight a b c d (x+1) ≤ net T weight a b c d x + net T weight a b c d (x+2) := by
  classical
  have each (i) : 2*((weight i:ℤ)*max 0 (a i+b i*((x:ℤ)+1))) ≤
      (weight i:ℤ)*max 0 (a i+b i*(x:ℤ)) + (weight i:ℤ)*max 0 (a i+b i*((x:ℤ)+2)) := by
    have z:=mul_le_mul_of_nonneg_left (clip_second (a i+b i*(x:ℤ)) (b i)) (Int.natCast_nonneg (weight i))
    rw [show a i+b i*((x:ℤ)+1)=a i+b i*(x:ℤ)+b i by ring,
      show a i+b i*((x:ℤ)+2)=a i+b i*(x:ℤ)+2*b i by ring]
    linarith only [z]
  have total:=sum_le_sum (s:=T) (fun i _=>each i)
  rw [←Finset.mul_sum, Finset.sum_add_distrib] at total
  unfold net
  push_cast
  linarith only [total]
theorem from_two_heights (f : ℕ→ℤ) (lo : ℕ) (positive : 0<f lo)
    (next : f lo≤f (lo+1)) (convex : ∀ x,2*f (x+1)≤f x+f (x+2)) :
    ∀ y,lo≤y → 0<f y := by
  intro y hy
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hy
  have both : ∀ n, 0<f (lo+n) ∧ f (lo+n)≤f (lo+n+1) := by
    intro t
    induction t with
    | zero => exact ⟨positive,next⟩
    | succ t ih =>
      have := convex (lo+t)
      exact ⟨lt_of_lt_of_le ih.1 ih.2,by
        change f (lo+t+1)≤f (lo+t+2)
        omega⟩
  exact (both n).1
theorem sum_layer_gains (N width shift layers : ℕ) (delta : ℕ→ℕ) :
    (∑ W∈range N, ∑ i∈range layers,
      if width≤W ∧ W+shift*i<N then delta i else 0) =
      ∑ i∈range layers, (N-width-shift*i)*delta i := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have support : (range N).filter (fun W=>width≤W ∧ W+shift*i<N) = Ico width (N-shift*i) := by
    ext W
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  rw [←Finset.sum_filter,support,Finset.sum_const,Nat.card_Ico,nsmul_eq_mul]
  change (N-shift*i-width)*delta i=(N-width-shift*i)*delta i
  rw [Nat.sub_sub,Nat.sub_sub,Nat.add_comm (shift*i) width]
#print axioms sum_layer_gains
#print axioms net_convex
#print axioms from_two_heights
#print axioms avoiding_row
#print axioms layer_rank
#print axioms forced_power
#print axioms quotient_rank
end Lower6960.PowerLayers

end
end Merged_R6960PowerLayers

-- merged module R6960HelperSource
section Merged_R6960HelperSource
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.HelperSource
open Finset Polynomial
open K1_14 (Shape Jet FX L Banks shapeSum triangle slots seedHasse jetAt)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open K1_14_3 (RowCaps)
open K1_14_1 (PoleData CRTLift evaluated evaluated_mono evaluated_shape)
open P1_7 (Bank debit)
open P1_7_1 (nodeRows groupedPoleMoment)
open P1_7_5 (kept)
open PowerLayers (eligiblePositions layerCost)
open P1_7_5 (position_sum)
open P1_7_1 (pole_bound)
open P1_7_6 (slots_anti rise_of_convex)
def orderCap (s : Shape) (d c q j : ℕ) : ℕ :=
  if c = 0 then j/d else min (j/d) ((s.B-q)/c)
theorem le_orderCap (s : Shape) {d c q j k : ℕ} (hd : 0 < d) (hq : q ≤ s.B) :
    k ≤ orderCap s d c q j ↔ k*d ≤ j ∧ q+k*c ≤ s.B := by
  unfold orderCap
  split
  · rename_i hc
    rw [hc, Nat.mul_zero, Nat.add_zero, Nat.le_div_iff_mul_le hd]
    simp [hq]
  · rename_i hc
    rw [le_min_iff, Nat.le_div_iff_mul_le hd, Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hc)]
    omega
def coordinateGain (s : Shape) (A h r d c v q j : ℕ) : ℕ :=
  let C := kept s.U v (orderCap s d c q j)
  ∑ i ∈ range (orderCap s d c q j + 1),
    (C i - C (i+1)) * (s.m*A+j-q*(131071-h)-2*h*(r+i))
def gain (s : Shape) (A h r d c v : ℕ) : ℕ :=
  shapeSum s (coordinateGain s A h r d c v)
def cutoffCount (s : Shape) (A h r : ℕ) : ℕ := s.m*A-2*h*r
private theorem layerCost_eq (s : Shape) (h N W d c v : ℕ) (hd : 0 < d) :
    layerCost s h N W d c v =
      shapeSum s fun q j =>
        if q*(131071-h) ≤ W+j then
          kept s.U v (orderCap s d c q j) (1+(N-1-W)/(2*h))
        else 0 := by
  classical
  let k := 1+(N-1-W)/(2*h)
  unfold layerCost eligiblePositions
  change (((range (s.B+1)).product (range (s.J+1))).filter (fun a =>
    a.2≤a.1 ∧ k*d≤a.2 ∧ a.1+k*c≤s.B ∧ a.1*(131071-h)≤W+a.2)).card *
    slots s.U (k*v) = _
  rw [← Nat.nsmul_eq_mul, ← sum_const, sum_filter]
  change (∑ a ∈ range (s.B+1) ×ˢ range (s.J+1),
    if a.2≤a.1 ∧ k*d≤a.2 ∧ a.1+k*c≤s.B ∧ a.1*(131071-h)≤W+a.2 then slots s.U (k*v) else 0) = _
  rw [sum_product (range (s.B+1)) (range (s.J+1)) (fun a : ℕ×ℕ =>
    if a.2≤a.1 ∧ k*d≤a.2 ∧ a.1+k*c≤s.B ∧ a.1*(131071-h)≤W+a.2 then slots s.U (k*v) else 0)]
  unfold shapeSum
  apply sum_congr rfl
  intro q hq
  have hqb : q ≤ s.B := Nat.le_of_lt_succ (mem_range.mp hq)
  rw [← sum_subset (s₁ := range (min q s.J+1)) (s₂ := range (s.J+1))
    (range_mono (Nat.succ_le_succ (min_le_right _ _)))]
  · apply sum_congr rfl
    intro j hj
    have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
    change (if j≤q ∧ k*d≤j ∧ q+k*c≤s.B ∧ q*(131071-h)≤W+j then slots s.U (k*v) else 0) =
      if q*(131071-h)≤W+j then kept s.U v (orderCap s d c q j) k else 0
    simp only [kept, le_orderCap s hd hqb]
    by_cases hw : q*(131071-h) ≤ W+j
    · simp only [hjq, hw, true_and, and_true, ite_true]
    · simp only [hw, and_false, ite_false]
  · intro j hj hn
    have hq' : ¬ j≤q := by
      simp only [mem_range, Nat.lt_succ_iff, le_min_iff] at hj hn
      omega
    simp [hq']
private theorem coordinate_total (s : Shape) (A h r d c v q j : ℕ) (hh : 0<h)
    (hk : 1≤131071-h) (hj : j≤q) :
    let N := cutoffCount s A h r
    (∑ W ∈ range N, if q*(131071-h) ≤ W+j then
      kept s.U v (orderCap s d c q j) (1+(N-1-W)/(2*h)) else 0) +
    coordinateGain s A h r d c v q j = triangle s.U*(N+j-q*(131071-h)) := by
  dsimp only
  let N := cutoffCount s A h r
  let t := q*(131071-h)
  let g := orderCap s d c q j
  have hq : q ≤ t := by simpa [t] using Nat.mul_le_mul_left q hk
  have hjt : j ≤ t := hj.trans hq
  have he (i : ℕ) : N+0-(t-j)-2*h*(0+i) = s.m*A+j-t-2*h*(r+i) := by
    simp only [Nat.add_zero, Nat.zero_add]
    unfold N cutoffCount
    rw [Nat.mul_add]
    omega
  have eq := position_sum N (2*h) (t-j) 0 s.U v g (Nat.zero_le _) (by omega)
  simp only [Nat.add_zero, Nat.sub_zero, Nat.zero_add] at eq
  have hwidth : N-(t-j) = N+j-t := by omega
  have he' (i : ℕ) : N-(t-j)-2*h*i = s.m*A+j-t-2*h*(r+i) := by simpa using he i
  simp_rw [he'] at eq
  rw [hwidth] at eq
  have hsplit :
      coordinateGain s A h r d c v q j =
      (∑ a ∈ range g, (slots s.U (a*v) - slots s.U ((a+1)*v)) *
         (s.m*A+j-t-2*h*(r+a))) +
      slots s.U (g*v) * (s.m*A+j-t-2*h*(r+g)) := by
    unfold coordinateGain
    rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro i hi
      have h := mem_range.mp hi
      simp only [kept, ite_eq_left h.le, ite_eq_left (Nat.succ_le_of_lt h)]
      rfl
    · simp [kept, g, t]
  rw [hsplit]
  have hguard (W : ℕ) : t-j ≤ W ↔ t ≤ W+j := by omega
  simpa only [hguard] using eq
theorem cutoff_total (s : Shape) (A h r d c v : ℕ) (hh : 0 < h) (hk : 1 ≤ 131071-h)
    (hd : 0 < d) :
    let N := cutoffCount s A h r
    (∑ W ∈ range N, layerCost s h N W d c v) + gain s A h r d c v =
      triangle s.U * shapeSum s (fun q j => N+j-q*(131071-h)) := by
  dsimp only
  let N := cutoffCount s A h r
  have hswap (F : ℕ → ℕ → ℕ → ℕ) :
      (∑ W ∈ range N, shapeSum s (F W)) =
        shapeSum s (fun q j => ∑ W ∈ range N, F W q j) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  simp_rw [layerCost_eq s h (cutoffCount s A h r) _ d c v hd]
  rw [hswap]
  simp only [gain, shapeSum, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  exact coordinate_total s A h r d c v q j hh hk
    ((Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _))
theorem crt_rank_floor {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (t : Bank) (hh : 0<h) (hk : h≤131070)
    (hnodes : nodeRows t.shape = t.nodeRows)
    (hmoment : groupedPoleMoment t.shape.B t.shape.J ≤ t.poleMoment)
    (small : t.shape.B<K1.p) (W : ℕ)
    (hW : K1_14_1.rawWidthCond h t.shape W) :
    K1_14_1.rawVolumeAt h t.shape W ≤ debit h t +
      ∑ w ∈ range (W+1), Module.finrank FX (evaluated Crt word t.shape w) := by
  have hlocal := P1_7_1_1.of_children P1_7_1_1_1.proof P1_7_1_1_2.proof
  have hvol := P0_10_1.ambient_bound (by omega : h ≤ 131071) t.shape W hW
  have hcontact := P0_10_1.physical_bound h word t.shape W
  have hpole := pole_bound hlocal hh (hk.trans_lt (by decide)) Crt word t.shape small W
  have hsum := P1_7_1.telescope hk Crt word t.shape W
  have hphys : K1_14_1.physicalDebit t.shape = triangle t.shape.U * t.nodeRows := by
    rw [← hnodes]
    unfold K1_14_1.physicalDebit nodeRows
    rw [Nat.mul_assoc]
  rw [hphys] at hcontact
  have hextra := Nat.mul_le_mul_left (2*h*(t.shape.U+1)) hmoment
  unfold debit
  omega
def WidthGuard (t : Bank) (A h r : ℕ) : Prop :=
  t.shape.B * (131071-h) < cutoffCount t.shape A h r
theorem crt_supply {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (t : Bank) (A r d c v : ℕ) (hh : 0<h) (hk : h≤131070) (hd : 0<d)
    (hnodes : nodeRows t.shape = t.nodeRows)
    (hmoment : groupedPoleMoment t.shape.B t.shape.J ≤ t.poleMoment)
    (small : t.shape.B<K1.p) (width : WidthGuard t A h r)
    (surplus : debit h t < gain t.shape A h r d c v) :
    let N := cutoffCount t.shape A h r
    (∑ W ∈ range N, layerCost t.shape h N W d c v) <
      ∑ W ∈ range N, Module.finrank FX (evaluated Crt word t.shape W) := by
  dsimp only
  let N := cutoffCount t.shape A h r
  have hw : t.shape.B*(131071-h)<N := width
  have hcomplete : N-1+1=N := by omega
  have hf := crt_rank_floor Crt word t hh hk hnodes hmoment small (N-1) (by
    intro q hq j _
    rw [hcomplete]
    exact (Nat.mul_le_mul_right _ hq).trans (hw.le.trans (Nat.le_add_right N j)))
  unfold K1_14_1.rawVolumeAt at hf
  rw [hcomplete] at hf
  have ht := cutoff_total t.shape A h r d c v hh (by omega) hd
  dsimp only at ht
  change (∑ W ∈ range N, layerCost t.shape h N W d c v) + gain t.shape A h r d c v =
    triangle t.shape.U * shapeSum t.shape (fun q j => N+j-q*(131071-h)) at ht
  change (∑ W ∈ range N, layerCost t.shape h N W d c v) <
    ∑ W ∈ range N, Module.finrank FX (evaluated Crt word t.shape W)
  omega
theorem nonzero_of_supply {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (s : Shape) (N : ℕ) (supply : 0 < ∑ W ∈ range N, Module.finrank FX (evaluated Crt word s W)) :
    ∃ P ∈ evaluated Crt word s (N-1), P ≠ 0 := by
  by_contra! hz
  have hall : (∑ W ∈ range N, Module.finrank FX (evaluated Crt word s W)) = 0 := by
    apply sum_eq_zero
    intro W hW
    have hW' : W ≤ N-1 := by have := mem_range.mp hW; omega
    have hb : evaluated Crt word s W = ⊥ := by
      apply bot_unique
      intro P hP
      exact (Submodule.mem_bot FX).mpr
        (hz P (evaluated_mono Crt word rfl rfl rfl le_rfl hW' hP))
    rw [hb, finrank_bot]
  omega
theorem crt_avoiding_row {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (t : Bank) (A r d c v : ℕ) (hh : 0<h) (hk : h≤131070) (hd : 0<d)
    (hnodes : nodeRows t.shape = t.nodeRows)
    (hmoment : groupedPoleMoment t.shape.B t.shape.J ≤ t.poleMoment)
    (small : t.shape.B<K1.p) (smallSeed : t.shape.U<K1.p) (width : WidthGuard t A h r)
    (surplus : debit h t < gain t.shape A h r d c v)
    {G : Jet} (irr : Irreducible G) (seeded : UsesSeed G)
    (slope : d≤G.natDegree) (seed : v≤seedDegree G) (excess : G.natDegree+c≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word t.shape (cutoffCount t.shape A h r-1), ¬ G∣Q := by
  by_contra! shared
  let N := cutoffCount t.shape A h r
  have supply := crt_supply Crt word t A r d c v hh hk hd hnodes hmoment small width surplus
  obtain ⟨P, hP, hnP⟩ := nonzero_of_supply Crt word t.shape N (lt_of_le_of_lt (Nat.zero_le _) supply)
  have hpc (j i : ℕ) : ((P.coeff j).coeff i).totalDegree ≤ t.shape.U := by
    by_cases hz : ((P.coeff j).coeff i)=0
    · simp [hz]
    · exact (evaluated_shape Crt word hP j i hz).2.2
  obtain ⟨Q, hQ, hAvoid⟩ := PowerLayers.avoiding_row t.shape h N d c v hh
    (evaluated Crt word t.shape) G P irr (hd.trans_le slope) seeded hnP (shared P hP)
    smallSeed hpc slope seed excess
    (fun _ _ _ hR => evaluated_shape Crt word hR)
    (fun W _ R hR hnR => P0_10_1.leading_bound hh hk Crt word t.shape W R hR hnR)
    (fun _ _ _ hR i a hshift => evaluated_mono Crt word rfl rfl rfl le_rfl hshift
      (P0_10_1.evaluated_shift Crt word hR i a))
    supply
  exact hAvoid (shared Q hQ)
#print axioms cutoff_total
#print axioms crt_rank_floor
#print axioms crt_avoiding_row
def signedWidth (s : Shape) (A h r q j i : ℕ) : ℤ :=
  (s.m : ℤ)*A+j-(131071-(h : ℤ))*q-2*(h : ℤ)*(r+i)
theorem width_cast (s : Shape) (A h r q j i : ℕ) (hk : h≤131071) :
    ((s.m*A+j-q*(131071-h)-2*h*(r+i) : ℕ) : ℤ) =
      max 0 (signedWidth s A h r q j i) := by
  rw [Nat.sub_sub]
  have he : (↑(s.m*A+j : ℕ) : ℤ) - (↑(q*(131071-h)+2*h*(r+i) : ℕ) : ℤ) =
      signedWidth s A h r q j i := by
    simp only [signedWidth, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hk]
    ring
  generalize s.m*A+j = x at *
  generalize q*(131071-h)+2*h*(r+i) = y at *
  by_cases hxy : y≤x
  · rw [Int.ofNat_sub hxy, he, max_eq_right (by omega)]
  · have hz : x-y=0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz, Int.ofNat_zero, max_eq_left (by omega)]
private theorem weighted_convex (s : Shape) (A h r q j i c : ℕ) (hk : h+2≤131071) :
    let f := fun h => ((c*(s.m*A+j-q*(131071-h)-2*h*(r+i)) : ℕ) : ℤ)
    f (h+1) + f (h+1) ≤ f h + f (h+2) := by
  dsimp only
  simp only [Nat.cast_mul, width_cast s A h r q j i (by omega),
    width_cast s A (h+1) r q j i (by omega), width_cast s A (h+2) r q j i hk, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg c)
  by_cases hn : signedWidth s A (h+1) r q j i ≤ 0
  · rw [max_eq_left hn, zero_add]
    exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  · rw [max_eq_right (le_of_not_ge hn)]
    have hlin : signedWidth s A (h+1) r q j i + signedWidth s A (h+1) r q j i =
        signedWidth s A h r q j i + signedWidth s A (h+2) r q j i := by
      simp only [signedWidth, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      ring
    rw [hlin]
    exact add_le_add (le_max_right _ _) (le_max_right _ _)
def surplus (t : Bank) (A h r d c v : ℕ) : ℤ :=
  (gain t.shape A h r d c v : ℤ)-(debit h t : ℤ)
theorem surplus_convex (t : Bank) (A h r d c v : ℕ) (hk : h+2≤131071) :
    surplus t A (h+1) r d c v + surplus t A (h+1) r d c v ≤
      surplus t A h r d c v + surplus t A (h+2) r d c v := by
  have hg : (gain t.shape A (h+1) r d c v : ℤ) + gain t.shape A (h+1) r d c v ≤
      (gain t.shape A h r d c v : ℤ) + gain t.shape A (h+2) r d c v := by
    simp only [gain, shapeSum, coordinateGain, Nat.cast_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro q _
    apply sum_le_sum
    intro j _
    apply sum_le_sum
    intro i _
    exact weighted_convex t.shape A h r q j i _ hk
  have hd : (debit (h+1) t : ℤ) + debit (h+1) t = (debit h t : ℤ) + debit (h+2) t := by
    simp only [debit, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  unfold surplus
  omega
theorem surplus_positive (t : Bank) (A lo h r d c v : ℕ) (hl : lo≤h) (hk : h≤131070)
    (positive : 0<surplus t A lo r d c v)
    (increasing : surplus t A lo r d c v ≤ surplus t A (lo+1) r d c v) :
    debit h t < gain t.shape A h r d c v := by
  have inc := rise_of_convex (f := fun n => surplus t A n r d c v)
    (fun n hn => surplus_convex t A n r d c v (by omega)) hl increasing
  have hp := positive.trans_le inc.1
  unfold surplus at hp
  omega
theorem width_at_height (t : Bank) (A lo h r : ℕ) (hl : lo≤h) (hk : h≤131071)
    (hs : 2*r≤t.shape.B) (hw : WidthGuard t A lo r) :
    WidthGuard t A h r := by
  unfold WidthGuard cutoffCount at *
  have hl' : lo ≤ 131071 := hl.trans hk
  have z := Nat.mul_le_mul_left (h-lo) hs
  have hlip : t.shape.B*(131071-h) + 2*h*r ≤
      t.shape.B*(131071-lo) + 2*lo*r := by
    have h₁ : 131071-h+(h-lo)=131071-lo := by omega
    have h₂ : lo+(h-lo)=h := by omega
    have h₁' := congrArg (t.shape.B * ·) h₁
    have h₂' := congrArg (fun n : ℕ => 2*n*r) h₂
    simp only [Nat.mul_add, Nat.add_mul] at h₁' h₂'
    rw [Nat.mul_comm t.shape.B (h-lo)] at h₁'
    rw [Nat.mul_comm (2*(h-lo)) r, ←Nat.mul_assoc r 2 (h-lo),
      Nat.mul_comm r 2, Nat.mul_comm (2*r) (h-lo)] at h₂'
    omega
  omega
#print axioms surplus_positive
#print axioms width_at_height
end Lower6960.HelperSource

end Merged_R6960HelperSource

-- merged module R6960HelperSourceArithmetic
section Merged_R6960HelperSourceArithmetic
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.HelperSource
open Finset
open K1_14 (Shape shapeSum slots)
open P1_7 (Bank debit)
open P1_7_5 (kept)
open P1_7_6 (linearEnd lt_linearEnd)
open P1_7_1_3 (evaluate evaluate_eq)
open P1_7_6 (slots_anti)
def clippedSum (base step bound cap : ℕ) : ℕ :=
  let len := linearEnd base step bound cap
  len*bound-(len*base+step*(len*(len-1)/2))
theorem clippedSum_eq (base step bound cap : ℕ) :
    clippedSum base step bound cap = ∑ a ∈ range cap, (bound-(base+step*a)) := by
  let len := linearEnd base step bound cap
  have hle : len ≤ cap := by
    by_contra! bad
    exact (lt_linearEnd base step bound cap cap).mp bad |>.1.false
  rw [← sum_subset (range_mono hle) (f := fun a => bound-(base+step*a)) (by
    intro a ha hna
    apply Nat.sub_eq_zero_of_le
    have hn := fun h => hna (mem_range.mpr ((lt_linearEnd base step bound cap a).mpr
      ⟨mem_range.mp ha,h⟩))
    exact Nat.le_of_not_gt hn)]
  have hadd : (∑ a ∈ range len, (bound-(base+step*a))) +
      (∑ a ∈ range len, (base+step*a)) = len*bound := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _ ∈ range len, bound := by
        apply sum_congr rfl
        intro a ha
        exact Nat.sub_add_cancel ((lt_linearEnd base step bound cap a).mp (mem_range.mp ha)).2.le
      _ = _ := by simp
  rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul, Finset.sum_range_id] at hadd
  change len*bound-(len*base+step*(len*(len-1)/2)) = _
  exact (Nat.eq_sub_of_add_eq hadd).symm
private def boxPhase (s : Shape) (A h r d c v δ q j : ℕ) : ℕ :=
  ∑ i ∈ range (s.J/d+1),
    if j≤q ∧ (i+δ)*d≤j ∧ q+(i+δ)*c≤s.B then
      slots s.U ((i+δ)*v)*(s.m*A+j-q*(131071-h)-2*h*(r+i))
    else 0
private theorem coordinate_phases (s : Shape) (A h r d c v q j : ℕ)
    (hd : 0<d) (hq : q≤s.B) (hjq : j≤q) (hj : j≤s.J) :
    coordinateGain s A h r d c v q j + boxPhase s A h r d c v 1 q j =
      boxPhase s A h r d c v 0 q j := by
  let K := orderCap s d c q j
  let C := kept s.U v K
  let w := fun i => s.m*A+j-q*(131071-h)-2*h*(r+i)
  have hphase (δ : ℕ) : boxPhase s A h r d c v δ q j =
      ∑ i ∈ range (s.J/d+1), C (i+δ)*w i := by
    apply sum_congr rfl
    intro i _
    simp only [C, K, w, kept, le_orderCap s hd hq, hjq, true_and, ite_mul, zero_mul]
  have hmono : Antitone C := by
    intro i l hi
    by_cases hl : l≤K
    · simp only [C, kept, ite_eq_left hl, ite_eq_left (hi.trans hl)]
      exact slots_anti _ (Nat.mul_le_mul_right _ hi)
    · simp [C, kept, hl]
  have hK : K ≤ s.J/d := by
    have h := ((le_orderCap s hd hq).mp (le_rfl (a := K))).1.trans hj
    exact (Nat.le_div_iff_mul_le hd).mpr h
  have hsum : coordinateGain s A h r d c v q j =
      ∑ i ∈ range (s.J/d+1), (C i-C (i+1))*w i := by
    apply sum_subset (range_mono (Nat.succ_le_succ hK))
    intro i _ hi
    have hi' : ¬ i≤K := by
      intro h
      exact hi (mem_range.mpr (Nat.lt_succ_of_le h))
    have hi'' : ¬ i+1≤K := by omega
    change (C i-C (i+1))*w i = 0
    simp only [C, kept, ite_eq_right hi', ite_eq_right hi'', Nat.sub_self, Nat.zero_mul]
  rw [hsum, hphase 1, hphase 0, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [← Nat.add_mul, Nat.sub_add_cancel (hmono (Nat.le_succ i)), Nat.add_zero]
def column (s : Shape) (A h r c i δ j : ℕ) : ℕ :=
  clippedSum (j*(131071-h)+2*h*(r+i)) (131071-h) (s.m*A+j)
    (s.B+1-(i+δ)*c-j)
theorem column_eq (s : Shape) (A h r c i δ j : ℕ) :
    column s A h r c i δ j =
      ∑ q ∈ Ico j (s.B+1-(i+δ)*c), (s.m*A+j-q*(131071-h)-2*h*(r+i)) := by
  rw [column, clippedSum_eq, sum_Ico_eq_sum_range]
  apply sum_congr rfl
  intro a _
  have h := Nat.add_mul j a (131071-h)
  rw [Nat.sub_sub, h]
  congr 1
  ring
def phaseLayer (s : Shape) (A h r d c v δ i : ℕ) : ℕ :=
  slots s.U ((i+δ)*v) *
    evaluate (fun a => column s A h r c i δ ((i+δ)*d+a)) (s.J+1-(i+δ)*d)
def compressedPhase (s : Shape) (A h r d c v δ : ℕ) : ℕ :=
  evaluate (phaseLayer s A h r d c v δ) (s.J/d+1)
private theorem sum_boxPhase (s : Shape) (A h r d c v δ : ℕ) :
    (∑ q ∈ range (s.B+1), ∑ j ∈ range (s.J+1), boxPhase s A h r d c v δ q j) =
      compressedPhase s A h r d c v δ := by
  unfold boxPhase compressedPhase
  rw [evaluate_eq]
  conv_lhs =>
    enter [2, q]
    rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm, phaseLayer, evaluate_eq, ← sum_Ico_eq_sum_range, mul_sum]
  have hfilter : (range (s.J+1)).filter ((i+δ)*d ≤ ·) = Ico ((i+δ)*d) (s.J+1) := by
    ext j; simp [and_comm]
  rw [← hfilter, sum_filter]
  apply sum_congr rfl
  intro j _
  by_cases hj : (i+δ)*d≤j
  · rw [ite_eq_left hj, column_eq, mul_sum]
    have hqfilter :
        (range (s.B+1)).filter (fun q => j≤q ∧ q+(i+δ)*c≤s.B) =
          Ico j (s.B+1-(i+δ)*c) := by
      ext q
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    simp only [hj, true_and]
    rw [← sum_filter, hqfilter]
  · simp [hj]
theorem gain_eq_compressed (s : Shape) (A h r d c v : ℕ) (hd : 0<d) :
    gain s A h r d c v =
      compressedPhase s A h r d c v 0 - compressedPhase s A h r d c v 1 := by
  have hbox (δ q : ℕ) :
      (∑ j ∈ range (s.J+1), boxPhase s A h r d c v δ q j) =
        ∑ j ∈ range (min q s.J+1), boxPhase s A h r d c v δ q j := by
    symm
    apply sum_subset (range_mono (Nat.succ_le_succ (min_le_right _ _)))
    intro j hj hnot
    have hn : ¬ j≤q := by
      simp only [mem_range, Nat.lt_succ_iff, le_min_iff] at hj hnot
      omega
    simp [boxPhase, hn]
  apply Nat.eq_sub_of_add_eq
  rw [← sum_boxPhase, ← sum_boxPhase]
  simp only [hbox, gain, shapeSum, ← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (mem_range.mp hj)
  exact coordinate_phases s A h r d c v q j hd (Nat.le_of_lt_succ (mem_range.mp hq))
    (hj'.trans (min_le_left _ _)) (hj'.trans (min_le_right _ _))
#print axioms gain_eq_compressed
end Lower6960.HelperSource

end Merged_R6960HelperSourceArithmetic
