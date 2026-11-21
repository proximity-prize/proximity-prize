import ProximityPrize.SubmissionLower.PortLow6
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_9_7
noncomputable section
open K1_13 (Shape chart ceilDiv mixed32)
open P0_9 (linearChart taylorLength physicalDegree incidenceGap)
def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
def divisorBox : Shape := ⟨6300 + 952630000 / 33184, 2403 + 322000000 / 33184, 0⟩
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
open private topAt eval_topAt topAt_coeff topView_separant from ProximityPrize.SubmissionLower.Fast056
private def derivativeBox (p : Shape) : Shape := ⟨p.b - 1, p.j - 3, p.t - 1⟩
private theorem derivative_box (f : Row 4) {j : ℕ} (hj : 0 < j) :
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
open P0_9_7 (fatChart divisorBox)
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
  recovers : ∀ (L : Type) [Field L] [Algebra Geom L] (S : L[X]),
    S.natDegree ≤ physicalDegree → evalTrajectory f S = 0 →
    evalTrajectory (separant f) S ≠ 0 →
    evalTrajectory denom S ≠ 0 ∧ evalTrajectory test S = 0 ∧
      ∀ i, evalTrajectory (numer i) S = evalTrajectory denom S * C (S.coeff i.val)
abbrev CoeffRing := MvPolynomial (Fin taylorLength) Geom
def universalPolynomial : CoeffRing[X] :=
  ∑ i : Fin taylorLength, C (MvPolynomial.X i) * Polynomial.X ^ i.val
def universalEval (f : Row 4) : CoeffRing[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom (MvPolynomial.C : Geom →+* CoeffRing))
    (fun i => hasseDeriv i.val universalPolynomial) f
structure ActualFamily (f : Row 4) (P : Ideal CoeffRing) : Prop where
  prime : P.IsPrime
  dimension : 2 ≤ (MvPolynomial.affineHilbertPolynomial P).natDegree
  solves : ∀ i, (universalEval f).coeff i ∈ P
  regular : ∃ i, (universalEval (separant f)).coeff i ∉ P
end
end P0_9_7_2
end
section
namespace P0_9_7_2
noncomputable section
open K1_13 K1_13_6 K1_13_7 K1_13_7_2 K1_13_7_2_1 K1_13_7_2_1_2
open MvPolynomial UniqueFactorizationMonoid
open scoped Polynomial
open private geometric_injective liftLower_ne_zero from ProximityPrize.SubmissionLower.Fast070
open private local_length_one tangent_invariant from ProximityPrize.SubmissionLower.Fast070
open private top top_rename_lower top_map top_derivative from ProximityPrize.SubmissionLower.Fast070
private theorem local_generators (f : Row 4) (q : Row 3)
    (hq : Squarefree (genericRow q)) (surface : Ideal GeoJets)
    (h : LiftedSurface f q surface) : LocalGenerators f q surface h.minimal.isPrime := by
  let : surface.IsPrime := h.minimal.isPrime
  let A := Localization.AtPrime surface
  let l : GeoJets →+* A := algebraMap GeoJets A
  let J := intersectionIdeal f (liftLower q)
  let e : GeoJets ≃ₐ[GeoField] Lower[X] := top
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
open P0_9_7_2 (CoeffRing FatTaylor)
open scoped BigOperators
private theorem generic_degree_le (g : Row 4) : (toGeneric g).totalDegree ≤ g.totalDegree := by
  rw [toGeneric, MvPolynomial.totalDegree_eq, MvPolynomial.totalDegree_eq]
  exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
theorem generic_ne_zero {f : Row 4} (hf : Irreducible f) : toGeneric f ≠ 0 := by
  have hinj : Function.Injective genericCoeffs :=
    (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective Geom[X] GenericField)
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
open private lift_length_ge lift_length_finite from ProximityPrize.SubmissionLower.Fast066
open private supported_anchor supported_lower supported_coordinate mixed_matches from ProximityPrize.SubmissionLower.Fast066
private theorem common_section : K1_13_7_5_3.c1 :=
  K1_13_7_5_3_1.of_children K1_13_7_5_3_1_1.proof K1_13_7_5_3_1_2.proof
private theorem sparse_length : K1_13_7_5_3.c3 :=
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
open private supported_sub supported_C supported_X exists_coordinate_cut jetPoint_injective
  chart_section eval_chart_section weighted_ceil from ProximityPrize.SubmissionLower.Fast066
private theorem choose_linear_cut {f : Row 4} (ht : 0 < (shape f).t)
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
open private linearJet eval_linearJet separant_bound linearJet_bound K1_13_7_5_2.denominator ordinary_eq_hasse
  from ProximityPrize.SubmissionLower.Fast072
open private supported_of_fits eval_center from ProximityPrize.SubmissionLower.Fast072
open private supported_C_mul from ProximityPrize.SubmissionLower.Fast066
local notation "W" => MvPolynomial.weightedTotalDegree
private def numerator (L : ℕ) (f : Row 4) (n : ℕ) : Row 4 :=
  if hn : n < 4 then MvPolynomial.X ⟨n, hn⟩ * K1_13_7_5_2.denominator L f
  else
    MvPolynomial.C (Polynomial.C (↑n.factorial : Geom)⁻¹) *
      (separant f ^ (L - n) * linearJet f n)
private theorem denominator_bound (L : ℕ) (w : Fin 4 → ℕ) {f : Row 4} {B : ℕ}
    (hf : W w f ≤ B) : W w (K1_13_7_5_2.denominator L f) ≤ L * (B - w 3) :=
  (weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _ (separant_bound w hf))
private theorem numerator_bound {L n : ℕ} (hn : n ≤ L) (w : Fin 4 → ℕ) (Δ d₀ : ℕ)
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
private theorem coefficients_recover {L : ℕ} (hL : L < K1.p) {f : Row 4}
    (hf : (shape f).t = 1) (S : Geom[X]) (hon : atJet f S = 0) (hr : RegularAt f S) :
    evalGeneric S (toGeneric (K1_13_7_5_2.denominator L f)) ≠ 0 ∧
      ∀ i : Fin L, evalGeneric S (toGeneric (numerator L f i.val)) =
        evalGeneric S (toGeneric (K1_13_7_5_2.denominator L f)) * genericCoeffs (hasseDeriv i.val S) := by
  have hp : atJet (separant f) S ≠ 0 := hr
  have hden : atJet (K1_13_7_5_2.denominator L f) S = atJet (separant f) S ^ L :=
    map_pow (MvPolynomial.eval (jet S : Fin 4 → Geom[X])) _ _
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
    · let E := MvPolynomial.eval (jet S : Fin 4 → Geom[X])
      change E (_ * (_ ^ _ * _)) = _
      rw [map_mul, map_mul, map_pow, MvPolynomial.eval_C]
      change _ * (atJet (separant f) S ^ (L - i.val) *
        atJet (linearJet f i.val) S) = _
      rw [eval_linearJet hf S hon hr, ordinary_eq_hasse]
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
private theorem eval_taylor {L : ℕ} (S : K[X]) (hS : S.natDegree < L) (x : K) :
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
    ∃ C : ValueChart H, ∀ S : K[X], S.natDegree < L →
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
open private denominator denominator_bound topPartial_bound jet_bound ordinary_eq_hasse
  from ProximityPrize.SubmissionLower.Fast059
open private supported_of_fits constants center eval_center from ProximityPrize.SubmissionLower.Fast072
open private supported_C_mul from ProximityPrize.SubmissionLower.Fast066
local notation "W" => MvPolynomial.weightedTotalDegree
private def coefficientNumerator (L : ℕ) (g : Row 4) (n : ℕ) : Row 4 :=
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
private theorem coefficients_fit (L : ℕ) (g : Row 4) (p : Shape) (hB : InBox (shape g) p)
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
private theorem coefficients_recover (L : ℕ) (g : Row 4) (S : Geom[X])
    (hg : atJet g S = 0) (hr : RegularAt g S) :
    evalGeneric S (toGeneric (denominator L g)) ≠ 0 ∧
      ∀ n ≤ L, n < K1.p →
        evalGeneric S (toGeneric (coefficientNumerator L g n)) =
          evalGeneric S (toGeneric (denominator L g)) * genericCoeffs (hasseDeriv n S) := by
  have hp : atJet (separant g) S ≠ 0 := hr
  have hden : atJet (denominator L g) S = atJet (separant g) S ^ (2 * L) :=
    map_pow (MvPolynomial.eval (jet S : Fin 4 → Geom[X])) _ _
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
    · let E := MvPolynomial.eval (jet S : Fin 4 → Geom[X])
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
