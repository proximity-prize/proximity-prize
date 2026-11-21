import ProximityPrize.SubmissionLower.Fast077
import ProximityPrize.SubmissionLower.PortLowBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_9_6
noncomputable section
open Polynomial
open P0 (K)
open P0_9 (SmallFactor physicalDegree primaryBox primaryCutoff taylorLength TrueWeightLE)
open K1_13 (Geom Row Shape shape extend InBox OnFactor OrderAt chart mixed32)
open K1_13_6 (HighChart toGeneric markIdeal separant jetNumerator divisorIdeal cycleLength)
structure CutInput (Γ : Finset K) (s : K → K[X]) (f Q : Row 4) (l : ℕ) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  small : SmallFactor f
  onFactor : ∀ γ ∈ Γ, OnFactor f (extend (s γ))
  positive : 0 < l
  proper : ¬ f ∣ Q
  box : InBox (shape Q) primaryBox
  weight : TrueWeightLE Q primaryCutoff
  order : ∀ γ ∈ Γ, OrderAt Q (extend (s γ)) l
def membershipTest (g : Row 4) : Row 4 := jetNumerator g taylorLength
def nextTest (g : Row 4) : Row 4 := jetNumerator g (taylorLength + 1)
def auxCurves32 (x : Shape) : ℕ :=
  let p := x.chamber
  let h := chart taylorLength p
  mixed32 p primaryBox (primaryBox.plus (p.scale 4)) h + 2 * x.t * mixed32 p p p h
def auxPoints32 (x : Shape) : ℕ :=
  let p := x.chamber
  mixed32 p primaryBox (primaryBox.plus (p.scale 4)) p + 2 * x.t * mixed32 p p p p
end
end P0_9_6
end
section
namespace P0_9_6_1
noncomputable section
open K1_13 (Row Shape shape InBox)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength)
open K1_13_6_1 (anchorBox DerivativeWeight)
open P0_9 (primaryBox)
def SurfaceCut (f Q : Row 4) (surface : Ideal GeoJets) (P : Row 4) : Prop :=
  ∃ (hZ : (intersectionIdeal f Q).IsMinimalPrime surface) (v w : ℕ),
    0 < v ∧ cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞) ∧
    (w = 0 ∨ ∃ r, 0 < r ∧ r < (shape f).t ∧ DerivativeWeight f surface r w) ∧
    toGeneric P ∉ surface ∧
    InBox (shape P) (primaryBox.plus ((anchorBox f).scale (4*v + 2*w)))
end
end P0_9_6_1
end
section
namespace P0_9_6_1
noncomputable section
open Polynomial
open K1_13 (Row Geom Shape shape InBox extend atJet OnFactor OrderAt)
open K1_13_6 (GeoJets CanonicalChart HighMark Invariant separant toGeneric
  markIdeal intersectionIdeal cycleLength genericCoeffs)
open K1_13_6_1 (HasMark anchorBox tangentCut DerivativeWeight
  mem_markIdeal orderAt_vanishes tangentCut_vanishes)
open K1_13_6_1_2 (VanishesTo multiOrder hassePartial map_hassePartial
  cycleLength_pos cycleLength_ge_order pair_height hasse_inBox hasse_atJet_eq_zero)
open K1_13_6_1_3 (tangent_proper tangent_box anchor_fits derivative_fits)
open P0_9 (SmallFactor primaryBox)
open P0_9_6 (CutInput)
open private topAt topAt_coeff eval_topAt topView_separant from ProximityPrize.SubmissionLower.Fast056
theorem canonicalChart {f : Row 4} {surface : Ideal GeoJets} {S : Geom[X]}
    (htop : (shape f).t ≤ 10) (hon : OnFactor f S)
    (hfmem : toGeneric f ∈ surface) (hmark : surface ≤ markIdeal S) :
    ∃ r, CanonicalChart f surface r ∧
      InBox (shape (separant ((separant^[r]) f))) (anchorBox f) := by
  classical
  let t := (shape f).t
  let P := topAt S f
  have hdeg : P.natDegree ≤ t := Polynomial.natDegree_map_le.trans_eq
    (K1_13_1.topView_degree f)
  have hnz : (derivative^[t] P).coeff 0 ≠ 0 := by
    rw [coeff_iterate_derivative, Nat.zero_add, Nat.descFactorial_self, nsmul_eq_mul]
    change (t.factorial : Geom[X]) * P.coeff t ≠ 0
    rw [← map_natCast (Polynomial.C : Geom →+* Geom[X])]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      (K1_13_7_1.factorial_cast_ne_zero (htop.trans_lt (by decide : 10 < K1.p))))
      (by simpa only [P, t, topAt_coeff] using hon.2)
  have hc : derivative^[t] P = Polynomial.C ((derivative^[t] P).coeff 0) :=
    eq_C_of_natDegree_le_zero ((natDegree_iterate_derivative _ _).trans
      (by omega : P.natDegree - t ≤ 0))
  have he (k : ℕ) : atJet ((separant^[k]) f) S =
      (derivative^[k] P).eval (K1_13.jet S (3 : Fin 4)) := by
    rw [← eval_topAt]
    congr 1
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [Function.iterate_succ_apply']
      change (K1_13_1.topView (separant ((separant^[k]) f))).map
        (MvPolynomial.eval (K1_13.jet S)) = _
      rw [topView_separant, ← derivative_map]
      exact congrArg derivative ih
  have htSurface : toGeneric ((separant^[t]) f) ∉ surface := by
    intro hm
    have hv := mem_markIdeal.mp (hmark hm)
    rw [he, hc, Polynomial.eval_C] at hv
    exact hnz hv
  have hex : ∃ i, toGeneric ((separant^[i]) f) ∉ surface := ⟨t, htSurface⟩
  let n := Nat.find hex
  have hn : toGeneric ((separant^[n]) f) ∉ surface := Nat.find_spec hex
  have hnt : n ≤ (shape f).t := Nat.find_min' hex htSurface
  have hn0 : n ≠ 0 := by
    intro h
    exact hn (by simpa only [h, Function.iterate_zero_apply] using hfmem)
  have hstep : (n - 1).succ = n := by omega
  have hsep : separant ((separant^[n - 1]) f) = (separant^[n]) f := by
    rw [← Function.iterate_succ_apply' separant (n - 1) f, hstep]
  refine ⟨n - 1, ⟨by omega, ?_, ?_⟩, ?_⟩
  · intro i hi
    by_contra h
    exact Nat.find_min hex (show i < n by omega) h
  · rwa [hsep]
  · rw [hsep]
    exact derivative_fits f n
private theorem lowHasse {f Q : Row 4} {l : ℕ} {surface : Ideal GeoJets}
    (hZ : (intersectionIdeal f Q).IsMinimalPrime surface)
    (hf : Irreducible f) (hproper : ¬ f ∣ Q) (hbox : InBox (shape Q) primaryBox) :
    ∃ v : ℕ, 0 < v ∧ v ≤ (shape f).b * primaryBox.b ∧
      cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞) ∧
      (v < l → ∃ P : Row 4, toGeneric P ∉ surface ∧ InBox (shape P) primaryBox ∧
        ∀ S, OrderAt Q S l → atJet P S = 0) := by
  let _ : surface.IsPrime := hZ.isPrime
  have hf0 : toGeneric f ≠ 0 := fun h =>
    hf.ne_zero (K1_13_7_1.toGeneric_injective (h.trans (map_zero _).symm))
  have hrel := K1_13_7_1.proper_generic f Q hf hproper
  have hheight : surface.height = 2 := pair_height hf0 hrel hZ
  have hdeg (P : Row 4) : (toGeneric P).totalDegree ≤ (shape P).b :=
    Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  have hup : cycleLength (intersectionIdeal f Q) surface hZ.isPrime ≤
      (↑((shape f).b * primaryBox.b) : ℕ∞) :=
    (K1_13_6_1_2_1.proof _ _ _ hZ hf0 hrel).trans
      (by exact_mod_cast Nat.mul_le_mul (hdeg f) ((hdeg Q).trans hbox.1))
  have hnotop : cycleLength (intersectionIdeal f Q) surface hZ.isPrime ≠ ⊤ :=
    ne_of_lt (hup.trans_lt (ENat.natCast_lt_top _))
  let v := (cycleLength (intersectionIdeal f Q) surface hZ.isPrime).toNat
  have hv : cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞) :=
    (ENat.natCast_toNat hnotop).symm
  have hpos := cycleLength_pos hZ.isPrime hZ.le
  rw [hv] at hpos hup
  refine ⟨v, by exact_mod_cast hpos, by exact_mod_cast hup, hv, ?_⟩
  intro hl
  have hcut : ∃ a : Fin 4 →₀ ℕ, multiOrder a < v + 1 ∧
      toGeneric (hassePartial a Q) ∉ surface := by
    by_contra! hn
    have horder : VanishesTo surface (toGeneric Q) (v + 1) := by
      apply K1_13_6_1_2_2.proof _ surface (v + 1) hheight
      intro a ha
      change hassePartial a (MvPolynomial.map genericCoeffs Q) ∈ surface
      rw [← map_hassePartial genericCoeffs a Q]
      exact hn a ha
    have hfp : toGeneric f ∈ surface := hZ.le (Ideal.subset_span (by simp))
    have hge := cycleLength_ge_order hheight hfp horder
    rw [hv] at hge
    exact (by omega : ¬ v + 1 ≤ v) (by exact_mod_cast hge)
  obtain ⟨a, ha, hproper'⟩ := hcut
  exact ⟨hassePartial a Q, hproper', hasse_inBox a hbox,
    fun S hS => hasse_atJet_eq_zero (by omega) hS⟩
private theorem chart_cut {g P : Row 4} {surface : Ideal GeoJets}
    (hZ : (intersectionIdeal g P).IsMinimalPrime surface)
    (hrel : IsRelPrime (toGeneric g) (toGeneric P)) (hsep : toGeneric (separant g) ∉ surface)
    (hi : ¬ Invariant g surface) {v : ℕ} (hv : 0 < v) (hchar : v < K1.p)
    (hlen : cycleLength (intersectionIdeal g P) surface hZ.isPrime = (v : ℕ∞)) :
    toGeneric (tangentCut g P v) ∉ surface := by
  have hg : toGeneric g ∈ surface := hZ.le (Ideal.subset_span (Set.mem_insert _ _))
  have hlen' := K1_13_6_1_3_3.proof g P surface hZ v hlen hchar
  have hn := K1_13_6_1_3_2.proof g P surface hZ v hrel hsep hv hlen'
  exact tangent_proper hZ.isPrime hg hi hchar hn
private theorem derivative_proper {f : Row 4} (hf : Irreducible f) (ht : 0 < (shape f).t) (j : ℕ)
    (hj : 0 < j) (hg : (separant^[j]) f ≠ 0) : ¬ f ∣ (separant^[j]) f := by
  rintro ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    intro hz
    exact hg (by rw [hq, hz, mul_zero])
  have hd := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.ne_zero hq0
  have h := K1_13_7_1.derivative_degree f j
  change ((separant^[j]) f).degreeOf 3 ≤ f.degreeOf 3 - j at h
  change 0 < f.degreeOf 3 at ht
  rw [hq, hd] at h
  omega
private theorem box_charge {f P : Row 4} {k j : ℕ}
    (hP : InBox (shape P) ((anchorBox f).scale k)) (hkj : k ≤ j) :
    InBox (shape P) (primaryBox.plus ((anchorBox f).scale j)) := by
  rcases hP with ⟨h1, h2, h3⟩
  exact ⟨h1.trans ((Nat.mul_le_mul_right _ hkj).trans (Nat.le_add_left _ _)),
    h2.trans ((Nat.mul_le_mul_right _ hkj).trans (Nat.le_add_left _ _)),
    h3.trans ((Nat.mul_le_mul_right _ hkj).trans (Nat.le_add_left _ _))⟩
private theorem box_cutter_charge {f P : Row 4} {k j : ℕ}
    (hP : InBox (shape P) (primaryBox.plus ((anchorBox f).scale k))) (hkj : k ≤ j) :
    InBox (shape P) (primaryBox.plus ((anchorBox f).scale j)) := by
  rcases hP with ⟨h1, h2, h3⟩
  exact ⟨h1.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hkj) _),
    h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hkj) _),
    h3.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hkj) _)⟩
end
end P0_9_6_1
end
section
namespace P0_9_6
noncomputable section
open Polynomial
open P0 (K)
open P0_9 (physicalPrice primaryBox surfaceNumerator32 taylorLength)
open K1_13 (Row Shape Geom extend atJet shape ceilDiv)
open K1_13_6 (Pieces toGeneric
  separant jetNumerator HighMark divisorIdeal cycleLength eval_jetNumerator)
open K1_13_6_1 (mem_markIdeal mark_curve)
open scoped BigOperators
def c1 : Prop :=
  ∀ Γ s f Q l, CutInput Γ s f Q l →
    ∃ (C : Pieces Γ) (B : Finset K),
      C.curves s ∧
      (∀ γ ∈ Γ, ¬ HighMark f Q l (extend (s γ)) → γ ∈ C.union ∪ B) ∧
      32 * C.total ≤ auxCurves32 (shape f) ∧
      32 * (B.card + C.n) ≤ 2 * auxPoints32 (shape f)
end
end P0_9_6
end
section
namespace P0_9_6_1_1
noncomputable section
open K1_13 (Row Shape shape InBox chart mixed32)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength divisorIdeal separant)
open K1_13_6_1 (anchorBox DerivativeWeight CurveOnFactor sectionDegree)
open K1_13_6_1_4 (FullChamber pair_dimension curve_of_proper_cut surfaceDegree)
open K1_13_7_1 (Chamber GeoFits toGeneric_fits toGeneric_injective proper_generic shape_chamber chart_chamber)
open P0_9 (SmallFactor primaryBox taylorLength)
open P0_9_6_1 (SurfaceCut)
open scoped BigOperators
private theorem proper_divisor : K1_13_6_1_4.c1 :=
  K1_13_6_1_4_1.of_children K1_13_6_1_4_1_1.proof K1_13_6_1_4_1_2.proof
private theorem additive_sections : K1_13_6_1_4.c2 := by
  apply K1_13_6_1_4_2.of_children
  · apply K1_13_6_1_4_2_1.of_children
    · exact K1_13_6_1_4_2_1_1.of_children
        K1_13_6_1_4_2_1_1_1.proof K1_13_6_1_4_2_1_1_2.proof
    · exact K1_13_6_1_4_2_1_2.of_children K1_13_6_1_4_2_1_2_1.proof
        (K1_13_6_1_4_2_1_2_2.of_children
          K1_13_6_1_4_2_1_2_2_1.proof K1_13_6_1_4_2_1_2_2_2.proof)
  · exact K1_13_6_1_4_2_2.of_children
      K1_13_6_1_4_2_2_1.proof K1_13_6_1_4_2_2_2.proof
private theorem weighted_pair : K1_13_6_1_4.c3 := by
  refine K1_13_6_1_4_3.of_children K1_13_6_1_4_3_1.proof K1_13_6_1_4_3_2.proof ?_
  apply K1_13_6_1_4_3_3.of_children
  · exact K1_13_6_1_4_3_3_1.of_children
      K1_13_6_1_4_3_3_1_1.proof K1_13_6_1_4_3_3_1_2.proof
  · exact K1_13_6_1_4_3_3_2.of_children
      K1_13_6_1_4_3_3_2_1.proof K1_13_6_1_4_3_3_2_2.proof
  · exact K1_13_6_1_4_3_3_3.of_children K1_13_6_1_4_3_3_3_1.proof
      (K1_13_6_1_4_3_3_3_2.of_children
        K1_13_6_1_4_3_3_3_2_1.proof K1_13_6_1_4_3_3_3_2_2.proof)
private theorem full_chart (L : ℕ) (hL : 0 < L) (p : Shape) : FullChamber (chart L p) := by
  refine ⟨chart_chamber _ _, ?_⟩
  change 0 < min (2*L*(p.t-1)+L+1) ((2*L*(p.j-3)+L+3)/3)
  omega
private theorem full_plus {a b : Shape} (ha : FullChamber a) (hb : Chamber b) :
    FullChamber (a.plus b) := by
  obtain ⟨⟨ha₁, ha₂⟩, ha₃⟩ := ha
  obtain ⟨hb₁, hb₂⟩ := hb
  change (a.j + b.j ≤ a.b + b.b ∧ 3 * (a.t + b.t) ≤ a.j + b.j) ∧ 0 < a.t + b.t
  exact ⟨⟨by omega, by omega⟩, by omega⟩
private theorem chamber_scale {a : Shape} (ha : Chamber a) (k : ℕ) :
    Chamber (a.scale k) := by
  refine ⟨Nat.mul_le_mul_left k ha.1, ?_⟩
  simpa [Shape.scale, Nat.mul_left_comm 3 k] using Nat.mul_le_mul_left k ha.2
private theorem full_scale {a : Shape} (ha : FullChamber a) {k : ℕ} (hk : 0 < k) :
    FullChamber (a.scale k) :=
  ⟨chamber_scale ha.1 k, Nat.mul_pos hk ha.2⟩
private theorem charge_coord (q p v w : ℕ) (hv : 0 < v) :
    q + (4*v + 2*w) * p ≤ v*(q + 4*p) + (2*w)*p := by
  calc
    _ = q + v*(4*p) + (2*w)*p := by ring
    _ ≤ v*q + v*(4*p) + (2*w)*p := by
      have hq : q ≤ v*q := Nat.le_mul_of_pos_left q hv
      exact Nat.add_le_add_right (Nat.add_le_add_right hq _) _
    _ = _ := by ring
private theorem supported_charge {f P : Row 4} {v w : ℕ} (hv : 0 < v)
    (h : InBox (shape P) (primaryBox.plus ((anchorBox f).scale (4*v + 2*w)))) :
    GeoFits (toGeneric P)
      (((primaryBox.plus ((anchorBox f).scale 4)).scale v).plus ((anchorBox f).scale (2*w))) :=
  toGeneric_fits ⟨h.1.trans (charge_coord _ _ _ _ hv),
    h.2.1.trans (charge_coord _ _ _ _ hv), h.2.2.trans (charge_coord _ _ _ _ hv)⟩
private theorem sum_biUnion_bound {α β : Type*} [DecidableEq β]
    (s : Finset α) (pieces : α → Finset β) (d : β → ℕ) :
    (∑ b ∈ s.biUnion pieces, d b) ≤ ∑ a ∈ s, ∑ b ∈ pieces a, d b := by
  rw [← Finset.sup_eq_biUnion]
  refine s.apply_sup_le_sum (f := fun t => ∑ b ∈ t, d b) (by simp) ?_
  intro u v
  change (∑ b ∈ u ∪ v, d b) ≤ _
  have heq := Finset.sum_union_inter (s₁ := u) (s₂ := v) (f := d)
  omega
private theorem toGeneric_ne_zero {F : Row 4} (hF : F ≠ 0) : toGeneric F ≠ 0 := by
  intro h
  apply hF
  apply toGeneric_injective
  simpa only [toGeneric, map_zero] using h
end
end P0_9_6_1_1
end
section
namespace P0_9_6_1_2
noncomputable section
open Polynomial MvPolynomial
open K1 (K)
open K1_13 (Row Shape Geom InBox embed extend chart atJet)
open K1_13_6 (GeoJets GeoField genericCoeffs evalGeneric toGeneric separant jetNumerator
  eval_jetNumerator)
open K1_13_6_2_1 (three_weights separant_pow_bound jet_bound)
open K1_13_7 (RegularAt)
open K1_13_7_1 (Chamber GeoFits weight_X_le weight_const_mul_le factorial_cast_ne_zero
  evalGeneric_toGeneric genericCoeffs_injective)
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
private structure TaylorChart (L : ℕ) where
  denom : GeoJets
  numerator : Fin L → GeoJets
private def TaylorChart.Fits {L : ℕ} (T : TaylorChart L) (h : Shape) : Prop :=
  GeoFits T.denom h ∧ ∀ i, GeoFits (T.numerator i) h
private def TaylorChart.Recovers {L : ℕ} (T : TaylorChart L) (S : Geom[X]) : Prop :=
  evalGeneric S T.denom ≠ 0 ∧
    ∀ i, evalGeneric S (T.numerator i) =
      evalGeneric S T.denom * genericCoeffs (hasseDeriv i.val S)
private abbrev AffineForm (L : ℕ) := GeoField × (Fin L → GeoField)
private def TaylorChart.pullback {L : ℕ} (T : TaylorChart L) (a : AffineForm L) : GeoJets :=
  MvPolynomial.C a.1 * T.denom + ∑ i, MvPolynomial.C (a.2 i) * T.numerator i
private theorem TaylorChart.pullback_fits {L : ℕ} (T : TaylorChart L) {h : Shape}
    (hT : T.Fits h) (a : AffineForm L) : GeoFits (T.pullback a) h := by
  classical
  have hw (w : Fin 4 → ℕ) (d : ℕ) (hD : T.denom.weightedTotalDegree w ≤ d)
      (hN : ∀ i, (T.numerator i).weightedTotalDegree w ≤ d) :
      (T.pullback a).weightedTotalDegree w ≤ d := by
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.add_mem
    · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((weight_const_mul_le _ _ _).trans hD)
    · apply Submodule.sum_mem
      intro i _
      exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((weight_const_mul_le _ _ _).trans (hN i))
  refine ⟨?_, hw Fin.val h.j hT.1.2.1 (fun i => (hT.2 i).2.1), ?_⟩
  · simpa only [weightedTotalDegree_one] using hw 1 h.b
      (by simpa only [weightedTotalDegree_one] using hT.1.1)
      (fun i => by simpa only [weightedTotalDegree_one] using (hT.2 i).1)
  · simpa only [weightedTotalDegree_piSingle] using hw (Pi.single (3 : Fin 4) 1) h.t
      (by simpa only [weightedTotalDegree_piSingle] using hT.1.2.2)
      (fun i => by simpa only [weightedTotalDegree_piSingle] using (hT.2 i).2.2)
private def denominator (L : ℕ) (g : Row 4) : Row 4 :=
  separant g ^ (2 * L)
private def numerator (L : ℕ) (g : Row 4) (i : Fin L) : Row 4 :=
  if hi : i.val < 4 then MvPolynomial.X ⟨i.val, hi⟩ * denominator L g
  else
    MvPolynomial.C (Polynomial.C (↑i.val.factorial : Geom)⁻¹) *
      (separant g ^ (2 * (L - i.val)) * jetNumerator g i.val)
def recoveryChart (L : ℕ) (g : Row 4) : TaylorChart L where
  denom := toGeneric (denominator L g)
  numerator i := toGeneric (numerator L g i)
private theorem numerator_bound {L : ℕ} (w : Fin 4 → ℕ) (Δ d₀ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) (hw : ∀ i, w i ≤ d₀)
    {g : Row 4} {B : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (i : Fin L) :
    W w (numerator L g i) ≤ d₀ + 2 * L * (B - w 3) + L * Δ := by
  have hi : i.val ≤ L := i.isLt.le
  unfold numerator
  split_ifs
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add ((weight_X_le w _).trans (hw _)) (separant_pow_bound w hg _)).trans
        (Nat.le_add_right _ _))
  · apply (weight_const_mul_le _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _ ≤ 2 * (L - i.val) * (B - w 3) + (w 0 + i.val * (2 * (B - w 3) + Δ)) :=
        Nat.add_le_add (separant_pow_bound w hg _) (jet_bound w Δ hshift hB hg i.val)
      _ = w 0 + 2 * (i.val + (L - i.val)) * (B - w 3) + i.val * Δ := by ring
      _ ≤ _ := by
        rw [Nat.add_sub_of_le hi]
        exact Nat.add_le_add (Nat.add_le_add_right (hw 0) _) (Nat.mul_le_mul_right Δ hi)
private theorem chart_fits {L : ℕ} {g : Row 4} {p : Shape}
    (hg : InBox (K1_13.shape g) p) (hp : Chamber p) (ht : 0 < p.t) :
    (recoveryChart L g).Fits (chart L p) := by
  constructor
  · apply three_weights hg hp ht
    intro w Δ d₀ B _ _ _ hB
    exact (separant_pow_bound w hB (2 * L)).trans (by omega)
  · intro i
    exact three_weights hg hp ht (fun w Δ d₀ _ hs hw hwB hB =>
      numerator_bound w Δ d₀ hs hw hwB hB i)
private theorem ordinary_eq_hasse (S : Geom[X]) (n : ℕ) :
    derivative^[n] S = Polynomial.C (n.factorial : Geom) * hasseDeriv n S := by
  ext m
  rw [coeff_iterate_derivative, Polynomial.coeff_C_mul, hasseDeriv_coeff,
    Nat.descFactorial_eq_factorial_mul_choose]
  simp only [nsmul_eq_mul, Nat.cast_mul, mul_assoc]
private theorem chart_recovers {L : ℕ} (hL : L ≤ K1.p) {g : Row 4} {S : Geom[X]}
    (hg : atJet g S = 0) (hr : RegularAt g S) : (recoveryChart L g).Recovers S := by
  have hden : atJet (denominator L g) S = atJet (separant g) S ^ (2 * L) :=
    map_pow (MvPolynomial.eval (K1_13.jet S : Fin 4 → Geom[X])) _ _
  constructor
  · change evalGeneric S (toGeneric (denominator L g)) ≠ 0
    rw [evalGeneric_toGeneric, map_ne_zero_iff _ genericCoeffs_injective, hden]
    exact pow_ne_zero _ hr
  · intro i
    change evalGeneric S (toGeneric (numerator L g i)) =
      evalGeneric S (toGeneric (denominator L g)) * genericCoeffs (hasseDeriv i.val S)
    rw [evalGeneric_toGeneric, evalGeneric_toGeneric, ← map_mul]
    apply congrArg genericCoeffs
    unfold numerator
    split_ifs with hinit
    · unfold atJet
      rw [map_mul, MvPolynomial.eval_X, mul_comm]
      rfl
    · let E := MvPolynomial.eval (K1_13.jet S : Fin 4 → Geom[X])
      change E (_ * (_ ^ _ * _)) = _
      rw [map_mul, map_mul, map_pow, MvPolynomial.eval_C]
      change _ * (atJet (separant g) S ^ (2 * (L - i.val)) *
        atJet (jetNumerator g i.val) S) = _
      rw [eval_jetNumerator _ _ hg, ordinary_eq_hasse]
      have hinv : Polynomial.C (↑i.val.factorial : Geom)⁻¹ *
          Polynomial.C (↑i.val.factorial : Geom) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ (factorial_cast_ne_zero (i.isLt.trans_le hL)), map_one]
      have hpow : 2 * (L - i.val) + 2 * i.val = 2 * L := by
        rw [← Nat.mul_add, Nat.sub_add_cancel i.isLt.le]
      calc
        _ = (Polynomial.C (↑i.val.factorial : Geom)⁻¹ * Polynomial.C (↑i.val.factorial : Geom)) *
            ((atJet (separant g) S ^ (2 * (L - i.val)) * atJet (separant g) S ^ (2 * i.val)) *
              hasseDeriv i.val S) := by ring
        _ = _ := by rw [hinv, one_mul, ← pow_add, hpow, hden]
private abbrev constants : Geom →+* GeoField := genericCoeffs.comp Polynomial.C
private abbrev center : GeoField := genericCoeffs Polynomial.X
private def valueForm (L : ℕ) (x a : K) : AffineForm L :=
  (-constants (embed a), fun i => (constants (embed x) - center) ^ i.val)
private theorem eval_at_center (S : Geom[X]) : (S.map constants).eval center = genericCoeffs S := by
  rw [Polynomial.eval_map]
  change Polynomial.eval₂RingHom constants center S = genericCoeffs S
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [constants]
  · simp [center]
private theorem taylor_value {L : ℕ} (S : Geom[X]) (hS : S.natDegree < L) (x : Geom) :
    (∑ i : Fin L, genericCoeffs (hasseDeriv i.val S) * (constants x - center) ^ i.val) =
      constants (S.eval x) := by
  let P := S.map constants
  have hdeg : (taylor center P).natDegree < L := by
    rw [natDegree_taylor]
    exact natDegree_map_le.trans_lt hS
  have hcoeff (i : ℕ) :
      (taylor center P).coeff i = genericCoeffs (hasseDeriv i S) := by
    rw [taylor_coeff]
    change (hasseDeriv i (S.map constants)).eval center = _
    rw [hasseDeriv_map, eval_at_center]
  have heval := (taylor center P).eval_eq_sum_range' hdeg (constants x - center)
  rw [← Fin.sum_univ_eq_sum_range] at heval
  simp only [hcoeff] at heval
  rw [taylor_eval_sub, show P.eval (constants x) = constants (S.eval x) from
    Polynomial.eval_map_apply constants x] at heval
  exact heval.symm
private theorem value_cut_eval {L : ℕ} (T : TaylorChart L) {S : K[X]}
    (hS : S.natDegree < L) (hT : T.Recovers (extend S)) (x a : K) :
    evalGeneric (extend S) (T.pullback (valueForm L x a)) = 0 ↔ S.eval x = a := by
  have hdeg : (extend S).natDegree < L := natDegree_map_le.trans_lt hS
  have hval := taylor_value (extend S) hdeg (embed x)
  rw [Polynomial.eval_map_apply] at hval
  have hsum :
      (∑ i : Fin L, (constants (embed x) - center) ^ i.val *
        (evalGeneric (extend S) T.denom * genericCoeffs (hasseDeriv i.val (extend S)))) =
        evalGeneric (extend S) T.denom * constants (embed (S.eval x)) := by
    rw [← hval, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  unfold TaylorChart.pullback valueForm
  simp only [map_add, map_sum, map_mul, evalGeneric, MvPolynomial.eval_C]
  change (-constants (embed a)) * evalGeneric (extend S) T.denom +
      (∑ i : Fin L, (constants (embed x) - center) ^ i.val *
        evalGeneric (extend S) (T.numerator i)) = 0 ↔ _
  simp only [hT.2, hsum]
  rw [show -constants (embed a) * evalGeneric (extend S) T.denom +
      evalGeneric (extend S) T.denom * constants (embed (S.eval x)) =
      evalGeneric (extend S) T.denom * (constants (embed (S.eval x)) - constants (embed a)) by ring,
    mul_eq_zero, or_iff_right hT.1, sub_eq_zero]
  exact (genericCoeffs_injective.comp Polynomial.C_injective).eq_iff.trans embed.injective.eq_iff
theorem exists_value_cut {L : ℕ} (hL : L ≤ K1.p) {g : Row 4} {p : Shape}
    (hg : InBox (K1_13.shape g) p) (hp : Chamber p) (ht : 0 < p.t) (x a : K) :
    ∃ D : GeoJets, GeoFits D (chart L p) ∧
      ∀ S : K[X], S.natDegree < L → atJet g (extend S) = 0 → RegularAt g (extend S) →
        (evalGeneric (extend S) D = 0 ↔ S.eval x = a) := by
  let T := recoveryChart L g
  exact ⟨T.pullback (valueForm L x a), T.pullback_fits (chart_fits hg hp ht) _,
    fun S hS hvan hreg => value_cut_eval T hS (chart_recovers hL hvan hreg) x a⟩
end
end P0_9_6_1_2
end
section
namespace P0_9_6_1_2
noncomputable section
open Polynomial
open P0 (K)
open P0_9 (taylorLength)
open K1_13 (Shape InBox chart extend embed shape atJet)
open K1_13_6 (GeoJets CanonicalChart CurveSections evalGeneric markIdeal separant)
open K1_13_6_1 (CurveOnFactor anchorBox sectionDegree mem_markIdeal)
open K1_13_6_1_5 (coordinate_cut markPoint markPoint_injective)
open K1_13_7 (RegularAt)
open K1_13_7_1 (Chamber GeoFits derivative_in_box shape_chamber toGeneric_fits)
private theorem count_points : K1_13_6_1_5.c2 :=
  K1_13_6_1_5_2.of_children K1_13_6_1_5_2_1.proof K1_13_6_1_5_2_2.proof
private theorem count_marks {f C s p D} {Γ : Finset K}
    (hc : CurveOnFactor f C) (hp : InBox ⟨1, 3, 1⟩ p)
    (hD : GeoFits D p) (hproper : D ∉ C) (hinj : Set.InjOn s (Γ : Set K))
    {L : Finset K} (hL : L ⊆ Γ)
    (hmarks : ∀ γ ∈ L, C ≤ markIdeal (extend (s γ)) ∧ evalGeneric (extend (s γ)) D = 0) :
    6 * L.card ≤ sectionDegree C (p.scale 6) := by
  classical
  let point := fun γ => markPoint (extend (s γ))
  have hinjL : Set.InjOn point (L : Set K) := by
    intro γ hγ η hη he
    exact hinj (hL hγ) (hL hη)
      (Polynomial.map_injective embed embed.injective (markPoint_injective he))
  have hcount := count_points C p hc.prime hc.dim hp D hD hproper (L.image point) (by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact hmarks γ hγ)
  rwa [Finset.card_image_of_injOn hinjL] at hcount
private theorem chart_has_simplex (L : ℕ) (p : Shape) :
    InBox ⟨1, 3, 1⟩ (chart L p) := by
  unfold chart
  simp only [InBox]
  exact ⟨(Nat.le_add_right _ _).trans (le_max_left _ _),
    Nat.le_add_left _ _, le_min (by omega) (by omega)⟩
end
end P0_9_6_1_2
end
section
namespace P0_9_6_2
noncomputable section
open Polynomial
open P0 (K)
open P0_9 (physicalDegree primaryBox taylorLength)
open P0_9_6 (membershipTest nextTest)
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
end Branch
def budget5 (p : Shape) : ℕ :=
  let a := liftedChart (taylorLength + 1) p
  let b := liftedChart (taylorLength + 2) p
  mixed32 p primaryBox a b + (taylorLength + 1) * mixed32 p primaryBox (graphBox p) b +
    (taylorLength + 2) * mixed32 p primaryBox (graphBox p) a
end
end P0_9_6_2
end
section
namespace P0_9_6_2_3
noncomputable section
open P0_9 (primaryBox taylorLength)
open P0_9_6_2 (budget5)
open K1_13 (Shape liftedChart mixed32)
open K1_13_6 (GeoField)
open K1_13_6_2 (graphBox)
open K1_13_6_2_4 (Boxes Chamber Allowed Admissible allowed_coordinate
  DivisorBound divisor_bound mixedDegree diagonalExponents)
open K1_13_6_2_4_3 (volumeProduct sumCap diagonal)
open MvPolynomial
open scoped BigOperators
open private chart_chamber from ProximityPrize.SubmissionLower.Fast054
open private diagonal_coeff from ProximityPrize.SubmissionLower.Fast054
open private alt alt_insert alt_empty capDiff five_differences signed4_le
  from ProximityPrize.SubmissionLower.Fast054
theorem proper_cut_comparison : K1_13_6_2_4.ProperCutComparison :=
  K1_13_6_2_4_1.of_children K1_13_6_2_4_1_1.proof K1_13_6_2_4_1_2.proof
theorem cycle_comparison : K1_13_6_2_4.CycleComparison :=
  K1_13_6_2_4_2.of_children K1_13_6_2_4_2_1.proof
    (K1_13_6_2_4_2_2.of_children K1_13_6_2_4_2_2_1.proof K1_13_6_2_4_2_2_2.proof)
theorem divisor_comparison : DivisorBound :=
  divisor_bound proper_cut_comparison cycle_comparison
end
end P0_9_6_2_3
end
section
namespace P0_9_6_2_3
noncomputable section
open K1_13 (Row)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength GenericField GeoField)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (sectionIdeal cylinder oldEmbedding OfDim LengthAt)
open RingTheory.Sequence
open private weaklyRegular_pair_iff geometry_flat from ProximityPrize.SubmissionLower.Fast053
open private cylinder_regular cylinder_dimension relPrime_of_regular cylinder_minimal cylinder_length
  from ProximityPrize.SubmissionLower.Fast073
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem geometric_regular {f Q : Row 4} (hf : Irreducible f) (hQ : ¬ f ∣ Q) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {toGeneric f}) (toGeneric Q)) := by
  let I : Ideal (Row 4) := Ideal.span {f}
  let : I.IsPrime := (Ideal.span_singleton_prime hf.ne_zero).2 hf.prime
  have hphysical : IsWeaklyRegular (Row 4) [f, Q] := by
    rw [weaklyRegular_pair_iff]
    exact ⟨IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hf.ne_zero,
      IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
        (mt Ideal.Quotient.eq_zero_iff_mem.mp (Ideal.mem_span_singleton.not.mpr hQ))⟩
  let B := MvPolynomial (Fin 4) GenericField
  let T := (nonZeroDivisors (Polynomial K1_13.Geom)).map (MvPolynomial.C (σ := Fin 4))
  have h₁ := hphysical.of_isLocalization B T
  have := geometry_flat
  have h₂ := h₁.of_flat (S := GeoJets)
  simp only [List.map_cons, List.map_nil] at h₂
  change IsWeaklyRegular GeoJets
    [MvPolynomial.map (algebraMap GenericField GeoField)
      (MvPolynomial.map (algebraMap (Polynomial K1_13.Geom) GenericField) f),
     MvPolynomial.map (algebraMap GenericField GeoField)
      (MvPolynomial.map (algebraMap (Polynomial K1_13.Geom) GenericField) Q)] at h₂
  have h₃ : IsWeaklyRegular GeoJets [toGeneric f, toGeneric Q] := by
    simpa only [toGeneric, K1_13_6.genericCoeffs, MvPolynomial.map_map] using h₂
  exact ((weaklyRegular_pair_iff ..).mp h₃).2
theorem cylinder_comparison (f Q : Row 4) (hf : Irreducible f) (hQ : ¬ f ∣ Q) :
    let A := sectionIdeal ⊥ (oldEmbedding (toGeneric f))
    let J := sectionIdeal A (oldEmbedding (toGeneric Q))
    IsLeftRegular (Ideal.Quotient.mk A (oldEmbedding (toGeneric Q))) ∧
    ∀ P : Ideal GeoJets, ∀ h : (intersectionIdeal f Q).IsMinimalPrime P,
      OfDim (cylinder P) 3 ∧
        ∃ hc : J.IsMinimalPrime (cylinder P),
          cycleLength (intersectionIdeal f Q) P h.isPrime ≤ LengthAt J (cylinder P) hc.isPrime := by
  let F : Ideal GeoJets := Ideal.span {toGeneric f}
  have hA : sectionIdeal ⊥ (oldEmbedding (toGeneric f)) = cylinder F := by
    simp [sectionIdeal, cylinder, F, Ideal.map_span]
  have hJ : sectionIdeal (sectionIdeal ⊥ (oldEmbedding (toGeneric f))) (oldEmbedding (toGeneric Q)) =
      cylinder (intersectionIdeal f Q) := by
    rw [hA, intersectionIdeal, Ideal.span_insert]
    simp [sectionIdeal, cylinder, F, Ideal.map_sup, Ideal.map_span]
  have hreg := geometric_regular hf hQ
  have hF := K1_13_6_3_6.toGeneric_ne_zero hf.ne_zero
  dsimp only
  constructor
  · exact (congrArg (fun I : Ideal GeoJets5 =>
      IsLeftRegular (Ideal.Quotient.mk I (oldEmbedding (toGeneric Q)))) hA).mpr
      (cylinder_regular hreg)
  · intro P hP
    refine ⟨cylinder_dimension (K1_13_6_1_4.pair_dimension hF (relPrime_of_regular hF hreg) hP),
      ?_⟩
    apply (congrArg (fun I : Ideal GeoJets5 => ∃ hc : I.IsMinimalPrime (cylinder P),
      cycleLength (intersectionIdeal f Q) P hP.isPrime ≤ LengthAt I (cylinder P) hc.isPrime) hJ).mpr
    exact ⟨cylinder_minimal hP, (cylinder_length (intersectionIdeal f Q) P hP.isPrime).le⟩
end
end P0_9_6_2_3
end
section
set_option autoImplicit false
namespace P0_9_6_3
noncomputable section
open K1_13 (Row shape)
open K1_13_6 (toGeneric divisorIdeal intersectionIdeal cycleLength)
open K1_13_6_3 (CoeffIdeal JetIdeal dimension cycleWeight)
open P0_9 (primaryBox)
open P0_9_6 (membershipTest nextTest)
open MvPolynomial
open scoped BigOperators
structure SimpleCut (g : Row 4) (surface P : JetIdeal) : Prop where
  proper : toGeneric (membershipTest g) ∉ surface
  minimal : (divisorIdeal surface (membershipTest g)).IsMinimalPrime P
  one : cycleLength (divisorIdeal surface (membershipTest g)) P minimal.isPrime = 1
  next : toGeneric (nextTest g) ∈ P
structure CutCycle (f Q : Row 4) : Prop where
  local_bound : ∀ surface (hz : (intersectionIdeal f Q).IsMinimalPrime surface),
    dimension surface = 2 ∧ (1 : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface hz.isPrime ∧
    cycleLength (intersectionIdeal f Q) surface hz.isPrime ≤ ((shape f).b * primaryBox.b : ℕ)
  weighted_degree :
    ∑ surface ∈ (intersectionIdeal f Q).minimalPrimesFinset,
      (cycleWeight (intersectionIdeal f Q) surface : ℚ) * affineDegree surface
      ≤ ((shape f).b * primaryBox.b : ℕ)
end
end P0_9_6_3
end
section
set_option autoImplicit false
namespace P0_9_6_3
noncomputable section
open K1_13 K1_13_6 MvPolynomial
private theorem pderiv_degree (P : Row 4) (i : Fin 4) :
    (pderiv i P).totalDegree ≤ P.totalDegree - 1 := by
  simpa only [weightedTotalDegree_one, Pi.one_apply] using
    weightedTotalDegree_pderiv_le_sub (1 : Fin 4 → ℕ) i P
private theorem pderiv_zero_of_degree_zero {P : Row 4} (h : P.totalDegree = 0) (i : Fin 4) :
    pderiv i P = 0 := by
  rw [totalDegree_eq_zero_iff_eq_C.mp h, pderiv_C]
private theorem coefficientDerivative_degree (P : Row 4) :
    (coefficientDerivative P).totalDegree ≤ P.totalDegree := by
  unfold coefficientDerivative
  exact totalDegree_finsetSum_le fun m hm =>
    (totalDegree_monomial_le _ _).trans (le_totalDegree hm)
private theorem partialFlow_degree (P : Row 4) :
    (partialFlow P).totalDegree ≤ P.totalDegree := by
  unfold partialFlow
  apply (totalDegree_add _ _).trans
  refine max_le (coefficientDerivative_degree P) (totalDegree_finsetSum_le ?_)
  intro i _
  by_cases h : P.totalDegree = 0
  · simp [pderiv_zero_of_degree_zero h]
  · refine (totalDegree_mul _ _).trans ?_
    have hc : (MvPolynomial.C (Polynomial.C ((i.val + 1 : ℕ) : Geom)) *
        MvPolynomial.X i.succ : Row 4).totalDegree ≤ 1 :=
      (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X, zero_add])
    have hd := pderiv_degree P i.castSucc
    omega
private theorem flowNumerator_degree {g P : Row 4} {d : ℕ} (hd : g.totalDegree ≤ d) :
    (flowNumerator g P).totalDegree ≤ (d - 1) + P.totalDegree := by
  unfold flowNumerator
  apply (totalDegree_sub _ _).trans
  refine max_le ?_ ?_
  · apply (totalDegree_mul _ _).trans
    exact Nat.add_le_add (by exact (pderiv_degree g 3).trans (Nat.sub_le_sub_right hd _))
      (partialFlow_degree P)
  · by_cases h : P.totalDegree = 0
    · simp [separant, pderiv_zero_of_degree_zero h]
    · apply (totalDegree_mul _ _).trans
      have hg := (partialFlow_degree g).trans hd
      have hP : (separant P).totalDegree ≤ P.totalDegree - 1 := pderiv_degree P 3
      omega
private theorem clearedStep_degree {g P : Row 4} (a : ℕ) {d : ℕ} (hd : g.totalDegree ≤ d) :
    (clearedStep g a P).totalDegree ≤ P.totalDegree + 2 * (d - 1) := by
  unfold clearedStep
  apply (totalDegree_sub _ _).trans
  have hs : (separant g).totalDegree ≤ d - 1 :=
    (pderiv_degree g 3).trans (Nat.sub_le_sub_right hd _)
  refine max_le ?_ ?_
  · apply (totalDegree_mul _ _).trans
    have hp : (flowNumerator g P).totalDegree ≤ _ := flowNumerator_degree hd
    omega
  · apply (totalDegree_mul _ _).trans
    have hc : ((a : Row 4) * flowNumerator g (separant g)).totalDegree ≤
        (flowNumerator g (separant g)).totalDegree := by
      rw [← map_natCast (MvPolynomial.C : Polynomial Geom →+* Row 4) a]
      exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add])
    have hflow : (flowNumerator g (separant g)).totalDegree ≤ _ := flowNumerator_degree hd
    omega
private theorem jetNumerator_degree {g : Row 4} {d : ℕ} (hd : g.totalDegree ≤ d) (n : ℕ) :
    (jetNumerator g n).totalDegree ≤ 1 + 2 * n * (d - 1) := by
  induction n with
  | zero => simp [jetNumerator]
  | succ n ih =>
    rw [jetNumerator]
    apply (clearedStep_degree (2 * n) hd).trans
    rw [Nat.mul_succ, Nat.add_mul]
    omega
private theorem iterate_separant_degree (f : Row 4) (r : ℕ) :
    ((separant^[r]) f).totalDegree ≤ f.totalDegree := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact ((pderiv_degree _ 3).trans (Nat.sub_le _ _)).trans ih
end
end P0_9_6_3
end
section
set_option autoImplicit false
namespace P0_9_6_3
noncomputable section
open K1_13 K1_13_6
open K1_13_6_3 (JetIdeal)
open K1_13_6_3_1
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem flat_sepToGeo : Module.Flat SepJets GeoJets := by
  have h : Algebra.IsPushout SepField SepJets GeoField GeoJets := inferInstance
  exact Module.Flat.isBaseChange SepField SepJets GeoField GeoJets h.out
private theorem map_eq_maximal_of_length_one (J P : JetIdeal) [P.IsPrime]
    (h : cycleLength J P ‹P.IsPrime› = 1) :
    J.map (algebraMap GeoJets (Localization.AtPrime P)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  unfold cycleLength at h
  rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff] at h
  exact h
private theorem step_in_sep (g : Row 4) (D : Derivation ℤ SepJets SepJets)
    (hD : ∀ U : Row 4, D (rowToSep U) = rowToSep (flowNumerator g U))
    (n : ℕ) :
    rowToSep (jetNumerator g (n+1)) =
      rowToSep (separant g) * D (rowToSep (jetNumerator g n)) -
        (↑(2*n) : SepJets) * D (rowToSep (separant g)) * rowToSep (jetNumerator g n) := by
  simp only [jetNumerator, clearedStep, map_sub, map_mul, map_natCast, ← hD]
private theorem sep_sq_dvd_jet (g : Row 4) (D : Derivation ℤ SepJets SepJets)
    (hD : ∀ U : Row 4, D (rowToSep U) = rowToSep (flowNumerator g U))
    (n : ℕ) (hn : 1 ≤ n) :
    rowToSep (separant g)^2 ∣ rowToSep (jetNumerator g n) := by
  let s := rowToSep (separant g)
  change s^2 ∣ _
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      have hz : separant (MvPolynomial.X (0 : Fin 4) : Row 4) = 0 := by
        simp [separant, MvPolynomial.pderiv_X]
      use rowToSep (partialFlow (MvPolynomial.X 0))
      rw [step_in_sep g D hD 0, jetNumerator, hD, flowNumerator, hz]
      simp [s, pow_two, mul_assoc]
    | succ n =>
      obtain ⟨w, hw⟩ := ih (Nat.succ_pos _)
      rw [step_in_sep g D hD (n+1)]
      change s^2 ∣ s * D (rowToSep (jetNumerator g (n+1))) -
        (↑(2*(n+1)) : SepJets) * D s * rowToSep (jetNumerator g (n+1))
      rw [hw]
      use s * D w + 2 * D s * w - (↑(2*(n+1)) : SepJets) * D s * w
      simp only [pow_two, D.leibniz, smul_eq_mul]
      ring
private theorem nonvanishing_of_simple_cut {R : Type*} [CommRing R]
    (T P : Ideal R) [T.IsPrime] (hle : T ≤ P) {s e : R}
    (hs : s ∉ T) (he : s^2 ∣ e)
    (hsat : ∀ x ∈ P, ∃ t ∉ P, t * x ∈ T ⊔ Ideal.span {e}) : s ∉ P := by
  intro hsp
  obtain ⟨v, hv, hvs⟩ := hsat s hsp
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hvs
  obtain ⟨w, hw⟩ := he
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
  have hrel : s * (v - s * (w*c)) = a := by
    rw [hc, hw] at hab
    linear_combination -hab
  have hmem : v - s * (w*c) ∈ T :=
    (‹T.IsPrime›.mem_or_mem (hrel.symm ▸ ha)).resolve_left hs
  apply hv
  have hm := P.add_mem (hle hmem) (P.mul_mem_right (w*c) hsp)
  simpa using hm
private theorem stable_of_simple_cut {R : Type*} [CommRing R]
    (T P : Ideal R) [P.IsPrime] (hle : T ≤ P)
    (D : Derivation ℤ R R) (hT : ∀ u ∈ T, D u ∈ T)
    {e : R} (he : e ∈ P) (hDe : D e ∈ P)
    (hsat : ∀ x ∈ P, ∃ t ∉ P, t * x ∈ T ⊔ Ideal.span {e}) :
    ∀ u ∈ P, D u ∈ P := by
  intro u hu
  obtain ⟨t, ht, htu⟩ := hsat u hu
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htu
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
  have hDb : D b ∈ P := by
    rw [hc, D.leibniz, smul_eq_mul, smul_eq_mul]
    exact P.add_mem (P.mul_mem_right _ he) (P.mul_mem_left _ hDe)
  have hDtu : D (t*u) ∈ P := by
    rw [← hab, map_add]
    exact P.add_mem (hle (hT a ha)) hDb
  rw [D.leibniz, smul_eq_mul, smul_eq_mul] at hDtu
  exact (‹P.IsPrime›.mem_or_mem
    ((P.add_mem_iff_left (P.mul_mem_right (D t) hu)).mp hDtu)).resolve_left ht
end
end P0_9_6_3
end
section
set_option autoImplicit false
namespace P0_9_6_3
noncomputable section
open K1_13 K1_13_6
open K1_13_6_3 (JetIdeal dimension cycleWeight)
open K1_13_6_3_6 MvPolynomial RingTheory.Sequence
open scoped BigOperators TensorProduct Pointwise
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem coefficient_budget (J : JetIdeal) (hd : dimension J ≤ 2) : by
    classical
    exact (∀ P (hp : J.IsMinimalPrime P), cycleLength J P hp.isPrime ≠ ⊤) ∧
      ∑ P ∈ J.minimalPrimesFinset,
        (cycleWeight J P : ℚ) * (affineHilbertPolynomial P).coeff 2 ≤
        (affineHilbertPolynomial J).coeff 2 := by
  classical
  let T := J.minimalPrimesFinset
  suffices aux : ∀ I : JetIdeal, J ≤ I →
      (∀ P (hp : J.IsMinimalPrime P), cycleLength I P hp.isPrime ≠ ⊤) ∧
      ∑ P ∈ T, (cycleWeight I P : ℚ) * (affineHilbertPolynomial P).coeff 2 ≤
        (affineHilbertPolynomial I).coeff 2 from aux J le_rfl
  intro I
  induction I using WellFounded.induction (wellFounded_gt (α := JetIdeal)) with
  | h I ih =>
    intro hJI
    by_cases hI : I = ⊤
    · subst I
      have hz (P : JetIdeal) (hp : P.IsPrime) : cycleLength ⊤ P hp = 0 :=
        length_eq_zero_of_not_le hp (by simpa using hp.ne_top)
      exact ⟨fun P hp => by simp [hz P hp.isPrime], by
        refine le_of_eq ?_
        simp only [cycleWeight, affineHilbertPolynomial_top, Polynomial.coeff_zero]
        apply Finset.sum_eq_zero
        intro P hP
        have hp := (Ideal.mem_minimalPrimesFinset.mp hP).isPrime
        simp [dite_eq_left hp, hz P hp]⟩
    obtain ⟨g, hg, hprime⟩ := exists_prime_colon I hI
    let A : JetIdeal := I.colon {g}
    let B : JetIdeal := I ⊔ Ideal.span {g}
    have hIA : I ≤ A := Ideal.le_colon
    have hIB : I < B := lt_of_le_not_ge le_sup_left
      (fun h => hg (h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))))
    obtain ⟨hfin, hbudget⟩ := ih B hIB (hJI.trans hIB.le)
    have hstep (P : JetIdeal) (hp : J.IsMinimalPrime P) :
        cycleLength I P hp.isPrime =
          cycleLength A P hp.isPrime + cycleLength B P hp.isPrime :=
      length_step I P hp.isPrime g
    have hterm (P : JetIdeal) (hp : J.IsMinimalPrime P) :
        cycleLength A P hp.isPrime = if P = A then 1 else 0 := by
      split_ifs with h
      · subst P
        exact length_self A hp.isPrime
      · exact length_eq_zero_of_not_le hp.isPrime
          (fun hAP => h (le_antisymm (hp.2 ⟨hprime, hJI.trans hIA⟩ hAP) hAP))
    have hfinite (P : JetIdeal) (hp : J.IsMinimalPrime P) :
        cycleLength A P hp.isPrime ≠ ⊤ := by rw [hterm P hp]; split_ifs <;> simp
    have hweight (P : JetIdeal) (hP : P ∈ T) :
        (cycleWeight I P : ℚ) = (cycleWeight B P : ℚ) + (if P = A then 1 else 0) := by
      have hp := Ideal.mem_minimalPrimesFinset.mp hP
      simp only [cycleWeight, dite_eq_left hp.isPrime]
      rw [hstep P hp, ENat.toNat_add (hfinite P hp) (hfin P hp), hterm P hp, Nat.cast_add]
      split_ifs <;> simp [add_comm]
    have hdim := (natDegree_affineHilbertPolynomial_le_of_le hJI).trans hd
    refine ⟨fun P hp => by
      rw [hstep P hp]
      exact WithTop.add_ne_top.mpr ⟨hfinite P hp, hfin P hp⟩, ?_⟩
    calc
      _ = (∑ P ∈ T, (cycleWeight B P : ℚ) * (affineHilbertPolynomial P).coeff 2) +
          (if A ∈ T then (affineHilbertPolynomial A).coeff 2 else 0) := by
        rw [← Finset.sum_ite_eq' T A (fun P => (affineHilbertPolynomial P).coeff 2),
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [hweight P hP, add_mul, ite_mul, one_mul, zero_mul]
      _ ≤ (affineHilbertPolynomial B).coeff 2 + (affineHilbertPolynomial A).coeff 2 := by
        apply add_le_add hbudget
        split_ifs
        · exact le_rfl
        · exact coeff_two_nonneg A ((natDegree_affineHilbertPolynomial_le_of_le hIA).trans hdim)
      _ ≤ _ := hilbert_coeff_step I g hdim
end
end P0_9_6_3
end
section
set_option autoImplicit false
namespace P0_9_6_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 MvPolynomial
open scoped Polynomial
private theorem recovery_of_generators (rec : K1_13_6_3_3.c2) (g : Row 4) (h : FreshCoeffRing) :
    ∃ (u : GeoJets) (e : ℕ), ∀ A : CoeffIdeal, A.IsPrime → (extendIdeal A).IsPrime →
      toGeneric g ∈ freshImage A → toGeneric (separant g) ∉ freshImage A →
      h * freshJetMap (toGeneric (separant g)) ^ e - freshJetMap u ∈ extendIdeal A := by
  let s := toGeneric (separant g)
  induction h using MvPolynomial.induction_on with
  | C a =>
    refine ⟨MvPolynomial.C a, 0, fun A _ _ _ _ => ?_⟩
    simp [freshJetMap]
  | add h h' ih ih' =>
    obtain ⟨u, e, hu⟩ := ih
    obtain ⟨v, d, hv⟩ := ih'
    refine ⟨u * s ^ d + v * s ^ e, e + d, fun A hp he hg hs => ?_⟩
    let q := Ideal.Quotient.mk (extendIdeal A)
    have hu' := Ideal.Quotient.eq_zero_iff_mem.mpr (hu A hp he hg hs)
    have hv' := Ideal.Quotient.eq_zero_iff_mem.mpr (hv A hp he hg hs)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (h * freshJetMap s ^ e - freshJetMap u) = 0 at hu'
    change q (h' * freshJetMap s ^ d - freshJetMap v) = 0 at hv'
    change q ((h + h') * freshJetMap s ^ (e + d) - freshJetMap
      (u * s ^ d + v * s ^ e)) = 0
    simp only [map_add, map_mul, map_sub, map_pow, pow_add] at hu' hv' ⊢
    linear_combination q (freshJetMap s) ^ d * hu' + q (freshJetMap s) ^ e * hv'
  | mul_X h i ih =>
    obtain ⟨u, e, hu⟩ := ih
    obtain ⟨v, d, hv⟩ := rec g i
    refine ⟨u * v, e + d, fun A hp he hg hs => ?_⟩
    let q := Ideal.Quotient.mk (extendIdeal A)
    have hu' := Ideal.Quotient.eq_zero_iff_mem.mpr (hu A hp he hg hs)
    have hv' := Ideal.Quotient.eq_zero_iff_mem.mpr (hv A hp he hg hs)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (h * freshJetMap s ^ e - freshJetMap u) = 0 at hu'
    change q (MvPolynomial.X i * freshJetMap s ^ d - freshJetMap v) = 0 at hv'
    change q ((h * MvPolynomial.X i) * freshJetMap s ^ (e + d) - freshJetMap
      (u * v)) = 0
    simp only [map_mul, map_sub, map_pow, pow_add, sub_eq_zero] at hu' hv' ⊢
    calc
      _ = (q h * q (freshJetMap s) ^ e) *
          (q (MvPolynomial.X i) * q (freshJetMap s) ^ d) := by ac_rfl
      _ = _ := by rw [hu', hv']
private theorem fresh_prime {A : CoeffIdeal} (hA : (extendIdeal A).IsPrime) :
    (freshImage A).IsPrime := by
  let _ := hA
  exact inferInstanceAs ((extendIdeal A).comap freshJetMap).IsPrime
private theorem fresh_birational (rec : K1_13_6_3_3.c2) {A : CoeffIdeal} (hA : A.IsPrime)
    (hext : (extendIdeal A).IsPrime) {g : Row 4}
    (hg : toGeneric g ∈ freshImage A) (hs : toGeneric (separant g) ∉ freshImage A) :
    FreshBirational A := by
  intro h
  obtain ⟨u, e, hrel⟩ := recovery_of_generators rec g h
  refine ⟨u, toGeneric (separant g) ^ e, ?_, ?_⟩
  · intro hp
    exact hs ((fresh_prime hext).mem_of_pow_mem e hp)
  · rw [map_pow]
    exact hrel A hA hext hg hs
private def freshJetAlgHom : GeoJets →ₐ[GeoField] FreshCoeffRing :=
  MvPolynomial.aeval (fun i : Fin 4 => jetLinear genericArgument i.val)
private theorem freshJetAlgHom_toRingHom : freshJetAlgHom.toRingHom = freshJetMap := by
  ext a <;> simp [freshJetAlgHom, freshJetMap]
private theorem dim_fresh_of_recovery (rec : K1_13_6_3_3.c2) {A : CoeffIdeal}
    (hA : A.IsPrime) (hext : (extendIdeal A).IsPrime) {g : Row 4}
    (hg : toGeneric g ∈ freshImage A) (hs : toGeneric (separant g) ∉ freshImage A) :
    dimension (freshImage A) = dimension (extendIdeal A) := by
  let I := extendIdeal A
  let J := freshImage A
  let v := toGeneric (separant g)
  have hJ : J = I.comap freshJetAlgHom := by
    change I.comap freshJetMap = I.comap freshJetAlgHom.toRingHom
    rw [freshJetAlgHom_toRingHom]
  let F := Ideal.quotientMapₐ I freshJetAlgHom hJ.le
  have hinj : Function.Injective F := Ideal.quotientMap_injective' (H := hJ.le) hJ.ge
  apply le_antisymm (natDegree_affineHilbertPolynomial_le_of_injective F hinj)
  let vI := freshJetMap v
  have hFv : F (Ideal.Quotient.mk J v) = Ideal.Quotient.mk I vI := by
    rw [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk]
    change Ideal.Quotient.mk I (freshJetAlgHom.toRingHom v) = _
    rw [freshJetAlgHom_toRingHom]
  let L := Localization.Away (Ideal.Quotient.mk I vI)
  let _ : IsLocalization.Away (F (Ideal.Quotient.mk J v)) L := by
    rw [hFv]
    infer_instance
  let G := IsLocalization.Away.mapₐ (R := GeoField)
    (Localization.Away (Ideal.Quotient.mk J v)) L F (Ideal.Quotient.mk J v)
  have hsurj : Function.Surjective G := by
    apply (IsLocalization.Away.map_surjective_iff _ _ F.toRingHom (Ideal.Quotient.mk J v)).mpr
    intro x
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨u, e, hrel⟩ := recovery_of_generators rec g h
    have hEq := sub_eq_zero.mp (show
      Ideal.Quotient.mk I (h * vI ^ e) - Ideal.Quotient.mk I (freshJetMap u) = 0 by
      rw [← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hrel A hA hext hg hs))
    refine ⟨Ideal.Quotient.mk J u, e, ?_⟩
    change F (Ideal.Quotient.mk J u) = F (Ideal.Quotient.mk J v) ^ e * Ideal.Quotient.mk I h
    rw [hFv, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk]
    change Ideal.Quotient.mk I (freshJetAlgHom.toRingHom u) = _
    rw [freshJetAlgHom_toRingHom, ← hEq, map_mul, map_pow, mul_comm]
  let _ : I.IsPrime := hext
  have hreg : IsLeftRegular (Ideal.Quotient.mk I vI) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      (mt Ideal.Quotient.eq_zero_iff_mem.mp hs)
  exact natDegree_affineHilbertPolynomial_le_of_surjective_away_away hreg G hsurj
private theorem dim_lt_of_prime_lt {P J : JetIdeal} (hP : P.IsPrime) (hJ : J.IsPrime)
    (hlt : P < J) : dimension J < dimension P := by
  classical
  obtain ⟨s, hJmem, hPmem⟩ := SetLike.exists_of_lt hlt
  have hcut : P ⊔ Ideal.span {s} ≤ J :=
    sup_le hlt.le ((Ideal.span_singleton_le_iff_mem J).mpr hJmem)
  let _ := hJ
  obtain ⟨T, hT, hle⟩ := Ideal.exists_minimalPrimes_le hcut
  let _ := hP
  have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hPmem hT
  have hlt' : dimension T < dimension P := by
    change dimension T + 1 = dimension P at hd
    omega
  exact lt_of_le_of_lt (natDegree_affineHilbertPolynomial_le_of_le hle) hlt'
private theorem injective_on_regular (base : K1_13_6_3_3.c1) (rec : K1_13_6_3_3.c2) (f : Row 4) :
    Set.InjOn freshImage {A | A.IsPrime ∧ FreshRegular f A} := by
  intro A hA B hB himage
  obtain ⟨hAp, hAr⟩ := hA
  obtain ⟨hBp, _⟩ := hB
  obtain ⟨hAe, _, hAc⟩ := base A hAp
  obtain ⟨hBe, _, hBc⟩ := base B hBp
  obtain ⟨r, hgA, hsA⟩ := hAr
  let g := (separant^[r]) f
  have hgB : toGeneric g ∈ freshImage B := himage ▸ hgA
  have hsB : toGeneric (separant g) ∉ freshImage B := himage ▸ hsA
  have hEq : extendIdeal A = extendIdeal B := by
    ext h
    obtain ⟨u, e, hrel⟩ := recovery_of_generators rec g h
    let s := freshJetMap (toGeneric (separant g))
    have transfer (D : CoeffIdeal) (hDp : D.IsPrime) (hDe : (extendIdeal D).IsPrime)
        (hgD : toGeneric g ∈ freshImage D) (hsD : toGeneric (separant g) ∉ freshImage D) :
        h ∈ extendIdeal D ↔ u ∈ freshImage D := by
      have hdiff : h * s ^ e - freshJetMap u ∈ extendIdeal D := hrel D hDp hDe hgD hsD
      have hn : s ^ e ∉ extendIdeal D := fun hp => hsD (hDe.mem_of_pow_mem e hp)
      change _ ↔ freshJetMap u ∈ extendIdeal D
      constructor
      · intro hh
        have hm := Ideal.mul_mem_right (s ^ e) (extendIdeal D) hh
        exact ((extendIdeal D).sub_mem_iff_right hm).1 hdiff
      · intro hu
        have hm := ((extendIdeal D).sub_mem_iff_left hu).1 hdiff
        exact (hDe.mem_or_mem hm).resolve_right hn
    rw [transfer A hAp hAe hgA hsA, transfer B hBp hBe hgB hsB, himage]
  rw [← hAc, ← hBc, hEq]
theorem freshImage_injective (f : Row 4) :
    Set.InjOn freshImage {A | A.IsPrime ∧ FreshRegular f A} :=
  injective_on_regular K1_13_6_3_3_1.proof K1_13_6_3_3_2.proof f
end
end P0_9_6_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace P0_9_6_3
noncomputable section
open K1 K1_13 K1_13_6 Polynomial MvPolynomial
open K1_13_6_3
open P0_9 (primaryBox)
open scoped BigOperators
private theorem curve_degree : K1_13_6_3.c4 :=
  K1_13_6_3_4.of_children K1_13_6_3_4_1.proof K1_13_6_3_4_2.proof K1_13_6_3_4_3.proof
private theorem markPoint_inj {Γ : Finset K} {s : K → K[X]}
    (hdistinct : Set.InjOn s (Γ : Set K))
    (hdegree : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength) :
    Set.InjOn (markPoint s) (Γ : Set K) := by
  intro α hα β hβ hEq
  apply hdistinct hα hβ
  apply Polynomial.ext
  intro n
  by_cases hn : n < taylorLength
  · have hcoeff := congrFun hEq ⟨n, hn⟩
    exact embed.injective (by simpa only [markPoint, coeffPoint, Polynomial.coeff_map] using hcoeff)
  · have hlt := Nat.le_of_not_lt hn
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hdegree α hα).trans_le hlt),
      Polynomial.coeff_eq_zero_of_natDegree_lt ((hdegree β hβ).trans_le hlt)]
private theorem canonical_unique {f : Row 4} {surface : JetIdeal} {r t : ℕ}
    (hr : CanonicalChart f surface r) (ht : CanonicalChart f surface t) : r = t := by
  rcases lt_trichotomy r t with h | h | h
  · have hm := ht.2.1 (r + 1) (Nat.succ_le_of_lt h)
    rw [Function.iterate_succ_apply'] at hm
    exact False.elim (hr.2.2 hm)
  · exact h
  · have hm := hr.2.1 (t + 1) (Nat.succ_le_of_lt h)
    rw [Function.iterate_succ_apply'] at hm
    exact False.elim (ht.2.2 hm)
private theorem cycleWeight_ge {f Q : Row 4} (hc : CutCycle f Q) {surface : JetIdeal}
    (hz : (intersectionIdeal f Q).IsMinimalPrime surface) {l : ℕ}
    (hl : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface hz.isPrime) :
    l ≤ cycleWeight (intersectionIdeal f Q) surface := by
  classical
  have hne : cycleLength (intersectionIdeal f Q) surface hz.isPrime ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hc.local_bound surface hz).2.2
  simpa only [cycleWeight, dite_eq_left hz.isPrime, ENat.toNat_natCast] using ENat.toNat_le_toNat hl hne
private theorem surface_sum {f Q : Row 4} (hc : CutCycle f Q) (T : Finset JetIdeal)
    (hT : ∀ P ∈ T, (intersectionIdeal f Q).IsMinimalPrime P) :
    ∑ P ∈ T, affineDegree P ≤ ((shape f).b * primaryBox.b : ℕ) := by
  classical
  let S := (intersectionIdeal f Q).minimalPrimesFinset
  have hsub : T ⊆ S := fun P hP => Ideal.mem_minimalPrimesFinset.mpr (hT P hP)
  calc
    _ ≤ ∑ P ∈ S, affineDegree P :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun P _ _ => affineDegree_nonneg P)
    _ ≤ ∑ P ∈ S, (cycleWeight (intersectionIdeal f Q) P : ℚ) * affineDegree P := by
      apply Finset.sum_le_sum
      intro P hP
      have hz := Ideal.mem_minimalPrimesFinset.mp hP
      have h1 := cycleWeight_ge hc hz (hc.local_bound P hz).2.1
      exact le_mul_of_one_le_left (affineDegree_nonneg P) (by exact_mod_cast h1)
    _ ≤ _ := hc.weighted_degree
end
end P0_9_6_3
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace P0_9_6_3_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_2 Polynomial
private theorem iterate_zero_of_le {F : Type} [Field F] [Algebra Geom F]
    (D : Derivation Geom F F) (y : F) {L n : ℕ}
    (hcut : ((D : F → F)^[L]) y = 0) (hn : L ≤ n) :
    ((D : F → F)^[n]) y = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm L j, Function.iterate_add_apply, hcut]
  exact Function.iterate_fixed (f := (D : F → F)) D.map_zero j
private theorem differentialTaylor_degree {F : Type} [Field F] [Algebra Geom F]
    (D : Derivation Geom F F) (x y : F) {L : ℕ} (hL : 0 < L) (hbound : L ≤ taylorLength)
    (hcut : ((D : F → F)^[L]) y = 0) : (differentialTaylor D x y).natDegree < L := by
  have htrim : differentialTaylor D x y =
      fromTaylor (M := L) x (fun i => dividedIterate D y i.val) := by
    let term (i : ℕ) := C (dividedIterate D y i) * (Polynomial.X - C x) ^ i
    change (∑ i : Fin taylorLength, term i.val) = ∑ i : Fin L, term i.val
    rw [Fin.sum_univ_eq_sum_range term, Fin.sum_univ_eq_sum_range term]
    symm
    apply Finset.sum_subset (Finset.range_mono hbound)
    intro i _ hi
    have htail : L ≤ i := Nat.le_of_not_lt (fun h => hi (Finset.mem_range.mpr h))
    simp only [term, dividedIterate, iterate_zero_of_le D y hcut htail, zero_div, map_zero,
      zero_mul]
  rw [htrim]
  exact fromTaylor_degree _ _ hL
private theorem rowAt_eval (P : JetIdeal) (H : Row 4) :
    MvPolynomial.eval₂ (Polynomial.aeval (abscissa (rowAt P))).toRingHom
      (jetCoordinate (rowAt P)) H = rowAt P H := by
  change MvPolynomial.eval₂Hom _ _ H = rowAt P H
  have hc : (Polynomial.aeval (abscissa (rowAt P))).toRingHom =
      (rowAt P).comp MvPolynomial.C := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, RingHom.comp_apply]
      rfl
    · simp [abscissa]
  rw [hc]
  have h : MvPolynomial.eval₂Hom ((rowAt P).comp MvPolynomial.C)
      (jetCoordinate (rowAt P)) = rowAt P := by
    apply MvPolynomial.ringHom_ext <;> simp [jetCoordinate]
  rw [h]
private theorem initial_dividedIterate {F : Type} [Field F] [Algebra Geom F]
    (e : Row 4 →+* F) (D : Derivation Geom F F)
    (shift : ∀ i : Fin 3, D (jetCoordinate e i.castSucc) =
      ((i.val + 1 : ℕ) : F) * jetCoordinate e i.succ) (i : Fin 4) :
    dividedIterate D (jetCoordinate e 0) i.val = jetCoordinate e i := by
  have raw (j : Fin 4) : ((D : F → F)^[j.val]) (jetCoordinate e 0) =
      (j.val.factorial : F) * jetCoordinate e j := by
    induction j using Fin.induction with
    | zero => simp
    | succ j ih =>
      rw [Fin.val_succ, Function.iterate_succ_apply', ← Fin.val_castSucc j, ih]
      simp only [D.leibniz, D.map_natCast, smul_eq_mul, mul_zero, add_zero, shift,
        Fin.val_castSucc, Nat.factorial_succ, Nat.cast_mul]
      ring
  have hfact := factorial_ne_zero (algebraMap Geom F)
    (i.isLt.trans (by decide : 4 < K1.p))
  rw [dividedIterate, raw i, mul_div_cancel_left₀ _ hfact]
private theorem chartTaylor_toComponent (P : JetIdeal) [P.IsPrime] (g : Row 4) :
    (chartTaylor (rowAt P) g).map (toComponent P) = chartTaylor (componentRow P) g := by
  unfold chartTaylor abscissa
  rw [map_fromTaylor]
  simp only [map_div₀, map_pow, map_natCast, toComponent_rowAt]
end
end P0_9_6_3_1
end
