import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Localization.NormTrace
import ProximityPrize.SubmissionLower.Fast035
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace K1_14_3_2
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open scoped BigOperators Classical
def c1 : Prop :=
  ∀ P Q : Jet, P ≠ 0 → Q ≠ 0 →
    RowCaps P (cheapShape 0) → RowCaps Q (layeredShape 0) →
    NoMovingCommon P Q → Nonempty (PreparedPair P Q)
def c2 : Prop :=
  ∀ f : Equation, Irreducible f → 0 < f.natDegree → f.natDegree < p →
    ∃ g a, IsClearing f g a ∧ ProperPair (C f) (ordinaryCutter g) ∧
      ∀ z S, atMark f z S = 0 → jetAt (ordinaryCutter g) z S = 0
def c3 : Prop :=
  ∀ P Q : Jet, ProperPair P Q →
    RowCaps P (cheapShape 0) → RowCaps Q (layeredShape 0) →
    ∀ qs : Finset Surface, ComponentsOn P Q qs →
      FourMassCap qs 2828 60186 278957 2360484
def c4 : Prop :=
  ∀ (f : Equation) (g : ClearedEquation) (a : L[X]),
    Irreducible f → 0 < f.natDegree → f.natDegree < p → IsClearing f g a →
    ProperPair (C f) (ordinaryCutter g) →
    ∀ qs : Finset Surface, ComponentsOn (C f) (ordinaryCutter g) qs →
      FourMassCap qs f.natDegree (ordinarySeedDegree f)
        (2 * (ordinarySeedDegree f : ℚ) * f.natDegree) ((ordinarySeedDegree f : ℚ)^2)
def c5 : Prop :=
  ∀ qs : Finset Surface, TwoDimensional qs →
    ∃ C : SeedCover, (C.curve.totalDegree : ℚ) ≤ mass qs .mixed ∧
      (C.points.card : ℚ) ≤ mass qs .jets ∧
      ∀ q ∈ qs, ¬ SeedDominant q → ∀ z S, AtSurface q z S → C.Covers z
def c6 : Prop :=
  ∀ qs : Finset Surface, TwoDimensional qs →
    ∃ (ordinates : Finset FX) (G : JetPlane), G ≠ 0 ∧
      ordinates.card ≤ totalSectionDegree qs .seed ∧
      JetCaps G (totalSectionDegree qs .mixed) (totalSectionDegree qs .ordinate) ∧
      ∀ q ∈ qs, SeedDominant q → ¬ JetDominant q → ∀ z S, AtSurface q z S →
        atX S ∈ ordinates ∨ fixedAt G S = 0
def c7 : Prop :=
  ∀ q : Surface, q.asIdeal.height = 2 → SeedDominant q → JetDominant q →
    sectionDegree q .seed < p → sectionDegree q .jets < p → Parent q
private theorem mass_mono {A B : Finset Surface} (h : A ⊆ B) (s : Slice) :
    mass A s ≤ mass B s :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.cast_nonneg _)
private theorem mass_union (A B : Finset Surface) (s : Slice) :
    mass (A ∪ B) s ≤ mass A s + mass B s := by
  have hs : (A ∪ B) \ A ⊆ B := by
    intro q hq
    obtain ⟨hq, hqA⟩ := Finset.mem_sdiff.mp hq
    exact (Finset.mem_union.mp hq).resolve_left hqA
  linarith only [mass_sdiff (Finset.subset_union_left (s₁ := A) (s₂ := B)) s, mass_mono hs s]
private theorem mass_biUnion {ι : Type*} (I : Finset ι) (T : ι → Finset Surface) (s : Slice) :
    mass (I.biUnion T) s ≤ ∑ i ∈ I, mass (T i) s := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [mass]
  | @insert i I hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (mass_union (T i) (I.biUnion T) s).trans (add_le_add le_rfl ih)
theorem total_cast (qs : Finset Surface) (s : Slice) :
    (totalSectionDegree qs s : ℚ) = mass qs s := by
  simp [totalSectionDegree, mass]
theorem sum_ordinary {F : Finset Equation} {T : Equation → Finset Surface}
    (hc : ∀ f ∈ F, FourMassCap (T f) f.natDegree (ordinarySeedDegree f)
      (2 * (ordinarySeedDegree f : ℚ) * f.natDegree) ((ordinarySeedDegree f : ℚ)^2))
    (hu : ∑ f ∈ F, ordinarySeedDegree f ≤ 812) (hb : ∑ f ∈ F, f.natDegree ≤ 63) :
    FourMassCap (F.biUnion T) 63 812 102312 659344 := by
  have hu' : ∑ f ∈ F, (ordinarySeedDegree f : ℚ) ≤ 812 := by exact_mod_cast hu
  have hb' : ∑ f ∈ F, (f.natDegree : ℚ) ≤ 63 := by exact_mod_cast hb
  have huf (f : Equation) (hf : f ∈ F) : (ordinarySeedDegree f : ℚ) ≤ 812 :=
    (Finset.single_le_sum (fun g _ => Nat.cast_nonneg (ordinarySeedDegree g)) hf).trans hu'
  have hbf (f : Equation) (hf : f ∈ F) : (f.natDegree : ℚ) ≤ 63 :=
    (Finset.single_le_sum (fun g _ => Nat.cast_nonneg (Polynomial.natDegree g)) hf).trans hb'
  refine ⟨(mass_biUnion F T .seed).trans
      ((Finset.sum_le_sum fun f hf => (hc f hf).seed).trans hb'),
    (mass_biUnion F T .ordinate).trans
      ((Finset.sum_le_sum fun f hf => (hc f hf).ordinate).trans hu'), ?_, ?_⟩
  · calc
      _ ≤ ∑ f ∈ F, mass (T f) .mixed := mass_biUnion F T .mixed
      _ ≤ ∑ f ∈ F, (126 : ℚ) * ordinarySeedDegree f := by
        apply Finset.sum_le_sum
        intro f hf
        refine (hc f hf).mixed.trans ?_
        calc
          2 * (ordinarySeedDegree f : ℚ) * f.natDegree ≤
              2 * (ordinarySeedDegree f : ℚ) * 63 :=
            mul_le_mul_of_nonneg_left (hbf f hf) (by positivity)
          _ = _ := by ring
      _ = (126 : ℚ) * ∑ f ∈ F, (ordinarySeedDegree f : ℚ) := (Finset.mul_sum _ _ _).symm
      _ ≤ 102312 := by linarith only [hu']
  · calc
      _ ≤ ∑ f ∈ F, mass (T f) .jets := mass_biUnion F T .jets
      _ ≤ ∑ f ∈ F, (812 : ℚ) * ordinarySeedDegree f := by
        apply Finset.sum_le_sum
        intro f hf
        refine (hc f hf).jets.trans ?_
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (huf f hf) (by positivity)
      _ = (812 : ℚ) * ∑ f ∈ F, (ordinarySeedDegree f : ℚ) := (Finset.mul_sum _ _ _).symm
      _ ≤ 659344 := by linarith only [hu']
theorem unionCaps {A B : Finset Surface}
    (hA : FourMassCap A 2828 60186 278957 2360484)
    (hB : FourMassCap B 63 812 102312 659344) :
    FourMassCap (A ∪ B) 2891 60998 381269 3019828 := by
  constructor
  · linarith only [mass_union A B .seed, hA.seed, hB.seed]
  · linarith only [mass_union A B .ordinate, hA.ordinate, hB.ordinate]
  · linarith only [mass_union A B .mixed, hA.mixed, hB.mixed]
  · linarith only [mass_union A B .jets, hA.jets, hB.jets]
theorem ordCover (test : c2) (bound : c4)
    (f : Equation) (hi : Irreducible f) (hd : 0 < f.natDegree) (hp : f.natDegree < p) :
    ∃ qs : Finset Surface, TwoDimensional qs ∧
      FourMassCap qs f.natDegree (ordinarySeedDegree f)
        (2 * (ordinarySeedDegree f : ℚ) * f.natDegree) ((ordinarySeedDegree f : ℚ)^2) ∧
      ∀ z S, atMark f z S = 0 → ∃ q ∈ qs, AtSurface q z S := by
  obtain ⟨g, a, ha, hproper, htest⟩ := test f hi hd hp
  obtain ⟨qs, hqs, hcover⟩ := properPairCover hproper
  refine ⟨qs, fun q hq => (hqs q hq).1, bound f g a hi hd hp ha hproper qs hqs, ?_⟩
  intro z S hz
  apply hcover z S ?_ (htest z S hz)
  simpa only [jetAt, eval₂_C, coe_eval₂RingHom, atMark] using hz
theorem allOrdinary (test : c2) (bound : c4) {P Q : Jet} (B : PreparedPair P Q) :
    ∃ qs : Finset Surface, TwoDimensional qs ∧ FourMassCap qs 63 812 102312 659344 ∧
      ∀ f ∈ B.ordinary, ∀ z S, atMark f z S = 0 → ∃ q ∈ qs, AtSurface q z S := by
  have branch (f : Equation) (hf : f ∈ B.ordinary) :=
    ordCover test bound f (B.ordinary_factors f hf).1 (B.ordinary_factors f hf).2
      (lt_of_le_of_lt
        ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans B.ordinary_y)
        (by decide))
  let T (f : Equation) : Finset Surface := if hf : f ∈ B.ordinary then
    Classical.choose (branch f hf) else ∅
  have data (f : Equation) (hf : f ∈ B.ordinary) :
      TwoDimensional (T f) ∧ FourMassCap (T f) f.natDegree (ordinarySeedDegree f)
        (2 * (ordinarySeedDegree f : ℚ) * f.natDegree) ((ordinarySeedDegree f : ℚ)^2) ∧
        ∀ z S, atMark f z S = 0 → ∃ q ∈ T f, AtSurface q z S := by
    simpa only [T, dite_eq_left hf] using Classical.choose_spec (branch f hf)
  refine ⟨B.ordinary.biUnion T, ?_,
    sum_ordinary (fun f hf => (data f hf).2.1) B.ordinary_seed B.ordinary_y, ?_⟩
  · intro q hq
    obtain ⟨f, hf, hq⟩ := Finset.mem_biUnion.mp hq
    exact (data f hf).1 q hq
  · intro f hf z S hz
    obtain ⟨q, hq, hmark⟩ := (data f hf).2.2 z S hz
    exact ⟨q, Finset.mem_biUnion.mpr ⟨f, hf, hq⟩, hmark⟩
theorem allSurfaces (test : c2) (residual : c3) (ordinary : c4)
    {P Q : Jet} (B : PreparedPair P Q) :
    ∃ qs : Finset Surface, TwoDimensional qs ∧ FourMassCap qs 2891 60998 381269 3019828 ∧
      ∀ z S, jetAt P z S = 0 → jetAt Q z S = 0 →
        graphEval z B.seedContent = 0 ∨ fixedAt B.fixedCheap S = 0 ∨
          fixedAt B.fixedLayered S = 0 ∨ ∃ q ∈ qs, AtSurface q z S := by
  obtain ⟨A, hA, hAcover⟩ := properPairCover B.proper
  obtain ⟨D, hD, hDbound, hDcover⟩ := allOrdinary test ordinary B
  refine ⟨A ∪ D, ?_, unionCaps (residual _ _ B.proper B.cheap_caps B.layered_caps A hA) hDbound, ?_⟩
  · intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact (hA q hq).1
    · exact hD q hq
  · intro z S hP hQ
    rcases B.cover z S hP hQ with h | h | h | ⟨hP', hQ'⟩ | ⟨f, hf, hz⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · obtain ⟨q, hq, h⟩ := hAcover z S hP' hQ'
      exact Or.inr (Or.inr (Or.inr ⟨q, Finset.mem_union_left D hq, h⟩))
    · obtain ⟨q, hq, h⟩ := hDcover f hf z S hz
      exact Or.inr (Or.inr (Or.inr ⟨q, Finset.mem_union_right A hq, h⟩))
theorem section_le_total {qs : Finset Surface} {q : Surface} (hq : q ∈ qs) (s : Slice) :
    sectionDegree q s ≤ totalSectionDegree qs s := by
  unfold totalSectionDegree
  exact Finset.single_le_sum (fun r _ => Nat.zero_le (sectionDegree r s)) hq
private theorem total_le {qs : Finset Surface} {s : Slice} {n : ℕ} (h : mass qs s ≤ n) :
    totalSectionDegree qs s ≤ n := by
  rw [← total_cast] at h
  exact_mod_cast h
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (h5 : c5) (h6 : c6) (h7 : c7) : K1_14_3.c2 := by
  classical
  intro u del M Γ F P Q hP hQ hPc hQc hnc hmarks
  obtain ⟨B⟩ := h1 P Q hP hQ hPc hQc hnc
  obtain ⟨qs, hdim, hm, hcover⟩ := allSurfaces h2 h3 h4 B
  obtain ⟨C, hCdeg, hCpoints, hCcover⟩ := h5 qs hdim
  obtain ⟨O, G, hG, hO, hGcaps, hGcover⟩ := h6 qs hdim
  have ha : totalSectionDegree qs .seed ≤ 2891 := total_le (by exact hm.seed)
  have hc : totalSectionDegree qs .ordinate ≤ 60998 := total_le (by exact hm.ordinate)
  have hz : totalSectionDegree qs .mixed ≤ 381269 := total_le (by exact hm.mixed)
  have he : totalSectionDegree qs .jets ≤ 3019828 := total_le (by exact hm.jets)
  let qs' := qs.filter (fun q => SeedDominant q ∧ JetDominant q)
  have hsub : qs' ⊆ qs := Finset.filter_subset _ _
  let seeds : SeedCover := ⟨B.seedContent * C.curve, mul_ne_zero B.seedContent_ne C.curve_ne, C.points⟩
  have hsdeg : C.curve.totalDegree ≤ 381269 := by
    have h := hCdeg.trans hm.mixed
    exact_mod_cast h
  have hspoints : C.points.card ≤ 3019828 := by
    have h := hCpoints.trans hm.jets
    exact_mod_cast h
  refine ⟨{
    parents := qs'
    geometric := ?_
    masses := ⟨(mass_mono hsub .seed).trans hm.seed, (mass_mono hsub .ordinate).trans hm.ordinate,
      (mass_mono hsub .mixed).trans hm.mixed⟩
    jetMass := (mass_mono hsub .jets).trans hm.jets
    seeds := seeds
    seedDegree := ?_
    seedPoints := hspoints
    ordinates := O
    ordinateCount := hO.trans ha
    lowJet := G
    fixedCheap := B.fixedCheap
    fixedLayered := B.fixedLayered
    lowJet_ne := hG
    fixedCheap_ne := B.fixedCheap_ne
    fixedLayered_ne := B.fixedLayered_ne
    lowJet_caps := ?_
    fixedCheap_caps := B.fixedCheap_caps
    fixedLayered_caps := B.fixedLayered_caps
    cover := ?_ }⟩
  · intro q hq
    obtain ⟨hq₀, ht, hj⟩ := Finset.mem_filter.mp hq
    exact h7 q (hdim q hq₀) ht hj
      (((section_le_total hq₀ .seed).trans ha).trans_lt (by decide))
      (((section_le_total hq₀ .jets).trans he).trans_lt (by decide))
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      (by linarith only [B.seedContent_degree, hsdeg])
  · intro v y h
    obtain ⟨hb, hj⟩ := hGcaps v y h
    exact ⟨hb.trans hz, hj.trans hc⟩
  · intro γ hγ
    let z := M.label γ
    let S := F.scalar γ
    obtain ⟨hPγ, hQγ⟩ := hmarks γ hγ
    rcases hcover z S hPγ hQγ with h | h | h | ⟨q, hq, hmark⟩
    · left
      left
      change graphEval z (B.seedContent * C.curve) = 0
      rw [map_mul, h, zero_mul]
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · by_cases ht : SeedDominant q
      · by_cases hj : JetDominant q
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨q, Finset.mem_filter.mpr ⟨hq, ht, hj⟩, hmark⟩))))
        · rcases hGcover q hq ht hj z S hmark with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
      · left
        rcases hCcover q hq ht z S hmark with h | h
        · left
          change graphEval z (B.seedContent * C.curve) = 0
          rw [map_mul, h, mul_zero]
        · exact Or.inr h
end
end K1_14_3_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
namespace K1_14_3_2_7
noncomputable section
open K1_14 K1_14_3
open scoped nonZeroDivisors
variable {B A : Type} [CommRing B] [CommRing A]
abbrev denominators (f : B →+* A) : Submonoid A :=
  (nonZeroDivisors B).map f.toMonoidHom
abbrev Localized (f : B →+* A) := Localization (M := A) (denominators f)
def localBase (f : B →+* A) : FractionRing B →+* Localized f :=
  IsLocalization.lift (M := nonZeroDivisors B)
    (g := (algebraMap A (Localized f)).comp f)
    (fun b => IsLocalization.map_units (M := denominators f) (Localized f)
      ⟨f b, b, b.property, rfl⟩)
instance (f : B →+* A) : Algebra (FractionRing B) (Localized f) :=
  (localBase f).toAlgebra
@[simp] theorem local_base (f : B →+* A) (b : B) :
    algebraMap (FractionRing B) (Localized f) (algebraMap B (FractionRing B) b) =
      algebraMap A (Localized f) (f b) :=
  IsLocalization.lift_eq _ _
abbrev localizedPrime (f : B →+* A) (I : Ideal A) : Ideal (Localized f) :=
  I.map (algebraMap A (Localized f))
def GenericFibre (f : B →+* A) (I : Ideal A) := Localized f ⧸ localizedPrime f I
instance (f : B →+* A) (I : Ideal A) : CommRing (GenericFibre f I) :=
  inferInstanceAs (CommRing (Localized f ⧸ localizedPrime f I))
instance (f : B →+* A) (I : Ideal A) : Algebra (FractionRing B) (GenericFibre f I) :=
  inferInstanceAs (Algebra (FractionRing B) (Localized f ⧸ localizedPrime f I))
abbrev fibreField (f : B →+* A) (I : Ideal A) [(localizedPrime f I).IsMaximal] :
    Field (GenericFibre f I) := Ideal.Quotient.field (localizedPrime f I)
def toFibre (f : B →+* A) (I : Ideal A) : A →+* GenericFibre f I :=
  (Ideal.Quotient.mk _).comp (algebraMap A (Localized f))
@[simp] theorem fibre_base (f : B →+* A) (I : Ideal A) (b : B) :
    algebraMap (FractionRing B) (GenericFibre f I) (algebraMap B (FractionRing B) b) =
      toFibre f I (f b) := by
  change Ideal.Quotient.mk _ (algebraMap (FractionRing B) (Localized f)
    (algebraMap B (FractionRing B) b)) = _
  rw [local_base]
  rfl
variable [IsDomain B]
theorem disjoint_of_dominant (f : B →+* A) (I : Ideal A)
    (h : I.comap f = ⊥) :
    Disjoint (denominators f : Set A) (I : Set A) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨b, hb, rfl⟩ hq
  have : b ∈ I.comap f := hq
  rw [h, Ideal.mem_bot] at this
  exact (mem_nonZeroDivisors_iff_ne_zero.mp hb) this
theorem ker_toFibre (f : B →+* A) (I : Ideal A) [I.IsPrime] (h : I.comap f = ⊥) :
    RingHom.ker (toFibre f I) = I := by
  rw [toFibre, ← RingHom.comap_ker, Ideal.mk_ker]
  exact IsLocalization.under_map_of_isPrime_disjoint (denominators f) (Localized f)
    ‹I.IsPrime› (disjoint_of_dominant f I h)
def localizationEval (f : B →+* A) (x : Fin 2 → A) :
    MvPolynomial (Fin 2) (FractionRing B) →ₐ[FractionRing B] Localized f :=
  MvPolynomial.aeval (fun i => algebraMap A (Localized f) (x i))
theorem localizationEval_surjective (f : B →+* A) (x : Fin 2 → A)
    (hgen : Function.Surjective (MvPolynomial.eval₂Hom f x)) :
    Function.Surjective (localizationEval f x) := by
  have heq : (localizationEval f x).toRingHom.comp
      (MvPolynomial.map (algebraMap B (FractionRing B))) =
      (algebraMap A (Localized f)).comp (MvPolynomial.eval₂Hom f x) := by
    apply MvPolynomial.ringHom_ext <;>
      simp [localizationEval, MvPolynomial.aeval_def, local_base]
  intro z
  obtain ⟨⟨a, d⟩, hz⟩ := IsLocalization.surj (denominators f) z
  obtain ⟨b, hb, hd⟩ := d.property
  change f b = (d : A) at hd
  obtain ⟨u, rfl⟩ := hgen a
  refine ⟨MvPolynomial.map (algebraMap B (FractionRing B)) u *
    MvPolynomial.C ((algebraMap B (FractionRing B) b)⁻¹), ?_⟩
  apply (IsLocalization.map_units (M := denominators f) (Localized f) d).mul_right_cancel
  have hu := RingHom.congr_fun heq u
  have hb' : algebraMap B (FractionRing B) b ≠ 0 :=
    fun he => (mem_nonZeroDivisors_iff_ne_zero.mp hb)
      ((IsFractionRing.injective B (FractionRing B)) (by simpa using he))
  trans algebraMap A (Localized f) (MvPolynomial.eval₂Hom f x u)
  · rw [map_mul, ← hd, ← local_base f b]
    rw [show localizationEval f x (MvPolynomial.C ((algebraMap B (FractionRing B) b)⁻¹)) =
      algebraMap (FractionRing B) (Localized f) ((algebraMap B (FractionRing B) b)⁻¹) from
        MvPolynomial.aeval_C _ _]
    rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hb', map_one, mul_one]
    exact hu
  · exact hz.symm
theorem fibre_maximal (f : B →+* A) (x : Fin 2 → A)
    (hgen : Function.Surjective (MvPolynomial.eval₂Hom f x))
    (I : Ideal A) [I.IsPrime] (hd : I.comap f = ⊥) (hh : I.height = 2) :
    (localizedPrime f I).IsMaximal := by
  have hdisj := disjoint_of_dominant f I hd
  let : (localizedPrime f I).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (denominators f) (Localized f)
      I ‹I.IsPrime› hdisj
  have hheight : (localizedPrime f I).height = 2 :=
    (IsLocalization.height_map_of_disjoint (denominators f) I hdisj).trans hh
  have hup : ringKrullDim (Localized f) ≤ 2 := by
    have h := ringKrullDim_le_of_surjective (localizationEval f x).toRingHom
      (localizationEval_surjective f x hgen)
    simpa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field] using h
  have hlow : 2 ≤ ringKrullDim (Localized f) := by
    simpa only [hheight, WithBot.coe_ofNat] using
      (Ideal.height_le_ringKrullDim_of_isPrime (I := localizedPrime f I))
  have hdim := le_antisymm hup hlow
  let : FiniteRingKrullDim (Localized f) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr (by
      rw [hdim]
      exact ⟨WithBot.coe_ne_bot, fun h => ENat.ofNat_ne_top 2 (WithBot.coe_inj.mp h)⟩)
  exact Ideal.isMaximal_of_height_eq_ringKrullDim (by rw [hheight, hdim, WithBot.coe_ofNat])
theorem fibre_finite (f : B →+* A) (x : Fin 2 → A)
    (hgen : Function.Surjective (MvPolynomial.eval₂Hom f x))
    (I : Ideal A) [(localizedPrime f I).IsMaximal] :
    Module.Finite (FractionRing B) (GenericFibre f I) := by
  let g := (Ideal.Quotient.mkₐ (FractionRing B) (localizedPrime f I)).comp
    (localizationEval f x)
  have hg : Function.Surjective g :=
    (Ideal.Quotient.mkₐ_surjective (FractionRing B) (localizedPrime f I)).comp (localizationEval_surjective f x hgen)
  let : Algebra.FiniteType (FractionRing B) (GenericFibre f I) :=
    Algebra.FiniteType.of_surjective g hg
  letI : Field (GenericFibre f I) := fibreField f I
  exact finite_of_finite_type_of_isJacobsonRing (FractionRing B) (GenericFibre f I)
end
end K1_14_3_2_7
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 4000000
namespace K1_14_3_2_7
noncomputable section
open K1_14 K1_14_3 Polynomial
open scoped TensorProduct nonZeroDivisors
abbrev Four (R : Type) [CommRing R] := Polynomial (Polynomial (MvPolynomial (Fin 2) R))
def scalar {R : Type} [CommRing R] : R →+* Four R := C.comp (C.comp MvPolynomial.C)
theorem scalar_eq_algebraMap {R : Type} [CommRing R] (a : R) :
    scalar a = algebraMap R (Four R) a := rfl
def seedVar {R : Type} [CommRing R] (i : Fin 2) : Four R := C (C (MvPolynomial.X i))
def yVar {R : Type} [CommRing R] : Four R :=
  Polynomial.C (R := (MvPolynomial (Fin 2) R)[X]) (Polynomial.X (R := MvPolynomial (Fin 2) R))
def vVar {R : Type} [CommRing R] : Four R :=
  Polynomial.X (R := (MvPolynomial (Fin 2) R)[X])
theorem four_ext {R T : Type} [CommRing R] [CommRing T] {f g : Four R →+* T}
    (hc : ∀ a, f (scalar a) = g (scalar a))
    (ht : ∀ i, f (seedVar i) = g (seedVar i))
    (hy : f yVar = g yVar) (hv : f vVar = g vVar) : f = g := by
  apply Polynomial.ringHom_ext' _ hv
  apply Polynomial.ringHom_ext' _ hy
  exact MvPolynomial.ringHom_ext hc ht
def evaluate {R T : Type} [CommRing R] [CommRing T] (a : R →+* T)
    (t : Fin 2 → T) (y v : T) : Four R →+* T :=
  eval₂RingHom (eval₂RingHom (MvPolynomial.eval₂Hom a t) y) v
@[simp] theorem evaluate_scalar {R T : Type} [CommRing R] [CommRing T]
    (a : R →+* T) (t : Fin 2 → T) (y v : T) (c : R) :
    evaluate a t y v (scalar c) = a c := by simp [evaluate, scalar]
@[simp] theorem evaluate_seed {R T : Type} [CommRing R] [CommRing T]
    (a : R →+* T) (t : Fin 2 → T) (y v : T) (i : Fin 2) :
    evaluate a t y v (seedVar i) = t i := by simp [evaluate, seedVar]
@[simp] theorem evaluate_y {R T : Type} [CommRing R] [CommRing T]
    (a : R →+* T) (t : Fin 2 → T) (y v : T) :
    evaluate a t y v yVar = y := by simp [evaluate, yVar]
@[simp] theorem evaluate_v {R T : Type} [CommRing R] [CommRing T]
    (a : R →+* T) (t : Fin 2 → T) (y v : T) :
    evaluate a t y v vVar = v := by simp [evaluate, vVar]
def extendScalars {R G : Type} [CommRing R] [CommRing G] (k : R →+* G) :
    Four R →+* Four G :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (MvPolynomial.map k))
@[simp] theorem extend_scalar {R G : Type} [CommRing R] [CommRing G] (k : R →+* G) (c : R) :
    extendScalars k (scalar c) = scalar (k c) := by simp [extendScalars, scalar]
@[simp] theorem extend_seed {R G : Type} [CommRing R] [CommRing G] (k : R →+* G) (i : Fin 2) :
    extendScalars k (seedVar i) = seedVar i := by simp [extendScalars, seedVar]
@[simp] theorem extend_y {R G : Type} [CommRing R] [CommRing G] (k : R →+* G) :
    extendScalars k yVar = yVar := by simp [extendScalars, yVar]
@[simp] theorem extend_v {R G : Type} [CommRing R] [CommRing G] (k : R →+* G) :
    extendScalars k vVar = vVar := by simp [extendScalars, vVar]
structure Projection (R G B : Type) [CommRing R] [Field G] [CommRing B] where
  intoJet : B →+* Four R
  intoSection : B →+* G
  injective : Function.Injective intoSection
  baseScalar : R →+* B
  baseVar : Fin 2 → B
  ext : ∀ {T : Type} [CommRing T] {f g : B →+* T},
    (∀ a, f (baseScalar a) = g (baseScalar a)) →
    (∀ i, f (baseVar i) = g (baseVar i)) → f = g
  scalar_jet : ∀ a, intoJet (baseScalar a) = scalar a
  coeffMap : R →+* G
  scalar_section : ∀ a, intoSection (baseScalar a) = coeffMap a
  cutSet : Set (Four G)
  cuts : cutSet = Set.range
    (fun i => extendScalars coeffMap (intoJet (baseVar i)) - scalar (intoSection (baseVar i)))
variable {R G B : Type} [CommRing R] [Field G] [CommRing B]
abbrev sectionIdeal (P : Projection R G B) (I : Ideal (Four R)) : Ideal (Four G) :=
  I.map (extendScalars P.coeffMap) ⊔ Ideal.span P.cutSet
abbrev SectionQuotient (P : Projection R G B) (I : Ideal (Four R)) :=
  Four G ⧸ sectionIdeal P I
theorem section_finrank [IsDomain B]
    (P : Projection R G B) (I : Ideal (Four R))
    [Module.Finite (FractionRing B) (GenericFibre P.intoJet I)] :
    Module.finrank G (SectionQuotient P I) =
      Module.finrank (FractionRing B) (GenericFibre P.intoJet I) := by
  let F := FractionRing B
  let E := GenericFibre P.intoJet I
  let S := SectionQuotient P I
  let sectionBase : F →+* G := IsFractionRing.lift P.injective
  letI : Algebra F G := sectionBase.toAlgebra
  letI : Algebra F S := Algebra.compHom S (algebraMap F G)
  letI : IsScalarTower F G S := IsScalarTower.of_algebraMap_eq' rfl
  let T := G ⊗[F] E
  let left : G →+* T := algebraMap G T
  let right : E →ₐ[F] T := Algebra.TensorProduct.includeRight
  let j : Four R →+* E := toFibre P.intoJet I
  let g : Four R →+* T := right.toRingHom.comp j
  let mk : (Four G) →ₐ[G] S := Ideal.Quotient.mkₐ _ _
  let image : Four R →+* S := mk.toRingHom.comp (extendScalars P.coeffMap)
  have hb (b : B) : g (P.intoJet b) = left (P.intoSection b) := by
    change right (toFibre P.intoJet I (P.intoJet b)) = _
    rw [← fibre_base P.intoJet I b, right.commutes]
    change left (sectionBase (algebraMap B F b)) = _
    rw [IsFractionRing.lift_algebraMap]
  let out : (Four G) →+* T := evaluate left (fun i => g (seedVar i))
    (g yVar) (g vVar)
  have hout : out.comp (extendScalars P.coeffMap) = g := by
    apply four_ext
    · intro a
      change out (extendScalars P.coeffMap (scalar a)) = g (scalar a)
      rw [extend_scalar, show out (scalar (P.coeffMap a)) = left (P.coeffMap a) from
        evaluate_scalar left _ _ _ _, ← P.scalar_section a, ← P.scalar_jet a]
      exact (hb (P.baseScalar a)).symm
    · intro i; simp [out]
    · simp [out]
    · simp [out]
  let outA : (Four G) →ₐ[G] T :=
    { out with commutes' := fun c => evaluate_scalar left _ _ _ c }
  have hkill : sectionIdeal P I ≤ RingHom.ker out := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker, hout]
      intro a ha
      change right (j a) = 0
      rw [show j a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)]
      exact map_zero _
    · rw [Ideal.span_le, P.cuts]
      rintro _ ⟨i, rfl⟩
      change out (_ - _) = 0
      rw [map_sub, ← RingHom.comp_apply, hout, sub_eq_zero]
      simpa [out] using hb (P.baseVar i)
  let forward : S →ₐ[G] T :=
    Ideal.Quotient.liftₐ _ outA (fun a ha => hkill ha)
  have hforward (a : Four R) : forward (image a) = g a := RingHom.congr_fun hout a
  have hpin : image.comp P.intoJet =
      (algebraMap G S).comp P.intoSection := by
    apply P.ext
    · intro a
      change mk ((extendScalars P.coeffMap) (P.intoJet (P.baseScalar a))) =
        algebraMap G S (P.intoSection (P.baseScalar a))
      rw [P.scalar_jet, P.scalar_section, extend_scalar, scalar_eq_algebraMap, mk.commutes]
    · intro i
      have hm : (extendScalars P.coeffMap) (P.intoJet (P.baseVar i)) - (scalar (P.intoSection (P.baseVar i)) : (Four G)) ∈
          sectionIdeal P I := by
        have hle : Ideal.span P.cutSet ≤ sectionIdeal P I := le_sup_right
        exact hle (Ideal.subset_span (by rw [P.cuts]; exact ⟨i, rfl⟩))
      have hz := (Ideal.Quotient.eq_zero_iff_mem (I := sectionIdeal P I)).mpr hm
      change mk (_ - _) = 0 at hz
      rw [map_sub, sub_eq_zero] at hz
      exact hz
  have hunits : ∀ d : denominators P.intoJet, IsUnit (image d) := by
    rintro ⟨_, b, hb', rfl⟩
    change IsUnit (image (P.intoJet b))
    rw [← RingHom.comp_apply, hpin, RingHom.comp_apply]
    exact (isUnit_iff_ne_zero.mpr (fun e => (mem_nonZeroDivisors_iff_ne_zero.mp hb')
      (P.injective (e.trans (map_zero _).symm)))).map (algebraMap G S)
  let fromLocal : Localized P.intoJet →+* S := IsLocalization.lift hunits
  let fromE : E →+* S := Ideal.Quotient.lift _ fromLocal (by
    have hk : localizedPrime P.intoJet I ≤ RingHom.ker fromLocal := by
      rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
      change I ≤ RingHom.ker ((IsLocalization.lift (S := Localized P.intoJet) hunits).comp _)
      rw [IsLocalization.lift_comp]
      intro a ha
      have hle : I.map (extendScalars P.coeffMap) ≤ sectionIdeal P I := le_sup_left
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.mem_map_of_mem _ ha))
    exact fun a ha => hk ha)
  have hfromE (a : Four R) : fromE (j a) = image a := IsLocalization.lift_eq hunits a
  let up : E →ₐ[F] S :=
    { fromE with
      commutes' := by
        have hcomm : fromE.comp (algebraMap F E) = algebraMap F S := by
          apply IsLocalization.ringHom_ext (nonZeroDivisors B)
          apply RingHom.ext
          intro b
          change fromE (algebraMap F E (algebraMap B F b)) =
            (algebraMap G S) (sectionBase (algebraMap B F b))
          rw [fibre_base P.intoJet I b, IsFractionRing.lift_algebraMap]
          exact (hfromE (P.intoJet b)).trans (RingHom.congr_fun hpin b)
        exact RingHom.congr_fun hcomm }
  let backward : T →ₐ[G] S := AlgHom.liftEquiv F G E S up
  have hbackward (a : E) : backward (right a) = up a :=
    AlgHom.congr_fun ((AlgHom.liftEquiv F G E S).left_inv up) a
  have h1 : forward.comp backward = AlgHom.id G T := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.coe_ringHom_injective
    apply Ideal.Quotient.ringHom_ext
    apply IsLocalization.ringHom_ext (denominators P.intoJet)
    exact RingHom.ext fun a => by
      change forward (backward (right (j a))) = right (j a)
      rw [hbackward]
      exact (congrArg forward (hfromE a)).trans (hforward a)
  have hround (a : Four R) : backward (forward (image a)) = image a :=
    (congrArg backward (hforward a)).trans ((hbackward _).trans (hfromE _))
  have h2 : backward.comp forward = AlgHom.id G S := by
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.coe_ringHom_injective
    apply four_ext
    · intro c
      change (backward.comp forward) (mk (scalar c)) = mk (scalar c)
      rw [scalar_eq_algebraMap, mk.commutes, (backward.comp forward).commutes]
    · intro i
      change backward (forward (mk (seedVar i))) = mk (seedVar i)
      simpa [image] using hround (seedVar i)
    · change backward (forward (mk yVar)) = mk yVar
      simpa [image] using hround yVar
    · change backward (forward (mk vVar)) = mk vVar
      simpa [image] using hround vVar
  let e : S ≃ₐ[G] T := AlgEquiv.ofAlgHom forward backward h1 h2
  let b := Module.finBasis F E
  change Module.finrank G S = Module.finrank F E
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_eq_card_basis (b.baseChange G)]
  exact Fintype.card_fin _
end
end K1_14_3_2_7
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_3_2_5
noncomputable section
open K1_14 K1_14_3 Polynomial
def seedImage (q : Surface) : Ideal Seeds :=
  q.asIdeal.comap (C.comp C : Seeds →+* Jet)
def sectionIdeal (q : Surface) (s : Slice) : Ideal SectionJet :=
  q.asIdeal.map sectionMap ⊔ Ideal.span (sectionEquations s)
abbrev SectionRing (q : Surface) (s : Slice) :=
  SectionJet ⧸ sectionIdeal q s
def sectionParameter (i : Fin 4) : SectionField :=
  algebraMap (MvPolynomial (Fin 4) FX) SectionField (MvPolynomial.X i)
def seedBase : Seeds →+* SectionSeeds :=
  MvPolynomial.map (algebraMap FX SectionField)
def seedLine : SectionSeeds :=
  MvPolynomial.X 0 + MvPolynomial.C (sectionParameter 0) * MvPolynomial.X 1 -
    MvPolynomial.C (sectionParameter 2)
def curveSectionIdeal (f : Seeds) : Ideal SectionSeeds :=
  Ideal.span {seedBase f, seedLine}
abbrev CurveSection (f : Seeds) :=
  SectionSeeds ⧸ curveSectionIdeal f
def curveSectionMap (q : Surface) (f : Seeds) (he : seedImage q = Ideal.span {f}) :
    CurveSection f →ₐ[SectionField] SectionRing q .mixed := by
  let e₁ : SectionSeeds →ₐ[SectionField] Polynomial SectionSeeds := Polynomial.CAlgHom
  let e₂ : Polynomial SectionSeeds →ₐ[SectionField] SectionJet := Polynomial.CAlgHom
  let e := (Ideal.Quotient.mkₐ SectionField (sectionIdeal q .mixed)).comp (e₂.comp e₁)
  apply Ideal.Quotient.liftₐ _ e
  intro g hg
  change Ideal.Quotient.mk (sectionIdeal q .mixed) (C (C g)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hf : f ∈ seedImage q := he ▸ Ideal.subset_span (by simp)
  have hbase : C (C (seedBase f)) ∈ sectionIdeal q .mixed := by
    have hx : sectionMap (C (C f)) ∈ sectionIdeal q .mixed :=
      (le_sup_left : q.asIdeal.map sectionMap ≤ sectionIdeal q .mixed)
        (Ideal.mem_map_of_mem sectionMap hf)
    simpa [sectionMap, seedBase] using hx
  have hline : C (C seedLine) ∈ sectionIdeal q .mixed := by
    apply (le_sup_right : Ideal.span (sectionEquations .mixed) ≤ sectionIdeal q .mixed)
    apply Ideal.subset_span
    left
    simp [seedLine, sectionScalar, sectionParameter]
  have hle : curveSectionIdeal f ≤ (sectionIdeal q .mixed).comap (C.comp C) := by
    apply Ideal.span_le.mpr
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hbase
    · exact hline
  exact hle hg
end
end K1_14_3_2_5
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
namespace K1_14_3_2_5
noncomputable section
open K1 K1_14 K1_14_3 K1_14_3_2 Polynomial
theorem seedImage_le_mark {q : Surface} {z : K} {S : K[X]} (h : AtSurface q z S) :
    seedImage q ≤ RingHom.ker (graphEval z) := by
  intro f hf
  have hz : markEval z S (C (C f)) = 0 := h hf
  simpa [markEval] using hz
theorem seedImage_prime (q : Surface) : (seedImage q).IsPrime :=
  Ideal.comap_isPrime _ _
theorem seedImage_cases {q : Surface} (hproper : ¬ SeedDominant q) {z : K} {S : K[X]}
    (hmark : AtSurface q z S) :
    (∃ f : Seeds, f ≠ 0 ∧ seedImage q = Ideal.span {f}) ∨
      seedImage q = RingHom.ker (graphEval z) := by
  have : (seedImage q).IsPrime := seedImage_prime q
  have : (RingHom.ker (graphEval z)).IsPrime := RingHom.ker_isPrime _
  by_cases hpoint : seedImage q = RingHom.ker (graphEval z)
  · exact Or.inr hpoint
  left
  have hnonzero : seedImage q ≠ ⊥ := hproper
  have hlt := lt_of_le_of_ne (seedImage_le_mark hmark) hpoint
  have hdim : ringKrullDim Seeds = 2 := by
    simp
  have htop : (RingHom.ker (graphEval z)).height ≤ 2 := by
    have h := Ideal.height_le_ringKrullDim_of_isPrime (I := RingHom.ker (graphEval z))
    rw [hdim] at h
    exact WithBot.coe_le_coe.mp h
  have hle : (seedImage q).height + 1 ≤ 2 :=
    (Ideal.height_add_one_le_of_lt_of_isPrime hlt).trans htop
  have hlo : 1 ≤ (seedImage q).height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hnonzero)
  have hone : (seedImage q).height = 1 := by
    apply le_antisymm _ hlo
    apply (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp
    rw [show (1 : ℕ∞) + 1 = 2 by decide]
    exact hle
  obtain ⟨f, hf, hp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹(seedImage q).IsPrime› hnonzero
  exact ⟨f, hp.ne_zero, Ideal.eq_span_singleton_of_height_eq_one hone hf hp⟩
theorem same_mark_seed {q : Surface} {z z' : K} {S : K[X]}
    (he : seedImage q = RingHom.ker (graphEval z)) (hm : AtSurface q z' S) :
    (seedEmbedding z', seedEmbedding z' ^ p) =
      (seedEmbedding z, seedEmbedding z ^ p) := by
  have h₀ : MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (seedEmbedding z) ∈ seedImage q := by
    rw [he, RingHom.mem_ker]
    simp [graphEval]
  have h₁ : MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (seedEmbedding z ^ p) ∈ seedImage q := by
    rw [he, RingHom.mem_ker]
    simp [graphEval]
  have he₀ := RingHom.mem_ker.mp (seedImage_le_mark hm h₀)
  have he₁ := RingHom.mem_ker.mp (seedImage_le_mark hm h₁)
  exact Prod.ext (sub_eq_zero.mp (by simpa [graphEval] using he₀))
    (sub_eq_zero.mp (by simpa [graphEval] using he₁))
def pointJetMap (z : K) : Jet →+* JetPlane :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (graphEval z))
theorem evaluationKernel_height {k : Type} [Field k] (a b : k) :
    2 ≤ (RingHom.ker
      (Polynomial.mapRingHom (Polynomial.mapRingHom
        (MvPolynomial.eval ![a, b] : MvPolynomial (Fin 2) k →+* k)))).height := by
  let s : MvPolynomial (Fin 2) k →+* k := MvPolynomial.eval ![a, b]
  let t : MvPolynomial (Fin 2) k →+* k[X] :=
    MvPolynomial.eval₂Hom (Polynomial.C : k →+* k[X]) ![Polynomial.C a, Polynomial.X (R := k)]
  let e := Polynomial.mapRingHom (Polynomial.mapRingHom s)
  let g := Polynomial.mapRingHom (Polynomial.mapRingHom t)
  let j := RingHom.ker e
  let i := RingHom.ker g
  change 2 ≤ j.height
  have : j.IsPrime := RingHom.ker_isPrime e
  have : i.IsPrime := RingHom.ker_isPrime g
  have hgraph : (evalRingHom b).comp t = s := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [s, t]
    · intro k
      fin_cases k <;> simp [s, t]
  have hij : i ≤ j := by
    have hgj : e = (Polynomial.mapRingHom (Polynomial.mapRingHom (evalRingHom b))).comp g := by
      simp only [e, g, Polynomial.mapRingHom_comp, hgraph]
    intro x hx
    change e x = 0
    have hx' : g x = 0 := hx
    simp [hgj, hx']
  let f₀ : MvPolynomial (Fin 2) k := MvPolynomial.X 0 - MvPolynomial.C a
  let f₁ : MvPolynomial (Fin 2) k := MvPolynomial.X 1 - MvPolynomial.C b
  have hf₀ : f₀ ≠ 0 := by
    intro hz
    have hc := congrArg (MvPolynomial.eval ![a + 1, b]) hz
    simp [f₀] at hc
  have hi₀ : i ≠ ⊥ := by
    intro hi
    have hmem : C (C f₀) ∈ i := by
      change g (C (C f₀)) = 0
      simp [g, f₀, t]
    rw [hi, Ideal.mem_bot, Polynomial.C_eq_zero, Polynomial.C_eq_zero] at hmem
    exact hf₀ hmem
  have hij' : i < j := by
    apply lt_of_le_of_ne hij
    intro h
    have hmem : C (C f₁) ∈ j := by
      change e (C (C f₁)) = 0
      simp [e, f₁, s]
    rw [← h] at hmem
    have hf : g (C (C f₁)) = 0 := hmem
    have hc : t f₁ = Polynomial.X (R := k) - C b := by
      simp [f₁, t]
    simp only [g, Polynomial.coe_mapRingHom, Polynomial.map_C, hc] at hf
    exact X_sub_C_ne_zero _ (Polynomial.C_eq_zero.mp (Polynomial.C_eq_zero.mp hf))
  have h₁ : 1 ≤ i.height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hi₀)
  calc
    2 = 1 + 1 := by decide
    _ ≤ i.height + 1 := add_le_add_left h₁ 1
    _ ≤ j.height := Ideal.height_add_one_le_of_lt_of_isPrime hij'
theorem pointJetMap_ker_eq {q : Surface} (hh : q.asIdeal.height = 2) {z : K}
    (he : seedImage q = RingHom.ker (graphEval z)) :
    RingHom.ker (pointJetMap z) = q.asIdeal := by
  let j := RingHom.ker (pointJetMap z)
  have : j.IsPrime := RingHom.ker_isPrime (pointJetMap z)
  have htwo : 2 ≤ j.height := evaluationKernel_height (seedEmbedding z) (seedEmbedding z ^ p)
  have hjq : j ≤ q.asIdeal := by
    change RingHom.ker (pointJetMap z) ≤ q.asIdeal
    rw [pointJetMap, Polynomial.ker_mapRingHom, Polynomial.ker_mapRingHom, Ideal.map_map, ← he]
    exact Ideal.map_comap_le
  classical
  have : q.asIdeal.IsPrime := q.isPrime
  have : q.asIdeal.FiniteHeight := by simp [Ideal.finiteHeight_iff, hh]
  refine eq_of_le_of_not_lt hjq fun hlt => ?_
  exact (not_lt_of_ge (hh ▸ htwo)) (Ideal.height_strict_mono_of_isPrime_of_isPrime hlt)
def sectionGraph (z : K) : SectionSeeds →+* SectionField :=
  MvPolynomial.eval fun i => algebraMap FX SectionField
    (![seedEmbedding z, seedEmbedding z ^ p] i)
def pointSectionEval (z : K) : SectionJet →+* SectionField :=
  eval₂RingHom (eval₂RingHom (sectionGraph z) (sectionParameter 2)) (sectionParameter 3)
theorem evalMapComp {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    (f : R →+* A) (g : A →+* B) (x : B) :
    (eval₂RingHom g x).comp (Polynomial.mapRingHom f) = eval₂RingHom (g.comp f) x := by
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_map]
theorem pointSection_pos {q : Surface} (hh : q.asIdeal.height = 2) {z : K}
    (he : seedImage q = RingHom.ker (graphEval z)) :
    1 ≤ sectionDegree q .jets := by
  let J := sectionIdeal q .jets
  let Q := SectionRing q .jets
  let e := pointSectionEval z
  let m : SectionJet →+* Q := Ideal.Quotient.mk J
  let a : SectionField →+* Q := algebraMap SectionField Q
  have hgraph : (sectionGraph z).comp seedBase = (algebraMap FX SectionField).comp (graphEval z) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [sectionGraph, seedBase, graphEval]
    · intro i
      simp [sectionGraph, seedBase, graphEval]
  have hmap : e.comp sectionMap =
      (eval₂RingHom (eval₂RingHom (algebraMap FX SectionField) (sectionParameter 2))
        (sectionParameter 3)).comp (pointJetMap z) := by
    simp only [e, pointSectionEval, sectionMap, pointJetMap, evalMapComp]
    change eval₂RingHom (eval₂RingHom ((sectionGraph z).comp seedBase) _) _ = _
    rw [hgraph]
  let Y₀ : SectionJet := C (Polynomial.X (R := SectionSeeds))
  let V₀ : SectionJet := Polynomial.X (R := Polynomial SectionSeeds)
  have hy : Y₀ - sectionScalar 2 ∈ J := by
    apply (le_sup_right : Ideal.span (sectionEquations .jets) ≤ J)
    apply Ideal.subset_span
    left
    rfl
  have hv : V₀ - sectionScalar 3 ∈ J := by
    apply (le_sup_right : Ideal.span (sectionEquations .jets) ≤ J)
    apply Ideal.subset_span
    right
    exact Set.mem_singleton _
  have hJ : J ≤ RingHom.ker e := by
    apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      have hx' : pointJetMap z x = 0 := by
        change x ∈ RingHom.ker (pointJetMap z)
        rwa [pointJetMap_ker_eq hh he]
      change e (sectionMap x) = 0
      have heq := RingHom.congr_fun hmap x
      simpa [hx'] using heq
    · apply Ideal.span_le.mpr
      intro x hx
      simp only [sectionEquations, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;>
        simp [e, pointSectionEval, sectionGraph, sectionScalar, sectionParameter]
  have hseed (i : Fin 2) :
      C (C (MvPolynomial.X i - MvPolynomial.C
        (algebraMap FX SectionField (![seedEmbedding z, seedEmbedding z ^ p] i)))) ∈ J := by
    let f : Seeds :=
      MvPolynomial.X i - MvPolynomial.C (![seedEmbedding z, seedEmbedding z ^ p] i)
    have hf : f ∈ seedImage q := by
      rw [he, RingHom.mem_ker]
      simp [f, graphEval]
    have hx : sectionMap (C (C f)) ∈ J :=
      (le_sup_left : q.asIdeal.map sectionMap ≤ J) (Ideal.mem_map_of_mem sectionMap hf)
    simpa [sectionMap, f] using hx
  have hcoeff : (m.comp C).comp C = ((a.comp e).comp C).comp C := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change m (C (C (MvPolynomial.C r))) = a (e (C (C (MvPolynomial.C r))))
      change a r = a (e (C (C (MvPolynomial.C r))))
      simp [e, pointSectionEval, sectionGraph]
    · intro i
      let r := algebraMap FX SectionField (![seedEmbedding z, seedEmbedding z ^ p] i)
      change m (C (C (MvPolynomial.X i))) = a (e (C (C (MvPolynomial.X i))))
      have hx : e (C (C (MvPolynomial.X i))) = r := by
        simp [e, pointSectionEval, sectionGraph, r]
      rw [hx]
      change m (C (C (MvPolynomial.X i))) = m (C (C (MvPolynomial.C r)))
      rw [← sub_eq_zero, ← map_sub, ← map_sub, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hseed i)
  have hmiddle : m.comp C = (a.comp e).comp C := by
    apply Polynomial.ringHom_ext' hcoeff
    change m Y₀ = a (e Y₀)
    have hx : e Y₀ = sectionParameter 2 := by simp [e, pointSectionEval, Y₀]
    rw [hx]
    change m Y₀ = m (sectionScalar 2)
    rw [← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hy
  have hall : m = a.comp e := by
    apply Polynomial.ringHom_ext' hmiddle
    change m V₀ = a (e V₀)
    have hx : e V₀ = sectionParameter 3 := by simp [e, pointSectionEval, V₀]
    rw [hx]
    change m V₀ = m (sectionScalar 3)
    rw [← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hv
  have hsurj : Function.Surjective a := by
    intro b
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (I := J) b
    exact ⟨e x, (RingHom.congr_fun hall x).symm.trans hx⟩
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (RingHom.ker_ne_top e) hJ)
  let : Module.Finite SectionField Q :=
    Module.Finite.of_surjective (Algebra.linearMap SectionField Q) hsurj
  exact Module.finrank_pos (R := SectionField) (M := Q)
end
end K1_14_3_2_5
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_3_2_5
noncomputable section
open K1 K1_14 K1_14_3 K1_14_3_2 Polynomial
open scoped BigOperators
def c1 : Prop :=
  ∀ f : Seeds, f ≠ 0 → Module.finrank SectionField (CurveSection f) = f.totalDegree
def c2 : Prop :=
  ∀ (q : Surface) (f : Seeds), q.asIdeal.height = 2 → f ≠ 0 →
    ∀ he : seedImage q = Ideal.span {f}, Function.Injective (curveSectionMap q f he)
def c3 : Prop :=
  ∀ (q : Surface) (f : Seeds), q.asIdeal.height = 2 → f ≠ 0 →
    seedImage q = Ideal.span {f} → Module.Finite SectionField (SectionRing q .mixed)
theorem localCover (h1 : c1) (h2 : c2) (h3 : c3)
    {q : Surface} (hh : q.asIdeal.height = 2) :
    ∃ C : SeedCover,
      C.curve.totalDegree ≤ sectionDegree q .mixed ∧ C.points.card ≤ sectionDegree q .jets ∧
      (¬ SeedDominant q → ∀ z S, AtSurface q z S → C.Covers z) := by
  classical
  by_cases hq : ¬ SeedDominant q ∧ ∃ z S, AtSurface q z S
  · rcases hq with ⟨hproper, z, S, hmark⟩
    rcases seedImage_cases hproper hmark with ⟨f, hf, he⟩ | he
    · have hdegree : f.totalDegree ≤ sectionDegree q .mixed := by
        change f.totalDegree ≤ Module.finrank SectionField (SectionRing q .mixed)
        let : Module.Finite SectionField (SectionRing q .mixed) := h3 q f hh hf he
        rw [← h1 f hf]
        exact LinearMap.finrank_le_finrank_of_injective
          (f := (curveSectionMap q f he).toLinearMap) (h2 q f hh hf he)
      refine ⟨⟨f, hf, ∅⟩, hdegree, by simp, ?_⟩
      intro _ z' S' hm
      have hmem : f ∈ seedImage q := by rw [he]; exact Ideal.subset_span (by simp)
      exact Or.inl (RingHom.mem_ker.mp (seedImage_le_mark hm hmem))
    · refine ⟨⟨1, one_ne_zero, {(seedEmbedding z, seedEmbedding z ^ p)}⟩,
        by simp, by simpa using pointSection_pos hh he, ?_⟩
      intro _ z' S' hm
      exact Or.inr (Finset.mem_singleton.mpr (same_mark_seed he hm))
  · refine ⟨⟨1, one_ne_zero, ∅⟩, by simp, by simp, ?_⟩
    intro hproper z S hmark
    exact (hq ⟨hproper, z, S, hmark⟩).elim
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_14_3_2.c5 := by
  classical
  intro qs hh
  have hlocal (q : Surface) (hq : q ∈ qs) :=
    localCover h1 h2 h3 (hh q hq)
  let C (q : Surface) : SeedCover :=
    if hq : q ∈ qs then Classical.choose (hlocal q hq) else ⟨1, one_ne_zero, ∅⟩
  have hC (q : Surface) (hq : q ∈ qs) :
      (C q).curve.totalDegree ≤ sectionDegree q .mixed ∧
      (C q).points.card ≤ sectionDegree q .jets ∧
      (¬ SeedDominant q → ∀ z S, AtSurface q z S → (C q).Covers z) := by
    simpa only [C, dite_eq_left hq] using Classical.choose_spec (hlocal q hq)
  refine ⟨joinCovers qs C, ?_, ?_, ?_⟩
  · calc
      _ ≤ ∑ q ∈ qs, ((C q).curve.totalDegree : ℚ) := by exact_mod_cast joinCovers_degree qs C
      _ ≤ mass qs .mixed := Finset.sum_le_sum fun q hq => by exact_mod_cast (hC q hq).1
  · calc
      _ ≤ ∑ q ∈ qs, ((C q).points.card : ℚ) := by exact_mod_cast joinCovers_points qs C
      _ ≤ mass qs .jets := Finset.sum_le_sum fun q hq => by exact_mod_cast (hC q hq).2.1
  · intro q hq hp z S hm
    exact joinCovers_covers hq ((hC q hq).2.2 hp z S hm)
end
end K1_14_3_2_5
end
section
set_option autoImplicit false
namespace K1_14_3_2_3
noncomputable section
open K1 K1_14 K1_14_3
abbrev Plane := MvPolynomial (Fin 2) SectionField
def parameter (i : Fin 4) : SectionField :=
  algebraMap (MvPolynomial (Fin 4) FX) SectionField (MvPolynomial.X i)
def seedCoordinates : Slice → Fin 2 → Plane
  | .seed => ![MvPolynomial.C (parameter 2), MvPolynomial.C (parameter 3)]
  | .ordinate | .mixed =>
    ![MvPolynomial.C (parameter 2) - MvPolynomial.C (parameter 0) * MvPolynomial.X 0,
      MvPolynomial.X 0]
  | .jets => MvPolynomial.X
def ordinateCoordinate : Slice → Plane
  | .seed => MvPolynomial.X 0
  | .ordinate => MvPolynomial.C (parameter 3)
  | .mixed => MvPolynomial.C (parameter 3) - MvPolynomial.C (parameter 1) * MvPolynomial.X 1
  | .jets => MvPolynomial.C (parameter 2)
def derivativeCoordinate : Slice → Plane
  | .jets => MvPolynomial.C (parameter 3)
  | _ => MvPolynomial.X 1
def sliceMap (s : Slice) : SectionJet →ₐ[SectionField] Plane :=
  Polynomial.aevalTower
    (Polynomial.aevalTower (MvPolynomial.aeval (seedCoordinates s)) (ordinateCoordinate s))
    (derivativeCoordinate s)
def planeMap (s : Slice) : Jet →+* Plane :=
  (sliceMap s).toRingHom.comp sectionMap
def planeIdeal (s : Slice) (q : Surface) : Ideal Plane :=
  q.asIdeal.map (planeMap s)
def PrimeTransport (s : Slice) : Prop :=
  ∀ q : Surface, planeIdeal s q = ⊤ ∨
    (planeIdeal s q).IsPrime ∧ (planeIdeal s q).comap (planeMap s) = q.asIdeal
structure PlaneProper (F G : Plane) : Prop where
  left_ne : F ≠ 0
  right_ne : G ≠ 0
  no_common : ∀ D : Plane, Irreducible D → D ∣ F → ¬ D ∣ G
def PlaneCaps (s : Slice) (B J U : ℕ) (F : Plane) : Prop :=
  match s with
  | .seed => F.totalDegree ≤ B ∧ F.degreeOf 1 ≤ J
  | .ordinate => F.degreeOf 0 ≤ U ∧ F.degreeOf 1 ≤ J
  | .mixed => F.degreeOf 0 ≤ U ∧ F.degreeOf 1 ≤ B
  | .jets => F.totalDegree ≤ U
abbrev PlaneQuotient (F G : Plane) := Plane ⧸ Ideal.span ({F, G} : Set Plane)
end
end K1_14_3_2_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1500000
namespace K1_14_3_2_3
noncomputable section
open K1_14_3 Polynomial
private abbrev t (i : Fin 2) : SectionJet := C (C (MvPolynomial.X i))
private abbrev y : SectionJet := C (Polynomial.X (R := SectionSeeds))
private abbrev v : SectionJet := Polynomial.X (R := Polynomial SectionSeeds)
private def free : Slice → Fin 2 → SectionJet
  | .seed => ![y, v]
  | .ordinate | .mixed => ![t 1, v]
  | .jets => ![t 0, t 1]
private abbrev CutQuotient (s : Slice) := SectionJet ⧸ Ideal.span (sectionEquations s)
def cutMk (s : Slice) : SectionJet →ₐ[SectionField] CutQuotient s :=
  Ideal.Quotient.mkₐ _ _
private def restore (s : Slice) : Plane →ₐ[SectionField] CutQuotient s :=
  MvPolynomial.aeval (cutMk s ∘ free s)
@[simp] private theorem slice_t (s : Slice) (i : Fin 2) :
    sliceMap s (t i) = seedCoordinates s i := by
  simp [sliceMap]
@[simp] private theorem slice_y (s : Slice) :
    sliceMap s y = ordinateCoordinate s := by simp [sliceMap]
@[simp] private theorem slice_v (s : Slice) :
    sliceMap s v = derivativeCoordinate s := by simp [sliceMap]
@[simp] private theorem slice_scalar (s : Slice) (i : Fin 4) :
    sliceMap s (sectionScalar i) = MvPolynomial.C (parameter i) :=
  (sliceMap s).commutes (parameter i)
@[simp] private theorem restore_const (s : Slice) (i : Fin 4) :
    restore s (MvPolynomial.C (parameter i)) = cutMk s (sectionScalar i) :=
  (restore s).commutes (parameter i)
@[simp] private theorem restore_X (s : Slice) (i : Fin 2) :
    restore s (MvPolynomial.X i) = cutMk s (free s i) := by simp [restore]
end
end K1_14_3_2_3
end
