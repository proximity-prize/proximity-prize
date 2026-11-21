import ProximityPrize.SubmissionLower.Fast061
import ProximityPrize.SubmissionLower.Fast062
import ProximityPrize.SubmissionLower.Fast063
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3
open K1_13 K1_13_7_1 K1_13_7_1_1 K1_13_6_1_4_3
open MvPolynomial MeasureTheory Filter
open scoped Pointwise Topology
def c1 : Prop :=
  ∀ (k : Type) [Field k] (f : Fin 4 → Jets k),
    Module.Finite k (CutAlgebra f) →
    Module.Finite k (CutAlgebra (fun i => f i ^ 2)) ∧
      Module.finrank k (CutAlgebra (fun i => f i ^ 2)) =
        16 * Module.finrank k (CutAlgebra f)
def c2 : Prop :=
  ∀ (k : Type) [Field k] (P : Fin 4 → Shape) (f : Fin 4 → Jets k),
    (∀ i, (↑(f i).support : Set Exponent) ⊆ lattice (P i)) →
    Module.Finite k (CutAlgebra f) →
    Module.Finite (CoefficientField k P) (GenericAlgebra k P) →
    Module.finrank k (CutAlgebra f) ≤
      Module.finrank (CoefficientField k P) (GenericAlgebra k P)
def c3 : Prop :=
  ∀ (k : Type) [Field k] (P : Fin 4 → Shape),
    (∀ i, Chamber (P i) ∧ Even (P i).j ∧ Even (P i).t) →
    Module.Finite (CoefficientField k P) (GenericAlgebra k P) ∧
      ∃ R : Shape, Chamber R ∧ ∀ n : ℕ,
        (Module.finrank (CoefficientField k P) (GenericAlgebra k P) : ℝ) * (n : ℝ)^4 =
          fourDifference (fun x => ((lattice x).ncard : ℝ)) (fun i => (P i).scale n) R
private theorem scale_plus (p q : Shape) (n : ℕ) :
    (p.plus q).scale n = (p.scale n).plus (q.scale n) := by
  cases p
  cases q
  simp [Shape.plus, Shape.scale, Nat.mul_add]
theorem difference_limit {R p : Shape} {F : ℕ → Shape → ℝ} {G : Set RealPoint → ℝ}
    (h : ∀ x : Shape, Chamber x →
      Tendsto (fun n : ℕ => F n (R.plus (x.scale n)) / (n : ℝ)^4)
        atTop (𝓝 (G (cap x)))) (hp : Chamber p)
    (x : Shape) (hx : Chamber x) :
    Tendsto (fun n : ℕ => shapeDifference (F n) (p.scale n) (R.plus (x.scale n)) / (n : ℝ)^4)
      atTop (𝓝 (bodyDifference G (cap p) (cap x))) := by
  rw [bodyDifference, ← cap_add hx hp]
  apply ((h _ (chamber_plus hx hp)).sub (h x hx)).congr
  intro n
  have he : R.plus ((x.plus p).scale n) = (R.plus (x.scale n)).plus (p.scale n) := by
    rw [scale_plus]
    cases R
    cases x
    cases p
    simp [Shape.plus, Nat.add_assoc]
  rw [shapeDifference, sub_div, he]
theorem generic_length_eq (h3 : c3) (k : Type) [Field k] (P : Fin 4 → Shape)
    (hP : ∀ i, Chamber (P i) ∧ Even (P i).j ∧ Even (P i).t) :
    Module.Finite (CoefficientField k P) (GenericAlgebra k P) ∧
      (Module.finrank (CoefficientField k P) (GenericAlgebra k P) : ℝ) =
        mixedVolume (cap (P 0)) (cap (P 1)) (cap (P 2)) (cap (P 3)) := by
  obtain ⟨hfin, R, hR, hRdef⟩ := h3 k P hP
  refine ⟨hfin, ?_⟩
  let F₀ (_ : ℕ) (x : Shape) := ((lattice x).ncard : ℝ)
  let F₁ (n : ℕ) := shapeDifference (F₀ n) ((P 0).scale n)
  let F₂ (n : ℕ) := shapeDifference (F₁ n) ((P 1).scale n)
  let F₃ (n : ℕ) := shapeDifference (F₂ n) ((P 2).scale n)
  let G₀ (B : Set RealPoint) := (volume B).toReal
  let G₁ := bodyDifference G₀ (cap (P 0))
  let G₂ := bodyDifference G₁ (cap (P 1))
  let G₃ := bodyDifference G₂ (cap (P 2))
  have h₀ (x : Shape) (hx : Chamber x) := lattice_ratio R x hR hx
  have h₁ := difference_limit (R := R) (F := F₀) (G := G₀) h₀ (hP 0).1
  have h₂ := difference_limit (R := R) (F := F₁) (G := G₁) h₁ (hP 1).1
  have h₃ := difference_limit (R := R) (F := F₂) (G := G₂) h₂ (hP 2).1
  have hlim := difference_limit (R := R) (F := F₃) (G := G₃) h₃ (hP 3).1
    ⟨0, 0, 0⟩ (⟨by decide, by decide⟩)
  rw [cap_zero] at hlim
  have hz (n : ℕ) : R.plus ((⟨0, 0, 0⟩ : Shape).scale n) = R := by
    cases R
    simp [Shape.plus, Shape.scale]
  simp only [hz] at hlim
  change Tendsto (fun n : ℕ =>
    fourDifference (fun x => ((lattice x).ncard : ℝ)) (fun i => (P i).scale n) R / (n : ℝ)^4)
      atTop (𝓝 (mixedVolume (cap (P 0)) (cap (P 1)) (cap (P 2)) (cap (P 3)))) at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ^ 4 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn))
  rw [← hRdef n, mul_div_cancel_right₀ _ hn0]
private theorem scaled_difference {F : Set RealPoint → ℝ} {G : Shape → ℤ}
    (heq : ∀ x : Shape, Chamber x → 32 * F (cap x) = (G x : ℝ))
    {a : Shape} (ha : Chamber a) (x : Shape) (hx : Chamber x) :
    32 * bodyDifference F (cap a) (cap x) = (difference G a x : ℝ) := by
  rw [bodyDifference, difference, Int.cast_sub, mul_sub, ← cap_add hx ha,
    heq _ (chamber_plus hx ha), heq _ hx]
private def signedMixed (p q a h : Shape) : ℤ :=
  difference (difference (difference (difference volume32 p) q) a) h ⟨0, 0, 0⟩
private theorem mixed_formula (p q a h : Shape)
    (hp : Chamber p) (hq : Chamber q) (ha : Chamber a) (hh : Chamber h) :
    32 * mixedVolume (cap p) (cap q) (cap a) (cap h) = (signedMixed p q a h : ℝ) := by
  have hv := scaled_difference
    (F := fun P => (volume P).toReal) (G := volume32) cap_volume32 hp
  have hm := scaled_difference (scaled_difference (scaled_difference hv hq) ha) hh
    ⟨0, 0, 0⟩ (⟨by decide, by decide⟩)
  rw [cap_zero] at hm
  exact hm
theorem mixed_scale_two (p q a h : Shape)
    (hp : Chamber p) (hq : Chamber q) (ha : Chamber a) (hh : Chamber h) :
    mixedVolume (cap (p.scale 2)) (cap (q.scale 2)) (cap (a.scale 2)) (cap (h.scale 2)) =
      16 * mixedVolume (cap p) (cap q) (cap a) (cap h) := by
  have hs : signedMixed (p.scale 2) (q.scale 2) (a.scale 2) (h.scale 2) =
      16 * signedMixed p q a h := by
    simp only [signedMixed, difference, volume32, Shape.plus, Shape.scale,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero]
    ring
  have hb := mixed_formula _ _ _ _ (chamber_scale hp 2) (chamber_scale hq 2)
    (chamber_scale ha 2) (chamber_scale hh 2)
  rw [hs, Int.cast_mul, Int.cast_ofNat] at hb
  linarith only [hb, mixed_formula p q a h hp hq ha hh]
theorem square_supported {k : Type} [Field k] {f : Jets k} {p : Shape}
    (hp : Chamber p) (hf : CapSupported f p) : CapSupported (f ^ 2) (p.scale 2) := by
  intro e he
  rw [pow_two] at he
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (support_mul f f he)
  have hshape : p.scale 2 = p.plus p := by
    cases p
    simp [Shape.scale, Shape.plus, two_mul]
  rw [hshape, cap_add hp hp]
  exact Set.mem_add.mpr ⟨_, hf u hu, _, hf v hv, by ext i; simp [Finsupp.add_apply]⟩
theorem tuple_ideal {k : Type} [Field k] (F G U V : Jets k) :
    CutIdeal ![F, G, U, V] = Ideal.span {F, G, U, V} := by
  apply congrArg Ideal.span
  ext e
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_6_1_4_3.c3 := by
  intro p q a h hp hq ha hh F G U V hF hG hU hV hfin
  let k := K1_13_6_1_4.PairSectionField a h
  let P : Fin 4 → Shape := ![p, q, a, h]
  let f : Fin 4 → Jets k := ![F, G, U, V]
  have hP (i : Fin 4) : Chamber (P i) := by
    fin_cases i <;> assumption
  have hf (i : Fin 4) : CapSupported (f i) (P i) := by
    fin_cases i <;> assumption
  have hJ : CutIdeal f = Ideal.span {F, G, U, V} := tuple_ideal F G U V
  have hfinit : Module.Finite k (CutAlgebra f) := by
    change Module.Finite k (Jets k ⧸ CutIdeal f)
    rw [hJ]
    exact hfin
  obtain ⟨hsq, hlen⟩ := h1 k f hfinit
  let Q := fun i => (P i).scale 2
  have heven (i : Fin 4) : Chamber (Q i) ∧ Even (Q i).j ∧ Even (Q i).t := by
    refine ⟨chamber_scale (hP i) 2, ⟨(P i).j, ?_⟩, ⟨(P i).t, ?_⟩⟩ <;>
      simp [Q, Shape.scale, two_mul]
  obtain ⟨hgfin, hglen⟩ := generic_length_eq h3 k Q heven
  have hsupp (i : Fin 4) : (↑(f i ^ 2).support : Set Exponent) ⊆ lattice (Q i) := by
    intro e he
    exact mem_lattice_iff.mpr (square_supported (hP i) (hf i) e he)
  have hcompare := h2 k Q (fun i => f i ^ 2) hsupp hsq hgfin
  have hcomp : (16 : ℝ) * (Module.finrank k (CutAlgebra f) : ℝ) ≤
      (Module.finrank (CoefficientField k Q) (GenericAlgebra k Q) : ℝ) := by
    rw [hlen] at hcompare
    exact_mod_cast hcompare
  have hm : mixedVolume (cap (Q 0)) (cap (Q 1)) (cap (Q 2)) (cap (Q 3)) =
      16 * mixedVolume (cap p) (cap q) (cap a) (cap h) := mixed_scale_two p q a h hp hq ha hh
  rw [hglen, hm] at hcomp
  have hbound := le_of_mul_le_mul_left hcomp (by norm_num : (0 : ℝ) < 16)
  change (Module.finrank k (Jets k ⧸ CutIdeal f) : ℝ) ≤ _ at hbound
  rw [hJ] at hbound
  exact hbound
end K1_13_6_1_4_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_3
noncomputable section
open K1_13 K1_13_7_1 K1_13_6_1_4_3_3 MvPolynomial
def c1 : Prop :=
  ∀ (k : Type) [Field k] (P : Fin 4 → Shape) (i : Fin 4) (p : GenericJets k P),
    genericEquation k P i * p ∈ prefixIdeal k P i.val → p ∈ prefixIdeal k P i.val
def c2 : Prop :=
  ∀ (k : Type) [Field k] (P : Fin 4 → Shape),
    (∀ i, Chamber (P i) ∧ Even (P i).j ∧ Even (P i).t) →
    ∃ q : ℕ, ∀ (b : ℕ) (d : Degree) (i : Fin 4), q ≤ b → (∀ j, q ≤ d j) →
      ∀ p ∈ piece k P b (shift d i 1), p ∈ prefixIdeal k P (i.val + 1) →
        ∃ r ∈ piece k P b d, p - genericEquation k P i * r ∈ prefixIdeal k P i.val
variable {k : Type} [Field k] {P : Fin 4 → Shape}
private def affineMk (r : ℕ) : GenericJets k P →ₐ[CoefficientField k P]
    GenericJets k P ⧸ prefixIdeal k P r :=
  Ideal.Quotient.mkₐ (CoefficientField k P) (prefixIdeal k P r)
private def quotPiece (r b : ℕ) (d : Degree) :
    Submodule (CoefficientField k P) (GenericJets k P ⧸ prefixIdeal k P r) :=
  (piece k P b d).map (affineMk r).toLinearMap
private instance (r b : ℕ) (d : Degree) : Module.Finite (CoefficientField k P)
    (quotPiece (k := k) (P := P) r b d) := by
  unfold quotPiece
  infer_instance
private def hilbert (r b : ℕ) (d : Degree) : ℕ :=
  Module.finrank (CoefficientField k P) (quotPiece (k := k) (P := P) r b d)
private theorem affineMk_zero (r : ℕ) (p : GenericJets k P) :
    affineMk r p = 0 ↔ p ∈ prefixIdeal k P r := Ideal.Quotient.eq_zero_iff_mem
private theorem affineMk_eq (r : ℕ) (p s : GenericJets k P) :
    affineMk r p = affineMk r s ↔ p - s ∈ prefixIdeal k P r := by
  rw [← affineMk_zero, map_sub, sub_eq_zero]
private theorem prefix_mono {r s : ℕ} (h : r ≤ s) :
    prefixIdeal k P r ≤ prefixIdeal k P s :=
  Ideal.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)
private theorem equation_mem_next (i : Fin 4) :
    genericEquation k P i ∈ prefixIdeal k P (i.val + 1) :=
  Ideal.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
private theorem hilbert_zero (b : ℕ) (d : Degree) :
    hilbert (k := k) (P := P) 0 b d = (lattice (shapeAt P b d)).ncard := by
  have hbot : prefixIdeal k P 0 = ⊥ := by simp [prefixIdeal]
  let f := (affineMk 0).toLinearMap.comp (piece k P b d).subtype
  have hrange : LinearMap.range f = quotPiece (k := k) (P := P) 0 b d := by
    simp [f, quotPiece, LinearMap.range_comp]
  have hinj : Function.Injective f := by
    intro p s he
    apply Subtype.ext
    change affineMk 0 (p : GenericJets k P) = affineMk 0 (s : GenericJets k P) at he
    have hm := (affineMk_eq 0 _ _).mp he
    rw [hbot, Ideal.mem_bot] at hm
    exact sub_eq_zero.mp hm
  unfold hilbert
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, finrank_piece]
private theorem prefix_four : prefixIdeal k P 4 = CutIdeal (genericEquation k P) := by
  have h : {i : Fin 4 | (i : ℕ) < 4} = Set.univ := Set.eq_univ_of_forall fun i => i.isLt
  rw [prefixIdeal, h, Set.image_univ]
private theorem hilbert_stable (hfinite : Module.Finite (CoefficientField k P) (GenericAlgebra k P)) :
    ∃ q : ℕ, ∀ b (d : Degree), q ≤ b →
      hilbert (k := k) (P := P) 4 b d =
        Module.finrank (CoefficientField k P) (GenericAlgebra k P) := by
  let hfin : Module.Finite (CoefficientField k P) (GenericJets k P ⧸ prefixIdeal k P 4) := by
    rw [prefix_four]; exact hfinite
  let N : ℕ →o Submodule (CoefficientField k P) (GenericJets k P ⧸ prefixIdeal k P 4) :=
    ⟨fun n => quotPiece 4 n (fun _ => 0),
      fun _ _ h => Submodule.map_mono (piece_mono h le_rfl)⟩
  have hsup : (⨆ n, N n) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective (CoefficientField k P) (prefixIdeal k P 4) x
    obtain ⟨n, hn⟩ := piece_exhaustive p
    exact le_iSup N n (Submodule.mem_map_of_mem hn)
  obtain ⟨q, hq⟩ := hfin.fg_top.stabilizes_of_iSup_eq N hsup
  refine ⟨q, ?_⟩
  intro b d hb
  have hqd : quotPiece (k := k) (P := P) 4 b d = ⊤ := top_unique (by
    rw [hq]
    exact Submodule.map_mono (piece_mono hb fun _ => Nat.zero_le _))
  unfold hilbert
  rw [hqd, finrank_top, prefix_four]
private theorem rank_step
    (hP : ∀ i, Chamber (P i) ∧ Even (P i).j ∧ Even (P i).t)
    (i : Fin 4) (b : ℕ) (d : Degree)
    (hinj : ∀ p : GenericJets k P, genericEquation k P i * p ∈ prefixIdeal k P i.val →
      p ∈ prefixIdeal k P i.val)
    (hlift : ∀ p ∈ piece k P b (shift d i 1), p ∈ prefixIdeal k P (i.val + 1) →
      ∃ r ∈ piece k P b d, p - genericEquation k P i * r ∈ prefixIdeal k P i.val) :
    hilbert (k := k) (P := P) (i.val + 1) b (shift d i 1) + hilbert (k := k) (P := P) i.val b d =
      hilbert (k := k) (P := P) i.val b (shift d i 1) := by
  let f := Ideal.Quotient.factorₐ (CoefficientField k P)
    (prefix_mono (k := k) (P := P) (Nat.le_succ i.val))
  have hf (p : GenericJets k P) : f (affineMk i.val p) = affineMk (i.val + 1) p := rfl
  let cut : quotPiece (k := k) (P := P) i.val b (shift d i 1) →ₗ[CoefficientField k P]
      quotPiece (k := k) (P := P) (i.val + 1) b (shift d i 1) :=
    f.toLinearMap.restrict (by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨p, hp, (hf p).symm⟩)
  let mul : quotPiece (k := k) (P := P) i.val b d →ₗ[CoefficientField k P]
      quotPiece (k := k) (P := P) i.val b (shift d i 1) :=
    (LinearMap.mulLeft (CoefficientField k P) (affineMk i.val (genericEquation k P i))).restrict (by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨_, equation_mul_mem_piece hP b d i hp, map_mul (affineMk i.val) _ _⟩)
  have hsurj : Function.Surjective cut := by
    intro y
    obtain ⟨p, hp, he⟩ := y.property
    exact ⟨⟨affineMk i.val p, ⟨p, hp, rfl⟩⟩, Subtype.ext ((hf p).trans he)⟩
  have hmul : Function.Injective mul := by
    apply (LinearMap.ker_eq_bot (f := mul)).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨p, _, hp⟩ := x.property
    change affineMk i.val (p : GenericJets k P) = (x : GenericJets k P ⧸ prefixIdeal k P i.val) at hp
    have hz : affineMk i.val (genericEquation k P i * p) = 0 := by
      rw [map_mul]
      have h := congrArg Subtype.val hx
      change affineMk i.val (genericEquation k P i) * (x : GenericJets k P ⧸ prefixIdeal k P i.val) = 0 at h
      rwa [hp]
    have hpI := hinj p ((affineMk_zero _ _).mp hz)
    exact Subtype.ext (hp.symm.trans ((affineMk_zero _ _).mpr hpI))
  have hk : LinearMap.range mul = LinearMap.ker cut := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change f (affineMk i.val (genericEquation k P i) * (x : GenericJets k P ⧸ prefixIdeal k P i.val)) = 0
      rw [map_mul, hf, (affineMk_zero _ _).mpr (equation_mem_next i), zero_mul]
    · intro hy
      obtain ⟨p, hp, he⟩ := y.property
      change affineMk i.val p = (y : GenericJets k P ⧸ prefixIdeal k P i.val) at he
      have hz := congrArg Subtype.val (LinearMap.mem_ker.mp hy)
      change f (y : GenericJets k P ⧸ prefixIdeal k P i.val) = 0 at hz
      rw [← he, hf] at hz
      obtain ⟨r, hr, hrel⟩ := hlift p hp ((affineMk_zero _ _).mp hz)
      refine ⟨⟨affineMk i.val r, ⟨r, hr, rfl⟩⟩, Subtype.ext ?_⟩
      change affineMk i.val (genericEquation k P i) * affineMk i.val r =
        (y : GenericJets k P ⧸ prefixIdeal k P i.val)
      rw [← he, ← map_mul]
      exact ((affineMk_eq _ _ _).mpr hrel).symm
  have hdim := LinearMap.finrank_range_add_finrank_ker cut
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, ← hk,
    LinearMap.finrank_range_of_inj hmul] at hdim
  exact hdim
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4_3_3.c3 := by
  intro k _ P hP
  have hfinite := generic_finite k P
  obtain ⟨q1, hq1⟩ := h2 k P hP
  obtain ⟨q2, hq2⟩ := hilbert_stable hfinite
  let q := max q1 q2
  let d : Degree := fun _ => q
  refine ⟨hfinite, shapeAt P q d, (shapeAt_admissible hP _ _).1, fun n => ?_⟩
  let H (r : ℕ) (e : Degree) : ℝ := hilbert (k := k) (P := P) r q e
  have hstep (i : Fin 4) (e : Degree) (he : ∀ j, q ≤ e j) :
      H i.val (shift e i 1) - H i.val e = H (i.val + 1) (shift e i 1) := by
    have hrank := rank_step hP i q e (h1 k P i) (hq1 q e i (le_max_left _ _) fun j =>
      (le_max_left _ _).trans (he j))
    dsimp only [H]
    rw [sub_eq_iff_eq_add]
    exact_mod_cast hrank.symm
  let C : ℝ := Module.finrank (CoefficientField k P) (GenericAlgebra k P)
  have htop (e : Degree) (_ : ∀ j, q ≤ e j) : H 4 e = C := by
    dsimp only [H, C]
    rw [hq2 q e (le_max_right _ _)]
  have hbox := fourfold_telescoping H C q hstep htop n d (fun _ => le_rfl)
  have hun : H 0 = fun e => ((lattice (shapeAt P q e)).ncard : ℝ) := by
    funext e
    exact congrArg Nat.cast (hilbert_zero (k := k) (P := P) q e)
  rw [hun, shape_differences P q n (fun x => ((lattice x).ncard : ℝ)) d [0, 1, 2, 3]] at hbox
  exact hbox.symm
end
end K1_13_6_1_4_3_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_3_2
noncomputable section
open K1_13 K1_13_7_1 K1_13_6_1_4_3_3 K1_13_6_1_4_3_3_3 MvPolynomial
open scoped Pointwise
abbrev SlotIndex := Option (Fin 4)
abbrev MultiDegree := SlotIndex → ℕ
def slotSupport (P : Fin 4 → Shape) : SlotIndex → Set Exponent
  | none => lattice auxiliary
  | some i => lattice (P i)
instance (P : Fin 4 → Shape) (i : SlotIndex) : Fintype (slotSupport P i) :=
  match i with
  | none => (lattice_finite auxiliary).fintype
  | some i => (lattice_finite (P i)).fintype
abbrev Slot (P : Fin 4 → Shape) := Σ i : SlotIndex, slotSupport P i
abbrev Chart (P : Fin 4 → Shape) := (i : SlotIndex) → slotSupport P i
abbrev SlotRing (k : Type) [Field k] (P : Fin 4 → Shape) :=
  MvPolynomial (Slot P) (CoefficientField k P)
def combinedDegree (b : ℕ) (d : Degree) : MultiDegree
  | none => b
  | some i => d i
def slotWeight (P : Fin 4 → Shape) (v : Slot P) : MultiDegree :=
  Pi.single v.1 1
abbrev slotPiece (k : Type) [Field k] (P : Fin 4 → Shape) (d : MultiDegree) :=
  weightedHomogeneousSubmodule (CoefficientField k P) (slotWeight P) d
def dehom (k : Type) [Field k] (P : Fin 4 → Shape) :
    SlotRing k P →ₐ[CoefficientField k P] GenericJets k P :=
  aeval fun v => monomial v.2.val 1
def relationGenerators (k : Type) [Field k] (P : Fin 4 → Shape) (r : ℕ) :
    Set (SlotRing k P) :=
  {f | (∃ d, f ∈ slotPiece k P d) ∧ dehom k P f ∈ prefixIdeal k P r}
def relationIdeal (k : Type) [Field k] (P : Fin 4 → Shape) (r : ℕ) :
    Ideal (SlotRing k P) :=
  Ideal.span (relationGenerators k P r)
def homogeneousEquation (k : Type) [Field k] (P : Fin 4 → Shape) (i : Fin 4) :
    SlotRing k P := by
  classical
  letI := (lattice_finite (P i)).fintype
  exact ∑ a : lattice (P i),
    C (algebraMap (CoefficientRing k P) (CoefficientField k P) (MvPolynomial.X ⟨i, a⟩)) *
      MvPolynomial.X ⟨some i, a⟩
def cutIdeal (k : Type) [Field k] (P : Fin 4 → Shape) (r : ℕ) : Ideal (SlotRing k P) :=
  relationIdeal k P 0 ⊔ Ideal.span (homogeneousEquation k P '' {i : Fin 4 | i.val < r})
def chartProduct (k : Type) [Field k] (P : Fin 4 → Shape) (a : Chart P) : SlotRing k P :=
  ∏ i : SlotIndex, MvPolynomial.X (⟨i, a i⟩ : Slot P)
def zeroChart (P : Fin 4 → Shape) : Chart P
  | none => ⟨0, zero_mem_lattice auxiliary⟩
  | some i => ⟨0, zero_mem_lattice (P i)⟩
def constantChart (k : Type) [Field k] (P : Fin 4 → Shape) : SlotRing k P :=
  chartProduct k P (zeroChart P)
private def affineWeight (P : Fin 4 → Shape) (v : Slot P) : Exponent :=
  v.2.val
private def exponentSet (P : Fin 4 → Shape) (d : MultiDegree) : Set Exponent :=
  ∑ i : SlotIndex, d i • slotSupport P i
private def exponentImage (P : Fin 4 → Shape) (d : MultiDegree) : Set Exponent :=
  {a | ∃ e : Slot P →₀ ℕ,
    Finsupp.weight (slotWeight P) e = d ∧ Finsupp.weight (affineWeight P) e = a}
private theorem exponentSet_add (P : Fin 4 → Shape) (d e : MultiDegree) :
    exponentSet P (d + e) = exponentSet P d + exponentSet P e := by
  simp only [exponentSet, Pi.add_apply, add_nsmul, Finset.sum_add_distrib]
private theorem exponentSet_single (P : Fin 4 → Shape) (i : SlotIndex) :
    exponentSet P (Pi.single i 1) = slotSupport P i := by
  classical
  unfold exponentSet
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_nsmul]
  · simp
private theorem sumset_eq_exponentImage (P : Fin 4 → Shape) (d : MultiDegree) :
    exponentSet P d = exponentImage P d := by
  classical
  have hadd (d e : MultiDegree) :
      exponentImage P d + exponentImage P e ⊆ exponentImage P (d + e) := by
    intro m hm
    obtain ⟨a, ⟨u, hu, rfl⟩, b, ⟨v, hv, rfl⟩, rfl⟩ := Set.mem_add.mp hm
    exact ⟨u + v, by rw [map_add, hu, hv], map_add _ _ _⟩
  have hzero : (0 : Exponent) ∈ exponentImage P 0 :=
    ⟨0, map_zero _, map_zero _⟩
  have hsingle (i : SlotIndex) : slotSupport P i ⊆ exponentImage P (Pi.single i 1) := by
    intro a ha
    let v : Slot P := ⟨i, ⟨a, ha⟩⟩
    exact ⟨Finsupp.single v 1, by rw [Finsupp.weight_single, one_smul]; rfl,
      by rw [Finsupp.weight_single, one_smul]; rfl⟩
  have hscale (i : SlotIndex) (n : ℕ) :
      n • slotSupport P i ⊆ exponentImage P (n • Pi.single i 1) := by
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
      rw [succ_nsmul, succ_nsmul]
      exact (Set.add_subset_add ih (hsingle i)).trans (hadd _ _)
  have hsum (s : Finset SlotIndex) :
      (∑ i ∈ s, d i • slotSupport P i) ⊆
        exponentImage P (∑ i ∈ s, d i • Pi.single i 1) := by
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (Set.add_subset_add (hscale i _) ih).trans (hadd _ _)
  apply Set.Subset.antisymm
  · have hdeg : (∑ i : SlotIndex, d i • Pi.single i (1 : ℕ)) = d := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    simpa only [exponentSet, hdeg] using hsum Finset.univ
  · clear hsum
    rintro _ ⟨e, rfl, rfl⟩
    induction e using Finsupp.induction_linear with
    | zero => simp [exponentSet]
    | add e f he hf =>
      rw [map_add, map_add, exponentSet_add]
      exact Set.mem_add.mpr ⟨_, he, _, hf, rfl⟩
    | single v n =>
      rw [Finsupp.weight_single, Finsupp.weight_single]
      have hv : affineWeight P v ∈ exponentSet P (slotWeight P v) := by
        rw [slotWeight, exponentSet_single]
        exact v.2.property
      induction n with
      | zero => simp [exponentSet]
      | succ n ih =>
        rw [succ_nsmul, succ_nsmul, exponentSet_add]
        exact Set.mem_add.mpr ⟨_, ih, _, hv, rfl⟩
variable {k : Type} [Field k] {P : Fin 4 → Shape}
private theorem dehom_monomial_one (e : Slot P →₀ ℕ) :
    dehom k P (monomial e 1) = monomial (Finsupp.weight (affineWeight P) e) 1 := by
  induction e using Finsupp.induction_linear with
  | zero => simp [monomial_zero']
  | add e f he hf =>
    rw [← one_mul (1 : CoefficientField k P), ← monomial_mul_monomial, map_mul, he, hf,
      monomial_mul_monomial, one_mul, map_add]
  | single v n =>
    rw [← X_pow_eq_monomial, map_pow, dehom, aeval_X]
    change (monomial (affineWeight P v) (1 : CoefficientField k P)) ^ n = _
    rw [monomial_pow, one_pow, Finsupp.weight_single]
theorem map_slotPiece
    (hP : ∀ i, Chamber (P i) ∧ Even (P i).j ∧ Even (P i).t) (b : ℕ) (d : Degree) :
    (slotPiece k P (combinedDegree b d)).map (dehom k P).toLinearMap = piece k P b d := by
  have hset : lattice (shapeAt P b d) = exponentImage P (combinedDegree b d) := by
    rw [← sumset_eq_exponentImage, lattice_shapeAt hP, exponentSet, Fintype.sum_option, Fin.sum_univ_four]
    simp only [slotSupport, combinedDegree]
    ac_rfl
  have hS : slotPiece k P (combinedDegree b d) = restrictSupport (CoefficientField k P)
      {e | Finsupp.weight (slotWeight P) e = combinedDegree b d} :=
    weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _
  rw [hS, restrictSupport_eq_span, Submodule.map_span, piece, hset, restrictSupport_eq_span]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    rw [AlgHom.toLinearMap_apply, dehom_monomial_one]
    exact ⟨_, ⟨e, he, rfl⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨e, he, hea⟩ := ha
    exact ⟨_, ⟨e, he, rfl⟩, by rw [AlgHom.toLinearMap_apply, dehom_monomial_one, hea]⟩
theorem combinedDegree_split (d : MultiDegree) :
    combinedDegree (d none) (fun i => d (some i)) = d := by
  funext i
  cases i <;> rfl
theorem combinedDegree_shift (b : ℕ) (d : Degree) (i : Fin 4) :
    combinedDegree b (shift d i 1) = combinedDegree b d + Pi.single (some i) 1 := by
  funext j
  cases j with
  | none => simp [combinedDegree]
  | some j => simp [combinedDegree, shift, Pi.single_apply]
theorem homogeneousEquation_mem (i : Fin 4) :
    homogeneousEquation k P i ∈ slotPiece k P (Pi.single (some i) 1) := by
  classical
  apply Submodule.sum_mem
  intro a _
  have hC := isWeightedHomogeneous_C (slotWeight P)
    (algebraMap (CoefficientRing k P) (CoefficientField k P) (MvPolynomial.X ⟨i, a⟩))
  have hX := isWeightedHomogeneous_X (CoefficientField k P) (slotWeight P) (⟨some i, a⟩ : Slot P)
  simpa only [mem_weightedHomogeneousSubmodule, zero_add, slotWeight] using hC.mul hX
theorem dehom_equation (i : Fin 4) :
    dehom k P (homogeneousEquation k P i) = genericEquation k P i := by
  classical
  simp only [homogeneousEquation, genericEquation, map_sum, map_mul, dehom, aeval_C,
    algebraMap_eq, aeval_X, C_mul_monomial, mul_one]
end
end K1_13_6_1_4_3_3_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_3_2
noncomputable section
open K1_13 K1_13_7_1 K1_13_6_1_4_3_3 K1_13_6_1_4_3_3_3 MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 : Prop :=
  ∀ (k : Type) [Field k] (P : Fin 4 → Shape) (r : ℕ),
    (∀ g ∈ relationGenerators k P r, ∀ a : Chart P,
      ∃ n : ℕ, chartProduct k P a ^ n * g ∈ cutIdeal k P r) →
    ∃ q : ℕ, ∀ d : MultiDegree, (∀ j, q ≤ d j) →
      ∀ f ∈ slotPiece k P d, f ∈ relationIdeal k P r → f ∈ cutIdeal k P r
def c2 : Prop :=
  ∀ (k : Type) [Field k] (P : Fin 4 → Shape) (r : ℕ) (a : Chart P)
    (f : SlotRing k P) (n : ℕ),
    constantChart k P ^ n * f ∈ cutIdeal k P r →
      ∃ m : ℕ, chartProduct k P a ^ m * f ∈ cutIdeal k P r
variable {k : Type} [Field k] {P : Fin 4 → Shape}
private theorem dehom_constantChart :
    dehom k P (constantChart k P) = 1 := by
  classical
  rw [constantChart, chartProduct, map_prod]
  apply Finset.prod_eq_one
  intro j _
  cases j <;> simp [zeroChart, dehom, monomial_zero']
private theorem constantChart_homogeneous :
    (constantChart k P).IsWeightedHomogeneous (slotWeight P) (fun _ => 1) := by
  classical
  have hweight : (∑ j : SlotIndex, (Pi.single j 1 : MultiDegree)) = fun _ => 1 := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [← hweight, constantChart, chartProduct]
  exact IsWeightedHomogeneous.prod _ _ _ fun j _ =>
    isWeightedHomogeneous_X (CoefficientField k P) (slotWeight P) (⟨j, zeroChart P j⟩ : Slot P)
theorem relation_on_constantChart
    (hP : ∀ i, Chamber (P i) ∧ Even (P i).j ∧ Even (P i).t)
    (r : ℕ) (f : SlotRing k P) (hf : f ∈ relationGenerators k P r) :
    ∃ n : ℕ, constantChart k P ^ n * f ∈ cutIdeal k P r := by
  classical
  obtain ⟨⟨d, hfd⟩, hfI⟩ := hf
  let s : Finset (Fin 4) := Finset.univ.filter fun j => j.val < r
  have hs : (↑s : Set (Fin 4)) = {j | j.val < r} := by
    ext j
    simp [s]
  have hfspan : dehom k P f ∈ Submodule.span (GenericJets k P) (genericEquation k P '' ↑s) := by
    rw [hs]
    exact hfI
  rw [Submodule.mem_span_image_finset_iff_exists_fun'] at hfspan
  obtain ⟨c, hc⟩ := hfspan
  simp only [smul_eq_mul] at hc
  choose q hq using fun j => piece_exhaustive (c j)
  let n := Finset.univ.sup q + 1
  let D : MultiDegree := (fun _ => n) + d
  have hsingle (j : Fin 4) (l : SlotIndex) : (Pi.single (some j) 1 : MultiDegree) l ≤ 1 := by
    by_cases h : l = some j
    · simp [h]
    · simp [Pi.single_eq_of_ne h]
  have hdegree (j : Fin 4) : D - Pi.single (some j) 1 + Pi.single (some j) 1 = D := by
    funext l
    have hj := hsingle j l
    change D l - (Pi.single (some j) 1 : MultiDegree) l + (Pi.single (some j) 1 : MultiDegree) l = D l
    apply Nat.sub_add_cancel
    change (Pi.single (some j) 1 : MultiDegree) l ≤ Finset.univ.sup q + 1 + d l
    omega
  have hlift (j : Fin 4) : ∃ u ∈ slotPiece k P (D - Pi.single (some j) 1), dehom k P u = c j := by
    let E := D - Pi.single (some j) 1
    have hpad : q j ≤ E none := by
      have hqj : q j ≤ Finset.univ.sup q := Finset.le_sup (Finset.mem_univ j)
      have hj := hsingle j none
      change q j ≤ Finset.univ.sup q + 1 + d none - (Pi.single (some j) 1 : MultiDegree) none
      omega
    have hm := piece_mono hpad (show (fun _ : Fin 4 => 0) ≤ fun l => E (some l) from
      fun _ => Nat.zero_le _) (hq j)
    rw [← map_slotPiece hP, combinedDegree_split] at hm
    exact hm
  choose u hu hud using hlift
  let g := ∑ j ∈ s, u j * homogeneousEquation k P j
  have hgd : g ∈ slotPiece k P D := by
    apply Submodule.sum_mem
    intro j _
    rw [← hdegree j]
    exact (show (u j).IsWeightedHomogeneous _ _ from hu j).mul
      (show (homogeneousEquation k P j).IsWeightedHomogeneous _ _ from homogeneousEquation_mem j)
  have hg : dehom k P g = dehom k P f := by
    simpa only [g, map_sum, map_mul, hud, dehom_equation] using hc
  have hgcut : g ∈ Ideal.span (homogeneousEquation k P '' {j : Fin 4 | j.val < r}) := by
    apply Ideal.sum_mem
    intro j hj
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, (Finset.mem_filter.mp hj).2, rfl⟩)
  have hweight : n • (fun _ => 1 : MultiDegree) = fun _ => n := by
    funext j
    simp [Pi.smul_apply]
  have hpower := (constantChart_homogeneous (k := k) (P := P)).pow n
  rw [hweight] at hpower
  have hprod : (constantChart k P ^ n * f).IsWeightedHomogeneous (slotWeight P) D :=
    hpower.mul hfd
  have hrel : constantChart k P ^ n * f - g ∈ relationIdeal k P 0 := by
    apply Ideal.subset_span
    refine ⟨⟨D, hprod.sub hgd⟩, ?_⟩
    rw [map_sub, map_mul, map_pow, dehom_constantChart, one_pow, one_mul, hg, sub_self]
    exact (prefixIdeal k P 0).zero_mem
  have hrem : constantChart k P ^ n * f - g ∈ cutIdeal k P r :=
    Submodule.mem_sup_left hrel
  have hcut : g ∈ cutIdeal k P r := Submodule.mem_sup_right hgcut
  exact ⟨n, by simpa only [sub_add_cancel] using (cutIdeal k P r).add_mem hrem hcut⟩
private theorem component_mul {g : SlotRing k P} {e : MultiDegree}
    (hg : g ∈ slotPiece k P e) (f : SlotRing k P) (d : MultiDegree) :
    weightedHomogeneousComponent (slotWeight P) (d + e) (f * g) =
      weightedHomogeneousComponent (slotWeight P) d f * g := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial a c =>
    have ha := isWeightedHomogeneous_monomial (slotWeight P) a c rfl
    have hg' : g.IsWeightedHomogeneous (slotWeight P) e := hg
    simp only [weightedHomogeneousComponent_of_mem (ha.mul hg'),
      weightedHomogeneousComponent_of_mem ha, add_right_cancel_iff]
    split <;> simp_all
  | add p r hp hr => simp [add_mul, hp, hr]
private theorem relationIdeal_le (r : ℕ) :
    relationIdeal k P r ≤ (prefixIdeal k P r).comap (dehom k P).toRingHom :=
  Ideal.span_le.mpr fun _ h => h.2
private theorem relationIdeal_homogeneous (r : ℕ) :
    (relationIdeal k P r).IsHomogeneous (slotPiece k P) :=
  Ideal.homogeneous_span _ _ fun _ h => h.1
private theorem prefix_mono {r s : ℕ} (h : r ≤ s) :
    prefixIdeal k P r ≤ prefixIdeal k P s :=
  Ideal.span_mono (Set.image_mono fun _ hj => lt_of_lt_of_le hj h)
private theorem cutIdeal_le_next (i : Fin 4) :
    cutIdeal k P (i.val + 1) ≤ relationIdeal k P i.val ⊔ Ideal.span {homogeneousEquation k P i} := by
  have hzero : relationIdeal k P 0 ≤ relationIdeal k P i.val := by
    apply Ideal.span_mono
    intro f hf
    exact ⟨hf.1, prefix_mono (Nat.zero_le i.val) hf.2⟩
  apply sup_le (hzero.trans le_sup_left)
  apply Ideal.span_le.mpr
  rintro _ ⟨j, hj, rfl⟩
  change j.val < i.val + 1 at hj
  by_cases hji : j = i
  · subst j
    exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)
  · have hlt : j.val < i.val := by
      have hn : j.val ≠ i.val := fun he => hji (Fin.ext he)
      omega
    apply Submodule.mem_sup_left
    apply Ideal.subset_span
    exact ⟨⟨_, homogeneousEquation_mem j⟩, by
      rw [dehom_equation]
      exact Ideal.subset_span ⟨j, hlt, rfl⟩⟩
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4_3_3_3.c2 := by
  classical
  intro k _ P hP
  have hlocal (r : ℕ) (f : SlotRing k P) (hf : f ∈ relationGenerators k P r) (a : Chart P) :
      ∃ n : ℕ, chartProduct k P a ^ n * f ∈ cutIdeal k P r := by
    obtain ⟨n, hn⟩ := relation_on_constantChart hP r f hf
    exact h2 k P r a f n hn
  choose q hq using fun i : Fin 4 => h1 k P (i.val + 1) (hlocal (i.val + 1))
  refine ⟨Finset.univ.sup q, ?_⟩
  intro b d i hb hd p hp hpI
  rw [← map_slotPiece hP] at hp
  obtain ⟨f, hf, hfp⟩ := hp
  change dehom k P f = p at hfp
  have hfI : f ∈ relationIdeal k P (i.val + 1) :=
    Ideal.subset_span ⟨⟨_, hf⟩, hfp ▸ hpI⟩
  have hqi : q i ≤ Finset.univ.sup q := Finset.le_sup (Finset.mem_univ i)
  have hqd : ∀ j, q i ≤ combinedDegree b (shift d i 1) j := by
    intro j
    cases j with
    | none => exact hqi.trans hb
    | some j => exact hqi.trans ((hd j).trans (Nat.le_add_right _ _))
  have hJ := cutIdeal_le_next i (hq i _ hqd f hf hfI)
  rw [sup_comm] at hJ
  obtain ⟨m, g, hg, hsum⟩ := Ideal.mem_span_singleton_sup.mp hJ
  let u := weightedHomogeneousComponent (slotWeight P) (combinedDegree b d) m
  let s := weightedHomogeneousComponent (slotWeight P) (combinedDegree b (shift d i 1)) g
  have hs : s ∈ relationIdeal k P i.val :=
    weightedHomogeneousComponent_mem_of_mem _ _ (relationIdeal_homogeneous i.val) hg _
  have hfg : u * homogeneousEquation k P i + s = f := by
    have he := congrArg (weightedHomogeneousComponent (slotWeight P) (combinedDegree b (shift d i 1))) hsum
    rw [map_add, weightedHomogeneousComponent_eq_self (show f.IsWeightedHomogeneous _ _ from hf)]
      at he
    change weightedHomogeneousComponent (slotWeight P) (combinedDegree b (shift d i 1))
      (m * homogeneousEquation k P i) + s = f at he
    conv at he => lhs; lhs; rw [combinedDegree_shift, component_mul (homogeneousEquation_mem i)]
    exact he
  have hsI : dehom k P s ∈ prefixIdeal k P i.val := relationIdeal_le i.val hs
  refine ⟨dehom k P u, ?_, ?_⟩
  · rw [← map_slotPiece hP]
    exact ⟨u, weightedHomogeneousComponent_mem _ _ _, rfl⟩
  · have he := congrArg (dehom k P) hfg
    rw [map_add, map_mul, dehom_equation, hfp] at he
    rw [← he, mul_comm (genericEquation k P i), add_sub_cancel_left]
    exact hsI
end
end K1_13_6_1_4_3_3_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_3_1
noncomputable section
open K1_13 K1_13_6_1_4_3_3 K1_13_6_1_4_3_3_3 MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance latticeFintype (p : Shape) : Fintype (lattice p) :=
  (lattice_finite p).fintype
private abbrev Index (P : Fin 4 → Shape) := Σ i : Fin 4, lattice (P i)
abbrev IntegralJets (k : Type) [Field k] (P : Fin 4 → Shape) :=
  MvPolynomial (Fin 4) (CoefficientRing k P)
private abbrev Rest (k : Type) [Field k] {P : Fin 4 → Shape} (v : Index P) :=
  MvPolynomial {w : Index P // w ≠ v} (Jets k)
variable {k : Type} [Field k] {P : Fin 4 → Shape}
def constantExponent (i : Fin 4) : lattice (P i) := ⟨0, zero_mem_lattice _⟩
def constantIndex (i : Fin 4) : Index P := ⟨i, constantExponent i⟩
private def pivotEquiv (v : Index P) : IntegralJets k P ≃+* Polynomial (Rest k v) := by
  classical
  exact (commAlgEquiv k (Fin 4) (Index P)).toRingEquiv.trans
    ((renameEquiv (Jets k) (Equiv.optionSubtypeNe v).symm).toRingEquiv.trans
      (optionEquivLeft (Jets k) {w : Index P // w ≠ v}).toRingEquiv)
private theorem pivotEquiv_pivot (v : Index P) :
    pivotEquiv (k := k) v (C (MvPolynomial.X v)) = Polynomial.X := by
  classical
  simp [pivotEquiv, renameEquiv_apply]
private theorem pivotEquiv_other (v w : Index P) (h : w ≠ v) :
    pivotEquiv (k := k) v (C (MvPolynomial.X w)) = Polynomial.C (MvPolynomial.X ⟨w, h⟩) := by
  classical
  simp [pivotEquiv, renameEquiv_apply, Equiv.optionSubtypeNe_symm_of_ne h]
private theorem pivotEquiv_X (v : Index P) (j : Fin 4) :
    pivotEquiv (k := k) v (MvPolynomial.X j) = Polynomial.C (C (MvPolynomial.X j)) := by
  classical
  simp [pivotEquiv, renameEquiv_apply]
private theorem pivotEquiv_monomial (v : Index P) (a : Exponent) :
    pivotEquiv (k := k) v (monomial a 1) = Polynomial.C (C (monomial a 1)) := by
  simp only [monic_monomial_eq, Finsupp.prod, map_prod, map_pow, pivotEquiv_X]
private def integralTerm (k : Type) [Field k] (P : Fin 4 → Shape) (j : Fin 4)
    (a : lattice (P j)) : IntegralJets k P :=
  C (MvPolynomial.X (⟨j, a⟩ : Index P)) * monomial a.1 1
private def integralEquation (k : Type) [Field k] (P : Fin 4 → Shape) (j : Fin 4) :
    IntegralJets k P :=
  ∑ a : lattice (P j), integralTerm k P j a
private def integralPrefix (k : Type) [Field k] (P : Fin 4 → Shape) (i : Fin 4) :
    Ideal (IntegralJets k P) :=
  Ideal.span (integralEquation k P '' {j : Fin 4 | j.val < i.val})
private def restTerm (v : Index P) (j : Fin 4) (a : lattice (P j)) : Rest k v := by
  classical
  exact if h : (⟨j, a⟩ : Index P) = v then 0
    else MvPolynomial.X ⟨⟨j, a⟩, h⟩ * C (monomial a.1 1)
private def restEquation (v : Index P) (j : Fin 4) : Rest k v :=
  ∑ a : lattice (P j), restTerm v j a
private theorem pivotEquiv_integralTerm (v : Index P) (j : Fin 4) (a : lattice (P j))
    (h : (⟨j, a⟩ : Index P) ≠ v) :
    pivotEquiv v (integralTerm k P j a) = Polynomial.C (restTerm v j a) := by
  simp [integralTerm, restTerm, h, pivotEquiv_other v _ h, pivotEquiv_monomial]
private theorem pivotEquiv_previous (i j : Fin 4) (hji : j.val < i.val) :
    pivotEquiv (constantIndex i) (integralEquation k P j) =
      Polynomial.C (restEquation (constantIndex i) j) := by
  rw [integralEquation, restEquation, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => pivotEquiv_integralTerm _ _ _ ?_
  exact fun h => (ne_of_lt hji) (congrArg (fun w : Index P => w.1.val) h)
private theorem pivotEquiv_current (i : Fin 4) :
    pivotEquiv (constantIndex i) (integralEquation k P i) =
      Polynomial.X + Polynomial.C (restEquation (constantIndex i) i) := by
  classical
  let a₀ : lattice (P i) := constantExponent i
  let v : Index P := constantIndex i
  change pivotEquiv v (integralEquation k P i) = Polynomial.X + Polynomial.C (restEquation v i)
  have hterm : integralTerm k P i a₀ = C (MvPolynomial.X v) := by
    change C (MvPolynomial.X v) * monomial (0 : Exponent) 1 = C (MvPolynomial.X v)
    rw [monomial_zero', C_1, mul_one]
  have h₀ : pivotEquiv v (integralTerm k P i a₀) = Polynomial.X := by
    rw [hterm, pivotEquiv_pivot]
  have hr₀ : restTerm (k := k) v i a₀ = 0 := by
    unfold restTerm
    exact dite_eq_left (show (⟨i, a₀⟩ : Index P) = v from rfl)
  rw [integralEquation, restEquation, map_sum, map_sum,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a₀),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a₀), h₀, hr₀, map_zero, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun a ha => pivotEquiv_integralTerm _ _ _ ?_
  intro h
  apply (Finset.mem_erase.mp ha).1
  exact Subtype.ext (congrArg (fun w : Index P => (w.2 : Exponent)) h)
private theorem cancel_monic_linear {B : Type*} [CommRing B] (J : Ideal B) (b : B)
    (q : Polynomial B) (h : (Polynomial.X + Polynomial.C b) * q ∈ J.map Polynomial.C) :
    q ∈ J.map Polynomial.C := by
  let f := Polynomial.mapRingHom (Ideal.Quotient.mk J)
  have hf : RingHom.ker f = J.map Polynomial.C := by
    dsimp only [f]
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
  rw [← hf, RingHom.mem_ker, map_mul] at h
  rw [← hf, RingHom.mem_ker]
  apply (Polynomial.monic_X_add_C (Ideal.Quotient.mk J b)).mul_right_eq_zero_iff.mp
  simpa [f] using h
private theorem integral_cancel (i : Fin 4) (q : IntegralJets k P)
    (h : integralEquation k P i * q ∈ integralPrefix k P i) :
    q ∈ integralPrefix k P i := by
  let v : Index P := constantIndex i
  let e := pivotEquiv (k := k) v
  let J : Ideal (Rest k v) := Ideal.span (restEquation v '' {j : Fin 4 | j.val < i.val})
  have hJ : (integralPrefix k P i).map e.toRingHom = J.map Polynomial.C := by
    dsimp only [J]
    rw [integralPrefix, Ideal.map_span, Ideal.map_span, Set.image_image, Set.image_image]
    exact congrArg Ideal.span (Set.image_congr fun j hj => pivotEquiv_previous (k := k) i j hj)
  have hq := Ideal.mem_map_of_mem e.toRingHom h
  change e (integralEquation k P i * q) ∈ (integralPrefix k P i).map e.toRingHom at hq
  rw [hJ, map_mul, show e (integralEquation k P i) =
    Polynomial.X + Polynomial.C (restEquation v i) from pivotEquiv_current (k := k) i] at hq
  have hq' := cancel_monic_linear J (restEquation v i) (e q) hq
  rw [← hJ] at hq'
  obtain ⟨r, hr, he⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hq'
  exact (e.injective he) ▸ hr
private theorem map_integralEquation (j : Fin 4) :
    algebraMap (IntegralJets k P) (GenericJets k P) (integralEquation k P j) =
      genericEquation k P j := by
  simp only [integralEquation, integralTerm, genericEquation, MvPolynomial.algebraMap_def,
    map_sum, MvPolynomial.map_monomial, C_mul_monomial, mul_one]
theorem proof : K1_13_6_1_4_3_3_3.c1 := by
  intro k _ P i p hp
  let M : Submonoid (IntegralJets k P) := (CoefficientRing k P)⁰.map (C (σ := Fin 4))
  let J := integralPrefix k P i
  let f := algebraMap (IntegralJets k P) (GenericJets k P)
  have hJ : J.map f = prefixIdeal k P i.val := by
    dsimp only [J]
    rw [integralPrefix, prefixIdeal, Ideal.map_span, Set.image_image]
    exact congrArg Ideal.span (Set.image_congr fun j _ => map_integralEquation j)
  obtain ⟨⟨q, s⟩, hs⟩ := IsLocalization.surj M p
  change p * f s = f q at hs
  have h : f (integralEquation k P i * q) ∈ J.map f := by
    rw [map_mul, show f (integralEquation k P i) = genericEquation k P i from
      map_integralEquation i, ← hs, ← mul_assoc, hJ]
    exact (prefixIdeal k P i.val).mul_mem_right _ hp
  obtain ⟨t, ht, htq⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M (GenericJets k P) J _).mp h
  have hq : t * q ∈ J := by
    apply integral_cancel i
    rw [mul_left_comm]
    exact htq
  have hfp : f q ∈ J.map f :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M (GenericJets k P) J q).mpr ⟨t, ht, hq⟩
  rw [hJ, ← hs] at hfp
  exact (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units (GenericJets k P) s)).mp hfp
end
end K1_13_6_1_4_3_3_3_1
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_3_2_2
noncomputable section
open K1_13 K1_13_6_1_4_3_3 K1_13_6_1_4_3_3_3 K1_13_6_1_4_3_3_3_2 MvPolynomial
abbrev CoeffSlot (P : Fin 4 → Shape) := Σ i : Fin 4, lattice (P i)
private abbrev degreeExponent : MultiDegree ≃+ (SlotIndex →₀ ℕ) :=
  Finsupp.addEquivFunOnFinite.symm
private def affineExponent (P : Fin 4 → Shape) : (Slot P →₀ ℕ) →+ (Fin 4 →₀ ℕ) :=
  Finsupp.weight fun v => v.2.val
private def taggedExponent (P : Fin 4 → Shape) : (Slot P →₀ ℕ) →+ ((SlotIndex ⊕ Fin 4) →₀ ℕ) :=
  Finsupp.sumFinsuppAddEquivProdFinsupp.symm.toAddMonoidHom.comp
    ((degreeExponent.toAddMonoidHom.comp (Finsupp.weight (slotWeight P))).prod (affineExponent P))
private theorem taggedExponent_eq {P : Fin 4 → Shape} {e f : Slot P →₀ ℕ} :
    taggedExponent P e = taggedExponent P f ↔
      Finsupp.weight (slotWeight P) e = Finsupp.weight (slotWeight P) f ∧
        affineExponent P e = affineExponent P f := by
  change Finsupp.sumFinsuppAddEquivProdFinsupp.symm (_, _) =
    Finsupp.sumFinsuppAddEquivProdFinsupp.symm (_, _) ↔ _
  rw [EquivLike.apply_eq_iff_eq, Prod.ext_iff]
  change (degreeExponent (Finsupp.weight (slotWeight P) e) =
    degreeExponent (Finsupp.weight (slotWeight P) f) ∧ _) ↔ _
  rw [EquivLike.apply_eq_iff_eq]
private def monomialHom {R σ τ : Type*} [CommRing R] (w : (σ →₀ ℕ) →+ (τ →₀ ℕ)) :
    MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  AddMonoidAlgebra.mapDomainAlgHom R R w
private theorem monomialHom_apply {R σ τ : Type*} [CommRing R]
    (w : (σ →₀ ℕ) →+ (τ →₀ ℕ)) (e : σ →₀ ℕ) (c : R) :
    monomialHom w (monomial e c) = monomial (w e) c := by
  change AddMonoidAlgebra.mapDomain w (AddMonoidAlgebra.single e c) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl
def binomialIdeal (P : Fin 4 → Shape) (R : Type*) [CommRing R] : Ideal (MvPolynomial (Slot P) R) :=
  Ideal.span {p | ∃ e f : Slot P →₀ ℕ, taggedExponent P e = taggedExponent P f ∧
    p = monomial e 1 - monomial f 1}
theorem map_binomialIdeal {R S : Type*} [CommRing R] [CommRing S]
    (P : Fin 4 → Shape) (g : R →+* S) :
    (binomialIdeal P R).map (MvPolynomial.map g) = binomialIdeal P S := by
  rw [binomialIdeal, Ideal.map_span, binomialIdeal]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨e, f, h, rfl⟩, rfl⟩
    exact ⟨e, f, h, by simp⟩
  · rintro ⟨e, f, h, rfl⟩
    exact ⟨_, ⟨e, f, h, rfl⟩, by simp⟩
private theorem lift_monomials {P : Fin 4 → Shape} {R τ : Type*} [CommRing R]
    (s : Set (Slot P →₀ ℕ)) (w : (Slot P →₀ ℕ) → (τ →₀ ℕ))
    (h : ∀ e ∈ s, ∀ f ∈ s, w e = w f → taggedExponent P e = taggedExponent P f) :
    ∃ l : MvPolynomial τ R →ₗ[R] (MvPolynomial (Slot P) R ⧸ binomialIdeal P R),
      ∀ e ∈ s, l (monomial (w e) 1) = Ideal.Quotient.mk _ (monomial e 1) := by
  classical
  let J := binomialIdeal P R
  let g (a : τ →₀ ℕ) : MvPolynomial (Slot P) R ⧸ J :=
    if ha : ∃ e ∈ s, w e = a then Ideal.Quotient.mk J (monomial ha.choose 1) else 0
  refine ⟨(basisMonomials τ R).constr R g, fun e he => ?_⟩
  change (basisMonomials τ R).constr R g ((basisMonomials τ R) (w e)) = _
  rw [Module.Basis.constr_basis]
  let he' : ∃ f ∈ s, w f = w e := ⟨e, he, rfl⟩
  dsimp only [g]
  rw [dite_eq_left he', Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span ⟨_, _, h _ he'.choose_spec.1 e he he'.choose_spec.2, rfl⟩
private theorem tagged_ker (P : Fin 4 → Shape) (R : Type*) [CommRing R] :
    RingHom.ker (monomialHom (R := R) (taggedExponent P)).toRingHom = binomialIdeal P R := by
  let J := binomialIdeal P R
  let φ := monomialHom (R := R) (taggedExponent P)
  obtain ⟨l, hl⟩ := lift_monomials (R := R) Set.univ (taggedExponent P)
    (fun _ _ _ _ h => h)
  have hfac : l.comp φ.toLinearMap = (Ideal.Quotient.mkₐ R J).toLinearMap := by
    apply (basisMonomials (Slot P) R).ext
    intro e
    simp only [coe_basisMonomials, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [show φ (monomial e 1) = monomial (taggedExponent P e) 1 from monomialHom_apply _ _ _]
    exact hl e (Set.mem_univ _)
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := DFunLike.congr_fun hfac p
    change l (φ p) = Ideal.Quotient.mk J p at h
    change φ p = 0 at hp
    simpa [hp] using h.symm
  · apply Ideal.span_le.mpr
    rintro _ ⟨e, f, h, rfl⟩
    change monomialHom (R := R) (taggedExponent P) (monomial e 1 - monomial f 1) = 0
    rw [map_sub, monomialHom_apply, monomialHom_apply, h, sub_self]
private theorem dehom_eq_monomialHom (k : Type) [Field k] (P : Fin 4 → Shape) :
    dehom k P = monomialHom (affineExponent P) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [dehom, aeval_X, MvPolynomial.X, monomialHom_apply, affineExponent, Finsupp.weight_single, one_smul]
theorem relationIdeal_zero (k : Type) [Field k] (P : Fin 4 → Shape) :
    relationIdeal k P 0 = binomialIdeal P (CoefficientField k P) := by
  classical
  have hprefix : prefixIdeal k P 0 = ⊥ := by simp [prefixIdeal]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨⟨d, hd⟩, hp⟩
    have hz : dehom k P p = 0 := by simpa [hprefix] using hp
    let J := binomialIdeal P (CoefficientField k P)
    obtain ⟨l, hl⟩ := lift_monomials (R := CoefficientField k P)
      {e | Finsupp.weight (slotWeight P) e = d} (affineExponent P)
      (fun e he f hf h => taggedExponent_eq.mpr ⟨he.trans hf.symm, h⟩)
    let q := Ideal.Quotient.mkₐ (CoefficientField k P) J
    have hfac : l (dehom k P p) = q p := by
      calc
        l (dehom k P p) = l (dehom k P (∑ e ∈ p.support, monomial e (p.coeff e))) :=
          congrArg (fun r => l (dehom k P r)) p.as_sum
        _ = q (∑ e ∈ p.support, monomial e (p.coeff e)) := by
          simp only [map_sum]
          apply Finset.sum_congr rfl
          intro e he
          rw [show monomial e (p.coeff e) = p.coeff e • monomial e 1 by
            simp [smul_monomial]]
          simp only [map_smul, dehom_eq_monomialHom, monomialHom_apply,
            hl e (hd (mem_support_iff.mp he))]
          rfl
        _ = q p := (congrArg q p.as_sum).symm
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p = 0
    rw [← hfac, hz, map_zero]
  · apply Ideal.span_le.mpr
    rintro _ ⟨e, f, h, rfl⟩
    obtain ⟨hd, ha⟩ := taggedExponent_eq.mp h
    apply Ideal.subset_span
    refine ⟨⟨_, Submodule.sub_mem (slotPiece k P (Finsupp.weight (slotWeight P) e)) ?_ ?_⟩, ?_⟩
    · exact isWeightedHomogeneous_monomial _ _ _ rfl
    · exact isWeightedHomogeneous_monomial _ _ _ hd.symm
    · rw [hprefix, Ideal.mem_bot, map_sub, dehom_eq_monomialHom,
        monomialHom_apply, monomialHom_apply, ha, sub_self]
abbrev MonomialRing (k : Type) [Field k] (P : Fin 4 → Shape) :=
  MvPolynomial (Slot P) k ⧸ binomialIdeal P k
instance (k : Type) [Field k] (P : Fin 4 → Shape) : IsDomain (MonomialRing k P) := by
  have : (binomialIdeal P k).IsPrime := by
    rw [← tagged_ker]
    exact RingHom.ker_isPrime _
  infer_instance
theorem monomialCoordinate_ne_zero {k : Type} [Field k] {P : Fin 4 → Shape} (v : Slot P) :
    Ideal.Quotient.mk (binomialIdeal P k) (MvPolynomial.X v) ≠ 0 := by
  intro h
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp h
  rw [← tagged_ker] at hm
  change monomialHom (R := k) (taggedExponent P) (MvPolynomial.X v) = 0 at hm
  rw [MvPolynomial.X, monomialHom_apply, monomial_eq_zero] at hm
  exact one_ne_zero hm
end
end K1_13_6_1_4_3_3_3_2_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_1
open K1_13_6_1_4_3_3 Ideal IsLocalRing RingTheory.Sequence
def c1 : Prop :=
  ∀ (k : Type) [Field k] (p : Ideal (Jets k)) [p.IsMaximal],
    ∃ s : List (Localization.AtPrime p), s.length = 4 ∧
      (∀ x ∈ s, x ∈ maximalIdeal (Localization.AtPrime p)) ∧
      IsRegular (Localization.AtPrime p) s
def c2 : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (f : Fin 4 → R),
    (∃ s : List R, s.length = 4 ∧ (∀ x ∈ s, x ∈ maximalIdeal R) ∧ IsRegular R s) →
    (Ideal.span (Set.range f)).radical = maximalIdeal R →
    ∀ (i : Fin 4) (x : R), f i * x ∈ otherIdeal f i → x ∈ otherIdeal f i
theorem prime_isMaximal_of_finite_quotient {k R : Type*}
    [Field k] [CommRing R] [Algebra k R] (J P : Ideal R) [P.IsPrime]
    [Module.Finite k (R ⧸ J)] (hle : J ≤ P) : P.IsMaximal := by
  let m := Ideal.Quotient.mk J
  let Q := P.map m
  have : IsArtinianRing (R ⧸ J) := IsArtinianRing.of_finite k _
  have : Q.IsPrime := Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by simpa only [m, Ideal.mk_ker] using hle)
  have he : Q.comap m = P := by
    rw [show Q = P.map m from rfl, Ideal.comap_map_of_surjective m Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, show RingHom.ker m = J from Ideal.mk_ker,
      sup_eq_left.mpr hle]
  rw [← he]
  exact Ideal.comap_isMaximal_of_surjective m Ideal.Quotient.mk_surjective
theorem radical_map_of_finite_quotient {k R : Type*}
    [Field k] [CommRing R] [Algebra k R] (J p : Ideal R) [p.IsMaximal]
    [Module.Finite k (R ⧸ J)] (hle : J ≤ p) :
    (J.map (algebraMap R (Localization.AtPrime p))).radical =
      maximalIdeal (Localization.AtPrime p) := by
  let S := Localization.AtPrime p
  let φ := algebraMap R S
  have hp : p.map φ = maximalIdeal S := Localization.AtPrime.map_eq_maximalIdeal (I := p)
  apply le_antisymm
  · exact (maximalIdeal.isMaximal S).isPrime.radical_le_iff.mpr
      ((Ideal.map_mono (f := φ) hle).trans_eq hp)
  · intro y hy
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro Q hQ
    have : Q.IsPrime := hQ.2
    let P := Q.comap φ
    have : P.IsPrime := Ideal.comap_isPrime φ Q
    have hJP : J ≤ P := Ideal.map_le_iff_le_comap.mp hQ.1
    have hPp : P ≤ p := by
      have hQmax := IsLocalRing.le_maximalIdeal (J := Q) hQ.2.ne_top
      exact (Ideal.comap_mono (f := φ) hQmax).trans_eq
        (Localization.AtPrime.under_maximalIdeal (I := p))
    have hP : P = p :=
      (prime_isMaximal_of_finite_quotient (k := k) J P hJP).eq_of_le
        (show p ≠ ⊤ from Ideal.IsMaximal.ne_top inferInstance) hPp
    have hQp : Q = maximalIdeal S := by
      calc
        Q = P.map φ := (IsLocalization.map_under p.primeCompl S Q).symm
        _ = maximalIdeal S := (congrArg (Ideal.map φ) hP).trans hp
    exact hQp.symm ▸ hy
theorem cancel_other {k : Type} [Field k] (h₁ : c1) (h₂ : c2)
    (f : Fin 4 → Jets k) [Module.Finite k (CutAlgebra f)]
    (i : Fin 4) (x : Jets k) (hx : f i * x ∈ otherIdeal f i) :
    x ∈ otherIdeal f i := by
  by_contra h
  let I := otherIdeal f i
  let T := I.colon {x}
  have hT : T ≠ ⊤ := by
    intro ht
    have ht' : (1 : Jets k) ∈ T := by simp [ht]
    have hx' := Submodule.mem_colon_singleton.mp ht'
    exact h (by simpa only [one_smul] using hx')
  obtain ⟨p, hp, hTp⟩ := Ideal.exists_le_maximal T hT
  have hIp : I ≤ p := Ideal.le_colon.trans hTp
  have hfp : CutIdeal f ≤ p := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · subst j
      exact hTp (Submodule.mem_colon_singleton.mpr hx)
    · exact hIp (Ideal.subset_span ⟨j, hj, rfl⟩)
  let S := Localization.AtPrime p
  let φ := algebraMap (Jets k) S
  have hJ : (CutIdeal f).map φ = Ideal.span (Set.range (φ ∘ f)) := by
    rw [Ideal.map_span, Set.range_comp]
  have hI : I.map φ = otherIdeal (φ ∘ f) i := by
    change (Ideal.span (f '' {j | j ≠ i})).map φ = Ideal.span ((φ ∘ f) '' {j | j ≠ i})
    rw [Ideal.map_span, Set.image_image]
    rfl
  have hrad : (Ideal.span (Set.range (φ ∘ f))).radical = maximalIdeal S := by
    rw [← hJ]
    exact radical_map_of_finite_quotient (k := k) _ _ hfp
  have hmul : (φ ∘ f) i * φ x ∈ otherIdeal (φ ∘ f) i := by
    rw [← hI]
    change φ (f i) * φ x ∈ I.map φ
    rw [← map_mul]
    exact Ideal.mem_map_of_mem φ hx
  have hloc := h₂ S (φ ∘ f) (h₁ k p) hrad i (φ x) hmul
  rw [← hI] at hloc
  obtain ⟨m, hm, hmx⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl S I x).mp hloc
  exact (Ideal.mem_primeCompl_iff.mp hm) (hTp (Submodule.mem_colon_singleton.mpr hmx))
theorem span_update {R : Type*} [CommRing R] (f : Fin 4 → R) (i : Fin 4) (a : R) :
    Ideal.span (Set.range (Function.update f i a)) = otherIdeal f i ⊔ Ideal.span {a} := by
  classical
  rw [otherIdeal, ← Ideal.span_union]
  congr 1
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    by_cases hj : j = i
    · subst j
      exact Or.inr (by simp)
    · exact Or.inl ⟨j, hj, (Function.update_of_ne hj a f).symm⟩
  · rintro (⟨j, hj, rfl⟩ | h)
    · exact ⟨j, Function.update_of_ne hj a f⟩
    · obtain rfl := Set.mem_singleton_iff.mp h
      exact ⟨i, by simp⟩
theorem square_at {k : Type} [Field k] (h₁ : c1) (h₂ : c2) (f : Fin 4 → Jets k)
    [Module.Finite k (CutAlgebra f)] (i : Fin 4) :
    Module.Finite k (CutAlgebra (Function.update f i (f i ^ 2))) ∧
      Module.finrank k (CutAlgebra (Function.update f i (f i ^ 2))) =
        2 * Module.finrank k (CutAlgebra f) := by
  classical
  have hJ : CutIdeal f = otherIdeal f i ⊔ Ideal.span {f i} := by
    simpa only [Function.update_eq_self] using span_update f i (f i)
  have : Module.Finite k (Jets k ⧸ (otherIdeal f i ⊔ Ideal.span {f i})) := by
    rw [← hJ]
    infer_instance
  change Module.Finite k (Jets k ⧸ CutIdeal (Function.update f i (f i ^ 2))) ∧
    Module.finrank k (Jets k ⧸ CutIdeal (Function.update f i (f i ^ 2))) =
      2 * Module.finrank k (Jets k ⧸ CutIdeal f)
  have hJ₂ : CutIdeal (Function.update f i (f i ^ 2)) =
      otherIdeal f i ⊔ Ideal.span {f i ^ 2} := span_update f i (f i ^ 2)
  rw [hJ₂, hJ]
  exact square_length (k := k) _ _ (cancel_other h₁ h₂ f i)
theorem of_children (h₁ : c1) (h₂ : c2) : K1_13_6_1_4_3_3.c1 := by
  classical
  intro k _ f hf
  let f₁ := Function.update f 0 (f 0 ^ 2)
  let f₂ := Function.update f₁ 1 (f₁ 1 ^ 2)
  let f₃ := Function.update f₂ 2 (f₂ 2 ^ 2)
  let f₄ := Function.update f₃ 3 (f₃ 3 ^ 2)
  obtain ⟨hf₁, hlen₁⟩ := square_at h₁ h₂ f 0
  change Module.Finite k (CutAlgebra f₁) at hf₁
  obtain ⟨hf₂, hlen₂⟩ := square_at h₁ h₂ f₁ 1
  change Module.Finite k (CutAlgebra f₂) at hf₂
  obtain ⟨hf₃, hlen₃⟩ := square_at h₁ h₂ f₂ 2
  change Module.Finite k (CutAlgebra f₃) at hf₃
  obtain ⟨hf₄, hlen₄⟩ := square_at h₁ h₂ f₃ 3
  have he : f₄ = fun i => f i ^ 2 := by
    funext i
    fin_cases i <;> simp [f₄, f₃, f₂, f₁, Function.update]
  rw [← he]
  refine ⟨hf₄, ?_⟩
  change Module.finrank k (CutAlgebra f₄) = _
  change Module.finrank k (CutAlgebra f₄) = 2 * Module.finrank k (CutAlgebra f₃) at hlen₄
  change Module.finrank k (CutAlgebra f₃) = 2 * Module.finrank k (CutAlgebra f₂) at hlen₃
  change Module.finrank k (CutAlgebra f₂) = 2 * Module.finrank k (CutAlgebra f₁) at hlen₂
  change Module.finrank k (CutAlgebra f₁) = 2 * Module.finrank k (CutAlgebra f) at hlen₁
  omega
end K1_13_6_1_4_3_3_1
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_2
noncomputable section
open K1_13 K1_13_6_1_4_3_3 K1_13_5_4_2_4_1 MvPolynomial
open scoped nonZeroDivisors
def c1 : Prop :=
  ∀ (L : Type) [Field L] (g : Fin 4 → Total L),
    Module.Finite L (CutAlgebra (fun i => reduce (g i))) →
    ∀ (m : Ideal (Total L)) [m.IsMaximal], specialIdeal g ≤ m →
      ∃ rs : List (Localization.AtPrime m),
        rs.length = 5 ∧
        (∀ r ∈ rs, r ∈ (specialIdeal g).map (algebraMap (Total L) (Localization.AtPrime m))) ∧
        RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime m) rs
def c2 : Prop :=
  ∀ (L R : Type) [Field L] [Infinite L] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra L R] (u : Fin 4 → R) (t : R),
    let J := Ideal.span (Set.range u)
    let I := J ⊔ Ideal.span {t}
    I ≤ IsLocalRing.maximalIdeal R →
    (∃ rs : List R, rs.length = 5 ∧ (∀ r ∈ rs, r ∈ I) ∧
      RingTheory.Sequence.IsWeaklyRegular R rs) →
    IsSMulRegular (R ⧸ J) (Ideal.Quotient.mk J t)
section Relations
variable {L : Type} [Field L]
private theorem reduce_surjective : Function.Surjective (reduce (L := L)) := by
  apply MvPolynomial.map_surjective
  intro a
  exact ⟨Polynomial.C a, Polynomial.eval_C⟩
theorem equations_map_reduce (g : Fin 4 → Total L) :
    (equationsIdeal g).map reduce = CutIdeal (fun i => reduce (g i)) := by
  simp only [equationsIdeal, Ideal.map_span, ← Set.range_comp']
private theorem clear_generic_ideal (g : Fin 4 → Total L) (p : Total L)
    (h : genericClass g p = 0) :
    ∃ d : Polynomial L, d ≠ 0 ∧ C d * p ∈ equationsIdeal g := by
  let : Algebra (Total L) (Affine (ParameterField L)) := MvPolynomial.algebraMvPolynomial
  let S := (Polynomial L)⁰.map (C (σ := Fin 4))
  have : IsLocalization S (Affine (ParameterField L)) :=
    MvPolynomial.isLocalization (Polynomial L)⁰ (ParameterField L)
  have hmem : algebraMap (Total L) (Affine (ParameterField L)) p ∈
      (equationsIdeal g).map (algebraMap (Total L) (Affine (ParameterField L))) :=
    Ideal.Quotient.eq_zero_iff_mem.mp h
  obtain ⟨_, ⟨d, hd, rfl⟩, hp⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff S _ (equationsIdeal g) p).mp hmem
  exact ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp hd, hp⟩
theorem local_parameter_regular [Infinite L] (h1 : c1) (h2 : c2)
    (g : Fin 4 → Total L) (hfinite : Module.Finite L (CutAlgebra (fun i => reduce (g i))))
    (m : Ideal (Total L)) [m.IsMaximal] (hm : specialIdeal g ≤ m) :
    IsSMulRegular (Localization.AtPrime m ⧸
      (equationsIdeal g).map (algebraMap (Total L) (Localization.AtPrime m)))
      (Ideal.Quotient.mk ((equationsIdeal g).map (algebraMap (Total L) (Localization.AtPrime m)))
        (algebraMap (Total L) (Localization.AtPrime m) (C Polynomial.X))) := by
  let R := Localization.AtPrime m
  let loc := algebraMap (Total L) R
  let : Algebra L R := (loc.comp (algebraMap L (Total L))).toAlgebra
  let u (i : Fin 4) := loc (g i)
  let t := loc (C Polynomial.X)
  have hJ : (equationsIdeal g).map loc = Ideal.span (Set.range u) := by
    simp only [equationsIdeal, Ideal.map_span, ← Set.range_comp', u]
  have hI : (specialIdeal g).map loc = Ideal.span (Set.range u) ⊔ Ideal.span {t} := by
    rw [specialIdeal, Ideal.map_sup, hJ, Ideal.map_span, Set.image_singleton]
  have hle : (specialIdeal g).map loc ≤ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m R]
    exact Ideal.map_mono hm
  have hrs := h1 L g hfinite m hm
  change ∃ rs : List R, rs.length = 5 ∧ (∀ r ∈ rs, r ∈ (specialIdeal g).map loc) ∧
    RingTheory.Sequence.IsWeaklyRegular R rs at hrs
  rw [hI] at hle hrs
  have hreg := h2 L R u t hle hrs
  change IsSMulRegular (R ⧸ (equationsIdeal g).map loc)
    (Ideal.Quotient.mk ((equationsIdeal g).map loc) t)
  rw [hJ]
  exact hreg
theorem relation_reduces [Infinite L] (h1 : c1) (h2 : c2)
    (g : Fin 4 → Total L) (hfinite : Module.Finite L (CutAlgebra (fun i => reduce (g i))))
    (p : Total L) (hp : genericClass g p = 0) :
    reduce p ∈ CutIdeal (fun i => reduce (g i)) := by
  let J := equationsIdeal g
  let J₀ := CutIdeal (fun i => reduce (g i))
  change reduce p ∈ J₀
  by_contra hnot
  let I := J₀.colon {reduce p}
  have hone : (1 : Affine L) ∉ I := by
    intro h
    exact hnot (by simpa only [one_smul] using Submodule.mem_colon_singleton.mp h)
  obtain ⟨m₀, hm₀, hI⟩ := Ideal.exists_le_maximal I (mt (Ideal.eq_top_iff_one I).mp hone)
  let m := m₀.comap reduce
  have : m.IsMaximal := Ideal.comap_isMaximal_of_surjective reduce reduce_surjective
  have hm : specialIdeal g ≤ m := by
    apply sup_le
    · rw [show m = m₀.comap reduce from rfl, ← Ideal.map_le_iff_le_comap, equations_map_reduce]
      exact le_trans (fun a ha => Submodule.mem_colon_singleton.mpr (J₀.mul_mem_right _ ha)) hI
    · apply (Ideal.span_singleton_le_iff_mem m).mpr
      change reduce (C Polynomial.X) ∈ m₀
      simp [reduce]
  let R := Localization.AtPrime m
  let loc := algebraMap (Total L) R
  let mk : Total L →+* (R ⧸ J.map loc) := (Ideal.Quotient.mk _).comp loc
  let t := mk (C Polynomial.X)
  have hreg : IsSMulRegular (R ⧸ J.map loc) t :=
    local_parameter_regular h1 h2 g hfinite m hm
  obtain ⟨d, hd, hdp⟩ := clear_generic_ideal g p hp
  obtain ⟨q, hfactor, hq⟩ := d.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hd (0 : L)
  rw [Polynomial.C_0, sub_zero] at hfactor hq
  have hq0 : q.eval 0 ≠ 0 := by
    rwa [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero] at hq
  have hqu : (C q : Total L) ∉ m := by
    change reduce (C q) ∉ m₀
    rw [show reduce (C q) = C (q.eval 0) by simp [reduce]]
    exact m₀.notMem_of_isUnit ((Ne.isUnit hq0).map C)
  have hunit : IsUnit (mk (C q)) :=
    (IsLocalization.map_units R (⟨C q, hqu⟩ : m.primeCompl)).map (Ideal.Quotient.mk _)
  have hzero : mk (C d * p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hdp)
  have hzero' : t ^ d.rootMultiplicity 0 * (mk (C q) * mk p) = 0 := by
    rw [hfactor] at hzero
    simpa only [map_mul, map_pow, mul_assoc, t] using hzero
  have hcancel : mk (C q) * mk p = 0 :=
    (hreg.pow (d.rootMultiplicity 0)) (by simpa only [smul_eq_mul, mul_zero] using hzero')
  have hmk : mk p = 0 :=
    hunit.mul_left_cancel (by simpa only [mul_zero] using hcancel)
  have hmem : loc p ∈ J.map loc := Ideal.Quotient.eq_zero_iff_mem.mp hmk
  obtain ⟨s, hs, hsp⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff m.primeCompl R J p).mp hmem
  have hprod := Ideal.mem_map_of_mem reduce hsp
  rw [show J.map reduce = J₀ from equations_map_reduce g, map_mul] at hprod
  exact hs (hI (Submodule.mem_colon_singleton.mpr hprod))
end Relations
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4_3_3.c2 := by
  classical
  intro k _ P f hs hf hg
  let L := CoefficientField k P
  let : Nonempty (Σ i : Fin 4, lattice (P i)) := ⟨⟨0, ⟨0, by simp [lattice]⟩⟩⟩
  have : Infinite L := Infinite.of_injective (algebraMap (CoefficientRing k P) L)
    (IsFractionRing.injective (CoefficientRing k P) L)
  let g := deformation P f
  have hI : CutIdeal (fun i => reduce (g i)) =
      (CutIdeal f).map (MvPolynomial.map (algebraMap k L)) := by
    simp only [CutIdeal, Ideal.map_span, ← Set.range_comp', g,
      deformation_reduce P f hs]
    rfl
  have := hf
  obtain ⟨hsfinite, hsrank⟩ := finite_rank_map_ideal (L := L) (CutIdeal f)
  rw [← hI] at hsfinite hsrank
  obtain ⟨hgfinite, hgrank⟩ := deformation_generic P f hg
  have : Module.Finite (ParameterField L) (GenericFiber g) := hgfinite
  let s := Ideal.Quotient.mkₐ L (CutIdeal (fun i => reduce (g i)))
  have hr := specialization_rank g s.toLinearMap Ideal.Quotient.mk_surjective (fun p hp =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (relation_reduces h1 h2 g hsfinite p hp))
  rw [← hsrank, ← hgrank]
  exact hr
end
end K1_13_6_1_4_3_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_3_2_1
noncomputable section
open K1_13 K1_13_6_1_4_3_3 K1_13_6_1_4_3_3_3_2 MvPolynomial
variable {k : Type} [Field k] {P : Fin 4 → Shape}
private theorem weight_apply (e : Slot P →₀ ℕ) (i : SlotIndex) :
    Finsupp.weight (slotWeight P) e i = ∑ a : slotSupport P i, e ⟨i, a⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Finset.sum_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp [slotWeight, Pi.smul_apply]
  · intro j _ hj
    simp [slotWeight, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj)]
  · simp
private theorem monomial_mul_mem (J : Ideal (SlotRing k P)) (g : SlotRing k P) (N : ℕ)
    (hkill : ∀ a : Chart P, chartProduct k P a ^ N * g ∈ J)
    (e : Slot P →₀ ℕ) (c : CoefficientField k P)
    (he : ∀ i, Fintype.card (slotSupport P i) * N < Finsupp.weight (slotWeight P) e i) :
    monomial e c * g ∈ J := by
  classical
  have hpick (i : SlotIndex) : ∃ a : slotSupport P i, N ≤ e ⟨i, a⟩ := by
    by_contra! h
    have hsum : (∑ a : slotSupport P i, e ⟨i, a⟩) ≤ Fintype.card (slotSupport P i) * N := by
      calc
        _ ≤ ∑ _a : slotSupport P i, N := Finset.sum_le_sum fun a _ => (h a).le
        _ = _ := by simp
    exact (not_le_of_gt (he i)) ((weight_apply e i).trans_le hsum)
  choose a ha using hpick
  let v : Slot P →₀ ℕ := ∑ i : SlotIndex, Finsupp.single ⟨i, a i⟩ N
  have hv : v ≤ e := by
    rintro ⟨i, b⟩
    rw [show v ⟨i, b⟩ = Finsupp.single (⟨i, a i⟩ : Slot P) N ⟨i, b⟩ by
      simp only [v, Finsupp.finsetSum_apply]
      apply Finset.sum_eq_single i
      · intro j _ hj
        apply Finsupp.single_eq_of_ne
        intro h
        exact hj (congrArg Sigma.fst h).symm
      · simp]
    by_cases hab : a i = b
    · subst b
      simpa using ha i
    · simp [Ne.symm hab]
  have hchart : chartProduct k P a ^ N = monomial v (1 : CoefficientField k P) := by
    unfold chartProduct
    rw [← Finset.prod_pow]
    simp only [MvPolynomial.X_pow_eq_monomial, v, monomial_sum_one]
  have hfactor : monomial e c * g = monomial (e - v) c * (chartProduct k P a ^ N * g) := by
    rw [hchart, ← mul_assoc, monomial_mul_monomial, mul_one, add_comm (e - v),
      add_tsub_cancel_of_le hv]
  rw [hfactor]
  exact J.mul_mem_left _ (hkill a)
private theorem homogeneous_mul_mem (J : Ideal (SlotRing k P)) (g : SlotRing k P) (N : ℕ)
    (hkill : ∀ a : Chart P, chartProduct k P a ^ N * g ∈ J)
    {f : SlotRing k P} {d : MultiDegree} (hf : f ∈ slotPiece k P d)
    (hd : ∀ i, Fintype.card (slotSupport P i) * N < d i) : f * g ∈ J := by
  classical
  rw [f.as_sum, Finset.sum_mul]
  exact J.sum_mem fun e he => monomial_mul_mem J g N hkill e _ (by
    have hdeg := hf (mem_support_iff.mp he)
    intro i
    simpa only [hdeg] using hd i)
private theorem component_mul {g : SlotRing k P} {e : MultiDegree}
    (hg : g ∈ slotPiece k P e) (f : SlotRing k P) (d : MultiDegree) :
    weightedHomogeneousComponent (slotWeight P) (d + e) (f * g) =
      weightedHomogeneousComponent (slotWeight P) d f * g := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial a c =>
    have ha := isWeightedHomogeneous_monomial (slotWeight P) a c rfl
    have hg' : g.IsWeightedHomogeneous (slotWeight P) e := hg
    simp only [weightedHomogeneousComponent_of_mem (ha.mul hg'),
      weightedHomogeneousComponent_of_mem ha, add_right_cancel_iff]
    split <;> simp_all
  | add p r hp hr => simp [add_mul, hp, hr]
theorem proof : K1_13_6_1_4_3_3_3_2.c1 := by
  classical
  intro k _ P r hlocal
  obtain ⟨G, hG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    (R := SlotRing k P) (relationGenerators k P r)).mp (IsNoetherian.noetherian _)
  have hspan' : relationIdeal k P r = Ideal.span (↑G : Set (SlotRing k P)) := hspan
  choose D hD using fun g : G => (hG g.property).1
  choose n hn using fun g : G => hlocal g (hG g.property)
  let N (g : G) := Finset.univ.sup (n g)
  have hN (g : G) (a : Chart P) : chartProduct k P a ^ N g * (g : SlotRing k P) ∈ cutIdeal k P r := by
    have hle : n g a ≤ N g := Finset.le_sup (f := n g) (Finset.mem_univ a)
    have hpow : chartProduct k P a ^ N g * (g : SlotRing k P) =
        chartProduct k P a ^ (N g - n g a) * (chartProduct k P a ^ n g a * (g : SlotRing k P)) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [hpow]
    exact (cutIdeal k P r).mul_mem_left _ (hn g a)
  let bound (g : G) (i : SlotIndex) := D g i + Fintype.card (slotSupport P i) * N g + 1
  let q := Finset.univ.sup fun g : G => Finset.univ.sup (bound g)
  refine ⟨q, ?_⟩
  intro d hd f hf hrel
  rw [hspan'] at hrel
  obtain ⟨c, hc⟩ := Submodule.mem_span_finset'.mp hrel
  have hsum := congrArg (weightedHomogeneousComponent (slotWeight P) d) hc
  rw [map_sum, weightedHomogeneousComponent_eq_self (show f.IsWeightedHomogeneous _ d from hf)]
    at hsum
  rw [← hsum]
  refine (cutIdeal k P r).sum_mem fun g _ => ?_
  have hgd (i : SlotIndex) : bound g i ≤ d i :=
    (Finset.le_sup (f := bound g) (Finset.mem_univ i)).trans
      ((Finset.le_sup (f := fun x : G => Finset.univ.sup (bound x)) (Finset.mem_univ g)).trans (hd i))
  have hdiff (i : SlotIndex) : Fintype.card (slotSupport P i) * N g < (d - D g) i := by
    have hh := hgd i
    change D g i + Fintype.card (slotSupport P i) * N g + 1 ≤ d i at hh
    change _ < d i - D g i
    omega
  have heq : d - D g + D g = d := by
    funext i
    exact Nat.sub_add_cancel (by
      have hh := hgd i
      dsimp [bound] at hh
      omega)
  change weightedHomogeneousComponent (slotWeight P) d (c g * (g : SlotRing k P)) ∈ cutIdeal k P r
  rw [← heq, component_mul (hD g)]
  exact homogeneous_mul_mem (cutIdeal k P r) g (N g) (hN g)
    (weightedHomogeneousComponent_mem _ _ _) hdiff
end
end K1_13_6_1_4_3_3_3_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_3_2_2
noncomputable section
open K1_13 K1_13_6_1_4_3_3 K1_13_6_1_4_3_3_3_2 MvPolynomial
local instance latticeFintype (p : Shape) : Fintype (lattice p) :=
  (lattice_finite p).fintype
variable {k : Type} [Field k] {P : Fin 4 → Shape}
abbrev UniversalRing (k : Type) [Field k] (P : Fin 4 → Shape) :=
  MvPolynomial (CoeffSlot P) (MonomialRing k P)
def coordinate (v : Slot P) : MonomialRing k P :=
  Ideal.Quotient.mk (binomialIdeal P k) (MvPolynomial.X v)
def modelChart (k : Type) [Field k] (P : Fin 4 → Shape) (b : Chart P) : MonomialRing k P :=
  ∏ j : SlotIndex, coordinate ⟨j, b j⟩
theorem modelChart_ne_zero (b : Chart P) : modelChart k P b ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => monomialCoordinate_ne_zero ⟨j, b j⟩
def modelEquation (k : Type) [Field k] (P : Fin 4 → Shape) (i : Fin 4) : UniversalRing k P :=
  ∑ a : lattice (P i), C (coordinate ⟨some i, a⟩) * MvPolynomial.X ⟨i, a⟩
def modelIdeal (k : Type) [Field k] (P : Fin 4 → Shape) (r : ℕ) : Ideal (UniversalRing k P) :=
  Ideal.span (modelEquation k P '' {i : Fin 4 | i.val < r})
private theorem substitution {L : Type*} [CommRing L] (P : Fin 4 → Shape) (r : ℕ)
    (b : (j : Fin 4) → lattice (P j)) (z : CoeffSlot P → L) (w : Fin 4 → L)
    (hw : ∀ j, w j * z ⟨j, b j⟩ = 1) :
    ∃ E : MvPolynomial (CoeffSlot P) L →ₐ[L] MvPolynomial (CoeffSlot P) L,
      RingHom.ker E.toRingHom =
        Ideal.span ((fun j : Fin 4 => ∑ a : lattice (P j), C (z ⟨j, a⟩) * MvPolynomial.X ⟨j, a⟩) ''
          {j : Fin 4 | j.val < r}) := by
  classical
  let terms (j : Fin 4) (a : lattice (P j)) : MvPolynomial (CoeffSlot P) L :=
    C (z ⟨j, a⟩) * MvPolynomial.X ⟨j, a⟩
  let equation (j : Fin 4) := ∑ a, terms j a
  let rest (j : Fin 4) := ∑ a ∈ Finset.univ.erase (b j), terms j a
  let value (v : CoeffSlot P) : MvPolynomial (CoeffSlot P) L :=
    if v.1.val < r ∧ v.2 = b v.1 then - (C (w v.1) * rest v.1) else MvPolynomial.X v
  let E : MvPolynomial (CoeffSlot P) L →ₐ[L] MvPolynomial (CoeffSlot P) L := aeval value
  let J := Ideal.span (equation '' {j : Fin 4 | j.val < r})
  have hsum (j : Fin 4) : equation j = rest j + terms j (b j) :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ (b j))).symm
  have hrest (j : Fin 4) : E (rest j) = rest j := by
    simp only [rest, map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hne := (Finset.mem_erase.mp ha).1
    simp [terms, E, value, hne]
  have hpivot (j : Fin 4) (hj : j.val < r) :
      E (MvPolynomial.X ⟨j, b j⟩) = - (C (w j) * rest j) := by
    simp [E, value, hj]
  have hunit (j : Fin 4) : C (w j) * C (z ⟨j, b j⟩) = (1 : MvPolynomial (CoeffSlot P) L) := by
    rw [← map_mul, hw, map_one]
  refine ⟨E, show RingHom.ker E.toRingHom = J from le_antisymm ?_ ?_⟩
  · let q := Ideal.Quotient.mkₐ L J
    have hq : q.comp E = q := by
      apply MvPolynomial.algHom_ext
      rintro ⟨j, a⟩
      change q (E (MvPolynomial.X ⟨j, a⟩)) = q (MvPolynomial.X ⟨j, a⟩)
      by_cases h : j.val < r ∧ a = b j
      · obtain ⟨hj, rfl⟩ := h
        rw [hpivot j hj, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
        rw [show - (C (w j) * rest j) - MvPolynomial.X ⟨j, b j⟩ =
          -(C (w j) * rest j + MvPolynomial.X ⟨j, b j⟩) by abel]
        apply J.neg_mem
        have he : equation j ∈ J := Ideal.subset_span ⟨j, hj, rfl⟩
        have hm := J.mul_mem_left (C (w j)) he
        simpa only [hsum j, terms, mul_add, ← mul_assoc, hunit j, one_mul] using hm
      · simp [E, value, h]
    intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p = 0
    have hh := DFunLike.congr_fun hq p
    change q (E p) = q p at hh
    change E p = 0 at hp
    simpa only [hp, map_zero] using hh.symm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change E (equation j) = 0
    rw [hsum, map_add, hrest]
    simp only [terms, map_mul, hpivot j hj, mul_neg]
    rw [show E (C (z ⟨j, b j⟩)) = C (z ⟨j, b j⟩) by simp [E]]
    rw [← mul_assoc, mul_comm (C (z ⟨j, b j⟩)), hunit, one_mul, add_neg_cancel]
theorem model_saturate (r : ℕ) (b : Chart P)
    {a : MonomialRing k P} (ha : a ≠ 0) (u : UniversalRing k P) (n : ℕ)
    (hu : C a ^ n * u ∈ modelIdeal k P r) :
    ∃ m : ℕ, C (modelChart k P b) ^ m * u ∈ modelIdeal k P r := by
  classical
  let x := modelChart k P b
  let L := Localization.Away x
  have hx : x ≠ 0 := modelChart_ne_zero b
  let : IsDomain L := Localization.Away.isDomain hx
  let g := algebraMap (MonomialRing k P) L
  let z (v : CoeffSlot P) := g (coordinate ⟨some v.1, v.2⟩)
  have hux : IsUnit (∏ j : SlotIndex, g (coordinate ⟨j, b j⟩)) := by
    rw [← map_prod]
    exact IsLocalization.Away.algebraMap_isUnit (S := L) x
  have hz (j : Fin 4) : IsUnit (z ⟨j, b (some j)⟩) :=
    isUnit_of_dvd_unit
      (Finset.dvd_prod_of_mem (fun i : SlotIndex => g (coordinate ⟨i, b i⟩))
        (Finset.mem_univ (some j))) hux
  choose w hw using fun j => isUnit_iff_exists_inv.mp (hz j)
  obtain ⟨E, hE⟩ := substitution P r (fun j => b (some j)) z w
    (fun j => (mul_comm _ _).trans (hw j))
  let : Algebra (UniversalRing k P) (MvPolynomial (CoeffSlot P) L) :=
    MvPolynomial.algebraMvPolynomial
  let incl := algebraMap (UniversalRing k P) (MvPolynomial (CoeffSlot P) L)
  let M := (Submonoid.powers x).map (C (σ := CoeffSlot P))
  have : IsLocalization M (MvPolynomial (CoeffSlot P) L) :=
    MvPolynomial.isLocalization (Submonoid.powers x) L
  have hincl : incl = MvPolynomial.map g := rfl
  have hJ : (modelIdeal k P r).map incl = RingHom.ker E.toRingHom := by
    rw [hE, modelIdeal, Ideal.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro i _
    simp [hincl, modelEquation, z]
  have hmem := Ideal.mem_map_of_mem incl hu
  rw [hJ] at hmem
  change E (incl (C a ^ n * u)) = 0 at hmem
  have hga : g a ≠ 0 := by
    have hinj : Function.Injective g := IsLocalization.injective (S := L)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
    exact fun h => ha (hinj (h.trans (map_zero g).symm))
  have hEa : E (incl (C a)) = C (g a) := by simp [hincl]
  have heu : E (incl u) = 0 := by
    rw [map_mul, map_pow, map_mul, map_pow, hEa] at hmem
    exact (mul_eq_zero.mp hmem).resolve_left (pow_ne_zero _ (C_ne_zero.mpr hga))
  have hu' : incl u ∈ (modelIdeal k P r).map incl := by rw [hJ]; exact heu
  obtain ⟨_, ⟨_, ⟨m, rfl⟩, rfl⟩, hm⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M _ (modelIdeal k P r) u).mp hu'
  exact ⟨m, by simpa only [map_pow] using hm⟩
end
end K1_13_6_1_4_3_3_3_2_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_1_2
open CategoryTheory Abelian Ideal IsLocalRing RingTheory.Sequence
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
theorem exists_regular_add {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (a : R) (J : Ideal R)
    (h : ∀ p ∈ associatedPrimes R M, ¬ span {a} ⊔ J ≤ p) :
    ∃ b ∈ J, IsSMulRegular M (a + b) := by
  classical
  let S := (associatedPrimes.finite R M).toFinset
  let T := S.filter (fun p => Maximal (· ∈ S) p)
  let G := T.filter (fun p => a ∉ p)
  let B := T.filter (fun p => a ∈ p)
  let K := J ⊓ G.inf id
  have hS (p : Ideal R) : p ∈ S ↔ p ∈ associatedPrimes R M :=
    Set.Finite.mem_toFinset _
  have hT {p : Ideal R} (hp : p ∈ T) : Maximal (· ∈ S) p :=
    (Finset.mem_filter.mp hp).2
  have hprime {p : Ideal R} (hp : p ∈ T) : p.IsPrime :=
    (hS p |>.mp (hT hp).1).isPrime
  have hK {p : Ideal R} (hp : p ∈ B) : ¬ K ≤ p := by
    obtain ⟨hpT, hpa⟩ := Finset.mem_filter.mp hp
    intro hle
    rcases (hprime hpT).inf_le.mp hle with hJ | hG
    · exact h p ((hS p).mp (hT hpT).1)
        (sup_le ((span_singleton_le_iff_mem p).mpr hpa) hJ)
    · obtain ⟨q, hqG, hqp⟩ := (hprime hpT).inf_le'.mp hG
      obtain ⟨hqT, hqa⟩ := Finset.mem_filter.mp hqG
      have hEq : p = q := le_antisymm ((hT hqT).2 (hT hpT).1 hqp) hqp
      exact hqa (hEq ▸ hpa)
  have hb : ∃ b ∈ K, ∀ p ∈ B, b ∉ p := by
    by_contra! hh
    have hin : ((K : Set R) ⊆ ⋃ p ∈ (↑B : Set (Ideal R)), (p : Set R)) := by
      intro b hb
      obtain ⟨p, hp, hbp⟩ := hh b hb
      exact Set.mem_iUnion₂_of_mem hp hbp
    obtain ⟨p, hp, hle⟩ :=
      (Ideal.subset_union_prime (f := id) ⊤ ⊤
        (fun p hp _ _ => hprime (Finset.mem_filter.mp hp).1)).mp hin
    exact hK hp hle
  obtain ⟨b, hbK, hbB⟩ := hb
  refine ⟨b, (inf_le_left : K ≤ J) hbK, ?_⟩
  have havoid : a + b ∉ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    intro ha
    obtain ⟨p, hp, hap⟩ := Set.mem_iUnion₂.mp ha
    obtain ⟨q, hpq, hq⟩ := S.exists_le_maximal ((hS p).mpr hp)
    have hqT : q ∈ T := Finset.mem_filter.mpr ⟨hq.1, hq⟩
    have haq := hpq hap
    by_cases ham : a ∈ q
    · exact hbB q (Finset.mem_filter.mpr ⟨hqT, ham⟩) (add_sub_cancel_left a b ▸ q.sub_mem haq ham)
    · have hqG : q ∈ G := Finset.mem_filter.mpr ⟨hqT, ham⟩
      have hbq : b ∈ q := ((inf_le_right : K ≤ G.inf id).trans (Finset.inf_le hqG)) hbK
      exact ham (add_sub_cancel_right a b ▸ q.sub_mem haq hbq)
  rwa [biUnion_associatedPrimes_eq_compl_regular, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
    at havoid
omit [IsNoetherianRing R] in
private theorem ext_after_regular (N M : ModuleCat.{u} R) {a : R} (ha : IsSMulRegular M a)
    {n : ℕ} (h : ∀ i < n + 1, Subsingleton (Ext N M i)) :
    ∀ i < n, Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop a M)) i) := by
  intro i hi
  have h₀ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h i (by omega))
  have h₁ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h (i + 1) (by omega))
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.covariant_sequence_exact₃' N ha.smulShortComplex_shortExact i (i + 1) rfl)
    (h₀.eq_zero_of_src _) (h₁.eq_zero_of_tgt _)
omit [IsNoetherianRing R] in
theorem regular_mod_tail_congr {M : Type u} [AddCommGroup M] [Module R M]
    (J : Ideal R) {a b : R} (hb : b ∈ J) :
    IsSMulRegular (M ⧸ (J • ⊤ : Submodule R M)) (a + b) →
      IsSMulRegular (M ⧸ (J • ⊤ : Submodule R M)) a := by
  let Q := J • (⊤ : Submodule R M)
  have hzero (x : M ⧸ Q) : b • x = 0 := by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change (Submodule.Quotient.mk (b • x) : M ⧸ Q) = 0
      exact (Submodule.Quotient.mk_eq_zero Q).mpr (Submodule.smul_mem_smul hb Submodule.mem_top)
  intro h x y hxy
  exact h (by simpa only [add_smul, hzero, add_zero] using hxy)
variable [IsLocalRing R]
private abbrev residue (R : Type u) [CommRing R] [IsLocalRing R] : ModuleCat.{u} R :=
  ModuleCat.of R (R ⧸ maximalIdeal R)
theorem parameters_weaklyRegular (rs : List R) (M : ModuleCat.{u} R)
    [Module.Finite R M]
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (hrad : maximalIdeal R ≤ (ofList rs ⊔ Module.annihilator R M).radical)
    (hExt : ∀ i < rs.length, Subsingleton (Ext (residue R) M i)) :
    IsWeaklyRegular M rs := by
  induction rs generalizing M with
  | nil => exact IsWeaklyRegular.nil R M
  | cons a rs ih =>
    let J := ofList rs
    have ha : a ∈ maximalIdeal R := hmem a List.mem_cons_self
    have htail (r : R) (hr : r ∈ rs) : r ∈ maximalIdeal R :=
      hmem r (List.mem_cons_of_mem _ hr)
    have hHom : Subsingleton (residue R →ₗ[R] M) :=
      (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton_congr.mp (hExt 0 (by simp))
    obtain ⟨r, hr, hrReg⟩ := IsSMulRegular.subsingleton_linearMap_iff.mp hHom
    have hrm : r ∈ maximalIdeal R := by
      change r ∈ Module.annihilator R (R ⧸ maximalIdeal R) at hr
      rwa [Ideal.annihilator_quotient] at hr
    have hnot (p : Ideal R) (hp : p ∈ associatedPrimes R M) : ¬ span {a} ⊔ J ≤ p := by
      intro h
      have hle : ofList (a :: rs) ⊔ Module.annihilator R M ≤ p :=
        sup_le (ofList_cons a rs ▸ h)
          (Submodule.annihilator_top (R := R) (M := M) ▸ hp.annihilator_le)
      have hpr : p.IsPrime := hp.isPrime
      have hmr := hrad.trans (hpr.radical_le_iff.mpr hle) hrm
      have hbad : r ∈ ⋃ q ∈ associatedPrimes R M, (q : Set R) :=
        Set.mem_iUnion₂_of_mem hp hmr
      rw [biUnion_associatedPrimes_eq_compl_regular] at hbad
      exact hbad hrReg
    obtain ⟨b, hb, hab⟩ := exists_regular_add a J hnot
    have habm : a + b ∈ maximalIdeal R := (maximalIdeal R).add_mem ha (span_le.mpr htail hb)
    let Q := (a + b) • (⊤ : Submodule R M)
    let M' := ModuleCat.of R (M ⧸ Q)
    have hAnn : Module.annihilator R M ≤ Module.annihilator R M' :=
      Q.mkQ.annihilator_le_of_surjective Q.mkQ_surjective
    have habAnn : a + b ∈ Module.annihilator R M' := by
      rw [Module.mem_annihilator]
      intro y
      obtain ⟨x, rfl⟩ := Q.mkQ_surjective y
      rw [← map_smul]
      exact (Submodule.Quotient.mk_eq_zero Q).mpr
        ((Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x, Submodule.mem_top, rfl⟩)
    have hrad' : maximalIdeal R ≤ (J ⊔ Module.annihilator R M').radical := by
      apply hrad.trans (Ideal.radical_mono ?_)
      rw [ofList_cons]
      refine sup_le (sup_le ((span_singleton_le_iff_mem _).mpr ?_) le_sup_left)
        (hAnn.trans le_sup_right)
      have he : a = (a + b) - b := (add_sub_cancel_right a b).symm
      rw [he]
      exact (J ⊔ Module.annihilator R M').sub_mem
        ((le_sup_right : Module.annihilator R M' ≤ J ⊔ Module.annihilator R M') habAnn)
        ((le_sup_left : J ≤ J ⊔ Module.annihilator R M') hb)
    have hExt' : ∀ i < rs.length, Subsingleton (Ext (residue R) M' i) :=
      ext_after_regular (residue R) M hab (by simpa only [List.length_cons] using hExt)
    have hreg : IsWeaklyRegular M ((a + b) :: rs) :=
      IsWeaklyRegular.cons hab (ih M' htail hrad' hExt')
    have hreg' : IsWeaklyRegular M (rs ++ [a + b]) :=
      IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hreg
        (List.perm_append_singleton _ _).symm (by simpa using ⟨habm, htail⟩)
    rw [isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff] at hreg'
    have hreg'' : IsWeaklyRegular M (rs ++ [a]) :=
      (isWeaklyRegular_append_iff M rs [a]).mpr
        ⟨hreg'.1, (isWeaklyRegular_singleton_iff _ _).mpr
          (regular_mod_tail_congr J hb hreg'.2)⟩
    apply IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hreg''
      (List.perm_append_singleton _ _)
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact htail z hz
    · obtain rfl := List.mem_singleton.mp hz
      exact ha
theorem proof : K1_13_6_1_4_3_3_1.c2 := by
  classical
  intro R _ _ _ f href hrad i x hx
  obtain ⟨s, hlen, hs, hreg⟩ := href
  let M := ModuleCat.of R R
  have hSupp : Module.support R (residue R) ⊆ PrimeSpectrum.zeroLocus (maximalIdeal R) := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  have hlt : maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by
    change maximalIdeal R • (⊤ : Ideal R) < ⊤
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact (maximalIdeal.isMaximal R).ne_top.lt_top
  have hExt : ∀ j < 4, Subsingleton (Ext (residue R) M j) := by
    rw [← hlen]
    exact ModuleCat.subsingleton_ext_of_exists_isRegular _ _ hSupp _ hlt s hs hreg
  let rs : List R := List.ofFn (f ∘ i.succAbove)
  have hother : ofList rs = K1_13_6_1_4_3_3_1.otherIdeal f i := by
    unfold K1_13_6_1_4_3_3_1.otherIdeal
    change span {r | r ∈ rs} = _
    congr 1
    ext r
    change r ∈ rs ↔ _
    rw [List.mem_ofFn', Set.range_comp, Fin.range_succAbove]
    rfl
  have hall : ofList (rs ++ [f i]) = span (Set.range f) := by
    change span {r | r ∈ rs ++ [f i]} = _
    congr 1
    ext r
    change r ∈ rs ++ [f i] ↔ r ∈ Set.range f
    rw [List.mem_append, List.mem_singleton, List.mem_ofFn', Set.range_comp, Fin.range_succAbove]
    constructor
    · rintro (⟨j, _, rfl⟩ | rfl)
      · exact ⟨j, rfl⟩
      · exact ⟨i, rfl⟩
    · rintro ⟨j, rfl⟩
      by_cases h : j = i
      · exact Or.inr (congrArg f h)
      · exact Or.inl ⟨j, h, rfl⟩
  have hmem (r : R) (hr : r ∈ rs ++ [f i]) : r ∈ maximalIdeal R := by
    have hfull : r ∈ (ofList (rs ++ [f i])).radical := Ideal.le_radical (subset_span hr)
    rwa [hall, hrad] at hfull
  have hparam := parameters_weaklyRegular (rs ++ [f i]) M hmem
    (by rw [hall, ← hrad]; exact Ideal.radical_mono le_sup_left)
    (by simpa only [rs, List.length_append, List.length_ofFn, List.length_singleton] using hExt)
  rw [isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff] at hparam
  have he : (ofList rs • (⊤ : Submodule R R)) = K1_13_6_1_4_3_3_1.otherIdeal f i := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, hother]
  have hcancel :=
    ((Submodule.quotEquivOfEq _ _ he).isSMulRegular_congr (f i)).mp hparam.2
  exact mem_of_isSMulRegular_quotient_of_smul_mem hcancel hx
end K1_13_6_1_4_3_3_1_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_2_1
noncomputable section
open K1_13_5_4_2_4_1 K1_13_6_1_4_3_3 K1_13_6_1_4_3_3_2
open MvPolynomial RingTheory.Sequence
open scoped Pointwise nonZeroDivisors
def inVariable {R σ : Type} [CommRing R] (i : σ) (p : Polynomial R) :
    MvPolynomial σ R :=
  p.eval₂ C (MvPolynomial.X i)
theorem map_inVariable {R S σ : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (i : σ) (p : Polynomial R) :
    MvPolynomial.map f (inVariable i p) = inVariable i (p.map f) := by
  rw [inVariable, Polynomial.hom_eval₂, map_X, inVariable, Polynomial.eval₂_map, map_comp_C]
theorem regular_cons_of_quotient {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (x : R)
    (hk : RingHom.ker f = Ideal.span {x}) (hx : IsSMulRegular R x)
    (rs : List R) (hrs : IsWeaklyRegular S (rs.map f)) :
    IsWeaklyRegular R (x :: rs) := by
  let e₀ : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} :=
    Submodule.quotEquivOfEq _ _ (by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map]
      exact Ideal.map_id _)
  let e₁ : R ⧸ Ideal.span {x} ≃+* S :=
    (Ideal.quotEquivOfEq hk.symm).trans (f.quotientKerEquivOfSurjective hf)
  let e := e₀.toAddEquiv.trans e₁.toAddEquiv
  have he (z : R) : e (Submodule.Quotient.mk z) = f z := by
    change f.quotientKerEquivOfSurjective hf (Ideal.Quotient.mk _ z) = f z
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hf z
  apply IsWeaklyRegular.cons hx
  refine (e.isWeaklyRegular_congr (List.forall₂_map_right_iff.mpr
    (List.forall₂_same.mpr ?_))).mpr hrs
  intro y _ z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
  change e (y • Submodule.Quotient.mk z) = f y * e (Submodule.Quotient.mk z)
  rw [← Submodule.Quotient.mk_smul, he, he]
  exact map_mul f y z
theorem regular_ringEquiv {R S : Type} [CommRing R] [CommRing S]
    (e : R ≃+* S) (rs : List R) :
    IsWeaklyRegular R rs ↔ IsWeaklyRegular S (rs.map e) := by
  apply e.toAddEquiv.isWeaklyRegular_congr
  apply List.forall₂_map_right_iff.mpr
  exact List.forall₂_same.mpr fun y _ z => map_mul e y z
theorem regular_C_monic {R σ : Type} [CommRing R] (p : Polynomial R)
    (hp : p.Monic) : IsSMulRegular (MvPolynomial σ (Polynomial R))
      (C p : MvPolynomial σ (Polynomial R)) := by
  intro f g hfg
  have h : C p * (f - g) = 0 := by
    rw [mul_sub, sub_eq_zero]
    exact hfg
  have hdiff : f - g = 0 := by
    apply MvPolynomial.ext
    intro a
    change (f - g).coeff a = 0
    apply mem_nonZeroDivisors_iff_left.mp hp.mem_nonZeroDivisors
    simpa only [coeff_C_mul, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
      congrArg (fun v : MvPolynomial σ (Polynomial R) => v.coeff a) h
  exact sub_eq_zero.mp hdiff
theorem regular_separate (n : ℕ) : ∀ (R : Type) [CommRing R]
    (p : Fin n → Polynomial R), (∀ i, (p i).Monic) →
    IsWeaklyRegular (MvPolynomial (Fin n) R) (List.ofFn fun i => inVariable i (p i)) := by
  induction n with
  | zero =>
    intro R _ p hp
    simp
  | succ n ih =>
    intro R _ p hp
    let e : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin n) (Polynomial R) :=
      (renameEquiv R (_root_.finSuccEquiv n)).trans (optionEquivRight R (Fin n))
    have heC : e.toRingHom.comp C = (C : Polynomial R →+* _).comp Polynomial.C := by
      apply RingHom.ext
      intro a
      change optionEquivRight R (Fin n) (rename (_root_.finSuccEquiv n) (C a)) =
        C (Polynomial.C a)
      rw [rename_C, optionEquivRight_C]
    have heX (i : Fin (n + 1)) :
        e (MvPolynomial.X i) = (_root_.finSuccEquiv n i).elim (C Polynomial.X) MvPolynomial.X := by
      change optionEquivRight R (Fin n) (rename (_root_.finSuccEquiv n) (MvPolynomial.X i)) = _
      rw [rename_X]
      cases _root_.finSuccEquiv n i with
      | none => exact optionEquivRight_X_none R (Fin n)
      | some j => exact optionEquivRight_X_some R (Fin n) j
    have hevar (i : Fin (n + 1)) :
        e (inVariable i (p i)) =
          (p i).eval₂ ((C : Polynomial R →+* _).comp Polynomial.C) (e (MvPolynomial.X i)) := by
      change e.toRingHom ((p i).eval₂ C (MvPolynomial.X i)) = _
      rw [Polynomial.hom_eval₂, heC]
      rfl
    have hhead : e (inVariable 0 (p 0)) = C (p 0) := by
      rw [hevar, heX, finSuccEquiv_zero, Option.elim_none, ← Polynomial.hom_eval₂,
        Polynomial.eval₂_C_X]
    let B := Polynomial R ⧸ Ideal.span {p 0}
    let q : Polynomial R →+* B := Ideal.Quotient.mk (Ideal.span {p 0})
    let f : MvPolynomial (Fin n) (Polynomial R) →+* MvPolynomial (Fin n) B :=
      MvPolynomial.map q
    let tail := List.ofFn fun i : Fin n => e (inVariable i.succ (p i.succ))
    have ht : tail.map f = List.ofFn
        (fun i : Fin n => inVariable i ((p i.succ).map (q.comp Polynomial.C))) := by
      rw [List.map_ofFn]
      congr 1
      funext i
      change f (e (inVariable i.succ (p i.succ))) = _
      rw [hevar, heX, finSuccEquiv_succ]
      simp only [f, Option.elim_some, Polynomial.hom_eval₂, map_X, inVariable,
        Polynomial.eval₂_map, ← RingHom.comp_assoc, map_comp_C]
    let x : MvPolynomial (Fin n) (Polynomial R) := C (p 0)
    have hkq : RingHom.ker q = Ideal.span {p 0} := Ideal.mk_ker
    have hk : RingHom.ker f = Ideal.span {x} := by
      change RingHom.ker (MvPolynomial.map (σ := Fin n) q) = _
      rw [MvPolynomial.ker_map, hkq, Ideal.map_span, Set.image_singleton]
    have hf : Function.Surjective f :=
      MvPolynomial.map_surjective (σ := Fin n) q Ideal.Quotient.mk_surjective
    have htail : IsWeaklyRegular (MvPolynomial (Fin n) B) (tail.map f) := by
      rw [ht]
      exact ih B _ fun i => (hp i.succ).map _
    have hx : IsSMulRegular (MvPolynomial (Fin n) (Polynomial R)) x :=
      regular_C_monic (σ := Fin n) (p 0) (hp 0)
    have hreg : IsWeaklyRegular (MvPolynomial (Fin n) (Polynomial R)) (x :: tail) :=
      @regular_cons_of_quotient (MvPolynomial (Fin n) (Polynomial R)) (MvPolynomial (Fin n) B)
        inferInstance inferInstance f hf x hk hx tail htail
    apply (regular_ringEquiv e.toRingEquiv _).mpr
    rw [List.ofFn_succ, List.map_cons, List.map_ofFn]
    change IsWeaklyRegular _ (e (inVariable 0 (p 0)) :: tail)
    rw [hhead]
    exact hreg
private theorem ker_reduce (L : Type) [Field L] :
    RingHom.ker (reduce (L := L)) = Ideal.span {C Polynomial.X} := by
  simp only [reduce, MvPolynomial.ker_map, Polynomial.ker_evalRingHom, map_zero, sub_zero,
    Ideal.map_span, Set.image_singleton]
private theorem reduce_surjective (L : Type) [Field L] :
    Function.Surjective (reduce (L := L)) :=
  MvPolynomial.map_surjective _ fun a => ⟨Polynomial.C a, Polynomial.eval_C⟩
theorem comap_cutIdeal {L : Type} [Field L] (g : Fin 4 → Total L) :
    (CutIdeal (fun i => reduce (g i))).comap reduce = specialIdeal g := by
  have hmap : (equationsIdeal g).map reduce = CutIdeal (fun i => reduce (g i)) := by
    simp only [equationsIdeal, Ideal.map_span, ← Set.range_comp']
  rw [← hmap, Ideal.comap_map_of_surjective _ (reduce_surjective L),
    ← RingHom.ker_eq_comap_bot, ker_reduce, specialIdeal]
theorem fibre_monics {L : Type} [Field L] (g : Fin 4 → Total L)
    [Module.Finite L (CutAlgebra (fun i => reduce (g i)))] :
    ∃ p : Fin 4 → Polynomial L, (∀ i, (p i).Monic) ∧
      (∀ i, inVariable i (p i) ∈ CutIdeal (fun j => reduce (g j))) := by
  let J := CutIdeal (fun i => reduce (g i))
  let q := Ideal.Quotient.mk J
  have h (i : Fin 4) : IsIntegral L (q (MvPolynomial.X i)) :=
    IsIntegral.of_finite L (q (MvPolynomial.X i))
  choose p hp hroot using h
  refine ⟨p, hp, fun i => Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  change q ((p i).eval₂ C (MvPolynomial.X i)) = 0
  rw [Polynomial.hom_eval₂]
  exact hroot i
theorem proof : K1_13_6_1_4_3_3_2.c1 := by
  intro L _ g hfinite m _ _
  let := hfinite
  obtain ⟨p, hp, hmem⟩ := fibre_monics g
  let rs : List (Total L) := List.ofFn fun i => inVariable i ((p i).map Polynomial.C)
  let t : Total L := C Polynomial.X
  have hred (i : Fin 4) :
      reduce (inVariable i ((p i).map Polynomial.C) : Total L) = inVariable i (p i) := by
    have hcomp : (Polynomial.evalRingHom 0).comp (Polynomial.C (R := L)) = RingHom.id L := by
      ext a
      exact Polynomial.eval_C
    simp only [reduce, map_inVariable, Polynomial.map_map, hcomp, Polynomial.map_id]
  have hrs : rs.map reduce = List.ofFn (fun i => inVariable i (p i)) := by
    simp only [rs, List.map_ofFn]
    exact congrArg List.ofFn (funext hred)
  have hregular : IsWeaklyRegular (Total L) (t :: rs) := by
    refine regular_cons_of_quotient reduce (reduce_surjective L) t (ker_reduce L)
      (regular_C_monic _ Polynomial.monic_X) rs ?_
    rw [hrs]
    exact regular_separate 4 L p hp
  have hspecial : ∀ r ∈ t :: rs, r ∈ specialIdeal g := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (le_sup_right : Ideal.span {t} ≤ specialIdeal g)
        (Ideal.subset_span (Set.mem_singleton t))
    · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hr
      rw [← hi, ← comap_cutIdeal g, Ideal.mem_comap, hred]
      exact hmem i
  let R := Localization.AtPrime m
  let loc := algebraMap (Total L) R
  refine ⟨(t :: rs).map loc, by simp [rs], ?_, hregular.of_isLocalization R m.primeCompl⟩
  intro r hr
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
  exact Ideal.mem_map_of_mem loc (hspecial a ha)
end
end K1_13_6_1_4_3_3_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_2_2
open Ideal IsLocalRing RingTheory.Sequence CategoryTheory Abelian
open scoped Pointwise
universe u v
section Local
variable {k : Type v} [Field k] [Infinite k]
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra k R]
include k in
omit [IsLocalRing R] in
private theorem regular_add_mem {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : R) (J : Ideal R)
    (h : ∀ P ∈ associatedPrimes R M, a ∈ P → ¬ J ≤ P) :
    ∃ b ∈ J, IsSMulRegular M (a + b) := by
  classical
  let A := {P ∈ associatedPrimes R M | a ∈ P}
  have hA : A.Finite := (associatedPrimes.finite R M).subset fun _ hP => hP.1
  have hav : ¬ ((J : Set R) ⊆ ⋃ P ∈ A, (P : Set R)) := by
    intro hall
    obtain ⟨P, hP, hJP⟩ :=
      (J.subset_union_prime_finite hA (f := id) ⊥ ⊥
        (fun P hP _ _ => (show IsAssociatedPrime P M from hP.1).isPrime)).mp hall
    exact h P hP.1 hP.2 hJP
  obtain ⟨b, hb, hbA⟩ := Set.not_subset.mp hav
  have hb' (P : Ideal R) (hP : P ∈ associatedPrimes R M) (haP : a ∈ P) :
      b ∉ P := fun hbP => hbA (Set.mem_iUnion₂.mpr ⟨P, ⟨hP, haP⟩, hbP⟩)
  let bad (P : Ideal R) := {t : k | a + algebraMap k R t * b ∈ P}
  have hbad (P : Ideal R) (hP : P ∈ associatedPrimes R M) : (bad P).Finite := by
    apply Set.Subsingleton.finite
    intro s hs t ht
    by_contra hst
    have hp : P.IsPrime := (show IsAssociatedPrime P M from hP).isPrime
    have hd : algebraMap k R (s - t) * b ∈ P := by
      rw [map_sub, sub_mul]
      simpa only [add_sub_add_left_eq_sub] using P.sub_mem hs ht
    have hbP : b ∈ P := (hp.mem_or_mem hd).resolve_left fun hz =>
      hp.ne_top (P.eq_top_of_isUnit_mem hz ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hst)).map
        (algebraMap k R)))
    have haP : a ∈ P := by
      simpa only [add_sub_cancel_right] using P.sub_mem hs (P.mul_mem_left (algebraMap k R s) hbP)
    exact hb' P hP haP hbP
  have hfinite := (associatedPrimes.finite R M).biUnion hbad
  obtain ⟨t, ht⟩ := hfinite.exists_notMem
  refine ⟨algebraMap k R t * b, J.mul_mem_left _ hb, ?_⟩
  by_contra hreg
  have hh : a + algebraMap k R t * b ∈ ⋃ P ∈ associatedPrimes R M, (P : Set R) := by
    rwa [biUnion_associatedPrimes_eq_compl_regular R M]
  obtain ⟨P, hP, hhP⟩ := Set.mem_iUnion₂.mp hh
  exact ht (Set.mem_iUnion₂.mpr ⟨P, hP, hhP⟩)
abbrev TestModule (I : Ideal R) := ModuleCat.of R (R ⧸ I)
omit [IsNoetherianRing R] [IsLocalRing R] in
private theorem ext_after_regular (N M : ModuleCat.{u} R) {a : R}
    (ha : IsSMulRegular M a) {n : ℕ} (h : ∀ i < n + 1, Subsingleton (Ext N M i)) :
    ∀ i < n, Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop a M)) i) := by
  intro i hi
  have h₀ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h i (by omega))
  have h₁ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h (i + 1) (by omega))
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.covariant_sequence_exact₃' N ha.smulShortComplex_shortExact i (i + 1) rfl)
    (h₀.eq_zero_of_src _) (h₁.eq_zero_of_tgt _)
include k in
private theorem weaklyRegular_of_ext (I : Ideal R) (rs : List R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hm : ∀ a ∈ rs, a ∈ maximalIdeal R)
    (hI : I ≤ Ideal.ofList rs ⊔ Module.annihilator R M)
    (hext : ∀ i < rs.length, Subsingleton (Ext (TestModule I) M i)) :
    IsWeaklyRegular M rs := by
  induction rs generalizing M with
  | nil => exact IsWeaklyRegular.nil R M
  | cons a rs ih =>
    have hHom : Subsingleton (TestModule I →ₗ[R] M) :=
      (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton_congr.mp
        (hext 0 (by simp))
    obtain ⟨r, hr, hreg⟩ := IsSMulRegular.subsingleton_linearMap_iff.mp hHom
    have hAnn : Module.annihilator R (TestModule I) = I := Ideal.annihilator_quotient
    have hrI : r ∈ I := hAnn ▸ hr
    let J := Ideal.ofList rs
    have hJm : J ≤ maximalIdeal R := Ideal.span_le.mpr
      (fun z hz => hm z (List.mem_cons_of_mem _ hz))
    obtain ⟨b, hb, hab⟩ := regular_add_mem (k := k) (M := M) a J (by
      intro P hP haP hJP
      have hassoc : IsAssociatedPrime P M := hP
      have hle : Ideal.ofList (a :: rs) ⊔ Module.annihilator R M ≤ P := by
        rw [Ideal.ofList_cons]
        exact sup_le (sup_le ((Ideal.span_singleton_le_iff_mem P).mpr haP) hJP)
          (by simpa only [Submodule.annihilator_top] using hassoc.annihilator_le)
      have hrP := hle (hI hrI)
      have hru : r ∈ ⋃ P ∈ associatedPrimes R M, (P : Set R) :=
        Set.mem_iUnion₂.mpr ⟨P, hP, hrP⟩
      rw [biUnion_associatedPrimes_eq_compl_regular R M] at hru
      exact hru hreg)
    let M' := ModuleCat.of R (QuotSMulTop (a + b) M)
    have habann : a + b ∈ Module.annihilator R M' := QuotSMulTop.mem_annihilator M (a + b)
    have hann : Module.annihilator R M ≤ Module.annihilator R M' :=
      (Submodule.mkQ _).annihilator_le_of_surjective (Submodule.mkQ_surjective _)
    have hle : Ideal.ofList (a :: rs) ⊔ Module.annihilator R M ≤
        J ⊔ Module.annihilator R M' := by
      rw [Ideal.ofList_cons]
      refine sup_le (sup_le ((Ideal.span_singleton_le_iff_mem _).mpr ?_) le_sup_left)
        (hann.trans le_sup_right)
      have hsum : a + b ∈ J ⊔ Module.annihilator R M' := Ideal.mem_sup_right habann
      have hb' : b ∈ J ⊔ Module.annihilator R M' := Ideal.mem_sup_left hb
      simpa only [add_sub_cancel_right] using (J ⊔ Module.annihilator R M').sub_mem hsum hb'
    have htail := ih M' (fun z hz => hm z (List.mem_cons_of_mem _ hz))
      (hI.trans hle) (ext_after_regular _ M hab hext)
    have hcons : IsWeaklyRegular M ((a + b) :: rs) := IsWeaklyRegular.cons hab htail
    have happ : IsWeaklyRegular M (rs ++ [a + b]) :=
      IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hcons
        (show List.Perm ([a + b] ++ rs) (rs ++ [a + b]) from List.perm_append_comm) (by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Ideal.add_mem _ (hm a List.mem_cons_self) (hJm hb)
        · exact hm z (List.mem_cons_of_mem _ hz))
    obtain ⟨hrs, hlast⟩ := (isWeaklyRegular_append_iff M rs [a + b]).mp happ
    let T : Submodule R M := J • ⊤
    have hlast' : IsSMulRegular (M ⧸ T) (a + b) := (isWeaklyRegular_singleton_iff _ _).mp hlast
    have ha : IsSMulRegular (M ⧸ T) a := by
      rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at hlast' ⊢
      intro x hx
      apply hlast'
      have hbT : b • x ∈ T := by
        apply (Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem J).mpr hb) :
          Ideal.span {b} • (⊤ : Submodule R M) ≤ T)
        rw [Submodule.ideal_span_singleton_smul]
        exact Submodule.smul_mem_pointwise_smul x b ⊤ trivial
      rw [add_smul]
      exact T.add_mem hx hbT
    have hnew : IsWeaklyRegular M (rs ++ [a]) :=
      (isWeaklyRegular_append_iff M rs [a]).mpr
        ⟨hrs, (isWeaklyRegular_singleton_iff _ _).mpr ha⟩
    have hp : List.Perm (a :: rs) (rs ++ [a]) :=
      show List.Perm ([a] ++ rs) (rs ++ [a]) from List.perm_append_comm
    exact IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hnew hp.symm
      (fun z hz => hm z (hp.mem_iff.mpr hz))
include k in
theorem weaklyRegular_of_generators (ref rs : List R) (hlen : ref.length = rs.length)
    (hI : Ideal.ofList rs ≤ maximalIdeal R)
    (hmem : ∀ a ∈ ref, a ∈ Ideal.ofList rs) (href : IsWeaklyRegular R ref) :
    IsWeaklyRegular R rs := by
  let I := Ideal.ofList rs
  let N := TestModule I
  have hAnn : Module.annihilator R N = I := Ideal.annihilator_quotient
  have hSupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus I := by
    rw [Module.support_eq_zeroLocus, hAnn]
  have hlt : I • (⊤ : Submodule R R) < ⊤ := by
    change I • (⊤ : Ideal R) < ⊤
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact lt_of_le_of_lt hI (IsLocalRing.maximalIdeal.isMaximal R).ne_top.lt_top
  have hreg : IsRegular R ref :=
    IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R (fun a ha => hI (hmem a ha)) href
  have hext := ModuleCat.subsingleton_ext_of_exists_isRegular I N hSupp
    (ModuleCat.of R R) hlt ref hmem hreg
  exact weaklyRegular_of_ext (k := k) I rs (ModuleCat.of R R)
    (fun a ha => hI (Ideal.subset_span ha)) le_sup_left (fun i hi => hext i (hlen ▸ hi))
end Local
theorem proof : K1_13_6_1_4_3_3_2.c2 := by
  intro L R _ _ _ _ _ _ u t
  dsimp only
  intro hI ⟨ref, hlen, hmem, href⟩
  let front := List.ofFn u
  have hfront : Ideal.ofList front = Ideal.span (Set.range u) :=
    congrArg Ideal.span (Set.ext (List.mem_ofFn' u))
  have hfull : Ideal.ofList (front ++ [t]) =
      Ideal.span (Set.range u) ⊔ Ideal.span {t} := by
    rw [Ideal.ofList_append, Ideal.ofList_singleton, hfront]
  have hparams := weaklyRegular_of_generators (k := L) ref (front ++ [t])
    (by simpa [front] using hlen) (hfull.symm ▸ hI) (hfull.symm ▸ hmem) href
  have hlast := ((isWeaklyRegular_append_iff R front [t]).mp hparams).2
  have hc := (isWeaklyRegular_singleton_iff _ _).mp hlast
  rw [Ideal.smul_eq_mul, Ideal.mul_top, hfront] at hc
  exact hc
end K1_13_6_1_4_3_3_2_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_1_1
open Ideal IsLocalRing RingTheory.Sequence
open scoped Pointwise
theorem monic_regular_mod_coefficients {R : Type*} [CommRing R]
    (I : Ideal R) {f : Polynomial R} (hf : f.Monic) :
    IsSMulRegular (Polynomial R ⧸ I.map Polynomial.C) f := by
  let φ := Polynomial.mapRingHom (Ideal.Quotient.mk I)
  have hker : RingHom.ker φ = I.map Polynomial.C := by
    change RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk I)) = _
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
  have hregular : _root_.IsRegular (φ f) := (hf.map (Ideal.Quotient.mk I)).isRegular
  refine (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr ?_
  intro g hg
  change f * g ∈ I.map Polynomial.C at hg
  rw [← hker, RingHom.mem_ker] at hg ⊢
  rw [map_mul] at hg
  exact hregular.left (hg.trans (mul_zero _).symm)
theorem append_monic {R : Type*} [CommRing R]
    {s : List R} (hs : IsWeaklyRegular R s) {f : Polynomial R} (hf : f.Monic) :
    IsWeaklyRegular (Polynomial R) (s.map Polynomial.C ++ [f]) := by
  apply (isWeaklyRegular_append_iff _ _ _).mpr
  refine ⟨?_, (isWeaklyRegular_singleton_iff _ _).mpr ?_⟩
  · simpa only [Polynomial.algebraMap_eq] using hs.of_flat (S := Polynomial R)
  · rw [Ideal.smul_eq_mul, Ideal.mul_top, ← Ideal.map_ofList]
    exact monic_regular_mod_coefficients (Ideal.ofList s) hf
theorem map_weakly_regular {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {s : List R} (hs : IsWeaklyRegular R s) :
    IsWeaklyRegular S (s.map e) := by
  have hc : List.Forall₂ (fun (r : R) (z : S) => ∀ x : R, e (r • x) = z • e x)
      s (s.map e) :=
    List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x => e.map_mul r x)
  exact (e.toAddEquiv.isWeaklyRegular_congr hc).mp hs
theorem exists_weakly_regular (k : Type) [Field k] (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsMaximal] :
    ∃ s : List (MvPolynomial (Fin n) k), s.length = n ∧
      (∀ x ∈ s, x ∈ p) ∧ IsWeaklyRegular (MvPolynomial (Fin n) k) s := by
  induction n with
  | zero => exact ⟨[], rfl, by simp, IsWeaklyRegular.nil _ _⟩
  | succ n ih =>
    let R := MvPolynomial (Fin n) k
    let e : MvPolynomial (Fin (n + 1)) k ≃+* Polynomial R :=
      (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let P := p.map e.toRingHom
    have : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let C : R →+* Polynomial R := Polynomial.C
    let q := P.comap C
    have : q.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    obtain ⟨s, hlen, hmem, hreg⟩ := ih q
    obtain ⟨f, hf, hroot⟩ := Polynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing P
      (Ideal.Quotient.mk P Polynomial.X)
    have hfP : f ∈ P := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← Polynomial.eval₂_C_X (p := f), Polynomial.hom_eval₂]
      exact hroot
    let t := s.map C ++ [f]
    have htreg : IsWeaklyRegular (Polynomial R) t := append_monic hreg hf
    have htmem (y : Polynomial R) (hy : y ∈ t) : y ∈ P := by
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        exact hmem x hx
      · rwa [List.mem_singleton.mp hy]
    have he : P.comap e.toRingHom = p := Ideal.comap_map_of_bijective _ e.bijective
    refine ⟨t.map e.symm, by simp [t, hlen], ?_, map_weakly_regular e.symm htreg⟩
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    rw [← he, Ideal.mem_comap]
    change e (e.symm y) ∈ P
    simpa only [e.apply_symm_apply] using htmem y hy
theorem proof : K1_13_6_1_4_3_3_1.c1 := by
  intro k _ p _
  let S := Localization.AtPrime p
  obtain ⟨s, hlen, hmem, hreg⟩ := exists_weakly_regular k 4 p
  refine ⟨s.map (algebraMap _ S), by simpa only [List.length_map] using hlen, ?_,
    hreg.isRegular_of_isLocalization_of_mem S p hmem⟩
  intro z hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S p x).mpr (hmem x hx)
end K1_13_6_1_4_3_3_1_1
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_3_2_2
noncomputable section
open K1_13 K1_13_6_1_4_3_3 K1_13_6_1_4_3_3_3_2 MvPolynomial
open scoped nonZeroDivisors
local instance integralLatticeFintype (p : Shape) : Fintype (lattice p) :=
  (lattice_finite p).fintype
private abbrev IntegralSlots (k : Type) [Field k] (P : Fin 4 → Shape) := MvPolynomial (Slot P) (CoefficientRing k P)
private def integralEquation (k : Type) [Field k] (P : Fin 4 → Shape) (i : Fin 4) : IntegralSlots k P :=
  ∑ a : lattice (P i), C (MvPolynomial.X ⟨i, a⟩) * MvPolynomial.X ⟨some i, a⟩
private def integralChart (k : Type) [Field k] (P : Fin 4 → Shape) (b : Chart P) : IntegralSlots k P :=
  ∏ j : SlotIndex, MvPolynomial.X ⟨j, b j⟩
private def equationIdeal (k : Type) [Field k] (P : Fin 4 → Shape) (r : ℕ) : Ideal (IntegralSlots k P) :=
  Ideal.span (integralEquation k P '' {i : Fin 4 | i.val < r})
private def integralIdeal (k : Type) [Field k] (P : Fin 4 → Shape) (r : ℕ) : Ideal (IntegralSlots k P) :=
  binomialIdeal P (CoefficientRing k P) ⊔ equationIdeal k P r
private abbrev swap (k : Type) [Field k] (P : Fin 4 → Shape) := commAlgEquiv k (Slot P) (CoeffSlot P)
private def toModel (k : Type) [Field k] (P : Fin 4 → Shape) : IntegralSlots k P →+* UniversalRing k P :=
  (MvPolynomial.map (Ideal.Quotient.mk (binomialIdeal P k))).comp (swap k P).toRingHom
private theorem toModel_surjective (k : Type) [Field k] (P : Fin 4 → Shape) : Function.Surjective (toModel k P) :=
  (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective).comp (swap k P).surjective
private theorem toModel_ker (k : Type) [Field k] (P : Fin 4 → Shape) :
    RingHom.ker (toModel k P) = binomialIdeal P (CoefficientRing k P) := by
  have hswap : (swap k P).toRingHom.comp (MvPolynomial.map (C (σ := CoeffSlot P))) = C := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [swap]
    · intro v
      simp [swap]
  have hker : RingHom.ker (swap k P).toRingHom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot (swap k P).toRingHom).mp (swap k P).injective
  rw [toModel, ← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker, ← hswap,
    ← Ideal.map_map, Ideal.comap_map_of_surjective (swap k P).toRingHom (swap k P).surjective,
    ← RingHom.ker_eq_comap_bot, hker,
    sup_bot_eq, map_binomialIdeal]
private theorem toModel_chart (k : Type) [Field k] (P : Fin 4 → Shape) (b : Chart P) :
    toModel k P (integralChart k P b) = C (modelChart k P b) := by
  simp [integralChart, toModel, modelChart, coordinate]
private theorem integralIdeal_eq (k : Type) [Field k] (P : Fin 4 → Shape) (r : ℕ) :
    integralIdeal k P r = (modelIdeal k P r).comap (toModel k P) := by
  have hmap : (equationIdeal k P r).map (toModel k P) = modelIdeal k P r := by
    rw [equationIdeal, modelIdeal, Ideal.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro i _
    simp [integralEquation, modelEquation, toModel, coordinate]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [← hmap, Ideal.comap_map_of_surjective _ (toModel_surjective k P),
    ← RingHom.ker_eq_comap_bot, toModel_ker, integralIdeal, sup_comm]
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev extendCoefficients (k : Type) [Field k] (P : Fin 4 → Shape) := algebraMap (IntegralSlots k P) (SlotRing k P)
private theorem extend_chart (k : Type) [Field k] (P : Fin 4 → Shape) (b : Chart P) :
    extendCoefficients k P (integralChart k P b) = chartProduct k P b := by
  change MvPolynomial.map (algebraMap (CoefficientRing k P) (CoefficientField k P))
    (integralChart k P b) = chartProduct k P b
  simp only [integralChart, chartProduct, map_prod, map_X]
private theorem extend_ideal (k : Type) [Field k] (P : Fin 4 → Shape) (r : ℕ) :
    (integralIdeal k P r).map (extendCoefficients k P) = cutIdeal k P r := by
  change (integralIdeal k P r).map
    (MvPolynomial.map (algebraMap (CoefficientRing k P) (CoefficientField k P))) = cutIdeal k P r
  rw [integralIdeal, Ideal.map_sup, map_binomialIdeal,
    ← relationIdeal_zero, cutIdeal, equationIdeal, Ideal.map_span, Set.image_image]
  congr 2
  apply Set.image_congr
  intro i _
  simp only [integralEquation, homogeneousEquation, map_sum, map_mul, map_C, map_X]
set_option maxHeartbeats 800000 in
theorem proof : K1_13_6_1_4_3_3_3_2.c2 := by
  classical
  intro k _ P r b f n hf
  let b₀ := zeroChart P
  let I := integralIdeal k P r
  let e := extendCoefficients k P
  let M := (CoefficientRing k P)⁰.map (C (σ := Slot P))
  have : IsLocalization M (SlotRing k P) :=
    MvPolynomial.isLocalization (CoefficientRing k P)⁰ (CoefficientField k P)
  obtain ⟨⟨p, s⟩, hs⟩ := IsLocalization.surj M f
  change f * e s = e p at hs
  have hc : e (integralChart k P b₀) = constantChart k P := extend_chart k P b₀
  have hI : I.map e = cutIdeal k P r := extend_ideal k P r
  have hp : e (integralChart k P b₀ ^ n * p) ∈ I.map e := by
    rw [hI, map_mul, map_pow, hc, ← hs, ← mul_assoc]
    exact (cutIdeal k P r).mul_mem_right _ hf
  obtain ⟨d, hd, hpre⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M _ I _).mp hp
  have hpre' : integralChart k P b₀ ^ n * (d * p) ∈ I := by
    rwa [mul_left_comm (integralChart k P b₀ ^ n) d p]
  have hmod : C (modelChart k P b₀) ^ n * toModel k P (d * p) ∈ modelIdeal k P r := by
    rw [show I = (modelIdeal k P r).comap (toModel k P) from integralIdeal_eq k P r] at hpre'
    change toModel k P (integralChart k P b₀ ^ n * (d * p)) ∈ modelIdeal k P r at hpre'
    simpa only [map_mul, map_pow, toModel_chart] using hpre'
  obtain ⟨m, hm⟩ := model_saturate r b (modelChart_ne_zero b₀) (toModel k P (d * p)) n hmod
  have hm' : integralChart k P b ^ m * (d * p) ∈ I := by
    change _ ∈ integralIdeal k P r
    rw [integralIdeal_eq]
    change toModel k P (integralChart k P b ^ m * (d * p)) ∈ modelIdeal k P r
    simpa only [map_mul, map_pow, toModel_chart] using hm
  have hresult := Ideal.mem_map_of_mem e hm'
  rw [hI, map_mul, map_pow, extend_chart, map_mul, ← hs] at hresult
  have hds : IsUnit (e d) := IsLocalization.map_units (SlotRing k P) ⟨d, hd⟩
  have hss : IsUnit (e s) := IsLocalization.map_units (SlotRing k P) s
  refine ⟨m, (Ideal.unit_mul_mem_iff_mem _ (hds.mul hss)).mp ?_⟩
  rw [mul_assoc (e d) (e s), mul_left_comm (e s) (chartProduct k P b ^ m),
    mul_left_comm (e d) (chartProduct k P b ^ m), mul_comm (e s) f]
  exact hresult
end
end K1_13_6_1_4_3_3_3_2_2
end
section
namespace K1_13_6_1_4_3_2
open K1_13 K1_13_6 K1_13_6_1_4 K1_13_6_1_4_3
open scoped BigOperators
theorem proof : K1_13_6_1_4_3.c2 := by
  intro J a h _ _ hfinite surfaces v hsurfaces
  let F := PairSectionField a h
  let S := UniversalSlice a h
  have hflat : Module.Flat GeoJets S := universalSlice_flat a h
  have hmin (P : Ideal GeoJets) (hP : P ∈ surfaces) : J.IsMinimalPrime P := by
    obtain ⟨hm, _⟩ := hsurfaces P hP
    exact hm
  have hsum := weighted_length_le S F J surfaces hmin
  have hlength (P : Ideal GeoJets) (hP : J ≤ P) :
      Module.length F (S ⧸ P.map (algebraMap GeoJets S)) =
        (surfaceDegree P a h : ℕ∞) := by
    let IJ := J.map (extendCoeffs a h) ⊔ sectionIdeal a h
    let IP := P.map (extendCoeffs a h) ⊔ sectionIdeal a h
    have hIP : IJ ≤ IP := sup_le_sup (Ideal.map_mono hP) le_rfl
    let f : SliceAlgebra J a h →ₐ[F] SliceAlgebra P a h :=
      ⟨Ideal.Quotient.factor hIP, fun _ => rfl⟩
    have hfinP : Module.Finite F (SliceAlgebra P a h) :=
      Module.Finite.of_surjective f.toLinearMap (Ideal.Quotient.factor_surjective hIP)
    rw [(sliceEquiv P a h).toLinearEquiv.length_eq, Module.length_eq_finrank]
    rfl
  have hw (P : Ideal GeoJets) (hP : P ∈ surfaces) : localWeight J P = (v P : ℕ∞) := by
    obtain ⟨hm, hv⟩ := hsurfaces P hP
    let hp := hm.isPrime
    rw [localWeight_of_prime]
    exact hv
  apply ENat.natCast_le_natCast.mp
  push_cast
  calc
    _ = ∑ P ∈ surfaces, localWeight J P * Module.length F (S ⧸ P.map (algebraMap GeoJets S)) := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [hw P hP, hlength P (hmin P hP).le]
    _ ≤ _ := by
      change _ ≤ (surfaceDegree J a h : ℕ∞)
      rw [← hlength J le_rfl]
      exact hsum
end K1_13_6_1_4_3_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_13_5_5_1
noncomputable section
open K1_13 K1_13_5 K1_13_5_5
open scoped Polynomial
def chartIdeal (f : Row 3) : Ideal FreshJetRing := Ideal.span {freshRow f}
abbrev ChartRing (f : Row 3) := FreshJetRing ⧸ chartIdeal f
abbrev ChartField (f : Row 3) := FractionRing (ChartRing f)
def fractionQuotientMap {k σ : Type*} [Field k]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] :
    MvPolynomial σ k →+* FractionRing (MvPolynomial σ k ⧸ I) :=
  (algebraMap (MvPolynomial σ k ⧸ I) (FractionRing (MvPolynomial σ k ⧸ I))).comp
    (Ideal.Quotient.mk I)
def onChart (f : Row 3) [(chartIdeal f).IsPrime] : FreshJetRing →+* ChartField f :=
  fractionQuotientMap (chartIdeal f)
theorem fractionQuotientMap_eq_zero {k σ : Type*} [Field k]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (v : MvPolynomial σ k) :
    fractionQuotientMap I v = 0 ↔ v ∈ I := by
  change (algebraMap (MvPolynomial σ k ⧸ I) (FractionRing (MvPolynomial σ k ⧸ I)))
    (Ideal.Quotient.mk I v) = 0 ↔ _
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact IsFractionRing.injective (MvPolynomial σ k ⧸ I)
      (FractionRing (MvPolynomial σ k ⧸ I)) (h.trans (map_zero _).symm)
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]
theorem onChart_eq_zero (f : Row 3) [(chartIdeal f).IsPrime] (v : FreshJetRing) :
    onChart f v = 0 ↔ v ∈ chartIdeal f :=
  fractionQuotientMap_eq_zero (chartIdeal f) v
def freshConstants : Geom →+* FreshField :=
  (algebraMap Geom[X] FreshField).comp Polynomial.C
def chartConstants (f : Row 3) [(chartIdeal f).IsPrime] : Geom →+* ChartField f :=
  ((onChart f).comp MvPolynomial.C).comp freshConstants
def chartCenter (f : Row 3) [(chartIdeal f).IsPrime] : ChartField f :=
  onChart f (MvPolynomial.C freshCenter)
def chartJets (f : Row 3) [(chartIdeal f).IsPrime] (i : Fin 3) : ChartField f :=
  onChart f (MvPolynomial.X i)
def trajectory {F : Type*} [CommRing F] (k : Geom →+* F) (U : F[X]) :
    Row 3 →+* F[X] :=
  MvPolynomial.eval₂Hom (Polynomial.mapRingHom k) (fun i => Polynomial.hasseDeriv i.val U)
def jetAt {F : Type*} [CommRing F] (x : F) (U : F[X]) (i : Fin 3) : F :=
  (Polynomial.hasseDeriv i.val U).eval x
def rowAt {F : Type*} [CommRing F] (k : Geom →+* F) (x : F) (y : Fin 3 → F) :
    Row 3 →+* F :=
  MvPolynomial.eval₂Hom ((Polynomial.evalRingHom x).comp (Polynomial.mapRingHom k)) y
end
end K1_13_5_5_1
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_13_5_5_1
noncomputable section
open K1_13 K1_13_5 K1_13_5_5
open scoped Polynomial nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
abbrev rowMap : Row 3 →+* FreshJetRing :=
  MvPolynomial.map (algebraMap Geom[X] FreshField)
abbrev rowDenominators : Submonoid (Row 3) :=
  (Geom[X]⁰).map MvPolynomial.C
def originalIdeal (f : Row 3) : Ideal (Row 3) := Ideal.span {f}
theorem chartIdeal_map (f : Row 3) :
    (originalIdeal f).map rowMap = chartIdeal f := by
  simp [originalIdeal, chartIdeal, Ideal.map_span, freshRow, rowMap]
theorem rowMap_injective : Function.Injective rowMap :=
  MvPolynomial.map_injective (algebraMap Geom[X] FreshField)
    (IsFractionRing.injective Geom[X] FreshField)
theorem original_disjoint (f : Row 3) (hf : 0 < f.degreeOf 2) :
    Disjoint (rowDenominators : Set (Row 3)) (originalIdeal f : Set (Row 3)) := by
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨a, ha, rfl⟩ hmem
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hmem
  have ha' : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp ha
  have hC : (MvPolynomial.C a : Row 3) ≠ 0 :=
    fun h => ha' (MvPolynomial.C_injective (Fin 3) Geom[X]
      (h.trans (map_zero MvPolynomial.C).symm))
  have hn : f ≠ 0 := by
    intro he
    simp [he] at hf
  have hgn : g ≠ 0 := by
    intro he
    exact hC (by simpa [he] using hg)
  have hd := congrArg (MvPolynomial.degreeOf (2 : Fin 3)) hg
  rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_mul_eq hn hgn] at hd
  omega
theorem original_prime (f : Row 3) (hf : Irreducible f) :
    (originalIdeal f).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime hf.prime
theorem chart_prime (f : Row 3) (hf : Irreducible f) (hd : 0 < f.degreeOf 2) :
    (chartIdeal f).IsPrime := by
  rw [← chartIdeal_map]
  exact IsLocalization.isPrime_of_isPrime_disjoint rowDenominators FreshJetRing
    _ (original_prime f hf) (original_disjoint f hd)
theorem chart_contract (f : Row 3) (hf : Irreducible f) (hd : 0 < f.degreeOf 2) :
    (chartIdeal f).comap rowMap = originalIdeal f := by
  rw [← chartIdeal_map]
  exact IsLocalization.under_map_of_isPrime_disjoint rowDenominators FreshJetRing
    (original_prime f hf) (original_disjoint f hd)
theorem rowAt_chart (f : Row 3) [(chartIdeal f).IsPrime] :
    rowAt (chartConstants f) (chartCenter f) (chartJets f) = (onChart f).comp rowMap := by
  apply MvPolynomial.ringHom_ext
  · have h : (Polynomial.evalRingHom (chartCenter f)).comp
        (Polynomial.mapRingHom (chartConstants f)) =
          ((onChart f).comp MvPolynomial.C).comp (algebraMap Geom[X] FreshField) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp [chartConstants, freshConstants]
      · simp [chartCenter, freshCenter]
    intro a
    simpa [rowAt, rowMap] using RingHom.congr_fun h a
  · intro i
    simp [rowAt, rowMap, chartJets]
theorem eval_trajectory {F : Type*} [CommRing F] (k : Geom →+* F) (U : F[X])
    (x : F) (b : Row 3) :
    (trajectory k U b).eval x = rowAt k x (jetAt x U) b := by
  simp only [trajectory, rowAt, MvPolynomial.coe_eval₂Hom, MvPolynomial.polynomial_eval_eval₂]
  rfl
theorem map_trajectory {F L : Type*} [CommRing F] [CommRing L]
    (k : Geom →+* F) (a : F →+* L) (U : F[X]) (b : Row 3) :
    (trajectory k U b).map a = trajectory (a.comp k) (U.map a) b := by
  have h : (Polynomial.mapRingHom a).comp (trajectory k U) =
      trajectory (a.comp k) (U.map a) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [trajectory]
    · intro i
      simp [trajectory, Polynomial.hasseDeriv_map]
  exact RingHom.congr_fun h b
end
end K1_13_5_5_1
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_13_5_5_1
noncomputable section
open K1_13 K1_13_5_5
open scoped Polynomial nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
section PolynomialCoefficients
variable {k F σ : Type*} [CommRing k] [CommRing F]
def toPolynomial : MvPolynomial σ k[X] →+* (MvPolynomial σ k)[X] :=
  MvPolynomial.eval₂Hom (Polynomial.mapRingHom MvPolynomial.C) (Polynomial.C ∘ MvPolynomial.X)
def fromPolynomial : (MvPolynomial σ k)[X] →+* MvPolynomial σ k[X] :=
  Polynomial.eval₂RingHom (MvPolynomial.map Polynomial.C) (MvPolynomial.C Polynomial.X)
theorem fromPolynomial_toPolynomial (p : MvPolynomial σ k[X]) :
    fromPolynomial (toPolynomial p) = p := by
  have h : (fromPolynomial (k := k) (σ := σ)).comp toPolynomial = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · have hc : (fromPolynomial (k := k) (σ := σ)).comp
          (Polynomial.mapRingHom MvPolynomial.C) = MvPolynomial.C := by
        apply Polynomial.ringHom_ext <;> simp [fromPolynomial]
      intro c
      simpa [toPolynomial] using RingHom.congr_fun hc c
    · intro i
      simp [toPolynomial, fromPolynomial]
  exact RingHom.congr_fun h p
theorem ker_polynomialEval (kF : k →+* F) (point : σ → F) :
    RingHom.ker (MvPolynomial.eval₂Hom (Polynomial.mapRingHom kF) (Polynomial.C ∘ point)) =
      (RingHom.ker (MvPolynomial.eval₂Hom kF point)).map (MvPolynomial.map Polynomial.C) := by
  let e := MvPolynomial.eval₂Hom kF point
  let e' := MvPolynomial.eval₂Hom (Polynomial.mapRingHom kF) (Polynomial.C ∘ point)
  have h : (Polynomial.mapRingHom e).comp toPolynomial = e' := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [toPolynomial, e', e]
    · intro i
      simp [toPolynomial, e', e]
  have hc : e'.comp (MvPolynomial.map Polynomial.C) = Polynomial.C.comp e := by
    apply MvPolynomial.ringHom_ext <;> simp [e', e]
  change RingHom.ker e' = (RingHom.ker e).map _
  apply le_antisymm
  · intro p hp
    have hp' : toPolynomial p ∈ (RingHom.ker e).map Polynomial.C := by
      rw [← Polynomial.ker_mapRingHom]
      exact (RingHom.congr_fun h p).trans hp
    have hm := Ideal.mem_map_of_mem fromPolynomial hp'
    have hfrom : (fromPolynomial (k := k) (σ := σ)).comp Polynomial.C =
        MvPolynomial.map Polynomial.C := Polynomial.eval₂RingHom_comp_C _ _
    rwa [Ideal.map_map, hfrom, fromPolynomial_toPolynomial] at hm
  · rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker, hc]
    intro p hp
    change Polynomial.C (e p) = 0
    rw [show e p = 0 from hp, map_zero]
end PolynomialCoefficients
section FreshField
variable {F : Type*} [Field F]
abbrev NewField (F : Type*) [Field F] := FractionRing F[X]
def newConstants : F →+* NewField F :=
  (algebraMap F[X] (NewField F)).comp Polynomial.C
def newCenter : NewField F := algebraMap F[X] (NewField F) Polynomial.X
def newGround (k : Geom →+* F) : FreshField →+* NewField F :=
  IsFractionRing.lift (g := (algebraMap F[X] (NewField F)).comp (Polynomial.mapRingHom k))
    ((IsFractionRing.injective F[X] (NewField F)).comp (Polynomial.map_injective k k.injective))
@[simp] theorem newGround_polynomial (k : Geom →+* F) (b : Geom[X]) :
    newGround k (algebraMap Geom[X] FreshField b) =
      algebraMap F[X] (NewField F) (b.map k) := by
  simp [newGround]
@[simp] theorem newGround_constant (k : Geom →+* F) (a : Geom) :
    newGround k (freshConstants a) = newConstants (k a) := by
  simp [freshConstants, newConstants]
@[simp] theorem newGround_center (k : Geom →+* F) :
    newGround k freshCenter = (newCenter : NewField F) := by
  simp [freshCenter, newCenter]
def coeffEval (k : Geom →+* F) (point : CoeffIndex → F) : CoeffRing →+* F :=
  MvPolynomial.eval₂Hom k point
def freshCoeffEval (k : Geom →+* F) (point : CoeffIndex → F) :
    FreshCoeffRing →+* NewField F :=
  MvPolynomial.eval₂Hom (newGround k) (newConstants ∘ point)
theorem freshIdeal_eq_ker (k : Geom →+* F) (point : CoeffIndex → F) :
    freshIdeal (RingHom.ker (coeffEval k point)) = RingHom.ker (freshCoeffEval k point) := by
  let M := (Geom[X]⁰).map (MvPolynomial.C (σ := CoeffIndex))
  let e := MvPolynomial.eval₂Hom (Polynomial.mapRingHom k) (Polynomial.C ∘ point)
  let j : MvPolynomial CoeffIndex Geom[X] →+* FreshCoeffRing :=
    MvPolynomial.map (algebraMap Geom[X] FreshField)
  let inj := algebraMap F[X] (NewField F)
  let g := freshCoeffEval k point
  have h : g.comp j = inj.comp e := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp [j, g, freshCoeffEval, e, inj]
    · intro i
      simp [j, g, freshCoeffEval, e, inj, newConstants]
  have hc : (RingHom.ker g).comap j = RingHom.ker e := by
    rw [RingHom.comap_ker, h]
    ext b
    simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
    rw [← map_zero inj]
    exact (IsFractionRing.injective F[X] (NewField F)).eq_iff
  have he : RingHom.ker e =
      (RingHom.ker (coeffEval k point)).map (MvPolynomial.map Polynomial.C) :=
    ker_polynomialEval k point
  have hm := IsLocalization.map_under M FreshCoeffRing (RingHom.ker g)
  change ((RingHom.ker g).comap j).map j = _ at hm
  have hj : j.comp (MvPolynomial.map (σ := CoeffIndex) Polynomial.C) =
      MvPolynomial.map freshConstants := by
    apply MvPolynomial.ringHom_ext <;> simp [j, freshConstants]
  rw [hc, he, Ideal.map_map, hj] at hm
  exact hm
end FreshField
end
end K1_13_5_5_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_13_5_5_1
noncomputable section
open K1_13 K1_13_5 K1_13_5_5
open scoped Polynomial BigOperators
attribute [local instance] MvPolynomial.algebraMvPolynomial
section Evaluation
variable {F : Type*} [Field F]
theorem jetForm_eval (k : Geom →+* F) (U : F[X]) (hU : U.natDegree < taylorLength) (i : Fin 3) :
    freshCoeffEval k (fun a => U.coeff a.val) (jetForm freshCenter i.val) =
      jetAt newCenter (U.map newConstants) i := by
  have hpoly := Polynomial.as_sum_range_C_mul_X_pow' U hU
  have he := congrArg
    (fun P : F[X] => (Polynomial.hasseDeriv i.val (P.map newConstants)).eval newCenter) hpoly
  rw [← Fin.sum_univ_eq_sum_range (fun j => Polynomial.C (U.coeff j) * Polynomial.X ^ j)] at he
  simp only [Polynomial.map_sum, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.map_monomial,
    map_sum, Polynomial.hasseDeriv_monomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial] at he
  simp only [freshCoeffEval, jetForm, map_sum, map_mul, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', Function.comp_apply, map_pow, map_natCast, newGround_center]
  rw [jetAt, he]
  apply Finset.sum_congr rfl
  intro a _
  ring
def freshJetEval (k : Geom →+* F) (U : F[X]) : FreshJetRing →+* NewField F :=
  (freshCoeffEval k fun a => U.coeff a.val).comp freshProjection.toRingHom
theorem freshJetEval_eq (k : Geom →+* F) (U : F[X]) (hU : U.natDegree < taylorLength) :
    freshJetEval k U = MvPolynomial.eval₂Hom (newGround k) (jetAt newCenter (U.map newConstants)) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp [freshJetEval, freshProjection, freshCoeffEval]
  · intro i
    change freshCoeffEval k (fun a => U.coeff a.val)
      (MvPolynomial.aeval (fun j : Fin 3 => jetForm freshCenter j.val) (MvPolynomial.X i)) =
      MvPolynomial.eval₂Hom (newGround k) (jetAt newCenter (U.map newConstants)) (MvPolynomial.X i)
    rw [MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X']
    exact jetForm_eval k U hU i
theorem newTrajectory_eval (k : Geom →+* F) (U : F[X]) (b : Row 3) :
    rowAt (newConstants.comp k) newCenter (jetAt newCenter (U.map newConstants)) b =
      algebraMap F[X] (NewField F) (trajectory k U b) := by
  rw [← eval_trajectory, ← map_trajectory]
  have h : (Polynomial.evalRingHom (newCenter : NewField F)).comp
      (Polynomial.mapRingHom newConstants) = algebraMap F[X] (NewField F) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [newConstants]
    · simp [newCenter]
  exact RingHom.congr_fun h _
theorem rowAt_new (k : Geom →+* F) (y : Fin 3 → NewField F) :
    rowAt (newConstants.comp k) newCenter y = (MvPolynomial.eval₂Hom (newGround k) y).comp rowMap := by
  apply MvPolynomial.ringHom_ext
  · intro b
    have h : (Polynomial.evalRingHom (newCenter : NewField F)).comp
        (Polynomial.mapRingHom (newConstants.comp k)) =
          (newGround k).comp (algebraMap Geom[X] FreshField) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp [newConstants]
      · simp [newCenter]
    simpa [rowAt, rowMap] using RingHom.congr_fun h b
  · intro i
    simp [rowAt, rowMap]
theorem freshJetEval_row (k : Geom →+* F) (U : F[X]) (hU : U.natDegree < taylorLength)
    (b : Row 3) :
    freshJetEval k U (freshRow b) = algebraMap F[X] (NewField F) (trajectory k U b) := by
  rw [freshJetEval_eq k U hU, ← newTrajectory_eval, rowAt_new]
  rfl
theorem fresh_recovered_mem (k : Geom →+* F) (U : F[X]) (a : CoeffIndex) (m : ℕ)
    (d v : FreshJetRing)
    (h : freshJetEval k U d ^ m * newConstants (U.coeff a.val) = freshJetEval k U v) :
    freshProjection d ^ m * MvPolynomial.X a - freshProjection v ∈
      freshIdeal (RingHom.ker (coeffEval k (fun j => U.coeff j.val))) := by
  rw [freshIdeal_eq_ker, RingHom.mem_ker]
  let e := freshCoeffEval k (fun j => U.coeff j.val)
  change e (freshProjection d ^ m * MvPolynomial.X a - freshProjection v) = 0
  rw [map_sub e, map_mul e, map_pow e, sub_eq_zero]
  have he : e (MvPolynomial.X a) = newConstants (U.coeff a.val) :=
    MvPolynomial.eval₂Hom_X' _ _ _
  rw [he]
  exact h
end Evaluation
theorem freshJetEval_ker (f : Row 3) (hf : Irreducible f) (hd : 0 < f.degreeOf 2)
    [(chartIdeal f).IsPrime] (U : (ChartField f)[X]) (hU : U.natDegree < taylorLength)
    (hsol : trajectory (chartConstants f) U f = 0)
    (hinit : jetAt (chartCenter f) U = chartJets f) :
    RingHom.ker (freshJetEval (chartConstants f) U) = chartIdeal f := by
  let eval := freshJetEval (chartConstants f) U
  have hc : (RingHom.ker eval).comap rowMap = originalIdeal f := by
    apply le_antisymm
    · intro b hb
      change eval (freshRow b) = 0 at hb
      rw [freshJetEval_row _ _ hU] at hb
      have hz : trajectory (chartConstants f) U b = 0 :=
        (IsFractionRing.injective (ChartField f)[X] (NewField (ChartField f))) (hb.trans (map_zero _).symm)
      rw [← chart_contract f hf hd]
      change freshRow b ∈ chartIdeal f
      apply (onChart_eq_zero f _).mp
      have h := eval_trajectory (chartConstants f) U (chartCenter f) b
      rw [hinit, rowAt_chart, hz, Polynomial.eval_zero] at h
      exact h.symm
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      change eval (freshRow f) = 0
      rw [freshJetEval_row _ _ hU, hsol, map_zero]
  have hm := IsLocalization.map_under rowDenominators FreshJetRing (RingHom.ker eval)
  change ((RingHom.ker eval).comap rowMap).map rowMap = _ at hm
  rw [hc, chartIdeal_map] at hm
  exact hm.symm
end
end K1_13_5_5_1
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_13_5_5_1
noncomputable section
open K1_13 K1_13_5_5 K1_13_5
open scoped Polynomial
theorem eval_kernel_le_of_cleared {A R σ : Type*} {F L : Type u}
    [CommRing A] [CommRing R] [Field F] [Field L]
    (b : A →+* R) (e : R →+* F) (g : R →+* L)
    (hker : RingHom.ker e ≤ RingHom.ker g) (d : R) (m : ℕ) (v : σ → R)
    (he : e d ≠ 0) (hg : g d ≠ 0) (point : σ → F) (mark : σ → L)
    (hpoint : ∀ i, e d ^ m * point i = e (v i))
    (hmark : ∀ i, g d ^ m * mark i = g (v i)) :
    RingHom.ker (MvPolynomial.eval₂Hom (e.comp b) point) ≤
      RingHom.ker (MvPolynomial.eval₂Hom (g.comp b) mark) := by
  let S := Localization.Away d
  let den : Submonoid.powers d := ⟨d ^ m, ⟨m, rfl⟩⟩
  let l := MvPolynomial.eval₂Hom ((algebraMap R S).comp b)
    (fun i => IsLocalization.mk' S (v i) den)
  have ht {D : Type u} [Field D] (t : R →+* D) (h : t d ≠ 0) (p : σ → D)
      (hp : ∀ i, t d ^ m * p i = t (v i)) :
      (IsLocalization.Away.lift (S := S) d (g := t) h.isUnit).comp l =
        MvPolynomial.eval₂Hom (t.comp b) p := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [l]
    · intro i
      simp only [l, RingHom.coe_comp, Function.comp_apply, MvPolynomial.eval₂Hom_X']
      apply mul_left_cancel₀ (pow_ne_zero m h)
      have hh := congrArg (IsLocalization.Away.lift (S := S) d (g := t) h.isUnit)
        (IsLocalization.mk'_spec' S (v i) den)
      rw [hp i]
      simpa only [map_mul, IsLocalization.Away.lift_eq, den, map_pow] using hh
  let el := IsLocalization.Away.lift (S := S) d (g := e) he.isUnit
  let gl := IsLocalization.Away.lift (S := S) d (g := g) hg.isUnit
  have hk : RingHom.ker el ≤ RingHom.ker gl := by
    apply (IsLocalization.under_le_under_iff (Submonoid.powers d) S).mp
    change (RingHom.ker el).comap (algebraMap R S) ≤
      (RingHom.ker gl).comap (algebraMap R S)
    simpa only [RingHom.comap_ker, el, gl, IsLocalization.Away.lift_comp] using hker
  have he' : el.comp l = MvPolynomial.eval₂Hom (e.comp b) point := ht e he point hpoint
  have hg' : gl.comp l = MvPolynomial.eval₂Hom (g.comp b) mark := ht g hg mark hmark
  rw [← he', ← hg', ← RingHom.comap_ker, ← RingHom.comap_ker]
  exact Ideal.comap_mono hk
theorem trajectory_actual (S : Geom[X]) (b : Row 3) :
    trajectory (RingHom.id Geom) S b = atJet b S := by
  simp [trajectory, atJet, MvPolynomial.eval₂_id]
  rfl
theorem actual_eval (S : Geom[X]) (b : Row 3) :
    rowAt freshConstants freshCenter (jetAt freshCenter (S.map freshConstants)) b =
      algebraMap Geom[X] FreshField (atJet b S) := by
  rw [← eval_trajectory]
  have hm := map_trajectory (RingHom.id Geom) freshConstants S b
  rw [trajectory_actual, RingHom.comp_id] at hm
  rw [← hm]
  have h : (Polynomial.evalRingHom freshCenter).comp (Polynomial.mapRingHom freshConstants) =
      algebraMap Geom[X] FreshField := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [freshConstants]
    · simp [freshCenter]
  exact RingHom.congr_fun h _
theorem actual_eval_fresh (S : Geom[X]) :
    (rowAt freshConstants freshCenter (jetAt freshCenter (S.map freshConstants))) =
      (MvPolynomial.eval (jetAt freshCenter (S.map freshConstants))).comp rowMap := by
  apply MvPolynomial.ringHom_ext
  · intro a
    have h : (Polynomial.evalRingHom freshCenter).comp (Polynomial.mapRingHom freshConstants) =
        algebraMap Geom[X] FreshField := by
      apply Polynomial.ringHom_ext
      · intro c
        simp [freshConstants]
      · simp [freshCenter]
    simpa [rowAt, rowMap] using RingHom.congr_fun h a
  · intro i
    simp [rowAt, rowMap]
end
end K1_13_5_5_1
end
section
namespace K1_13_5_5_1_1
noncomputable section
open K1_13 K1_13_5 K1_13_5_5_1 Polynomial
open scoped BigOperators
@[simp] private theorem coeff_coeffDerivative (P : Row 3) (m : Fin 3 →₀ ℕ) :
    (coeffDerivative P).coeff m = derivative (P.coeff m) := by
  classical
  rw [coeffDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
private theorem coeffDerivative_C (p : Geom[X]) :
    coeffDerivative (MvPolynomial.C p : Row 3) = MvPolynomial.C (derivative p) := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_coeffDerivative]
  by_cases hm : 0 = m <;> simp [MvPolynomial.coeff_C, hm]
private theorem coeffDerivative_add (P Q : Row 3) :
    coeffDerivative (P + Q) = coeffDerivative P + coeffDerivative Q := by
  ext m
  simp
private theorem coeffDerivative_mul_X (P : Row 3) (j : Fin 3) :
    coeffDerivative (P * MvPolynomial.X j) = coeffDerivative P * MvPolynomial.X j := by
  classical
  ext m
  rw [coeff_coeffDerivative, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
  split_ifs <;> simp
section ChainRule
variable {F : Type*} [CommRing F]
private theorem eval_chain (k : Geom →+* F) (P : Row 3) (a : Fin 3 → F[X]) :
    let e := MvPolynomial.eval₂Hom (Polynomial.mapRingHom k) a
    derivative (e P) = e (coeffDerivative P) +
      ∑ i, derivative (a i) * e (MvPolynomial.pderiv i P) := by
  classical
  let e := MvPolynomial.eval₂Hom (Polynomial.mapRingHom k) a
  change derivative (e P) = e (coeffDerivative P) + _
  induction P using MvPolynomial.induction_on with
  | C c => simp [e, coeffDerivative_C, derivative_map]
  | add P Q hP hQ =>
    simp only [map_add, coeffDerivative_add, hP, hQ, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X P j ih =>
    have hx : e (MvPolynomial.X j) = a j := MvPolynomial.eval₂Hom_X' _ _ _
    rw [map_mul, hx, derivative_mul, ih, coeffDerivative_mul_X, map_mul, hx]
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib]
    have left : (∑ i, derivative (a i) * (e (MvPolynomial.pderiv i P) * e (MvPolynomial.X j))) =
        (∑ i, derivative (a i) * e (MvPolynomial.pderiv i P)) * a j := by
      simp only [hx, Finset.sum_mul, mul_assoc]
    have right : (∑ i, derivative (a i) * (e P * e (MvPolynomial.pderiv i (MvPolynomial.X j)))) =
        derivative (a j) * e P := by
      simp [MvPolynomial.pderiv_X, Pi.single_apply, mul_ite]
    rw [left, right]
    ring
private theorem derivative_hasse_one (U : F[X]) :
    derivative (hasseDeriv 1 U) = 2 * hasseDeriv 2 U := by
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := F) 1 1) U
  simpa [hasseDeriv_one', Nat.choose_one_right, nsmul_eq_mul] using h
private theorem eval_lowerTangent (k : Geom →+* F) (U : F[X]) (P : Row 3) :
    derivative (trajectory k U P) = trajectory k U (lowerTangent P) +
      derivative (hasseDeriv 2 U) * trajectory k U (separant P) := by
  change derivative (MvPolynomial.eval₂Hom (Polynomial.mapRingHom k)
    (fun i : Fin 3 => hasseDeriv i.val U) P) = _
  rw [eval_chain k P (fun i => hasseDeriv i.val U), Fin.sum_univ_three]
  simp only [lowerTangent, separant, map_add, map_mul, map_ofNat, MvPolynomial.eval₂Hom_X',
    trajectory]
  have hsecond : derivative (derivative U) = 2 * hasseDeriv 2 U := by
    simpa only [hasseDeriv_one] using derivative_hasse_one U
  simp only [show (0 : Fin 3).val = 0 by rfl, show (1 : Fin 3).val = 1 by rfl,
    show (2 : Fin 3).val = 2 by rfl, hasseDeriv_zero, LinearMap.id_apply,
    hasseDeriv_one, hsecond]
  ring
private theorem eval_tangentNumerator (k : Geom →+* F) (U : F[X]) (f P : Row 3)
    (hf : trajectory k U f = 0) :
    trajectory k U (tangentNumerator f P) =
      trajectory k U (separant f) * derivative (trajectory k U P) := by
  have hz : trajectory k U (lowerTangent f) +
      derivative (hasseDeriv 2 U) * trajectory k U (separant f) = 0 := by
    rw [← eval_lowerTangent, hf, map_zero]
  rw [tangentNumerator, map_sub, map_mul, map_mul]
  change trajectory k U (separant f) * trajectory k U (lowerTangent P) -
    trajectory k U (lowerTangent f) * trajectory k U (separant P) = _
  rw [eval_lowerTangent]
  linear_combination -trajectory k U (separant P) * hz
private theorem cleared_product_rule (a : ℕ) (S V : F[X]) :
    S * (S * derivative (S ^ a * V)) -
      (a : F[X]) * (S ^ a * V) * (S * derivative S) =
        S ^ (a + 2) * derivative V := by
  cases a with
  | zero => simp [pow_two, mul_assoc]
  | succ a =>
    rw [derivative_mul, derivative_pow, Nat.succ_sub_one,
      pow_add S (a + 1) 2, pow_succ' S a]
    simp only [Nat.cast_succ, C_add, C_1, C_eq_natCast]
    ring
theorem eval_compatibility (k : Geom →+* F) (U : F[X]) (f : Row 3)
    (hf : trajectory k U f = 0) (j : ℕ) :
    trajectory k U (compatibilityNumerator f j) =
      trajectory k U (separant f) ^ (2 * j + 1) *
        (derivative^[j + 1]) (hasseDeriv 2 U) := by
  induction j with
  | zero =>
    have hz : trajectory k U (lowerTangent f) +
        derivative (hasseDeriv 2 U) * trajectory k U (separant f) = 0 := by
      rw [← eval_lowerTangent, hf, map_zero]
    simp only [compatibilityNumerator, map_neg, Nat.mul_zero, Nat.zero_add, pow_one,
      Function.iterate_one]
    linear_combination -hz
  | succ j ih =>
    rw [compatibilityNumerator, map_sub, map_mul, map_mul, map_mul, map_natCast,
      eval_tangentNumerator _ _ _ _ hf, eval_tangentNumerator _ _ _ _ hf, ih,
      show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega,
      Function.iterate_succ_apply' derivative (j + 1) (hasseDeriv 2 U)]
    exact cleared_product_rule _ _ _
theorem twice_iterate_derivative_top (U : F[X]) (j : ℕ) :
    2 * (derivative^[j + 1]) (hasseDeriv 2 U) = (derivative^[j + 3]) U := by
  have hsecond : (derivative^[2]) U = 2 * hasseDeriv 2 U := by
    rw [Function.iterate_succ_apply' derivative 1 U, Function.iterate_one]
    simpa only [hasseDeriv_one'] using derivative_hasse_one U
  rw [show j + 3 = (j + 1) + 2 by omega,
    Function.iterate_add_apply derivative (j + 1) 2 U, hsecond]
  simpa only [Nat.cast_ofNat] using
    (Polynomial.iterate_derivative_natCast_mul (n := 2) (k := j + 1)
      (f := hasseDeriv 2 U)).symm
end ChainRule
end
end K1_13_5_5_1_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_5_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_5 Polynomial
open scoped nonZeroDivisors
local notation "PC" => Polynomial.C
local notation "PX" => Polynomial.X
local notation "MP" => MvPolynomial
local notation "MC" => MvPolynomial.C
local notation "MX" => MvPolynomial.X
local notation "qmk" => Ideal.Quotient.mk
abbrev Param := MP (Fin 4) FX
abbrev Den := nonZeroDivisors Param
abbrev frac : Param →+* SectionField := algebraMap _ _
private abbrev Local {R : Type} [CommRing R] (p : Param →+* R) :=
  Localization (Den.map p)
private abbrev numer {R : Type} [CommRing R] (p : Param →+* R) : R →+* Local p :=
  algebraMap _ _
private def coeff {R : Type} [CommRing R] (p : Param →+* R) :
    SectionField →+* Local p :=
  IsLocalization.lift (M := Den) (g := (numer p).comp p)
    fun d => IsLocalization.map_units (Local p) (M := Den.map p) ⟨p d, ⟨d, d.prop, rfl⟩⟩
@[simp] private theorem coeff_frac {R : Type} [CommRing R] (p : Param →+* R) (x : Param) :
    coeff p (frac x) = numer p (p x) := IsLocalization.lift_eq _ x
private def descend {R T : Type} [CommRing R] [CommRing T]
    (p : Param →+* R) (r : R →+* T) (k : SectionField →+* T)
    (h : r.comp p = k.comp frac) : Local p →+* T :=
  IsLocalization.lift (M := Den.map p) (g := r) <| by
    rintro ⟨_, x, hx, rfl⟩
    change IsUnit (r (p x))
    rw [show r (p x) = k (frac x) from RingHom.congr_fun h x]
    exact (IsLocalization.map_units SectionField (M := Den) ⟨x, hx⟩).map k
@[simp] private theorem descend_numer {R T : Type} [CommRing R] [CommRing T]
    {p : Param →+* R} {r : R →+* T} {k : SectionField →+* T}
    (h : r.comp p = k.comp frac) (x : R) :
    descend p r k h (numer p x) = r x := IsLocalization.lift_eq _ x
theorem descend_coeff {R T : Type} [CommRing R] [CommRing T]
    {p : Param →+* R} {r : R →+* T} {k : SectionField →+* T}
    (h : r.comp p = k.comp frac) :
    (descend p r k h).comp (coeff p) = k := by
  apply IsLocalization.ringHom_ext Den
  apply RingHom.ext
  intro x
  simpa only [RingHom.comp_apply, coeff_frac, descend_numer] using RingHom.congr_fun h x
theorem localMap_isLocalization {R T : Type} [CommRing R] [CommRing T]
    (p : Param →+* R) (f : R →+* T) :
    IsLocalization ((Den.map p).map f) (Local (f.comp p)) := by
  change IsLocalization ((Den.map p.toMonoidHom).map f.toMonoidHom) _
  rw [Submonoid.map_map]
  exact inferInstanceAs (IsLocalization (Den.map (f.comp p)) (Local (f.comp p)))
private def localMap {R T : Type} [CommRing R] [CommRing T]
    (p : Param →+* R) (f : R →+* T) : Local p →+* Local (f.comp p) :=
  letI := localMap_isLocalization p f
  IsLocalization.map _ f (Den.map p).le_comap_map
@[simp] private theorem localMap_numer {R T : Type} [CommRing R] [CommRing T]
    (p : Param →+* R) (f : R →+* T) (x : R) :
    localMap p f (numer p x) = numer (f.comp p) (f x) := by
  let := localMap_isLocalization p f
  unfold localMap
  apply IsLocalization.map_eq
theorem localMap_injective {R T : Type} [CommRing R] [CommRing T]
    (p : Param →+* R) (f : R →+* T) (hf : Function.Injective f) :
    Function.Injective (localMap p f) := by
  let := localMap_isLocalization p f
  unfold localMap
  apply IsLocalization.map_injective_of_injective
  exact hf
theorem localMap_coeff {R T : Type} [CommRing R] [CommRing T]
    (p : Param →+* R) (f : R →+* T) :
    (localMap p f).comp (coeff p) = coeff (f.comp p) := by
  apply IsLocalization.ringHom_ext Den
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, coeff_frac, localMap_numer]
private def slope {R : Type} [Zero R] (b : Bool) (s : R) : R := if b then s else 0
@[simp] private theorem map_slope {R T : Type} [CommRing R] [CommRing T]
    (f : R →+* T) (b : Bool) (s : R) : f (slope b s) = slope b (f s) := by
  cases b <;> simp [slope]
private def parameters {R : Type} [CommRing R] (c : FX →+* R) (b : Bool)
    (a s u y v : R) : Param →+* R :=
  MvPolynomial.eval₂Hom c ![a, s, u, y + slope b s * v]
theorem comp_parameters {R T : Type} [CommRing R] [CommRing T]
    (f : R →+* T) (c : FX →+* R) (b : Bool) (a s u y v : R) :
    f.comp (parameters c b a s u y v) =
      parameters (f.comp c) b (f a) (f s) (f u) (f y) (f v) := by
  apply MvPolynomial.ringHom_ext
  · intro x
    simp [parameters]
  · intro i
    fin_cases i <;> simp [parameters]
private theorem jetPlane_C (f : FX[X]) : jetPlaneIncl (PC f) = ordinateIncl f := by
  have h : (rootIncl.comp toRoot).comp (Polynomial.mapRingHom MC) = ordinateIncl := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [ordinateIncl, rootIncl, toRoot, rootSeeds]
    · simp [ordinateIncl, rootIncl, toRoot]
  simpa [jetPlaneIncl, toJet, fixedIncl, K1_14_3.fixedEmbedding] using RingHom.congr_fun h f
@[simp] private theorem jetPlane_Y : jetPlaneIncl ((PC (PX : FX[X])) : ODE) = MX 2 := by
  simp [jetPlane_C, ordinateIncl]
@[simp] private theorem jetPlane_V : jetPlaneIncl (PX : ODE) = MX 3 := by
  change ((PX : ODE).map (Polynomial.mapRingHom MC)).eval₂
    (rootIncl.comp toRoot) (MX 3) = _
  rw [Polynomial.map_X, Polynomial.eval₂_X]
@[simp] private theorem jetPlane_const (c : FX) : jetPlaneIncl (PC (PC c) : ODE) = MC c := by
  simp [jetPlane_C, ordinateIncl]
private abbrev Source (I : Ideal Ambient) := MP (Fin 3) (JetImage I)
private abbrev Parent (I : Ideal Ambient) := MP (Fin 2) (CoordinateRing I)
abbrev sourceC (I : Ideal Ambient) : ODE →+* Source I :=
  MvPolynomial.C.comp (qmk (I.comap jetPlaneIncl))
abbrev parentC (I : Ideal Ambient) : Ambient →+* Parent I :=
  MvPolynomial.C.comp (qmk I)
@[simp] private theorem seedLineLift_sourceC (I : Ideal Ambient) (z : ODE) :
    seedLineLift I (sourceC I z) = parentC I (jetPlaneIncl z) := by
  change seedLineLift I (MC (qmk (I.comap jetPlaneIncl) z)) = _
  simp only [seedLineLift, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Ideal.quotientMap_mk]
def sourceParam (I : Ideal Ambient) (b : Bool) : Param →+* Source I :=
  parameters ((sourceC I).comp (Polynomial.C.comp PC)) b (MX 0) (MX 1) (MX 2)
    (sourceC I (PC PX)) (sourceC I PX)
abbrev parentParam (I : Ideal Ambient) (b : Bool) : Param →+* Parent I :=
  (seedLineLift I).comp (sourceParam I b)
theorem parentParam_eq (I : Ideal Ambient) (b : Bool) :
    parentParam I b = parameters ((parentC I).comp MC) b (MX 0) (MX 1)
      (parentC I (MX 0) + MX 0 * parentC I (MX 1))
      (parentC I (MX 2)) (parentC I (MX 3)) := by
  unfold parentParam sourceParam
  rw [comp_parameters]
  have hc : (seedLineLift I).comp ((sourceC I).comp (Polynomial.C.comp PC)) =
      (parentC I).comp MC := by
    apply RingHom.ext
    intro x
    exact (seedLineLift_sourceC I (PC (PC x))).trans
      (congrArg (parentC I) (jetPlane_const x))
  rw [hc]
  simp [seedLineLift, parentC]
theorem frac_C (x : FX) : frac (MC x) = algebraMap FX SectionField x :=
  (IsScalarTower.algebraMap_apply FX Param SectionField x).symm
private def jetEval (b : Bool) : ODE →+* SectionField[X] :=
  eval₂RingHom (eval₂RingHom (Polynomial.C.comp (algebraMap FX SectionField))
    (PC (sliceParameter 3) - PC (slope b (sliceParameter 1)) * PX)) PX
theorem jetEval_ordinate (G : ODE) : jetEval false G = ordinatePolynomial G := by
  have h : jetEval false = Polynomial.mapRingHom
      (eval₂RingHom (algebraMap FX SectionField) (sliceParameter 3)) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro x
        simp [jetEval]
      · simp [jetEval, slope]
    · simp [jetEval]
  exact RingHom.congr_fun h G
abbrev ImageIdeal (G : ODE) (b : Bool) : Ideal SectionField[X] :=
  Ideal.span {jetEval b G}
def imageNumer (I : Ideal Ambient) (G : ODE) (b : Bool)
    (hi : I.comap jetPlaneIncl = Ideal.span {G}) :
    Source I →+* SectionField[X] ⧸ ImageIdeal G b :=
  MvPolynomial.eval₂Hom (Ideal.quotientMap (ImageIdeal G b) (jetEval b) (by
    rw [hi, Ideal.span_le]
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact Ideal.subset_span rfl))
    ![algebraMap _ _ (sliceParameter 0), algebraMap _ _ (sliceParameter 1),
      algebraMap _ _ (sliceParameter 2)]
theorem imageParam_compat (I : Ideal Ambient) (G : ODE) (b : Bool)
    (hi : I.comap jetPlaneIncl = Ideal.span {G}) :
    (imageNumer I G b hi).comp (sourceParam I b) =
      (algebraMap SectionField (SectionField[X] ⧸ ImageIdeal G b)).comp frac := by
  apply MvPolynomial.ringHom_ext
  · intro x
    simp [sourceParam, parameters, imageNumer, sourceC, Ideal.quotientMap_mk, jetEval, frac_C]
    rfl
  · intro i
    fin_cases i
    · simp [sourceParam, parameters, imageNumer, sliceParameter]
    · simp [sourceParam, parameters, imageNumer, sliceParameter]
    · simp [sourceParam, parameters, imageNumer, sliceParameter]
    · cases b <;>
        simp [sourceParam, parameters, sourceC, imageNumer, Ideal.quotientMap_mk, jetEval,
          slope, sliceParameter] <;> first | rfl | exact sub_add_cancel _ _
theorem image_to_local (I : Ideal Ambient) (G : ODE) (b : Bool)
    (hi : I.comap jetPlaneIncl = Ideal.span {G}) :
    ∃ f : (SectionField[X] ⧸ ImageIdeal G b) →+* Local (sourceParam I b),
      Function.Injective f ∧
      f.comp (algebraMap SectionField (SectionField[X] ⧸ ImageIdeal G b)) =
        coeff (sourceParam I b) := by
  let p := sourceParam I b
  let w : SectionField[X] →+* Local p :=
    eval₂RingHom (coeff p) (numer p (sourceC I PX))
  have hw : w.comp (jetEval b) = (numer p).comp (sourceC I) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro x
        simp [w, p, jetEval, ← frac_C, sourceParam, parameters]
      · cases b <;> simp [w, p, jetEval, sliceParameter, sourceParam, parameters, slope]
    · simp [w, jetEval]
  have hzero : w (jetEval b G) = 0 := by
    change (w.comp (jetEval b)) G = 0
    rw [hw]
    have hg : G ∈ I.comap jetPlaneIncl := by rw [hi]; exact Ideal.subset_span rfl
    change numer p (MC (qmk (I.comap jetPlaneIncl) G)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero, map_zero]
  have hker : ImageIdeal G b ≤ RingHom.ker w :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (RingHom.mem_ker.mpr hzero))
  let f := Ideal.Quotient.lift (ImageIdeal G b) w (fun z hz => RingHom.mem_ker.mp (hker hz))
  have hf : f.comp (algebraMap SectionField (SectionField[X] ⧸ ImageIdeal G b)) =
      coeff p := by
    apply RingHom.ext
    intro x
    change f (qmk (ImageIdeal G b) (PC x)) = coeff p x
    simp [f, w]
  let r := descend p (imageNumer I G b hi) _ (imageParam_compat I G b hi)
  have hr := descend_coeff (imageParam_compat I G b hi)
  have hid : r.comp f = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro x
      change (r.comp (f.comp (algebraMap SectionField (SectionField[X] ⧸ ImageIdeal G b)))) x = _
      rw [hf]
      exact RingHom.congr_fun hr x
    · change r (f (qmk (ImageIdeal G b) PX)) = qmk (ImageIdeal G b) PX
      simp [f, w, r, imageNumer, sourceC, Ideal.quotientMap_mk, jetEval]
  have hinv : Function.LeftInverse r f := fun x => RingHom.congr_fun hid x
  exact ⟨f, hinv.injective, hf⟩
private def jetLine (b : Bool) : SectionAmbient :=
  MX 2 + MC (slope b (sliceParameter 1)) * MX 3 - MC (sliceParameter 3)
abbrev TargetIdeal (I : Ideal Ambient) (b : Bool) : Ideal SectionAmbient :=
  I.map sectionBase ⊔ Ideal.span {sectionSeedLine, jetLine b}
private abbrev Target (I : Ideal Ambient) (b : Bool) := SectionAmbient ⧸ TargetIdeal I b
abbrev targetScalar (I : Ideal Ambient) (b : Bool) : SectionField →+* Target I b :=
  algebraMap _ _
def targetNumer (I : Ideal Ambient) (b : Bool) : Parent I →+* Target I b :=
  MvPolynomial.eval₂Hom
    (Ideal.quotientMap (TargetIdeal I b) sectionBase (Ideal.le_comap_map.trans
      (Ideal.comap_mono le_sup_left)))
    ![targetScalar I b (sliceParameter 0), targetScalar I b (sliceParameter 1)]
@[simp] private theorem targetNumer_parentC (I : Ideal Ambient) (b : Bool) (x : Ambient) :
    targetNumer I b (MC (qmk I x)) = qmk (TargetIdeal I b) (sectionBase x) := by
  simp [targetNumer, Ideal.quotientMap_mk]
@[simp] private theorem targetNumer_X (I : Ideal Ambient) (b : Bool) (i : Fin 2) :
    targetNumer I b (MX i) =
      ![targetScalar I b (sliceParameter 0), targetScalar I b (sliceParameter 1)] i :=
  MvPolynomial.eval₂Hom_X' _ _ _
theorem targetParam_compat (I : Ideal Ambient) (b : Bool) :
    (targetNumer I b).comp (parentParam I b) = (targetScalar I b).comp frac := by
  apply MvPolynomial.ringHom_ext
  · intro x
    simp only [RingHom.comp_apply, parentParam_eq, parameters, MvPolynomial.eval₂Hom_C,
      targetNumer_parentC, sectionBase, MvPolynomial.map_C, frac_C]
    rfl
  · intro i
    fin_cases i
    · simp [parentParam_eq, parameters, sliceParameter]
    · simp [parentParam_eq, parameters, sliceParameter]
    · simp [parentParam_eq, parameters, sectionBase]
      apply sub_eq_zero.mp
      change (qmk (TargetIdeal I b) (MX 0) + qmk (TargetIdeal I b) (MC (sliceParameter 0)) *
        qmk (TargetIdeal I b) (MX 1)) - qmk (TargetIdeal I b) (MC (sliceParameter 2)) = 0
      rw [← map_mul, ← map_add, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.subset_span
        (show sectionSeedLine ∈ {sectionSeedLine, jetLine b} by simp)))
    · simp [parentParam_eq, parameters, sectionBase]
      rw [← map_slope (targetScalar I b)]
      apply sub_eq_zero.mp
      change (qmk (TargetIdeal I b) (MX 2) +
        qmk (TargetIdeal I b) (MC (slope b (sliceParameter 1))) *
        qmk (TargetIdeal I b) (MX 3)) - qmk (TargetIdeal I b) (MC (sliceParameter 3)) = 0
      rw [← map_mul, ← map_add, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.subset_span
        (show jetLine b ∈ {sectionSeedLine, jetLine b} by simp)))
theorem map_graph {R T : Type} [CommRing R] [CommRing T]
    (f : R →+* T) (x a y : R) : f x + f a * f y - f (x + a * y) = 0 := by
  simp
theorem parent_section_extension {T : Type} [CommRing T] (I : Ideal Ambient) (b : Bool)
    (n : Parent I →+* T) (k : SectionField →+* T) (hk : k.comp frac = n.comp (parentParam I b)) :
    ∃ r : Target I b →+* T, r.comp (targetNumer I b) = n := by
  let w : SectionAmbient →+* T := MvPolynomial.eval₂Hom k (fun i => n (parentC I (MX i)))
  have hw : w.comp sectionBase = n.comp (parentC I) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [RingHom.comp_apply, sectionBase, MvPolynomial.map_C, w, MvPolynomial.eval₂Hom_C,
        ← frac_C]
      simpa only [RingHom.comp_apply, parentParam_eq, parameters, MvPolynomial.eval₂Hom_C]
        using RingHom.congr_fun hk (MC x)
    · intro i
      simp [w, sectionBase]
  have hcoeff (i : Fin 4) : k (sliceParameter i) = n
      (![MX 0, MX 1, parentC I (MX 0) + MX 0 * parentC I (MX 1),
        parentC I (MX 2) + slope b (MX 1) * parentC I (MX 3)] i) := by
    change k (frac (MX i)) = _
    simpa only [RingHom.comp_apply, parentParam_eq, parameters, MvPolynomial.eval₂Hom_X']
      using RingHom.congr_fun hk (MX i)
  have hwC (x : SectionField) : w (MC x) = k x := MvPolynomial.eval₂Hom_C _ _ _
  have hwX (i : Fin 4) : w (MX i) = n (parentC I (MX i)) := MvPolynomial.eval₂Hom_X' _ _ _
  have hw_seed : w sectionSeedLine = 0 := by
    simp only [sectionSeedLine, w.map_sub, w.map_add, w.map_mul, hwX, hwC]
    rw [hcoeff 0, hcoeff 2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    exact map_graph n (parentC I (MX 0)) (MX 0) (parentC I (MX 1))
  have hw_jet : w (jetLine b) = 0 := by
    simp only [jetLine, w.map_sub, w.map_add, w.map_mul, hwX, hwC, map_slope k]
    rw [hcoeff 1, hcoeff 3]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, ← map_slope n]
    exact map_graph n (parentC I (MX 2)) (slope b (MX 1)) (parentC I (MX 3))
  have hker : TargetIdeal I b ≤ RingHom.ker w := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker, hw]
      intro x hx
      apply RingHom.mem_ker.mpr
      change n (MC (qmk I x)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero, map_zero]
    · rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact RingHom.mem_ker.mpr hw_seed
      · exact RingHom.mem_ker.mpr hw_jet
  let r := Ideal.Quotient.lift (TargetIdeal I b) w (fun z hz => RingHom.mem_ker.mp (hker hz))
  have hrC (x : SectionField) : r (targetScalar I b x) = k x := by
    change r (qmk (TargetIdeal I b) (MC x)) = _
    rw [Ideal.Quotient.lift_mk, hwC]
  refine ⟨r, ?_⟩
  apply MvPolynomial.ringHom_ext
  · intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    change r (targetNumer I b (MC (qmk I x))) = n (parentC I x)
    rw [targetNumer_parentC]
    exact RingHom.congr_fun hw x
  · intro i
    rw [RingHom.comp_apply, targetNumer_X]
    fin_cases i
    · exact (hrC (sliceParameter 0)).trans (hcoeff 0)
    · exact (hrC (sliceParameter 1)).trans (hcoeff 1)
theorem local_to_target (I : Ideal Ambient) (b : Bool) :
    ∃ f : Local (parentParam I b) →+* Target I b,
      Function.Injective f ∧ f.comp (coeff (parentParam I b)) = targetScalar I b := by
  let p := parentParam I b
  let f := descend p (targetNumer I b) (targetScalar I b) (targetParam_compat I b)
  obtain ⟨r, hr⟩ := parent_section_extension I b (numer p) (coeff p)
    (RingHom.ext (coeff_frac p))
  have hid : r.comp f = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Den.map p)
    apply RingHom.ext
    intro x
    change r (f (numer p x)) = numer p x
    rw [show f (numer p x) = targetNumer I b x from descend_numer _ _]
    exact RingHom.congr_fun hr x
  have hinv : Function.LeftInverse r f := fun x => RingHom.congr_fun hid x
  exact ⟨f, hinv.injective, descend_coeff _⟩
theorem section_injection (I : Ideal Ambient) (G : ODE) (b : Bool)
    (hi : I.comap jetPlaneIncl = Ideal.span {G}) (hinj : Function.Injective (seedLineLift I)) :
    ∃ f : (SectionField[X] ⧸ ImageIdeal G b) →ₗ[SectionField] Target I b,
      Function.Injective f := by
  obtain ⟨f, hf, hfC⟩ := image_to_local I G b hi
  obtain ⟨g, hg, hgC⟩ := local_to_target I b
  let m := localMap (sourceParam I b) (seedLineLift I)
  have hm := localMap_injective (sourceParam I b) (seedLineLift I) hinj
  let e : (SectionField[X] ⧸ ImageIdeal G b) →ₐ[SectionField] Target I b :=
    { g.comp (m.comp f) with
      commutes' := fun x => by
        change (g.comp (m.comp (f.comp (algebraMap SectionField _)))) x = _
        rw [hfC, localMap_coeff, hgC] }
  exact ⟨e.toLinearMap, hg.comp (hm.comp hf)⟩
theorem proof : K1_14_2_2_5.c2 := by
  intro I G hi hinj
  constructor
  · let injects (J : Ideal SectionField[X]) (L : Ideal SectionAmbient) : Prop :=
      ∃ f : (SectionField[X] ⧸ J) →ₗ[SectionField] (SectionAmbient ⧸ L), Function.Injective f
    have h : injects (ImageIdeal G false) (TargetIdeal I false) :=
      section_injection I G false hi hinj
    have hsource : ImageIdeal G false = Ideal.span {ordinatePolynomial G} :=
      congrArg (fun z : SectionField[X] => Ideal.span {z}) (jetEval_ordinate G)
    have hline : jetLine false = MX 2 - MC (sliceParameter 3) := by simp [jetLine, slope]
    have htarget : TargetIdeal I false =
        I.map sectionBase ⊔ Ideal.span {sectionSeedLine, MX 2 - MC (sliceParameter 3)} :=
      congrArg (fun z => I.map sectionBase ⊔ Ideal.span {sectionSeedLine, z}) hline
    rw [hsource, htarget] at h
    exact h
  · exact section_injection I G true hi hinj
end
end K1_14_2_2_5_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_3_2_1
noncomputable section
open K1 K1_14 K1_14_3 K1_14_3_2 Polynomial UniqueFactorizationMonoid
open scoped BigOperators
abbrev seedToJet : Seeds →+* Jet := C.comp C
structure Stripped (P : Jet) where
  seeds : Seeds
  fixed : JetPlane
  row : Jet
  factorization : P = seedToJet seeds * fixedEmbedding fixed * row
  no_exceptional : ∀ D : Jet, Irreducible D → D ∣ row →
    D ∉ Set.range seedToJet ∧ D ∉ Set.range fixedEmbedding
theorem strip (P : Jet) (hP : P ≠ 0) : Nonempty (Stripped P) := by
  classical
  induction P using (wellFounded_dvdNotUnit (α := Jet)).induction with
  | h P ih =>
    by_cases hex : ∃ D : Jet, Irreducible D ∧ D ∣ P ∧
        (D ∈ Set.range seedToJet ∨ D ∈ Set.range fixedEmbedding)
    · obtain ⟨D, hD, ⟨R, hR⟩, hkind⟩ := hex
      have hn : R ≠ 0 := fun h => hP (by rw [hR, h, mul_zero])
      obtain ⟨A⟩ := ih R ⟨hn, D, hD.not_isUnit, hR.trans (mul_comm D R)⟩ hn
      rcases hkind with ⟨a, rfl⟩ | ⟨g, rfl⟩
      · refine ⟨⟨a * A.seeds, A.fixed, A.row, ?_, A.no_exceptional⟩⟩
        calc
          P = seedToJet a * R := hR
          _ = seedToJet a * (seedToJet A.seeds * fixedEmbedding A.fixed * A.row) :=
            congrArg (seedToJet a * ·) A.factorization
          _ = _ := by rw [map_mul]; ac_rfl
      · refine ⟨⟨A.seeds, g * A.fixed, A.row, ?_, A.no_exceptional⟩⟩
        calc
          P = fixedEmbedding g * R := hR
          _ = fixedEmbedding g * (seedToJet A.seeds * fixedEmbedding A.fixed * A.row) :=
            congrArg (fixedEmbedding g * ·) A.factorization
          _ = _ := by rw [map_mul]; ac_rfl
    · refine ⟨⟨1, 1, P, by simp, fun D hD hd => ?_⟩⟩
      exact not_or.mp (fun hk => hex ⟨D, hD, hd, hk⟩)
private theorem ordinary_factor {D : Jet} (hi : Irreducible D) (hv : D.natDegree = 0)
    (hs : D ∉ Set.range seedToJet) :
    C (D.coeff 0) = D ∧ Irreducible (D.coeff 0) ∧ 0 < (D.coeff 0).natDegree := by
  have hC := (eq_C_of_natDegree_eq_zero hv).symm
  have hiC : Irreducible (C (D.coeff 0) : Jet) := by rwa [hC]
  refine ⟨hC, ⟨fun h => hiC.not_isUnit (h.map C), ?_⟩, ?_⟩
  · intro a b hab
    have he : (C (D.coeff 0) : Jet) = C a * C b := by rw [← C_mul, hab]
    exact (hiC.isUnit_or_isUnit he).imp isUnit_C.mp isUnit_C.mp
  · by_contra! h
    exact hs ⟨(D.coeff 0).coeff 0, by
      change C (C ((D.coeff 0).coeff 0)) = D
      rw [← eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero h), hC]⟩
theorem markEval_C (z : K) (S : K[X]) (f : Equation) :
    markEval z S (C f) = atMark f z S := by
  change (C f : Jet).eval₂ _ _ = _
  rw [eval₂_C]
  rfl
theorem ordinary_cover (H : Jet) (hH : H ≠ 0)
    (hfactor : ∀ D : Jet, Irreducible D → D ∣ H →
      D.natDegree = 0 ∧ D ∉ Set.range seedToJet) :
    ∃ F : Finset Equation, (∀ f ∈ F, Irreducible f ∧ 0 < f.natDegree) ∧
      C (∏ f ∈ F, f) ∣ H ∧
      ∀ z S, markEval z S H = 0 → ∃ f ∈ F, atMark f z S = 0 := by
  classical
  let _ : StrongNormalizationMonoid Jet := UniqueFactorizationMonoid.strongNormalizationMonoid
  let M := normalizedFactors H
  let A := M.toFinset
  let F := A.image fun D => D.coeff 0
  have hD (D : Jet) (hDA : D ∈ A) :
      C (D.coeff 0) = D ∧ Irreducible (D.coeff 0) ∧ 0 < (D.coeff 0).natDegree := by
    have hi := irreducible_of_normalized_factor D (Multiset.mem_toFinset.mp hDA)
    obtain ⟨hv, hs⟩ := hfactor D hi (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hDA))
    exact ordinary_factor hi hv hs
  have hinj : Set.InjOn (fun D : Jet => D.coeff 0) (A : Set Jet) :=
    fun D hDA E hEA he => (hD D hDA).1.symm.trans ((congrArg C he).trans (hD E hEA).1)
  have hprod : C (∏ f ∈ F, f) = ∏ D ∈ A, D := by
    dsimp only [F]
    rw [Finset.prod_image hinj, map_prod]
    exact Finset.prod_congr rfl fun D hDA => (hD D hDA).1
  refine ⟨F, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨D, hDA, rfl⟩ := Finset.mem_image.mp hf
    exact (hD D hDA).2
  · rw [hprod]
    exact (Multiset.toFinset_prod_dvd_prod M).trans (prod_normalizedFactors hH).dvd
  · intro z S hz
    have hM := map_dvd (markEval z S) (prod_normalizedFactors hH).symm.dvd
    change markEval z S H ∣ markEval z S M.prod at hM
    rw [hz, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hM
    obtain ⟨D, hDM, hzero⟩ := hM
    have hDA : D ∈ A := Multiset.mem_toFinset.mpr hDM
    refine ⟨D.coeff 0, Finset.mem_image.mpr ⟨D, hDA, rfl⟩, ?_⟩
    rwa [← (hD D hDA).1, markEval_C] at hzero
theorem markEval_seed (z : K) (S : K[X]) (a : Seeds) :
    markEval z S (seedToJet a) = graphEval z a := by
  change markEval z S (C (C a)) = _
  rw [markEval_C, atMark, eval₂_C]
theorem markEval_fixed (z : K) (S : K[X]) (g : JetPlane) :
    markEval z S (fixedEmbedding g) = fixedAt g S := by
  have hgraph : (graphEval z).comp MvPolynomial.C = RingHom.id FX := by
    ext1 a
    exact MvPolynomial.eval_C _
  have hcoeff : (eval₂RingHom (graphEval z) (atX S)).comp
      (Polynomial.mapRingHom MvPolynomial.C) = evalRingHom (atX S) := by
    apply RingHom.ext
    intro f
    change (f.map MvPolynomial.C).eval₂ (graphEval z) (atX S) = f.eval (atX S)
    rw [eval₂_map, hgraph, eval₂_id]
  change (g.map (Polynomial.mapRingHom MvPolynomial.C)).eval₂
    (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative) = g.eval₂ _ _
  rw [eval₂_map, hcoeff]
theorem Stripped.cover {P : Jet} (A : Stripped P) (z : K) (S : K[X])
    (hP : markEval z S P = 0) :
    graphEval z A.seeds = 0 ∨ fixedAt A.fixed S = 0 ∨ markEval z S A.row = 0 := by
  have h := congrArg (markEval z S) A.factorization
  rw [hP, map_mul, map_mul, markEval_seed, markEval_fixed] at h
  simpa only [mul_eq_zero, or_assoc] using h.symm
end
end K1_14_3_2_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_3_2_1
noncomputable section
open K1_14 K1_14_3 K1_14_3_2 Polynomial
open scoped BigOperators
def moveJet (R : Type*) [CommSemiring R] :
    Polynomial (MvPolynomial (Fin 2) R) ≃ₐ[R] MvPolynomial (Fin 2) (Polynomial R) :=
  (MvPolynomial.optionEquivLeft R (Fin 2)).symm.trans (MvPolynomial.optionEquivRight R (Fin 2))
theorem moveJet_coeff {R : Type*} [CommSemiring R]
    (P : Polynomial (MvPolynomial (Fin 2) R)) (d : Fin 2 →₀ ℕ) (i : ℕ) :
    ((moveJet R P).coeff d).coeff i = (P.coeff i).coeff d := by
  change ((MvPolynomial.optionEquivRight R (Fin 2) ((MvPolynomial.optionEquivLeft R
    (Fin 2)).symm P)).coeff d).coeff i = _
  rw [MvPolynomial.optionEquivRight_coeff_coeff, ← MvPolynomial.optionEquivLeft_coeff_coeff]
  simp
private def seedView : Jet →+* MvPolynomial (Fin 2) JetPlane :=
  (moveJet (Polynomial FX)).toRingHom.comp
    (Polynomial.mapRingHom (moveJet FX).toRingHom)
private theorem seedView_coeff (P : Jet) (d : Fin 2 →₀ ℕ) (v y : ℕ) :
    (((seedView P).coeff d).coeff v).coeff y = ((P.coeff v).coeff y).coeff d := by
  change (((moveJet (Polynomial FX) (P.map (moveJet FX).toRingHom)).coeff d).coeff v).coeff y = _
  rw [moveJet_coeff, Polynomial.coeff_map]
  exact moveJet_coeff (P.coeff v) d y
def seedDegree (P : Jet) : ℕ := (seedView P).totalDegree
theorem seedDegree_le_iff (P : Jet) (u : ℕ) :
    seedDegree P ≤ u ↔ ∀ v y, ((P.coeff v).coeff y).totalDegree ≤ u := by
  simp only [seedDegree, MvPolynomial.totalDegree, Finset.sup_le_iff,
    MvPolynomial.mem_support_iff]
  constructor
  · intro h v y d hd
    apply h d
    intro hz
    exact hd (by rw [← seedView_coeff, hz, Polynomial.coeff_zero, Polynomial.coeff_zero])
  · intro h d hd
    obtain ⟨v, hv⟩ := Polynomial.support_nonempty.mpr hd
    obtain ⟨y, hy⟩ := Polynomial.support_nonempty.mpr (Polynomial.mem_support_iff.mp hv)
    apply h v y d
    rwa [← seedView_coeff, ← Polynomial.mem_support_iff]
theorem seedDegree_mul {P Q : Jet} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    seedDegree (P * Q) = seedDegree P + seedDegree Q := by
  have hi : Function.Injective seedView :=
    (moveJet (Polynomial FX)).injective.comp (Polynomial.map_injective _ (moveJet FX).injective)
  have hP' : seedView P ≠ 0 := by simpa only [map_zero] using hi.ne hP
  have hQ' : seedView Q ≠ 0 := by simpa only [map_zero] using hi.ne hQ
  unfold seedDegree
  rw [map_mul, MvPolynomial.totalDegree_mul_of_isDomain hP' hQ']
theorem rowCaps_iff (P : Jet) (s : Shape) :
    RowCaps P s ↔ Bivariate.totalDegree P ≤ s.B ∧ P.natDegree ≤ s.J ∧ seedDegree P ≤ s.U := by
  constructor
  · intro h
    refine ⟨?_, ?_, (seedDegree_le_iff P s.U).mpr ?_⟩
    · apply Finset.sup_le
      intro v hv
      exact (h v _ (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hv))).1
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro v hv
      by_contra hn
      exact (not_le_of_gt hv) (h v _ (leadingCoeff_ne_zero.mpr hn)).2.1
    · intro v y
      by_cases hn : (P.coeff v).coeff y = 0
      · simp [hn]
      · exact (h v y hn).2.2
  · rintro ⟨hb, hj, hu⟩ v y h
    have hv : P.coeff v ≠ 0 := fun hz => h (by simp [hz])
    refine ⟨?_, (le_natDegree_of_ne_zero hv).trans hj, (seedDegree_le_iff P s.U).mp hu v y⟩
    exact (Nat.add_le_add_right (le_natDegree_of_ne_zero h) v).trans
      ((Bivariate.coeff_totalDegree_le P (mem_support_iff.mpr hv)).trans hb)
theorem rowCaps_of_dvd {P Q : Jet} {s : Shape} (hP : P ≠ 0)
    (h : RowCaps P s) (hd : Q ∣ P) : RowCaps Q s := by
  obtain ⟨R, rfl⟩ := hd
  obtain ⟨hb, hj, hu⟩ := (rowCaps_iff _ _).mp h
  rw [Bivariate.totalDegree_mul (left_ne_zero_of_mul hP) (right_ne_zero_of_mul hP)] at hb
  rw [Polynomial.natDegree_mul (left_ne_zero_of_mul hP) (right_ne_zero_of_mul hP)] at hj
  rw [seedDegree_mul (left_ne_zero_of_mul hP) (right_ne_zero_of_mul hP)] at hu
  exact (rowCaps_iff _ _).mpr ⟨by omega, by omega, by omega⟩
theorem seedDegree_C (f : Equation) : seedDegree (C f) = ordinarySeedDegree f := by
  apply le_antisymm
  · apply (seedDegree_le_iff _ _).mpr
    intro v y
    by_cases hv : v = 0
    · subst v
      rw [coeff_C_zero]
      by_cases hy : f.coeff y = 0
      · simp [hy]
      · exact Finset.le_sup (f := fun i => (f.coeff i).totalDegree) (mem_support_iff.mpr hy)
    · simp [coeff_C, hv]
  · apply Finset.sup_le
    intro y _
    simpa only [coeff_C_zero] using (seedDegree_le_iff (C f) _).mp le_rfl 0 y
theorem ordinarySeedDegree_mul {f g : Equation} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordinarySeedDegree (f * g) = ordinarySeedDegree f + ordinarySeedDegree g := by
  simp only [← seedDegree_C, map_mul]
  exact seedDegree_mul (C_ne_zero.mpr hf) (C_ne_zero.mpr hg)
theorem ordinarySeedDegree_prod (F : Finset Equation) (hF : ∀ f ∈ F, f ≠ 0) :
    ordinarySeedDegree (∏ f ∈ F, f) = ∑ f ∈ F, ordinarySeedDegree f := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, ordinarySeedDegree]
    change (C (1 : Seeds)).support.sup (fun i => ((C (1 : Seeds)).coeff i).totalDegree) = 0
    rw [support_C (one_ne_zero : (1 : Seeds) ≠ 0), Finset.sup_singleton, coeff_C_zero,
      MvPolynomial.totalDegree_one]
  | @insert f F hf ih =>
    have hrest : ∀ g ∈ F, g ≠ 0 := fun g hg => hF g (Finset.mem_insert_of_mem hg)
    rw [Finset.prod_insert hf, Finset.sum_insert hf,
      ordinarySeedDegree_mul (hF f (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr hrest), ih hrest]
end
end K1_14_3_2_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 700000
namespace K1_14_3R_2
noncomputable section
open K1_14 K1_14_3_2 Polynomial UniqueFactorizationMonoid
open scoped Classical BigOperators
theorem seedDegree_one : ordinarySeedDegree 1 = 0 := by
  simpa using K1_14_3_2_1.ordinarySeedDegree_prod ∅ (by simp)
private theorem seedDegree_prod {α : Type*} (F : Finset α) (f : α → Equation)
    (hn : ∀ x ∈ F, f x ≠ 0) :
    ordinarySeedDegree (∏ x ∈ F, f x) = ∑ x ∈ F, ordinarySeedDegree (f x) := by
  induction F using Finset.induction_on with
  | empty => simp [seedDegree_one]
  | insert a F ha ih =>
    have hF : ∀ x ∈ F, f x ≠ 0 := fun x hx => hn x (Finset.mem_insert_of_mem hx)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, K1_14_3_2_1.ordinarySeedDegree_mul
      (hn a (Finset.mem_insert_self _ _)) (Finset.prod_ne_zero_iff.mpr hF), ih hF]
private theorem seedDegree_pow {f : Equation} (hf : f ≠ 0) (r : ℕ) :
    ordinarySeedDegree (f ^ r) = r * ordinarySeedDegree f := by
  induction r with
  | zero => simp [seedDegree_one]
  | succ r ih =>
    rw [pow_succ, K1_14_3_2_1.ordinarySeedDegree_mul (pow_ne_zero _ hf) hf, ih, Nat.succ_mul]
theorem factor_powers_dvd {R : Type*} [CommMonoidWithZero R]
    [UniqueFactorizationMonoid R] [NormalizationMonoid R] {H : R} {r : ℕ}
    (F : Finset R) (hF : ∀ f ∈ F, f ∈ normalizedFactors H ∧ f ^ r ∣ H) :
    (∏ f ∈ F, f ^ r) ∣ H := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro f hf g hg hne
    change IsRelPrime (f ^ r) (g ^ r)
    apply IsRelPrime.pow_left
    apply IsRelPrime.pow_right
    have hi := irreducible_of_normalized_factor f (hF f hf).1
    exact hi.isRelPrime_iff_not_dvd.mpr fun hd =>
      hne (normalizedFactors_eq_of_dvd H f (hF f hf).1 g (hF g hg).1 hd)
  · exact fun f hf => (hF f hf).2
theorem highFactors (H : Equation) (r : ℕ) (hH : H ≠ 0) (hr : 0 < r) :
    ∃ fs : Finset Equation,
      (∀ f ∈ fs, Irreducible f ∧ 0 < f.natDegree ∧ f ^ r ∣ H) ∧
      (∀ f : Equation, Irreducible f → 0 < f.natDegree → f ^ r ∣ H →
        ∃ g ∈ fs, f ∣ g) ∧
      r * (∑ f ∈ fs, f.natDegree) ≤ H.natDegree ∧
      r * (∑ f ∈ fs, ordinarySeedDegree f) ≤ ordinarySeedDegree H := by
  let : StrongNormalizationMonoid Equation := UniqueFactorizationMonoid.strongNormalizationMonoid
  let fs := (normalizedFactors H).toFinset.filter fun f => 0 < f.natDegree ∧ f ^ r ∣ H
  have hmem (f : Equation) (hf : f ∈ fs) : f ∈ normalizedFactors H :=
    Multiset.mem_toFinset.mp (Finset.mem_filter.mp hf).1
  have hp (f : Equation) (hf : f ∈ fs) : Irreducible f ∧ 0 < f.natDegree ∧ f ^ r ∣ H :=
    ⟨irreducible_of_normalized_factor f (hmem f hf), (Finset.mem_filter.mp hf).2⟩
  have hcover (f : Equation) (hi : Irreducible f) (hd : 0 < f.natDegree) (hpow : f ^ r ∣ H) :
      ∃ g ∈ fs, f ∣ g := by
    obtain ⟨g, hg, hassoc⟩ :=
      exists_mem_normalizedFactors_of_dvd hH hi ((dvd_pow_self _ hr.ne').trans hpow)
    have hg0 := ne_zero_of_mem_normalizedFactors hg
    have hdeg := (natDegree_le_of_dvd hassoc.dvd hg0)
    have hdiv := (hassoc.symm.pow_pow (n := r)).dvd.trans hpow
    exact ⟨g, Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hg, hd.trans_le hdeg, hdiv⟩,
      hassoc.dvd⟩
  let A := ∏ f ∈ fs, f ^ r
  have hA : A ∣ H := factor_powers_dvd fs (fun f hf => ⟨hmem f hf, (hp f hf).2.2⟩)
  have hne (f : Equation) (hf : f ∈ fs) : f ^ r ≠ 0 := pow_ne_zero _ (hp f hf).1.ne_zero
  refine ⟨fs, hp, hcover, ?_, ?_⟩
  · calc
      r * (∑ f ∈ fs, f.natDegree) = A.natDegree := by
        rw [natDegree_prod fs (fun f => f ^ r) hne, Finset.mul_sum]
        simp_rw [natDegree_pow]
      _ ≤ H.natDegree := natDegree_le_of_dvd hA hH
  · have hd : ordinarySeedDegree A ≤ ordinarySeedDegree H := by
      obtain ⟨B, he⟩ := hA
      rw [he, K1_14_3_2_1.ordinarySeedDegree_mul
        (fun hz => hH (by simp [he, hz])) (fun hz => hH (by simp [he, hz]))]
      exact Nat.le_add_right _ _
    calc
      r * (∑ f ∈ fs, ordinarySeedDegree f) = ordinarySeedDegree A := by
        rw [seedDegree_prod fs (fun f => f ^ r) hne, Finset.mul_sum]
        exact Finset.sum_congr rfl fun f hf => (seedDegree_pow (hp f hf).1.ne_zero r).symm
      _ ≤ ordinarySeedDegree H := hd
end
end K1_14_3R_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxRecDepth 3000
set_option maxHeartbeats 850000
namespace K1_14_3R_2
noncomputable section
open K1_14 K1_14_3 K1_14_3_2 Polynomial UniqueFactorizationMonoid
open scoped Classical
theorem factor_product (fs : Multiset Jet)
    (hf : ∀ D ∈ fs, D ∈ Set.range fixedEmbedding ∨ D ∈ Set.range (C : Equation →+* Jet)) :
    ∃ G : JetPlane, ∃ H : Equation, fs.prod = fixedEmbedding G * C H := by
  induction fs using Multiset.induction_on with
  | empty => exact ⟨1, 1, by simp⟩
  | cons D ds ih =>
    obtain ⟨G, H, he⟩ := ih (fun E hE => hf E (Multiset.mem_cons_of_mem hE))
    obtain (⟨F, rfl⟩ | ⟨f, rfl⟩) := hf D (Multiset.mem_cons_self _ _)
    · exact ⟨F * G, H, by rw [Multiset.prod_cons, he, map_mul, mul_assoc]⟩
    · exact ⟨G, f * H, by rw [Multiset.prod_cons, he, map_mul, mul_left_comm]⟩
theorem fullGcd (P Q : Jet) (s t : Shape) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hPs : RowCaps P s) (hQs : RowCaps Q t) (hno : NoMovingCommon P Q) :
    Nonempty (FullGcd P Q s t) := by
  obtain ⟨P₀, Q₀, D, hrel, hPD, hQD⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors P hP Q
  have hDP : D ∣ P := ⟨P₀, hPD.symm⟩
  have hDQ : D ∣ Q := ⟨Q₀, hQD.symm⟩
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hP hDP
  let : StrongNormalizationMonoid Jet := UniqueFactorizationMonoid.strongNormalizationMonoid
  have hclass (E : Jet) (hE : E ∈ normalizedFactors D) :
      E ∈ Set.range fixedEmbedding ∨ E ∈ Set.range (C : Equation →+* Jet) := by
    by_cases hdeg : E.natDegree = 0
    · exact Or.inr ⟨E.coeff 0, (eq_C_of_natDegree_eq_zero hdeg).symm⟩
    · have hdiv := dvd_of_mem_normalizedFactors hE
      exact Or.inl (hno E (irreducible_of_normalized_factor E hE)
        (hdiv.trans hDP) (hdiv.trans hDQ) (Nat.pos_of_ne_zero hdeg))
  obtain ⟨G, H, hprod⟩ := factor_product (normalizedFactors D) hclass
  have hAssoc : Associated (fixedEmbedding G * C H) D := hprod ▸ prod_normalizedFactors hD
  let W := fixedEmbedding G * C H
  have hW : W ≠ 0 := ne_zero_of_dvd_ne_zero hD hAssoc.dvd
  have hG : G ≠ 0 := by
    intro he
    exact hW (by simp [W, he])
  have hH : H ≠ 0 := by
    intro he
    exact hW (by simp [W, he])
  obtain ⟨u, hu⟩ := hAssoc
  let A := (u : Jet) * P₀
  let B := (u : Jet) * Q₀
  have hA : P = W * A := by
    rw [← hPD, ← hu]
    dsimp only [W, A]
    ac_rfl
  have hB : Q = W * B := by
    rw [← hQD, ← hu]
    dsimp only [W, B]
    ac_rfl
  have hAd : A ∣ P := ⟨W, hA.trans (mul_comm _ _)⟩
  have hBd : B ∣ Q := ⟨W, hB.trans (mul_comm _ _)⟩
  have hAH : RowCaps (C H) s := K1_14_3_2_1.rowCaps_of_dvd hP hPs
    ((dvd_mul_left _ _).trans (show W ∣ P from ⟨A, hA⟩))
  have hOrdY : H.natDegree ≤ s.B := by
    have hCoeff := leadingCoeff_ne_zero.mpr hH
    simpa only [coeff_C_zero, Nat.add_zero, coeff_natDegree] using
      (hAH 0 H.natDegree (by simpa only [coeff_C_zero, coeff_natDegree] using hCoeff)).1
  have hOrdU : ordinarySeedDegree H ≤ s.U := by
    apply Finset.sup_le
    intro y hy
    simpa only [coeff_C_zero] using
      (hAH 0 y (by simpa only [coeff_C_zero] using Polynomial.mem_support_iff.mp hy)).2.2
  refine ⟨⟨G, H, A, B, hG, hH, ?_, ?_, ?_, hOrdY, hOrdU, ?_, ?_⟩⟩
  · simpa only [W, mul_assoc] using hA
  · simpa only [W, mul_assoc] using hB
  · refine ⟨ne_zero_of_dvd_ne_zero hP hAd, ne_zero_of_dvd_ne_zero hQ hBd, ?_⟩
    intro E hi hEA hEB
    exact hi.not_isUnit (hrel (u.isUnit.dvd_mul_left.mp hEA) (u.isUnit.dvd_mul_left.mp hEB))
  · exact K1_14_3_2_1.rowCaps_of_dvd hP hPs hAd
  · exact K1_14_3_2_1.rowCaps_of_dvd hQ hQs hBd
end
end K1_14_3R_2
end
section
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
namespace K1_14_3R_2
noncomputable section
open K1 K1_14 K1_14_3 K1_14_3_2 K1_14_3R Polynomial
open scoped Classical BigOperators
def c1 : Prop :=
  ∀ (G : JetPlane) (H : Equation) (P : Jet) (q : Surface) (m r : ℕ),
    G ≠ 0 → H ≠ 0 → H.natDegree < p → Parent q →
    0 < r → r ≤ m → ¬ HighOn H r q →
    OrderAt q (fixedEmbedding G * (C H * P)) m →
    OrderAt q P (m + 1 - r)
def c2 : Prop :=
  ∀ (P Q : Jet) (q : Surface) (n : ℕ),
    ProperPair P Q → Parent q → 0 < n → OrderAt q P n → OrderAt q Q n →
    P ∈ q.asIdeal ∧ Q ∈ q.asIdeal ∧ (↑(n ^ 2 : ℕ) : ℕ∞) ≤ localLength P Q q
def c3 : Prop :=
  ∀ (P Q : Jet) (qs : Finset Surface) (k : Fin 3) (d : ℕ),
    ProperPair P Q → 0 < d → ComponentsOn P Q qs →
    (∀ q ∈ qs, (d : ℕ∞) ≤ localLength P Q q) →
    Module.Finite SectionField (SectionJet ⧸ slicedIdeal (pairIdeal P Q) (countedSlice k)) →
    (d : ℚ) * mass qs (countedSlice k) ≤
      (Module.finrank SectionField (SectionJet ⧸ slicedIdeal (pairIdeal P Q) (countedSlice k)) : ℚ)
def c4 : Prop :=
  ∀ (P Q : Jet) (s t : Shape) (k : Fin 3),
    ProperPair P Q → s.J ≤ s.B → t.J ≤ t.B → RowCaps P s → RowCaps Q t →
    Module.Finite SectionField (SectionJet ⧸ slicedIdeal (pairIdeal P Q) (countedSlice k)) ∧
      Module.finrank SectionField (SectionJet ⧸ slicedIdeal (pairIdeal P Q) (countedSlice k)) ≤
        pairCap s t k
private def threshold (i : Fin 4) (k : Fin 3) : ℕ :=
  (![![1, 1, 1], ![1, 1, 2], ![1, 1, 3], ![2, 2, 6]] : Fin 4 → Fin 3 → ℕ) i k
private def stageCap (i : Fin 4) (k : Fin 3) : ℚ :=
  ![seedMassCap i, ordinateMassCap i, mixedMassCap i] k
def graphCap (u b : ℚ) (k : Fin 3) : ℚ :=
  ![b, u, 2 * u * b] k
theorem threshold_range (i : Fin 4) (k : Fin 3) :
    0 < threshold i k ∧ threshold i k ≤ reserve i + 1 := by
  fin_cases i <;> fin_cases k <;> decide
theorem stage_arithmetic (i : Fin 4) (k : Fin 3) :
    let r := threshold i k
    let s := cheapShape i
    let t := layeredShape i
    let n := reserve i + 1 + 1 - r
    graphCap ((s.U : ℚ) / r) ((s.B : ℚ) / r) k + (pairCap s t k : ℚ) / (n ^ 2 : ℕ) =
      stageCap i k := by
  fin_cases i <;> fin_cases k <;>
    norm_num [threshold, cheapShape, layeredShape, reserve, graphCap, pairCap, stageCap,
      seedMassCap, ordinateMassCap, mixedMassCap]
theorem mass_le_biUnion_sum {α : Type*} (fs : Finset α) (T : α → Finset Surface)
    (k : Slice) : mass (fs.biUnion T) k ≤ ∑ f ∈ fs, mass (T f) k := by
  induction fs using Finset.induction_on with
  | empty => simp [mass]
  | insert f fs hf ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hf]
    have hu : mass (T f ∪ fs.biUnion T) k + mass (T f ∩ fs.biUnion T) k =
        mass (T f) k + mass (fs.biUnion T) k :=
      Finset.sum_union_inter
    have hn : 0 ≤ mass (T f ∩ fs.biUnion T) k :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    linarith
private theorem mass_mono {S T : Finset Surface} (h : S ⊆ T) (k : Slice) :
    mass S k ≤ mass T k :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => Nat.cast_nonneg _
theorem sum_graph_cap (fs : Finset Equation) (k : Fin 3)
    (u b : ℚ) (hu : (∑ f ∈ fs, (ordinarySeedDegree f : ℚ)) ≤ u)
    (hb : (∑ f ∈ fs, (f.natDegree : ℚ)) ≤ b) :
    (∑ f ∈ fs, graphCap (ordinarySeedDegree f) f.natDegree k) ≤ graphCap u b k := by
  fin_cases k
  · simpa [graphCap] using hb
  · simpa [graphCap] using hu
  · have hu0 : 0 ≤ u := (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _).trans hu
    change (∑ f ∈ fs, 2 * (ordinarySeedDegree f : ℚ) * f.natDegree) ≤ 2 * u * b
    calc
      (∑ f ∈ fs, 2 * (ordinarySeedDegree f : ℚ) * f.natDegree) ≤
          ∑ f ∈ fs, 2 * (ordinarySeedDegree f : ℚ) * b := by
        apply Finset.sum_le_sum
        intro f hf
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (Finset.single_le_sum (f := fun g => (g.natDegree : ℚ))
          (fun _ _ => Nat.cast_nonneg _) hf).trans hb
      _ = 2 * (∑ f ∈ fs, (ordinarySeedDegree f : ℚ)) * b := by
        rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ 2 * u * b := by
        have hb0 : 0 ≤ b := (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _).trans hb
        gcongr
theorem mass_split (H : Equation) (r : ℕ) (qs : Finset Surface) (k : Slice) :
    mass (qs.filter (HighOn H r)) k + mass (qs.filter fun q => ¬ HighOn H r q) k =
      mass qs k :=
  Finset.sum_filter_add_sum_filter_not _ _ _
theorem weighted_mass (hslice : c3) (hbezout : c4)
    (P Q : Jet) (s t : Shape) (qs : Finset Surface) (k : Fin 3) (d : ℕ)
    (hpair : ProperPair P Q) (hsj : s.J ≤ s.B) (htj : t.J ≤ t.B)
    (hs : RowCaps P s) (ht : RowCaps Q t) (hd : 0 < d)
    (hqs : ComponentsOn P Q qs)
    (hlen : ∀ q ∈ qs, (d : ℕ∞) ≤ localLength P Q q) :
    (d : ℚ) * mass qs (countedSlice k) ≤ (pairCap s t k : ℚ) := by
  obtain ⟨hf, hcap⟩ := hbezout P Q s t k hpair hsj htj hs ht
  exact (hslice P Q qs k d hpair hd hqs hlen hf).trans (by exact_mod_cast hcap)
theorem ordinary_graph_mass (hslice : c3) (hbezout : c4)
    (f : Equation) (g : ClearedEquation) (a : L[X]) (qs : Finset Surface)
    (hpos : 0 < f.natDegree) (ha : IsClearing f g a)
    (hpair : ProperPair (C f) (chainCutter g)) (k : Fin 3)
    (hqs : ComponentsOn (C f) (chainCutter g) qs) :
    mass qs (countedSlice k) ≤ graphCap (ordinarySeedDegree f) f.natDegree k := by
  let u := ordinarySeedDegree f
  let s : Shape := ⟨0, f.natDegree, 0, u⟩
  let t : Shape := ⟨0, f.natDegree, 1, u⟩
  have hf : RowCaps (C f) s := by
    intro v y h
    cases v with
    | zero =>
      rw [coeff_C_zero] at h ⊢
      exact ⟨by simpa using le_natDegree_of_ne_zero h, le_rfl,
        Finset.le_sup (f := fun j => (f.coeff j).totalDegree) (Polynomial.mem_support_iff.mpr h)⟩
    | succ v => simp [coeff_C_succ] at h
  have ht : RowCaps (C f) t := fun v y h => by
    obtain ⟨hb, hj, hu⟩ := hf v y h
    exact ⟨hb, hj.trans (show 0 ≤ 1 from Nat.zero_le _), hu⟩
  have hg := chainCutter_caps_of_dvd hpair.left_ne ht (le_refl 1) dvd_rfl ha
  have hbudget : (pairCap s t k : ℚ) = graphCap u f.natDegree k := by
    fin_cases k <;> simp [s, t, pairCap, graphCap] <;> ring
  simpa only [Nat.cast_one, one_mul, hbudget] using
    weighted_mass hslice hbezout (C f) (chainCutter g) s t qs k 1 hpair
      (Nat.zero_le _) hpos hf hg Nat.one_pos hqs
      (fun q hq => localLength_one (hqs q hq).2.1 (hqs q hq).2.2)
theorem high_mass (h3 : c3) (h4 : c4) (i : Fin 4) {P Q : Jet}
    (D : FullGcd P Q (cheapShape i) (layeredShape i))
    (qs : Finset Surface) (hg : OrdinaryGraphs P Q qs)
    (hp : ∀ q ∈ qs, Parent q) (r : ℕ) (hr : 0 < r) (k : Fin 3) :
    mass (qs.filter (HighOn D.ordinary r)) (countedSlice k) ≤
      graphCap (((cheapShape i).U : ℚ) / r) (((cheapShape i).B : ℚ) / r) k := by
  obtain ⟨fs, hf, hc, hb, hu⟩ := highFactors D.ordinary r D.ordinary_ne hr
  let T := fun f : Equation => qs.filter fun q => (C f : Jet) ∈ q.asIdeal
  have hcover : qs.filter (HighOn D.ordinary r) ⊆ fs.biUnion T := by
    intro q hq
    obtain ⟨hm, f, hi, hd, hdiv, hmem⟩ := Finset.mem_filter.mp hq
    obtain ⟨g, hg, v, hv⟩ := hc f hi hd hdiv
    rw [Finset.mem_biUnion]
    refine ⟨g, hg, Finset.mem_filter.mpr ⟨hm, ?_⟩⟩
    rw [hv, map_mul]
    exact q.asIdeal.mul_mem_right _ hmem
  have hDvdP : (C D.ordinary : Jet) ∣ P := by
    exact ⟨fixedEmbedding D.fixed * D.left, D.left_factor.trans (mul_left_comm _ _ _)⟩
  have hDvdQ : (C D.ordinary : Jet) ∣ Q := by
    exact ⟨fixedEmbedding D.fixed * D.right, D.right_factor.trans (mul_left_comm _ _ _)⟩
  have hBp : (cheapShape i).B < p := by fin_cases i <;> decide
  have hrc : (0 : ℚ) < r := by exact_mod_cast hr
  have hBoundB : (∑ f ∈ fs, (f.natDegree : ℚ)) ≤ ((cheapShape i).B : ℚ) / r := by
    apply (le_div_iff₀ hrc).mpr
    rw [mul_comm, ← Nat.cast_sum, ← Nat.cast_mul]
    exact_mod_cast hb.trans D.ordinary_y
  have hBoundU : (∑ f ∈ fs, (ordinarySeedDegree f : ℚ)) ≤ ((cheapShape i).U : ℚ) / r := by
    apply (le_div_iff₀ hrc).mpr
    rw [mul_comm, ← Nat.cast_sum, ← Nat.cast_mul]
    exact_mod_cast hu.trans D.ordinary_seed
  calc
    _ ≤ mass (fs.biUnion T) (countedSlice k) := mass_mono hcover _
    _ ≤ ∑ f ∈ fs, mass (T f) (countedSlice k) := mass_le_biUnion_sum fs T _
    _ ≤ ∑ f ∈ fs, graphCap (ordinarySeedDegree f) f.natDegree k := by
      apply Finset.sum_le_sum
      intro f hmem
      obtain ⟨hi, hpos, hpow⟩ := hf f hmem
      have hdiv : f ∣ D.ordinary := (dvd_pow_self _ hr.ne').trans hpow
      have hdeg := (natDegree_le_of_dvd hdiv D.ordinary_ne).trans_lt (D.ordinary_y.trans_lt hBp)
      have hdiv' := map_dvd (C : Equation →+* Jet) hdiv
      obtain ⟨g, a, ha, hproper, hmemGraph⟩ :=
        hg f hi hpos hdeg (hdiv'.trans hDvdP) (hdiv'.trans hDvdQ)
      apply ordinary_graph_mass h3 h4 f g a (T f) hpos ha hproper k
      intro q hq
      have h := Finset.mem_filter.mp hq
      exact ⟨(hp q h.1).height_two, h.2, hmemGraph q h.1 h.2⟩
    _ ≤ _ := sum_graph_cap fs k _ _ hBoundU hBoundB
theorem residual_mass (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (i : Fin 4)
    {P Q : Jet} (D : FullGcd P Q (cheapShape i) (layeredShape i))
    (qs : Finset Surface) (m r : ℕ) (hr : 0 < r) (hrm : r ≤ m)
    (hp : ∀ q ∈ qs, Parent q ∧ OrderAt q P m ∧ OrderAt q Q m) (k : Fin 3) :
    mass (qs.filter fun q => ¬ HighOn D.ordinary r q) (countedSlice k) ≤
      (pairCap (cheapShape i) (layeredShape i) k : ℚ) / ((m + 1 - r) ^ 2 : ℕ) := by
  let n := m + 1 - r
  let S := qs.filter fun q => ¬ HighOn D.ordinary r q
  have hn : 0 < n := by dsimp [n]; omega
  have hd : 0 < n ^ 2 := pow_pos hn _
  have hBp : (cheapShape i).B < p := by fin_cases i <;> decide
  have hHp := D.ordinary_y.trans_lt hBp
  have hparts : ∀ q ∈ S, q.asIdeal.height = 2 ∧ D.left ∈ q.asIdeal ∧
      D.right ∈ q.asIdeal ∧ (↑(n ^ 2 : ℕ) : ℕ∞) ≤ localLength D.left D.right q := by
    intro q hq
    obtain ⟨hm, hlow⟩ := Finset.mem_filter.mp hq
    obtain ⟨hPar, hP, hQ⟩ := hp q hm
    rw [D.left_factor] at hP
    rw [D.right_factor] at hQ
    exact ⟨hPar.height_two, h2 D.left D.right q n D.proper hPar hn
      (h1 D.fixed D.ordinary D.left q m r D.fixed_ne D.ordinary_ne hHp hPar hr hrm hlow hP)
      (h1 D.fixed D.ordinary D.right q m r D.fixed_ne D.ordinary_ne hHp hPar hr hrm hlow hQ)⟩
  have hcJ : (cheapShape i).J ≤ (cheapShape i).B := by fin_cases i <;> decide
  have htJ : (layeredShape i).J ≤ (layeredShape i).B := by fin_cases i <;> decide
  have hlength := weighted_mass h3 h4 D.left D.right (cheapShape i) (layeredShape i) S k
    (n ^ 2) D.proper hcJ htJ D.left_caps D.right_caps hd (by
      intro q hq
      obtain ⟨hh, hP, hQ, _⟩ := hparts q hq
      exact ⟨hh, hP, hQ⟩) (fun q hq => (hparts q hq).2.2.2)
  have hdc : (0 : ℚ) < (n ^ 2 : ℕ) := by exact_mod_cast hd
  exact (le_div_iff₀ hdc).mpr (by simpa only [mul_comm] using hlength)
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) : K1_14_3R.c2 := by
  intro i P Q hP hQ hPs hQs hno qs hgraphs hpass
  obtain ⟨D⟩ := fullGcd P Q (cheapShape i) (layeredShape i) hP hQ hPs hQs hno
  have hstage (k : Fin 3) : mass qs (countedSlice k) ≤ stageCap i k := by
    let r := threshold i k
    obtain ⟨hr, hrm⟩ := threshold_range i k
    rw [← mass_split D.ordinary r qs (countedSlice k), ← stage_arithmetic i k]
    exact add_le_add
      (high_mass h3 h4 i D qs hgraphs (fun q hq => (hpass q hq).1) r hr k)
      (residual_mass h1 h2 h3 h4 i D qs (reserve i + 1) r hr hrm hpass k)
  exact ⟨hstage 0, hstage 1, hstage 2⟩
end
end K1_14_3R_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_4
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 MvPolynomial
open RingTheory.Sequence
open scoped Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem freshCoeff_injective : Function.Injective freshCoeff :=
  (IsFractionRing.injective GeometricX[X] FreshField).comp
    (Polynomial.map_injective _ (RingHom.injective (algebraMap Geom GeometricX)))
theorem freshRow_ne_zero {f : Row 3} (hf : f ≠ 0) : freshRow f ≠ 0 := by
  simpa only [freshRow, Ne, map_eq_zero_iff _ (map_injective _ freshCoeff_injective)] using hf
theorem freshRow_degree_le (f : Row 3) : (freshRow f).totalDegree ≤ f.totalDegree :=
  Finset.sup_mono (support_map_subset freshCoeff f)
private theorem quotient_regular_iff {R : Type*} [CommRing R] (a b : R) :
    IsSMulRegular (QuotSMulTop a R) b ↔
      IsLeftRegular (Ideal.Quotient.mk (Ideal.span {a}) b) := by
  let e : QuotSMulTop a R ≃ₗ[R] R ⧸ (Ideal.span {a} : Ideal R) :=
    Submodule.quotEquivOfEq _ _ (by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map]
      change ((Ideal.span {a}).map (RingHom.id R) : Ideal R) = Ideal.span {a}
      rw [Ideal.map_id])
  exact e.isSMulRegular_congr b
private theorem flat_of_injective {A B : Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDomain B] (φ : A →+* B) (hφ : Function.Injective φ) : φ.Flat := by
  let : Algebra A B := φ.toAlgebra
  change Module.Flat A B
  have : Module.IsTorsionFree A B :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hφ
  infer_instance
private theorem regular_cut_of_flat_map {A B σ : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Flat) {f g : MvPolynomial σ A}
    (hf : IsSMulRegular (MvPolynomial σ A) f)
    (hg : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {f}) g)) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {MvPolynomial.map φ f}) (MvPolynomial.map φ g)) := by
  let : Algebra A B := φ.toAlgebra
  have : Module.Flat A B := hφ
  have hbase : IsBaseChange (MvPolynomial σ A)
      (IsScalarTower.toAlgHom A B (MvPolynomial σ B)).toLinearMap :=
    Algebra.IsPushout.out
  have : Module.Flat (MvPolynomial σ A) (MvPolynomial σ B) :=
    Module.Flat.isBaseChange (R := A) (S := MvPolynomial σ A) (M := B)
      (N := MvPolynomial σ B) hbase
  have hseq : IsWeaklyRegular (MvPolynomial σ A) [f, g] := by
    rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff, quotient_regular_iff]
    exact ⟨hf, hg⟩
  have h := hseq.of_flat (S := MvPolynomial σ B)
  change IsWeaklyRegular (MvPolynomial σ B) [MvPolynomial.map φ f, MvPolynomial.map φ g] at h
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff, quotient_regular_iff] at h
  exact h.2
theorem freshCut_regular {f : Row 3} (hf : Irreducible f) (hw : ¬ Whole f) :
    IsLeftRegular (Ideal.Quotient.mk (freshHypersurface f) (freshRow (oldCut f))) := by
  have hp : (Ideal.span {f} : Ideal (Row 3)).IsPrime :=
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf.prime
  have hc : oldCut f ∉ (Ideal.span {f} : Ideal (Row 3)) :=
    fun h => hw (Ideal.mem_span_singleton.mp h)
  apply regular_cut_of_flat_map freshCoeff (flat_of_injective freshCoeff freshCoeff_injective)
  · exact fun _ _ h => mul_left_cancel₀ hf.ne_zero h
  · exact fun _ _ h => mul_left_cancel₀ (mt Ideal.Quotient.eq_zero_iff_mem.mp hc) h
end
end K1_13_5_4_4
end
section
set_option autoImplicit false
namespace K1_13_5_4_4
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 MvPolynomial Finset
open scoped BigOperators
private theorem curve_minimal {J Q : FreshJetIdeal} (hQ : Q.IsPrime) (hJQ : J ≤ Q)
    (hJdim : (affineHilbertPolynomial J).natDegree ≤ 1)
    (hQdim : (affineHilbertPolynomial Q).natDegree = 1) :
    Q ∈ J.minimalPrimes := by
  let := hQ
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hJQ
  rcases eq_or_lt_of_le hPQ with he | hlt
  · exact he ▸ hP
  · obtain ⟨x, hxQ, hxP⟩ := SetLike.exists_of_lt hlt
    have hdimP := (natDegree_affineHilbertPolynomial_le_of_le hP.le).trans hJdim
    have hle : P ⊔ Ideal.span {x} ≤ Q :=
      sup_le hPQ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxQ))
    have hdrop := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hP.isPrime hxP le_rfl).1
    have hdimQ := natDegree_affineHilbertPolynomial_le_of_le hle
    omega
theorem factor_degree_sum (f : Row 3) (hf : Irreducible f) (hw : ¬ Whole f)
    (T : Finset FreshJetIdeal)
    (hT : ∀ Q ∈ T, Q.IsPrime ∧ freshDivisor f ≤ Q ∧
      (affineHilbertPolynomial Q).natDegree = 1) :
    (∑ Q ∈ T, affineDegree Q) ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
  classical
  by_cases hEmpty : T = ∅
  · rw [hEmpty, sum_empty]
    positivity
  have hPproper : freshHypersurface f ≠ ⊤ := by
    obtain ⟨Q, hQ⟩ := nonempty_iff_ne_empty.mpr hEmpty
    exact ne_top_of_le_ne_top (hT Q hQ).1.ne_top
      (le_sup_left.trans (hT Q hQ).2.1)
  have hPdim : (affineHilbertPolynomial (freshHypersurface f)).natDegree = 2 := by
    have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
      (freshRow_ne_zero hf.ne_zero) hPproper
    rw [Nat.card_fin] at h
    change (affineHilbertPolynomial (freshHypersurface f)).natDegree + 1 = 3 at h
    omega
  have hcut := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    (freshCut_regular hf hw) (freshRow_degree_le (oldCut f))
  rw [hPdim] at hcut
  have hJdim : (affineHilbertPolynomial (freshDivisor f)).natDegree ≤ 1 := hcut.1
  have hsub : T ⊆ (freshDivisor f).minimalPrimesFinset := by
    intro Q hQ
    obtain ⟨hp, hle, hdim⟩ := hT Q hQ
    exact Ideal.mem_minimalPrimesFinset.mpr (curve_minimal hp hle hJdim hdim)
  have hdeg : affineDegree (freshHypersurface f) ≤ (f.totalDegree : ℚ) := by
    rw [freshHypersurface, affineDegree_span_singleton (freshRow_ne_zero hf.ne_zero)]
    exact_mod_cast freshRow_degree_le f
  calc
    (∑ Q ∈ T, affineDegree Q) = ∑ Q ∈ T, (affineHilbertPolynomial Q).coeff 1 := by
      apply sum_congr rfl
      intro Q hQ
      rw [affineDegree, (hT Q hQ).2.2, Polynomial.leadingCoeff, (hT Q hQ).2.2]
      simp
    _ ≤ ∑ Q ∈ (freshDivisor f).minimalPrimesFinset, (affineHilbertPolynomial Q).coeff 1 := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro Q hQ _
      have hle := (Ideal.mem_minimalPrimesFinset.mp hQ).le
      exact Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg
        ((natDegree_affineHilbertPolynomial_le_of_le hle).trans hJdim)
        (eventually_eval_affineHilbertPolynomial_nonneg Q)
    _ ≤ (affineHilbertPolynomial (freshDivisor f)).coeff 1 :=
      sum_coeff_affineHilbertPolynomial_minimalPrimes_le _ hJdim
    _ ≤ ((oldCut f).totalDegree : ℚ) * affineDegree (freshHypersurface f) := by
      simpa [freshDivisor, affineDegree, hPdim, mul_assoc] using hcut.2
    _ ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
      rw [Nat.cast_mul, mul_comm (f.totalDegree : ℚ)]
      exact mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg _)
theorem curve_degree_nat (Q : CoefficientIdeal) (hQ : Q.IsPrime)
    (hdim : (affineHilbertPolynomial Q).natDegree = 1) :
    ∃ d : ℕ, 0 < d ∧ affineDegree Q = (d : ℚ) := by
  let H := affineHilbertPolynomial Q
  have hlin : H = Polynomial.C (H.coeff 0) + Polynomial.C (H.coeff 1) * Polynomial.X := by
    have hH : H.natDegree < 2 := by change (affineHilbertPolynomial Q).natDegree < 2; omega
    simpa [Finset.sum_range_succ] using H.as_sum_range_C_mul_X_pow' hH
  have evalH (u : ℚ) : H.eval u = H.coeff 0 + H.coeff 1 * u := by
    conv_lhs => rw [hlin]
    simp
  obtain ⟨N, hN⟩ := exists_eval_affineHilbertPolynomial Q
  let m := affineHilbertFunction Q (N + 1)
  let n := affineHilbertFunction Q N
  have hdiff : affineDegree Q = (m : ℚ) - (n : ℚ) := by
    rw [affineDegree, hdim, Nat.factorial_one, Nat.cast_one, one_mul, Polynomial.leadingCoeff, hdim]
    dsimp only [m, n]
    rw [← hN (N + 1) (Nat.le_succ _), ← hN N le_rfl]
    change H.coeff 1 = H.eval ((N + 1 : ℕ) : ℚ) - H.eval (N : ℚ)
    rw [evalH, evalH, Nat.cast_add, Nat.cast_one]
    ring
  have hmn : n < m := by
    have hpos := affineDegree_pos hQ.ne_top
    rw [hdiff] at hpos
    exact_mod_cast sub_pos.mp hpos
  exact ⟨m - n, Nat.sub_pos_of_lt hmn, hdiff.trans (Nat.cast_sub hmn.le).symm⟩
end
end K1_13_5_4_4
end
section
set_option autoImplicit false
namespace K1_13_5_4_4
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 MvPolynomial Finset
open scoped BigOperators
def c1 : Prop :=
  ∀ f : Row 3,
    (∀ Q : CoefficientIdeal, ActualSolutionCurve f Q → FreshChart f Q) ∧
      Set.InjOn freshImage {Q : CoefficientIdeal | ActualSolutionCurve f Q}
def c2 : Prop :=
  ∀ Q : CoefficientIdeal, Q.IsPrime →
    (affineHilbertPolynomial Q).natDegree = 1 → (extendIdeal Q).IsPrime →
    FreshBirational Q →
    (affineHilbertPolynomial (freshImage Q)).natDegree = 1 ∧
      affineDegree Q ≤ affineDegree (freshImage Q)
private theorem curve_family_bound (h1 : c1) (h2 : c2) (f : Row 3)
    (hf : Irreducible f) (hw : ¬ Whole f) (C : Finset CoefficientIdeal)
    (hC : ∀ Q ∈ C, ActualSolutionCurve f Q) :
    (∑ Q ∈ C, affineDegree Q) ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
  classical
  have hinj : Set.InjOn freshImage (C : Set CoefficientIdeal) := (h1 f).2.mono hC
  have hcompare (Q : CoefficientIdeal) (hQ : Q ∈ C) :=
    let h := (h1 f).1 Q (hC Q hQ)
    h2 Q (hC Q hQ).prime (hC Q hQ).dimension h.extended_prime h.birational
  calc
    (∑ Q ∈ C, affineDegree Q) ≤ ∑ Q ∈ C, affineDegree (freshImage Q) :=
      sum_le_sum fun Q hQ => (hcompare Q hQ).2
    _ = ∑ P ∈ C.image freshImage, affineDegree P := (sum_image hinj).symm
    _ ≤ ((f.totalDegree * (oldCut f).totalDegree : ℕ) : ℚ) := by
      apply factor_degree_sum f hf hw
      intro P hP
      obtain ⟨Q, hQ, rfl⟩ := mem_image.mp hP
      have h := (h1 f).1 Q (hC Q hQ)
      exact ⟨h.extended_prime.comap freshProjection, h.on_divisor, (hcompare Q hQ).1⟩
private def cutterBound (b : ℕ) : ℕ :=
  1 + (2 * (taylorLength + 1) - 7) * (b - 1)
private theorem cutterBound_mono : Monotone cutterBound := by
  intro a b hab
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hab _)) _
theorem of_children (h1 : c1) (h2 : c2) : K1_13_5_4.c4 := by
  classical
  intro n f hf hcut C hsource
  by_cases hEmpty : C = ∅
  · subst C
    exact ⟨fun _ => 0, by simp, by simp⟩
  obtain ⟨Q₀, hQ₀⟩ := nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨i₀, _⟩ := hsource Q₀ hQ₀
  let pick (Q : CoefficientIdeal) : Fin n :=
    if hQ : Q ∈ C then Classical.choose (hsource Q hQ) else i₀
  have hpick (Q : CoefficientIdeal) (hQ : Q ∈ C) :
      ¬ Whole (f (pick Q)) ∧ ActualSolutionCurve (f (pick Q)) Q := by
    simpa only [pick, dite_eq_left hQ] using Classical.choose_spec (hsource Q hQ)
  let part (i : Fin n) := C.filter fun Q => pick Q = i
  have hlocal (i : Fin n) : (∑ Q ∈ part i, affineDegree Q) ≤
      ((f i).totalDegree * (oldCut (f i)).totalDegree : ℕ) := by
    have hpart (Q : CoefficientIdeal) (hQ : Q ∈ part i) :
        ¬ Whole (f i) ∧ ActualSolutionCurve (f i) Q := by
      obtain ⟨hm, hi⟩ := mem_filter.mp hQ
      simpa only [hi] using hpick Q hm
    by_cases hw : Whole (f i)
    · have he : part i = ∅ := eq_empty_iff_forall_notMem.mpr fun Q hQ => (hpart Q hQ).1 hw
      rw [he, sum_empty]
      positivity
    exact curve_family_bound h1 h2 _ (hf.irreducible i) hw _ fun Q hQ => (hpart Q hQ).2
  have hnat : (∑ i : Fin n, (f i).totalDegree * (oldCut (f i)).totalDegree) ≤ invariantBudget := by
    calc
      _ ≤ ∑ i : Fin n, (f i).totalDegree * cutterBound 120 := by
        apply sum_le_sum
        intro i _
        have hi := (single_le_sum (f := fun j => (f j).totalDegree)
          (fun _ _ => Nat.zero_le _) (mem_univ i)).trans hf.total
        exact Nat.mul_le_mul_left _ ((hcut i).trans (cutterBound_mono hi))
      _ = (∑ i : Fin n, (f i).totalDegree) * cutterBound 120 := by rw [sum_mul]
      _ ≤ invariantBudget := Nat.mul_le_mul_right _ hf.total
  have hsum : (∑ Q ∈ C, affineDegree Q) ≤ (invariantBudget : ℚ) := by
    calc
      _ = ∑ i : Fin n, ∑ Q ∈ part i, affineDegree Q :=
        (sum_fiberwise_of_maps_to (t := (univ : Finset (Fin n)))
          (g := pick) (fun _ _ => mem_univ _) affineDegree).symm
      _ ≤ ∑ i : Fin n, (((f i).totalDegree * (oldCut (f i)).totalDegree : ℕ) : ℚ) :=
        sum_le_sum fun i _ => hlocal i
      _ ≤ (invariantBudget : ℚ) := by exact_mod_cast hnat
  have hex (Q : CoefficientIdeal) : ∃ d : ℕ, Q ∈ C → 0 < d ∧ affineDegree Q = (d : ℚ) := by
    by_cases hQ : Q ∈ C
    · have h := (hpick Q hQ).2
      obtain ⟨d, hd, he⟩ := curve_degree_nat Q h.prime h.dimension
      exact ⟨d, fun _ => ⟨hd, he⟩⟩
    · exact ⟨0, fun h => False.elim (hQ h)⟩
  let d (Q : CoefficientIdeal) := Classical.choose (hex Q)
  have hd (Q : CoefficientIdeal) (hQ : Q ∈ C) : 0 < d Q ∧ affineDegree Q = (d Q : ℚ) :=
    Classical.choose_spec (hex Q) hQ
  refine ⟨d, fun Q hQ => ⟨(hd Q hQ).1, (hd Q hQ).2.le⟩, ?_⟩
  have hcast : (∑ Q ∈ C, (d Q : ℚ)) ≤ (invariantBudget : ℚ) :=
    (sum_congr rfl fun Q hQ => (hd Q hQ).2.symm).trans_le hsum
  exact_mod_cast hcast
end
end K1_13_5_4_4
end
section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 900000
set_option linter.style.haveILetI false
namespace K1_13_5_4_4_2
noncomputable section
open K1_13 K1_13_5_4 K1_13_5_4_4 K1_13_6_3_4 MvPolynomial
open scoped Polynomial
abbrev FreshClosure := AlgebraicClosure FreshField
private def freshEmbedding : GeometricX[X] →+* FreshClosure :=
  (algebraMap FreshField FreshClosure).comp (algebraMap GeometricX[X] FreshField)
private def oldEmbedding : GeometricX →+* FreshClosure := freshEmbedding.comp Polynomial.C
private theorem linear_sum_homogeneous {k σ : Type*} [Field k] [Fintype σ] (c : σ → k) :
    (∑ i : σ, MvPolynomial.C (c i) * MvPolynomial.X i).IsHomogeneous 1 :=
  (homogeneousSubmodule σ k 1).sum_mem fun i _ => isHomogeneous_C_mul_X _ i
theorem jetForm_homogeneous (j : ℕ) : (K1_13_5_5.jetForm freshArgument j).IsHomogeneous 1 :=
  linear_sum_homogeneous fun i : Fin taylorLength =>
    (i.val.choose j : FreshField) * freshArgument ^ (i.val - j)
private theorem eval₂_scale {k K σ : Type*} [Field k] [Field K] [Fintype σ]
    (f : k →+* K) (x : σ → K) (t : K) {p : MvPolynomial σ k} {n : ℕ}
    (hp : p.IsHomogeneous n) : eval₂ f (fun i => t * x i) p = t ^ n * eval₂ f x p := by
  classical
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hd) (hp.coeff_eq_zero h)
  rw [show (∏ i : σ, (t * x i) ^ d i) = t ^ n * ∏ i : σ, x i ^ d i by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      ← Finsupp.degree_eq_sum, hdeg]]
  ring
theorem aeval_scale_zero {k K σ : Type*} [Field k] [Field K] [Algebra k K] [Fintype σ]
    (x : σ → K) (t : K) {p : MvPolynomial σ k} {n : ℕ} (hp : p.IsHomogeneous n)
    (h : aeval x p = 0) : aeval (fun i => t * x i) p = 0 := by
  rw [aeval_def] at h ⊢
  rw [eval₂_scale _ _ _ hp, h, mul_zero]
private theorem map_boundary_generator {k K σ : Type*} [Field k] [Field K]
    (f : k →+* K) (I : Ideal (MvPolynomial σ k)) {p : MvPolynomial σ k} {n : ℕ}
    (hp : p ∈ I) (hn : p.totalDegree ≤ n) :
    MvPolynomial.map f (homogeneousComponent n p) ∈ boundaryIdeal (I.map (MvPolynomial.map f)) := by
  have he : MvPolynomial.map f (homogeneousComponent n p) =
      homogeneousComponent n (MvPolynomial.map f p) := by
    ext d
    by_cases hd : d.degree = n <;>
      simp only [coeff_homogeneousComponent, coeff_map, hd, ite_true, ite_false, map_zero]
  have hd : (MvPolynomial.map f p).totalDegree ≤ p.totalDegree :=
    Finset.sup_mono (support_map_subset f p)
  exact Ideal.subset_span ⟨MvPolynomial.map f p, n, Ideal.mem_map_of_mem _ hp, hd.trans hn, he⟩
private theorem normalize_boundary (Q : CoefficientIdeal) {x : Fin taylorLength → FreshClosure}
    (hx : x ∈ zeroLocus FreshClosure (boundaryIdeal (extendIdeal Q))) {i : Fin taylorLength}
    (hi : x i ≠ 0) :
    letI : Algebra GeometricX FreshClosure := oldEmbedding.toAlgebra
    (fun j => (x i)⁻¹ * x j) ∈ zeroLocus FreshClosure (boundaryChart Q i) := by
  change boundaryChart Q i ≤ RingHom.ker (eval₂Hom oldEmbedding (fun j => (x i)⁻¹ * x j))
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro _ ⟨p, n, hp, hn, rfl⟩
    have he := hx _ (map_boundary_generator (algebraMap GeometricX FreshField) Q hp hn)
    rw [aeval_def, eval₂_map] at he
    change eval₂ oldEmbedding x (homogeneousComponent n p) = 0 at he
    change eval₂ oldEmbedding (fun j => (x i)⁻¹ * x j) (homogeneousComponent n p) = 0
    rw [eval₂_scale oldEmbedding x ((x i)⁻¹) (homogeneousComponent_isHomogeneous ..), he,
      mul_zero]
  · apply Ideal.span_le.mpr
    rintro _ (rfl : _ = MvPolynomial.X i - 1)
    change eval₂ oldEmbedding (fun j => (x i)⁻¹ * x j) (MvPolynomial.X i - 1) = 0
    rw [eval₂_sub, eval₂_X, eval₂_one]
    exact sub_eq_zero.mpr (inv_mul_cancel₀ hi)
private theorem finite_chart_coordinates {k K σ : Type*} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [Finite σ] (J : Ideal (MvPolynomial σ k))
    (hJ : (affineHilbertPolynomial J).natDegree = 0)
    {x : σ → K} (hx : x ∈ zeroLocus K J) (j : σ) : ∃ c : k, algebraMap k K c = x j := by
  letI : Module.Finite k (MvPolynomial σ k ⧸ J) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hJ
  let e : (MvPolynomial σ k ⧸ J) →ₐ[k] K := Ideal.Quotient.liftₐ J (aeval x) hx
  have h : IsIntegral k (x j) := by
    have hJX := (Algebra.IsIntegral.isIntegral (R := k) (Ideal.Quotient.mk J (MvPolynomial.X j))).map e
    change IsIntegral k (aeval x (MvPolynomial.X j)) at hJX
    simpa only [aeval_X] using hJX
  apply h.mem_range_algHom_of_minpoly_splits (K := k) _ (Algebra.ofId k K)
  simpa only [Algebra.algebraMap_self, Polynomial.map_id] using
    IsAlgClosed.splits (minpoly k (x j))
theorem polynomial_sum_ne_zero {k σ : Type*} [Field k] [Fintype σ]
    (d : σ → ℕ) (hd : Function.Injective d) (a : σ → k) {i : σ} (hi : a i ≠ 0) :
    (∑ j : σ, Polynomial.monomial (d j) (a j)) ≠ 0 := by
  classical
  let P : Polynomial k := ∑ j : σ, Polynomial.monomial (d j) (a j)
  have hc : P.coeff (d i) = a i := by
    rw [show P.coeff (d i) = ∑ j : σ, (Polynomial.monomial (d j) (a j)).coeff (d i) from
      map_sum (Polynomial.lcoeff k (d i)) _ _]
    rw [Finset.sum_eq_single i]
    · exact Polynomial.coeff_monomial_same _ _
    · intro j _ hj
      exact Polynomial.coeff_monomial_of_ne _ (fun h => hj (hd h.symm))
    · simp
  intro h
  change P = 0 at h
  exact hi (by rw [← hc, h, Polynomial.coeff_zero])
private theorem fresh_value_ne_zero {a : Fin taylorLength → GeometricX} {i : Fin taylorLength}
    (hi : a i ≠ 0) : aeval (oldEmbedding ∘ a) (K1_13_5_5.jetForm freshArgument 0) ≠ 0 := by
  classical
  have hne : coefficientPolynomial a ≠ 0 :=
    polynomial_sum_ne_zero (fun j : Fin taylorLength => j.val) Fin.val_injective a hi
  have hinj : Function.Injective freshEmbedding :=
    (algebraMap FreshField FreshClosure).injective.comp (IsFractionRing.injective _ _)
  have hval : aeval (oldEmbedding ∘ a) (K1_13_5_5.jetForm freshArgument 0) =
      freshEmbedding (coefficientPolynomial a) := by
    unfold K1_13_5_5.jetForm coefficientPolynomial
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, aeval_C, aeval_X, Nat.choose_zero_right, Nat.cast_one, one_mul,
      Nat.sub_zero, Function.comp_apply, oldEmbedding, freshEmbedding, RingHom.comp_apply,
      freshArgument, map_pow, mul_comm]
  rw [hval]
  exact fun h => hne (hinj (h.trans freshEmbedding.map_zero.symm))
theorem freshValueReduction (Q : CoefficientIdeal)
    (hd : (affineHilbertPolynomial Q).natDegree = 1) :
    ValueReduction (extendIdeal Q) (K1_13_5_5.jetForm freshArgument 0) := by
  apply valueReduction_of_geometric (K := FreshClosure) _ (jetForm_homogeneous 0)
  intro x hx hval
  funext i
  change x i = 0
  by_contra hi
  letI : Algebra GeometricX FreshClosure := oldEmbedding.toAlgebra
  let b : Fin taylorLength → FreshClosure := fun j => (x i)⁻¹ * x j
  have hb : b ∈ zeroLocus FreshClosure (boundaryChart Q i) := normalize_boundary Q hx hi
  choose a ha using fun j => finite_chart_coordinates (boundaryChart Q i)
    (boundaryChart_dimension Q hd i) hb j
  have he : oldEmbedding ∘ a = b := funext ha
  have hai : a i ≠ 0 := by
    intro ha₀
    have hz := ha i
    change oldEmbedding (a i) = (x i)⁻¹ * x i at hz
    rw [ha₀, map_zero, inv_mul_cancel₀ hi] at hz
    exact zero_ne_one hz
  apply fresh_value_ne_zero hai
  rw [he]
  exact aeval_scale_zero (σ := Fin taylorLength) x ((x i)⁻¹) (jetForm_homogeneous 0) hval
end
end K1_13_5_4_4_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_14_2_2_7_4_4_8
noncomputable section
open K1_14_2_2_7_4_4 K1_13_6_3_5_3_2 IsDedekindDomain
open scoped WithZero IntermediateField.algebraAdjoinAdjoin
variable {F K : Type} [Field F] [Field K] [Algebra F K]
private theorem adjoin_inv (x : K) :
    IntermediateField.adjoin F ({x⁻¹} : Set K) = IntermediateField.adjoin F {x} := by
  apply le_antisymm <;> apply IntermediateField.adjoin_le_iff.mpr
  · exact Set.singleton_subset_iff.mpr
      (IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self F x))
  · apply Set.singleton_subset_iff.mpr
    change x ∈ IntermediateField.adjoin F ({x⁻¹} : Set K)
    simpa only [inv_inv] using
      (IntermediateField.adjoin F ({x⁻¹} : Set K)).inv_mem
        (IntermediateField.mem_adjoin_simple_self F x⁻¹)
private theorem poleOrder_eq_zero {x : K} (w : Place F K) (h : w.val x ≤ 1) :
    poleOrder w x = 0 := by
  by_cases hx : w.val x = 0
  · simp [poleOrder, hx]
  have hlog := (WithZero.log_le_log hx one_ne_zero).mpr h
  rw [WithZero.log_one] at hlog
  unfold poleOrder
  omega
private theorem valuation_eq_of_equiv {v w : Valuation K ℤᵐ⁰}
    (hv : Function.Surjective v) (hw : Function.Surjective w) (h : v.IsEquiv w) :
    v = w := by
  open WithZero in
  have hsmall {z : ℤᵐ⁰} (hz : z < 1) : z ≤ exp (-1 : ℤ) := by
    apply (lt_mul_exp_iff_le (y := exp (-1 : ℤ)) exp_ne_zero).mp
    simpa only [← exp_add, neg_add_cancel, exp_zero] using hz
  obtain ⟨π, hπ⟩ := hv (WithZero.exp (-1 : ℤ))
  obtain ⟨τ, hτ⟩ := hw (WithZero.exp (-1 : ℤ))
  have hπw : w π = WithZero.exp (-1 : ℤ) := by
    apply le_antisymm
    · apply hsmall
      apply h.lt_one_iff_lt_one.mp
      simp [hπ]
    · rw [← hτ, ← h.le_iff_le, hπ]
      apply hsmall
      apply h.lt_one_iff_lt_one.mpr
      simp [hτ]
  ext a
  by_cases ha : a = 0
  · simp [ha]
  · have hpow (u : Valuation K ℤᵐ⁰) (hu : u π = WithZero.exp (-1 : ℤ)) :
        u (π ^ (-WithZero.log (v a))) = v a := by
      rw [map_zpow₀, hu, ← WithZero.exp_zsmul]
      have hs : (-WithZero.log (v a)) • (-1 : ℤ) = WithZero.log (v a) := by simp
      rw [hs, WithZero.exp_log (v.ne_zero_iff.mpr ha)]
    exact (hpow w hπw).symm.trans (h.eq_iff.mp (hpow v hπ))
section Chart
variable {t : K}
local notation "A" => ParameterRing F K t
local notation "B" => Normalization F K t
local notation "p" => origin F K t
private abbrev parameter : A := ⟨t, Algebra.self_mem_adjoin_singleton F t⟩
private def originEquiv (ht : Transcendental F t) : (A ⧸ p) ≃ₐ[F] F := by
  let e := Polynomial.algEquivOfTranscendental F t ht
  refine (Ideal.quotientEquivAlg (Ideal.span {Polynomial.X}) p e ?_).symm.trans ?_
  · rw [Ideal.map_span, Set.image_singleton]
    unfold origin
    change Ideal.span {parameter} = Ideal.span {e Polynomial.X}
    simp only [e, parameter, Polynomial.algEquivOfTranscendental_apply_X]
  · rw [show (Ideal.span {Polynomial.X} : Ideal (Polynomial F)) =
        Ideal.span {Polynomial.X - Polynomial.C (0 : F)} by rw [map_zero, sub_zero]]
    exact Polynomial.quotientSpanXSubCAlgEquiv (0 : F)
private theorem chart_le_one (w : Place F K) (hw : w.val t < 1) (a : A) :
    w.val (algebraMap A K a) ≤ 1 := by
  obtain ⟨a, ha⟩ := a
  change w.val a ≤ 1
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact hw.le
  | algebraMap c =>
    by_cases hc : c = 0
    · simp [hc]
    · exact (w.trivial c hc).le
  | add a b ha hb hwa hwb =>
    exact (w.val.map_add _ _).trans (max_le hwa hwb)
  | mul a b ha hb hwa hwb =>
    rw [map_mul]
    exact mul_le_one' hwa hwb
private theorem normalization_le_one (w : Place F K) (hw : w.val t < 1) (b : B) :
    w.val (algebraMap B K b) ≤ 1 := by
  let O := w.val.valuationSubring
  let f : A →+* O := (algebraMap A K).codRestrict O.toSubring (chart_le_one w hw)
  let : Algebra A O := f.toAlgebra
  let : IsScalarTower A O K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hb : IsIntegral O (b.val : K) := IsIntegral.tower_top b.property
  exact (Valuation.valuationSubring.integers w.val).isIntegral_iff_v_le_one.mp hb
private def centerMap (w : Place F K) (hw : w.val t < 1) : B →ₐ[F] w.val.valuationSubring :=
  { (algebraMap B K).codRestrict w.val.valuationSubring.toSubring
      (normalization_le_one w hw) with
    commutes' := fun c => Subtype.ext ((IsScalarTower.algebraMap_apply F B K c).symm) }
def residueMap (w : Place F K) (hw : w.val t < 1) :
    B →ₐ[F] IsLocalRing.ResidueField w.val.valuationSubring :=
  (IsScalarTower.toAlgHom F w.val.valuationSubring _).comp (centerMap w hw)
private def centerIdeal (w : Place F K) (hw : w.val t < 1) : Ideal B :=
  RingHom.ker (residueMap w hw)
private theorem mem_centerIdeal (w : Place F K) (hw : w.val t < 1) (b : B) :
    b ∈ centerIdeal w hw ↔ w.val (algebraMap B K b) < 1 := by
  change IsLocalRing.residue _ (centerMap w hw b) = 0 ↔ _
  rw [IsLocalRing.residue_eq_zero_iff]
  exact w.val.mem_maximalIdeal_iff
private def center (ht : Transcendental F t) (w : Place F K) (hw : w.val t < 1) :
    Ideal.primesOver p B := by
  let P := centerIdeal w hw
  have : P.IsPrime := RingHom.ker_isPrime (residueMap w hw).toRingHom
  refine ⟨P, inferInstance, ⟨(origin_isMaximal ht).eq_of_le
    (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩
  change Ideal.span {parameter} ≤ P.under A
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  change algebraMap A B parameter ∈ centerIdeal w hw
  exact (mem_centerIdeal w hw _).mpr hw
theorem image_parameter_ne_zero (ht : Transcendental F t) :
    algebraMap A B parameter ≠ 0 := by
  intro h
  exact ht.ne_zero (congrArg Subtype.val h)
private def heightOne (ht : Transcendental F t) (P : Ideal.primesOver p B) :
    HeightOneSpectrum B := by
  have : P.val.LiesOver p := P.property.2
  refine ⟨P.val, P.property.1, ?_⟩
  intro h
  have hmem : algebraMap A B parameter ∈ P.val :=
    (P.val.mem_of_liesOver p _).mp (Ideal.mem_span_singleton_self _)
  rw [h, Ideal.mem_bot] at hmem
  exact image_parameter_ne_zero ht hmem
variable [IsDedekindDomain (Normalization F K t)] [IsFractionRing (Normalization F K t) K]
private theorem center_valuation (ht : Transcendental F t) (w : Place F K) (hw : w.val t < 1) :
    (heightOne ht (center ht w hw)).valuation K = w.val := by
  let v := heightOne ht (center ht w hw)
  have hbelow : v.valuationSubringAtPrime K ≤ w.val.valuationSubring := by
    intro y hy
    rw [v.valuationSubringAtPrime_eq_valuationSubring] at hy
    obtain ⟨a, s, hs⟩ := v.exists_primeCompl_mul_eq_of_integer y hy
    have hsV : w.val (algebraMap B K s) = 1 :=
      le_antisymm (normalization_le_one w hw s)
        (le_of_not_gt fun h => s.property ((mem_centerIdeal w hw s).mpr h))
    change w.val y ≤ 1
    have hval := congrArg (fun b : K => w.val b) hs
    rw [map_mul, hsV, mul_one] at hval
    exact hval.trans_le (normalization_le_one w hw a)
  have hproper : w.val.valuationSubring ≠ ⊤ := by
    rw [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    exact (Valuation.isNontrivial_iff_exists_lt_one w.val).mpr ⟨t, ht.ne_zero, hw⟩
  have hring := (v.valuationSubringAtPrime_eq_valuationSubring (K := K)).symm.trans
    (ValuationSubring.eq_of_le_of_ne_top _ hbelow hproper)
  exact valuation_eq_of_equiv (v.valuation_surjective K) w.surj
    ((Valuation.isEquiv_iff_valuationSubring (v.valuation K) w.val).mpr hring)
theorem center_injective (ht : Transcendental F t) :
    Function.Injective (fun w : {w : Place F K // w.val t < 1} => center ht w.1 w.2) := by
  rintro ⟨w, hw⟩ ⟨v, hv⟩ h
  apply Subtype.ext
  have he := congrArg (fun P : Ideal.primesOver p B => (heightOne ht P).valuation K) h
  rw [center_valuation ht w hw, center_valuation ht v hv] at he
  cases w
  cases v
  cases he
  rfl
theorem center_order (ht : Transcendental F t) (w : Place F K) (hw : w.val t < 1) :
    (-WithZero.log (w.val t)).toNat = (center ht w hw).val.ramificationIdx A := by
  let P := center ht w hw
  have : P.val.IsPrime := P.property.1
  have : P.val.LiesOver p := P.property.2
  let v := heightOne ht P
  let b : B := algebraMap A B parameter
  have hb : b ≠ 0 := image_parameter_ne_zero ht
  have hspan : Ideal.map (algebraMap A B) p = Ideal.span {b} := by
    simp only [origin, Ideal.map_span, Set.image_singleton, b, parameter]
  have hmap : Ideal.map (algebraMap A B) p ≠ ⊥ := by
    rw [hspan, ne_eq, Ideal.span_singleton_eq_bot]
    exact hb
  change (-WithZero.log (w.val t)).toNat = P.val.ramificationIdx A
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p P.val hmap, hspan]
  rw [← center_valuation ht w hw]
  change (-WithZero.log (v.valuation K (algebraMap B K b))).toNat =
    multiplicity v.asIdeal (Ideal.span {b})
  simp only [v.valuation_of_algebraMap, v.intValuation_eq_exp_neg_multiplicity hb,
    WithZero.log_exp, neg_neg, Int.toNat_natCast]
theorem residueMap_surjective (ht : Transcendental F t)
    (w : Place F K) (hw : w.val t < 1) : Function.Surjective (residueMap w hw) := by
  let P := center ht w hw
  have : P.val.LiesOver p := P.property.2
  have : Ideal.IsMaximal p := origin_isMaximal ht
  have : P.val.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P.val p
  let v := heightOne ht P
  let f := residueMap w hw
  let e : (B ⧸ P.val) →ₐ[F] IsLocalRing.ResidueField w.val.valuationSubring :=
    Ideal.kerLiftAlg f
  let : Field (B ⧸ P.val) := Ideal.Quotient.field P.val
  intro y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := w.val.valuationSubring) y
  have ha : v.valuation K (a : K) ≤ 1 := by
    rw [center_valuation ht w hw]
    exact a.property
  obtain ⟨b, d, hbd⟩ := v.exists_primeCompl_mul_eq_of_integer (a : K) ha
  have hd : Ideal.Quotient.mk P.val (d : B) ≠ 0 :=
    fun h => d.property (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective ((Ideal.Quotient.mk P.val (d : B))⁻¹)
  have hdz : f (d : B) * f z = 1 := by
    change e (Ideal.Quotient.mk P.val (d : B)) * e (Ideal.Quotient.mk P.val z) = 1
    rw [← map_mul, hz, mul_inv_cancel₀ hd, map_one]
  have hmul : a * centerMap w hw d = centerMap w hw b := Subtype.ext hbd
  have hres := congrArg (IsLocalRing.residue w.val.valuationSubring) hmul
  rw [map_mul] at hres
  change IsLocalRing.residue _ a * f d = f b at hres
  refine ⟨b * z, ?_⟩
  change f (b * z) = _
  rw [map_mul, ← hres, mul_assoc, hdz, mul_one]
theorem center_residue_degree (ht : Transcendental F t)
    (w : Place F K) (hw : w.val t < 1) :
    residueDegree w = (center ht w hw).val.inertiaDeg A := by
  let P := center ht w hw
  have : P.val.LiesOver p := P.property.2
  have : Ideal.IsMaximal p := origin_isMaximal ht
  have : P.val.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P.val p
  let e : (B ⧸ P.val) ≃ₐ[F] IsLocalRing.ResidueField w.val.valuationSubring :=
    Ideal.quotientKerAlgEquivOfSurjective (residueMap_surjective ht w hw)
  change Module.finrank F (IsLocalRing.ResidueField w.val.valuationSubring) = P.val.inertiaDeg A
  rw [← e.toLinearEquiv.finrank_eq, Ideal.inertiaDeg_eq_of_isMaximal p P.val]
  let e₀ := (originEquiv ht).symm
  apply Algebra.finrank_eq_of_equiv_equiv e₀.toRingEquiv (RingEquiv.refl (B ⧸ P.val))
  apply RingHom.ext
  intro c
  change algebraMap (A ⧸ p) (B ⧸ P.val) (e₀ c) = algebraMap F (B ⧸ P.val) c
  have he₀ : e₀ c = algebraMap F (A ⧸ p) c := by
    simpa only [Algebra.algebraMap_self_apply] using e₀.commutes c
  rw [he₀, ← IsScalarTower.algebraMap_apply F (A ⧸ p) (B ⧸ P.val)]
end Chart
theorem proof : K1_14_2_2_7_4_4.c8 := by
  classical
  intro F K _ _ _ x S hx
  let t := x⁻¹
  have ht : Transcendental F t := fun hi => hx.1 (IsAlgebraic.inv_iff.mp hi)
  let A := ParameterRing F K t
  let B := Normalization F K t
  let L := IntermediateField.adjoin F ({t} : Set K)
  let p := origin F K t
  have hL : L = IntermediateField.adjoin F ({x} : Set K) := adjoin_inv x
  have : Module.Finite L K := hL.symm ▸ hx.2.1
  have : Algebra.IsSeparable L K := hL.symm ▸ hx.2.2
  have : IsPrincipalIdealRing A := parameterRing_pid ht
  have : Module.IsTorsionFree A K := .trans_faithfulSMul A L K
  have : Module.Free A B := IsIntegralClosure.module_free A L K B
  have : Module.Finite A B := IsIntegralClosure.finite A L K B
  have : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A L K B
  have : IsFractionRing B K := integralClosure.isFractionRing_of_finite_extension L K
  have : Ideal.IsMaximal p := origin_isMaximal ht
  have : p.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  let T := S.subtype (fun w : Place F K => w.val t < 1)
  let centerOf : {w : Place F K // w.val t < 1} ↪ (Ideal.primesOver p B) :=
    ⟨fun w => center ht w.val w.property, center_injective ht⟩
  let weight (P : Ideal.primesOver p B) := P.val.ramificationIdx A * P.val.inertiaDeg A
  calc
    poleDegree S x = ∑ w ∈ T, residueDegree w.val * poleOrder w.val x := by
      dsimp only [T]
      rw [Finset.sum_subtype_eq_sum_filter (fun w : Place F K => residueDegree w * poleOrder w x)]
      unfold poleDegree
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro w hwS hw
      have h : w.val x ≤ 1 := by
        by_contra! h
        exact hw (Finset.mem_filter.mpr ⟨hwS, by
          change w.val x⁻¹ < 1
          rw [map_inv₀]
          exact inv_lt_one_of_one_lt₀ h⟩)
      simp [poleOrder_eq_zero w h]
    _ = ∑ P ∈ T.map centerOf, weight P := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro w _
      have ho := center_order ht w.val w.property
      have hlog : (-WithZero.log (w.val.val t)).toNat = poleOrder w.val x := by
        simp [t, poleOrder, map_inv₀, WithZero.log_inv]
      rw [hlog] at ho
      change _ = weight (center ht w.val w.property)
      rw [center_residue_degree ht w.val w.property, ho]
      exact Nat.mul_comm _ _
    _ ≤ ∑ P : Ideal.primesOver p B, weight P :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = Module.finrank A B := Ideal.sum_ramification_inertia_eq_finrank p B
    _ = Module.finrank L K := IsIntegralClosure.rank A L K B
    _ = _ := congrArg (fun M : IntermediateField F K => Module.finrank M K) hL
end
end K1_14_2_2_7_4_4_8
end
section
namespace K1_13_7_1
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_7
def c1 : Prop :=
  ∀ p h : Shape, Chamber p → Chamber h →
    ∀ f g u v : GeoJets, GeoFits f p → GeoFits g p → GeoFits u h → GeoFits v h →
      ∀ points : Finset GeoPoint,
        (∀ y ∈ points, Isolated f g u v y) →
        32 * points.card ≤ mixed32 p p h h
def c2 : Prop :=
  ∀ f g : GeoJets, f ≠ 0 → g ≠ 0 → IsRelPrime f g →
    ∀ (C : TaylorChart) (d : ℕ), SliceBound f g C d →
      ∀ (Γ : Finset K) (s : K → K[X]), Set.InjOn s (Γ : Set K) →
        (∀ γ ∈ Γ, (s γ).natDegree ≤ 133671 ∧
          evalGeneric (extend (s γ)) f = 0 ∧ evalGeneric (extend (s γ)) g = 0 ∧
          C.Recovers (extend (s γ))) →
        ∃ B : Pieces Γ, Γ ⊆ B.union ∧ B.surfaces s ∧
          (∀ i, 0 < B.degree i) ∧ B.total ≤ d
private theorem box_chamber (f : Row 4) : InBox (shape f) (shape f).chamber :=
  ⟨le_max_left _ _, le_rfl, le_rfl⟩
private theorem derivative_proper {f : Row 4} (hf : SmallFactor f) (j : ℕ)
    (hj : 0 < j) (hg : (separant^[j]) f ≠ 0) : ¬ f ∣ (separant^[j]) f := by
  rintro ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    intro hz
    exact hg (by rw [hq, hz, mul_zero])
  have hd := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.1.ne_zero hq0
  have h := derivative_degree f j
  have ht : 0 < f.degreeOf 3 := hf.2.1
  change ((separant^[j]) f).degreeOf 3 ≤ f.degreeOf 3 - j at h
  rw [hq, hd] at h
  omega
theorem one_piece (h1 : c1) (h2 : c2)
    {w Γ s} (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f) (j : ℕ)
    (hj : 0 < j)
    (hmarks : ∀ γ ∈ Γ, atJet f (extend (s γ)) = 0 ∧
      atJet ((separant^[j]) f) (extend (s γ)) = 0 ∧
      RegularAt ((separant^[j]) f) (extend (s γ))) :
    let p := (shape f).chamber
    let h := chart (taylorLength + 4) p
    Γ.card ≤ 4 * (mixed32 p p h h / 32) := by
  classical
  dsimp only
  by_cases hΓ : Γ.Nonempty
  · obtain ⟨γ, hγ⟩ := hΓ
    let g := (separant^[j]) f
    let p := (shape f).chamber
    let h := chart (taylorLength + 4) p
    let d := mixed32 p p h h / 32
    have hg0 : g ≠ 0 := by
      intro hz
      exact (hmarks γ hγ).2.2 (by simp [show (separant^[j]) f = 0 from hz, atJet])
    have hpf := box_chamber f
    have hpg : InBox (shape g) p := by
      have hb := derivative_in_box f j
      exact ⟨hb.1.trans hpf.1, hb.2.1.trans hpf.2.1, hb.2.2.trans hpf.2.2⟩
    have hp := shape_chamber f
    have ht : 0 < p.t := hf.2.1
    obtain ⟨C, hC, hrecover⟩ := exists_chart g p hpg hp ht
    have hbound : SliceBound (toGeneric f) (toGeneric g) C d := by
      intro a b points hpts
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 32)).mpr (by
        rw [Nat.mul_comm]
        exact h1 p h hp (chart_chamber _ _) _ _ _ _
          (toGeneric_fits hpf) (toGeneric_fits hpg) (C.pullback_fits hC a)
          (C.pullback_fits hC b) points (fun y hy => (hpts y hy).1))
    obtain ⟨B, hcover, hsurfaces, hpos, hsum⟩ :=
      h2 (toGeneric f) (toGeneric g)
        (fun hz => hf.1.ne_zero (toGeneric_injective (hz.trans (map_zero _).symm)))
        (fun hz => hg0 (toGeneric_injective (hz.trans (map_zero _).symm)))
        (proper_generic f g hf.1 (derivative_proper hf j hj hg0))
        C d hbound Γ s hm.distinct (fun a ha => by
          obtain ⟨hf', hg', hr⟩ := hmarks a ha
          refine ⟨hm.degree a ha, ?_, ?_, hrecover _ hg' hr⟩
          · rw [evalGeneric_toGeneric, hf', map_zero]
          · rw [evalGeneric_toGeneric, hg', map_zero])
    exact (Finset.card_le_card hcover).trans
      ((B.surface_capacity hm hsurfaces hpos).trans (Nat.mul_le_mul_left 4 hsum))
  · simp [Finset.not_nonempty_iff_eq_empty.mp hΓ]
theorem of_children (h1 : c1) (h2 : c2) : K1_13_7.c1 := by
  classical
  intro w Γ s hm f hf _ hmarks
  let t := (shape f).t
  have hcover (γ : K) (hγ : γ ∈ Γ) :
      ∃ j, 0 < j ∧ j < t ∧
        atJet ((separant^[j]) f) (extend (s γ)) = 0 ∧
        RegularAt ((separant^[j]) f) (extend (s γ)) :=
    regular_derivative f _ hf (hmarks γ hγ).1 (Classical.not_not.mp (hmarks γ hγ).2)
  by_cases ht : 1 < t
  · let p := (shape f).chamber
    let h := chart (taylorLength + 4) p
    let m := mixed32 p p h h
    let part (j : Fin t) := Γ.filter fun γ =>
      0 < j.val ∧ atJet ((separant^[j.val]) f) (extend (s γ)) = 0 ∧
        RegularAt ((separant^[j.val]) f) (extend (s γ))
    have hall : Γ ⊆ Finset.univ.biUnion part := by
      intro γ hγ
      obtain ⟨j, hj, hjt, hz, hr⟩ := hcover γ hγ
      exact Finset.mem_biUnion.mpr ⟨⟨j, hjt⟩, Finset.mem_univ _, Finset.mem_filter.mpr
        ⟨hγ, hj, hz, hr⟩⟩
    have hpart (j : Fin t) : (part j).card ≤ 4 * (m / 32) := by
      by_cases hj : 0 < j.val
      · apply one_piece h1 h2 (hm.mono (Finset.filter_subset _ _)) f hf j.val hj
        intro γ hγ
        have hp := Finset.mem_filter.mp hγ
        exact ⟨(hmarks γ hp.1).1.1, hp.2.2⟩
      · simp [part, hj]
    have hprice : 4 * t * (m / 32) ≤ ceilDiv (4 * t * m) 32 := by
      unfold ceilDiv
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 32)).mpr
      rw [Nat.mul_assoc]
      exact (Nat.mul_le_mul_left (4 * t) (Nat.div_mul_le_self m 32)).trans (by omega)
    have hchart : K1_13_7.fatChart (shape f) = h := by
      unfold K1_13_7.fatChart
      exact ite_eq_right (by omega : t ≠ 1)
    unfold singularPrice
    rw [ite_eq_left ht, hchart]
    change Γ.card ≤ ceilDiv (4 * t * m) 32 + t * (shape f).b ^ 2 + 1
    calc
      Γ.card ≤ (Finset.univ.biUnion part).card := Finset.card_le_card hall
      _ ≤ ∑ j : Fin t, (part j).card := Finset.card_biUnion_le
      _ ≤ ∑ _ : Fin t, 4 * (m / 32) := Finset.sum_le_sum fun j _ => hpart j
      _ = 4 * t * (m / 32) := by simp [Nat.mul_comm, Nat.mul_assoc]
      _ ≤ ceilDiv (4 * t * m) 32 := hprice
      _ ≤ _ := by omega
  · have hempty : Γ = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨γ, hγ⟩
      obtain ⟨j, hj, hjt, _, _⟩ := hcover γ hγ
      omega
    simp [hempty]
end
end K1_13_7_1
end
section
namespace K1_13_7_1_1
open K1_13 K1_13_6 K1_13_7_1 MeasureTheory
open scoped Pointwise
def c1 : Prop :=
  ∀ p h : Shape, Chamber p → Chamber h →
    ∀ f g u v : GeoJets, SupportedIn f (cap p) → SupportedIn g (cap p) →
      SupportedIn u (cap h) → SupportedIn v (cap h) →
      ∀ points : Finset GeoPoint,
        (∀ y ∈ points, Isolated f g u v y ∧ ∀ i, y i ≠ 0) →
        (points.card : ℝ) ≤ mixedVolume (cap p) (cap p) (cap h) (cap h)
def c2 : Prop :=
  ∀ p : Shape, Chamber p → 32 * (volume (cap p)).toReal = (volume32 p : ℝ)
private theorem scaled_difference {F : Set RealPoint → ℝ} {G : Shape → ℤ}
    (heq : ∀ x : Shape, Chamber x → 32 * F (cap x) = (G x : ℝ))
    {a : Shape} (ha : Chamber a) (x : Shape) (hx : Chamber x) :
    32 * bodyDifference F (cap a) (cap x) = (difference G a x : ℝ) := by
  rw [bodyDifference, difference, Int.cast_sub, mul_sub, ← cap_add hx ha,
    heq _ (chamber_plus hx ha), heq _ hx]
theorem of_children (h1 : c1) (h2 : c2) : K1_13_7_1.c1 := by
  intro p h hp hh f g u v hf hg hu hv points hpts
  obtain ⟨f', g', u', v', hf', hg', hu', hv', points', hc, hpts'⟩ :=
    move_to_torus hf hg hu hv points hpts
  have hb := h1 p h hp hh f' g' u' v' (supportedIn_cap hf') (supportedIn_cap hg')
    (supportedIn_cap hu') (supportedIn_cap hv') points' hpts'
  rw [hc] at hb
  have hfirst := scaled_difference (F := fun P => (volume P).toReal) (G := volume32) h2 hp
  have hm := scaled_difference (scaled_difference (scaled_difference hfirst hp) hh) hh
      ⟨0, 0, 0⟩ (⟨by decide, by decide⟩ : Chamber ⟨0, 0, 0⟩)
  rw [cap_zero] at hm
  change 32 * mixedVolume (cap p) (cap p) (cap h) (cap h) = _ at hm
  have hcast := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 32)
  rw [hm] at hcast
  have hz : (↑(32 * points.card) : ℤ) ≤
      difference (difference (difference (difference volume32 p) p) h) h ⟨0, 0, 0⟩ := by
    exact_mod_cast hcast
  simpa only [mixed32, Int.toNat_natCast] using Int.toNat_le_toNat hz
end K1_13_7_1_1
end
section
namespace K1_13_7_1_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_7_1 K1_13_7_1_1 MvPolynomial
open scoped Pointwise
abbrev Exponent := Fin 4 →₀ ℕ
abbrev Grades := Fin 4 → ℕ
def lattice (p : Shape) : Set Exponent :=
  {e | e 0 + e 1 + e 2 + e 3 ≤ p.b ∧ e 1 + 2 * e 2 + 3 * e 3 ≤ p.j ∧ e 3 ≤ p.t}
def gradedExponents (A : Fin 4 → Set Exponent) (B : Set Exponent)
    (b : ℕ) (w : Grades) : Set Exponent :=
  (((b • B + w 0 • A 0) + w 1 • A 1) + w 2 • A 2) + w 3 • A 3
def admissible (A : Fin 4 → Set Exponent) (B : Set Exponent) : Prop :=
  (∀ i, (A i).Finite ∧ 0 ∈ A i) ∧ B.Finite ∧ 0 ∈ B ∧
    ∀ i : Fin 4, Finsupp.single i 1 ∈ B
abbrev affineDim (P : Ideal GeoJets) : ℕ := (affineHilbertPolynomial P).natDegree
def hilbert (A : Fin 4 → Set Exponent) (B : Set Exponent) (P : Ideal GeoJets)
    (b : ℕ) (w : Grades) : ℝ :=
  Module.finrank GeoField ((restrictSupport GeoField (gradedExponents A B b w)).map
    (Ideal.Quotient.mkₐ GeoField P).toLinearMap)
def gradeDifference (F : Grades → ℝ) (i : Fin 4) (step : ℕ) (w : Grades) : ℝ :=
  F (w + Pi.single i step) - F w
def gradeDifferences (dirs : List (Fin 4)) (step : ℕ) (F : Grades → ℝ) : Grades → ℝ :=
  dirs.foldl (fun H i => gradeDifference H i step) F
def remainingDirections (k : ℕ) : List (Fin 4) :=
  (List.finRange 4).drop k
def IsMixedDegree (A : Fin 4 → Set Exponent) (B : Set Exponent)
    (P : Ideal GeoJets) (k : ℕ) (d : ℝ) : Prop :=
  ∃ N : ℕ, ∀ b w step, N ≤ b → (∀ i, N ≤ w i) →
    gradeDifferences (remainingDirections k) step (hilbert A B P b) w =
      (step : ℝ) ^ (4 - k) * d
abbrev pointIdeal (y : GeoPoint) : Ideal GeoJets := RingHom.ker (MvPolynomial.eval y)
end
end K1_13_7_1_1_1
end
section
namespace K1_13_7_1_1_1
open K1_13 K1_13_6 K1_13_7_1 K1_13_7_1_1 MvPolynomial
open scoped Pointwise
theorem shape_eq {p q : Shape} (hb : p.b = q.b) (hj : p.j = q.j) (ht : p.t = q.t) : p = q := by
  cases p
  cases q
  simp_all
theorem chamber_scale {p : Shape} (hp : Chamber p) (k : ℕ) : Chamber (p.scale k) := by
  exact ⟨Nat.mul_le_mul_left k hp.1, by
    simpa only [Shape.scale, mul_left_comm 3 k] using Nat.mul_le_mul_left k hp.2⟩
theorem lattice_zero_mem (p : Shape) : 0 ∈ lattice p := by simp [lattice]
theorem mem_lattice_iff {e : Exponent} {p : Shape} :
    e ∈ lattice p ↔ (fun i => (e i : ℝ)) ∈ cap p := by
  change (e 0 + e 1 + e 2 + e 3 ≤ p.b ∧ e 1 + 2 * e 2 + 3 * e 3 ≤ p.j ∧ e 3 ≤ p.t) ↔
    (∀ i : Fin 4, 0 ≤ (e i : ℝ)) ∧ (e 0 : ℝ) + e 1 + e 2 + e 3 ≤ p.b ∧
      (e 1 : ℝ) + 2 * e 2 + 3 * e 3 ≤ p.j ∧ (e 3 : ℝ) ≤ p.t
  constructor
  · intro ⟨hb, hj, ht⟩
    exact ⟨fun _ => Nat.cast_nonneg _, by exact_mod_cast hb, by exact_mod_cast hj,
      by exact_mod_cast ht⟩
  · intro ⟨_, hb, hj, ht⟩
    exact ⟨by exact_mod_cast hb, by exact_mod_cast hj, by exact_mod_cast ht⟩
theorem lattice_finite (p : Shape) : (lattice p).Finite := by
  have hbound (e : lattice p) (i : Fin 4) : e.val i < p.b + 1 := by
    have hb : e.val 0 + e.val 1 + e.val 2 + e.val 3 ≤ p.b := e.property.1
    fin_cases i
    · change e.val 0 < p.b + 1
      omega
    · change e.val 1 < p.b + 1
      omega
    · change e.val 2 < p.b + 1
      omega
    · change e.val 3 < p.b + 1
      omega
  let f (e : lattice p) (i : Fin 4) : Fin (p.b + 1) := ⟨e.val i, hbound e i⟩
  let : Finite (lattice p) := Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    ext i
    exact congrArg (fun z : Fin 4 → Fin (p.b + 1) => (z i).val) h)
  exact Set.toFinite _
theorem square_support {p : Shape} {f : GeoJets} (hf : SupportedIn f (cap p)) :
    ((f ^ 2).support : Set Exponent) ⊆ lattice (p.scale 2) := by
  classical
  intro e he
  rw [pow_two] at he
  have h := support_mul f f he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp h
  have ⟨hab, haj, hat⟩ := mem_lattice_iff.mpr (hf a ha)
  have ⟨hbb, hbj, hbt⟩ := mem_lattice_iff.mpr (hf b hb)
  change _ ≤ 2 * p.b ∧ _ ≤ 2 * p.j ∧ _ ≤ 2 * p.t
  simp only [Finsupp.add_apply]
  exact ⟨by omega, by omega, by omega⟩
theorem split_index_even {x y A B : ℕ} (he : A % 2 = 0)
    (h : x + 2 * y ≤ A + B) :
    ∃ u v : ℕ, u ≤ x ∧ v ≤ y ∧ u + 2 * v ≤ A ∧ (x - u) + 2 * (y - v) ≤ B := by
  let v := min y (A / 2)
  let u := min x (A - 2 * v)
  have hv : v ≤ A / 2 := min_le_right _ _
  have hu : u ≤ A - 2 * v := min_le_right _ _
  refine ⟨u, v, min_le_left _ _, min_le_left _ _, by omega, ?_⟩
  rcases le_total y (A / 2) with hsmall | hlarge
  · have hyv : v = y := min_eq_left hsmall
    rcases le_total x (A - 2 * v) with hsmall' | hlarge'
    · have hxu : u = x := min_eq_left hsmall'
      omega
    · have hxu : u = A - 2 * v := min_eq_right hlarge'
      omega
  · have hyv : v = A / 2 := min_eq_right hlarge
    omega
theorem split_index {x y A B : ℕ} (he : A % 2 = 0 ∨ B % 2 = 0)
    (h : x + 2 * y ≤ A + B) :
    ∃ u v : ℕ, u ≤ x ∧ v ≤ y ∧ u + 2 * v ≤ A ∧ (x - u) + 2 * (y - v) ≤ B := by
  rcases he with he | he
  · exact split_index_even he h
  · obtain ⟨u, v, hu, hv, hB, hA⟩ := split_index_even he (show x + 2 * y ≤ B + A by omega)
    exact ⟨x - u, y - v, by omega, by omega, hA, by omega⟩
theorem lattice_add {p q : Shape} (hp : Chamber p) (hq : Chamber q) :
    lattice ((p.plus q).scale 2) = lattice (p.scale 2) + lattice (q.scale 2) := by
  apply Set.Subset.antisymm
  · intro e he
    have ⟨hb, hj, ht⟩ : e 0 + e 1 + e 2 + e 3 ≤ 2 * (p.b + q.b) ∧
        e 1 + 2 * e 2 + 3 * e 3 ≤ 2 * (p.j + q.j) ∧ e 3 ≤ 2 * (p.t + q.t) := he
    simp only [Shape.scale, Shape.plus] at hb hj ht
    let z := min (e 3) (2 * p.t)
    let w := e 3 - z
    have hz₁ : z ≤ e 3 := min_le_left _ _
    have hz₂ : z ≤ 2 * p.t := min_le_right _ _
    have hw : w ≤ 2 * q.t := by
      rcases le_total (e 3) (2 * p.t) with hh | hh
      · have hz : z = e 3 := min_eq_left hh
        dsimp only [w]
        omega
      · have hz : z = 2 * p.t := min_eq_right hh
        dsimp only [w]
        omega
    let A := 2 * p.j - 3 * z
    let B := 2 * q.j - 3 * w
    have hp₁ := hp.1
    have hp₂ := hp.2
    have hq₁ := hq.1
    have hq₂ := hq.2
    have hsplit : e 1 + 2 * e 2 ≤ A + B := by dsimp only [A, B, w]; omega
    have hpar : A % 2 = 0 ∨ B % 2 = 0 := by
      rcases le_total (e 3) (2 * p.t) with hh | hh
      · have hz : z = e 3 := min_eq_left hh
        right
        dsimp only [B, w]
        omega
      · have hz : z = 2 * p.t := min_eq_right hh
        left
        dsimp only [A]
        omega
    obtain ⟨x, y, hx, hy, hxy, hxy'⟩ := split_index hpar hsplit
    have hleft : x + y + z ≤ 2 * p.b := by dsimp only [A] at hxy; omega
    have hright : (e 1 - x) + (e 2 - y) + w ≤ 2 * q.b := by dsimp only [B] at hxy'; omega
    let a₀ := min (e 0) (2 * p.b - x - y - z)
    have ha₀ : a₀ ≤ e 0 := min_le_left _ _
    have ha₀' : a₀ ≤ 2 * p.b - x - y - z := min_le_right _ _
    have hsum : (e 0 - a₀) + (e 1 - x) + (e 2 - y) + w ≤ 2 * q.b := by
      rcases le_total (e 0) (2 * p.b - x - y - z) with hh | hh
      · have heq : a₀ = e 0 := min_eq_left hh
        omega
      · have heq : a₀ = 2 * p.b - x - y - z := min_eq_right hh
        dsimp only [w] at *
        omega
    let a : Exponent := Finsupp.equivFunOnFinite.symm ![a₀, x, y, z]
    let b : Exponent := Finsupp.equivFunOnFinite.symm ![e 0 - a₀, e 1 - x, e 2 - y, w]
    apply Set.mem_add.mpr
    refine ⟨a, ?_, b, ?_, ?_⟩
    · change a₀ + x + y + z ≤ 2 * p.b ∧ x + 2 * y + 3 * z ≤ 2 * p.j ∧ z ≤ 2 * p.t
      dsimp only [A] at hxy
      exact ⟨by omega, by omega, hz₂⟩
    · change (e 0 - a₀) + (e 1 - x) + (e 2 - y) + w ≤ 2 * q.b ∧
        (e 1 - x) + 2 * (e 2 - y) + 3 * w ≤ 2 * q.j ∧ w ≤ 2 * q.t
      dsimp only [B] at hxy'
      exact ⟨hsum, by omega, hw⟩
    · ext i
      simp only [Finsupp.add_apply]
      fin_cases i
      · change a₀ + (e 0 - a₀) = e 0
        omega
      · change x + (e 1 - x) = e 1
        omega
      · change y + (e 2 - y) = e 2
        omega
      · change z + w = e 3
        dsimp only [w]
        omega
  · intro e he
    obtain ⟨a, ⟨ha₁, ha₂, ha₃⟩, b, ⟨hb₁, hb₂, hb₃⟩, rfl⟩ := Set.mem_add.mp he
    simp only [Shape.scale] at ha₁ ha₂ ha₃ hb₁ hb₂ hb₃
    change _ ≤ 2 * (p.b + q.b) ∧ _ ≤ 2 * (p.j + q.j) ∧ _ ≤ 2 * (p.t + q.t)
    simp only [Finsupp.add_apply]
    exact ⟨by omega, by omega, by omega⟩
private theorem lattice_zero : lattice ⟨0, 0, 0⟩ = 0 := by
  ext e
  change e ∈ lattice ⟨0, 0, 0⟩ ↔ e = 0
  constructor
  · intro he
    have h := mem_lattice_iff.mp he
    rw [cap_zero] at h
    have hz : (fun i => (e i : ℝ)) = 0 := h
    ext i
    change e i = 0
    have hi : (e i : ℝ) = 0 := congrFun hz i
    exact_mod_cast hi
  · rintro rfl
    exact lattice_zero_mem _
theorem lattice_nsmul {p : Shape} (hp : Chamber p) (n : ℕ) :
    n • lattice (p.scale 2) = lattice ((p.scale n).scale 2) := by
  induction n with
  | zero =>
      rw [zero_nsmul, ← lattice_zero]
      congr 1
      apply shape_eq <;> simp [Shape.scale]
  | succ n ih =>
      rw [succ_nsmul, ih, ← lattice_add (chamber_scale hp n) hp]
      congr 1
      apply shape_eq <;> simp [Shape.scale, Shape.plus, Nat.add_mul]
def auxShape : Shape := ⟨3, 3, 1⟩
theorem aux_chamber : Chamber auxShape := by norm_num [Chamber, auxShape]
theorem cap_admissible (S : Fin 4 → Shape) :
    admissible (fun i => lattice ((S i).scale 2)) (lattice (auxShape.scale 2)) := by
  refine ⟨fun _ => ⟨lattice_finite _, lattice_zero_mem _⟩, lattice_finite _,
    lattice_zero_mem _, ?_⟩
  intro i
  fin_cases i <;> norm_num [lattice, auxShape, Shape.scale, Finsupp.single_apply]
end K1_13_7_1_1_1
end
section
namespace K1_13_7_1_1_1
noncomputable section
open K1_13 K1_13_7_1_1 MeasureTheory Filter
open scoped Pointwise Topology
private def realCap (b j t : ℝ) : Set RealPoint :=
  {x | (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 + x 3 ≤ b ∧
    x 1 + 2 * x 2 + 3 * x 3 ≤ j ∧ x 3 ≤ t}
theorem realCap_closed (b j t : ℝ) : IsClosed (realCap b j t) := by
  have hnonneg : IsClosed {x : RealPoint | ∀ i, 0 ≤ x i} := by
    rw [show {x : RealPoint | ∀ i, 0 ≤ x i} = ⋂ i : Fin 4, {x | 0 ≤ x i} by
      ext x; simp]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hb : IsClosed {x : RealPoint | x 0 + x 1 + x 2 + x 3 ≤ b} :=
    isClosed_le (by fun_prop) continuous_const
  have hj : IsClosed {x : RealPoint | x 1 + 2 * x 2 + 3 * x 3 ≤ j} :=
    isClosed_le (by fun_prop) continuous_const
  have ht : IsClosed {x : RealPoint | x 3 ≤ t} := isClosed_le (continuous_apply _) continuous_const
  exact hnonneg.inter (hb.inter (hj.inter ht))
theorem realCap_compact (b j t : ℝ) : IsCompact (realCap b j t) := by
  apply isCompact_Icc.of_isClosed_subset (realCap_closed b j t)
    (t := realCap b j t) (s := Set.Icc (0 : RealPoint) (fun _ => b))
  intro x hx
  obtain ⟨hx, hxb, _, _⟩ := hx
  refine ⟨hx, fun i => ?_⟩
  have h₀ := hx 0
  have h₁ := hx 1
  have h₂ := hx 2
  have h₃ := hx 3
  change x i ≤ b
  fin_cases i
  · change x 0 ≤ b
    linarith
  · change x 1 ≤ b
    linarith
  · change x 2 ≤ b
    linarith
  · change x 3 ≤ b
    linarith
theorem realCap_convex (b j t : ℝ) : Convex ℝ (realCap b j t) := by
  intro x hx y hy a c ha hc hac
  obtain ⟨hx, hxb, hxj, hxt⟩ := hx
  obtain ⟨hy, hyb, hyj, hyt⟩ := hy
  change (∀ i, 0 ≤ (a • x + c • y) i) ∧ _ ∧ _ ∧ _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hc (hy i)), ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hxb ha, mul_le_mul_of_nonneg_left hyb hc,
      congrArg (fun z : ℝ => z * b) hac]
  · nlinarith [mul_le_mul_of_nonneg_left hxj ha, mul_le_mul_of_nonneg_left hyj hc,
      congrArg (fun z : ℝ => z * j) hac]
  · nlinarith [mul_le_mul_of_nonneg_left hxt ha, mul_le_mul_of_nonneg_left hyt hc,
      congrArg (fun z : ℝ => z * t) hac]
private def padded (s offset : Shape) (r : ℝ) : Set RealPoint :=
  realCap (s.b + r * offset.b) (s.j + r * offset.j) (s.t + r * offset.t)
theorem padded_mono (s offset : Shape) : Monotone (padded s offset) := by
  intro r r' hr x hx
  obtain ⟨hx, hb, hj, ht⟩ := hx
  exact ⟨hx, hb.trans (by gcongr), hj.trans (by gcongr), ht.trans (by gcongr)⟩
private def grid (n : ℕ) : Set RealPoint :=
  (n : ℝ)⁻¹ • (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4))) : Set RealPoint)
theorem grid_finite {E : Set RealPoint} (hs : Bornology.IsBounded E) {n : ℕ} (hn : 0 < n) :
    (E ∩ grid n).Finite := by
  let L := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  let e : ↑(E ∩ grid n) ≃ ↑((n : ℝ) • E ∩ (L : Set RealPoint)) :=
    Equiv.subtypeEquiv (Equiv.smulRight hn0) (fun x => by
      change (x ∈ E ∧ x ∈ (n : ℝ)⁻¹ • (L : Set RealPoint)) ↔
        ((n : ℝ) • x ∈ (n : ℝ) • E ∧ (n : ℝ) • x ∈ (L : Set RealPoint))
      rw [Set.smul_mem_smul_set_iff₀ hn0, ← Set.mem_inv_smul_set_iff₀ hn0])
  let : Finite ↑((n : ℝ) • E ∩ (L : Set RealPoint)) := (ZSpan.setFinite_inter _ (hs.smul₀ _)).to_subtype
  let := Finite.of_equiv _ e.symm
  exact Set.toFinite _
theorem realCap_grid (b j t : ℝ) :
    Tendsto (fun n : ℕ => ((realCap b j t ∩ grid n).ncard : ℝ) / (n : ℝ)^4)
      atTop (𝓝 (volume (realCap b j t)).toReal) := by
  simpa only [grid, Nat.card_coe_set_eq, Fintype.card_fin, measureReal_def] using
    tendsto_card_div_pow_atTop_volume (realCap b j t) (realCap_compact b j t).isBounded
      (realCap_closed b j t).measurableSet ((realCap_convex b j t).addHaar_frontier volume)
theorem div_mem_padded (s offset : Shape) {n : ℕ} (hn : 0 < n) (e : Exponent) :
    (fun i => (e i : ℝ) / (n : ℝ)) ∈ padded s offset (n : ℝ)⁻¹ ↔
      e ∈ lattice ((s.scale n).plus offset) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h (x c o : ℝ) :
      x / (n : ℝ) ≤ c + (n : ℝ)⁻¹ * o ↔ x ≤ (n : ℝ) * c + o := by
    rw [div_le_iff₀ hn', add_mul, mul_right_comm ((n : ℝ)⁻¹) o (n : ℝ),
      inv_mul_cancel₀ hn'.ne', one_mul, mul_comm c (n : ℝ)]
  simp only [padded, realCap, lattice, Shape.scale, Shape.plus, Set.mem_ofPred_eq,
    ← mul_div_assoc, ← add_div, h]
  constructor
  · intro ⟨_, hb, hj, ht⟩
    exact ⟨by exact_mod_cast hb, by exact_mod_cast hj, by exact_mod_cast ht⟩
  · intro ⟨hb, hj, ht⟩
    exact ⟨fun _ => by positivity, by exact_mod_cast hb, by exact_mod_cast hj,
      by exact_mod_cast ht⟩
theorem count_grid (s offset : Shape) {n : ℕ} (hn : 0 < n) :
    (lattice ((s.scale n).plus offset)).ncard =
      (padded s offset (n : ℝ)⁻¹ ∩ grid n).ncard := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let f (e : lattice ((s.scale n).plus offset)) : ↑(padded s offset (n : ℝ)⁻¹ ∩ grid n) :=
    ⟨fun i => (e.val i : ℝ) / (n : ℝ),
     (div_mem_padded s offset hn e.val).mpr e.property,
     BoxIntegral.unitPartition.mem_smul_span_iff.mpr (fun i => ⟨(e.val i : ℤ), by
       simp [mul_comm (n : ℝ), hn'.ne']⟩)⟩
  have hi : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    ext i
    have hv : (e.val i : ℝ) / (n : ℝ) = (e'.val i : ℝ) / (n : ℝ) :=
      congrFun (congrArg Subtype.val he) i
    exact_mod_cast (div_left_inj' hn'.ne').mp hv
  have hs : Function.Surjective f := by
    intro x
    have hx := x.property.1
    have hx' : ∀ i : Fin 4, 0 ≤ x.val i := hx.1
    have hgrid := BoxIntegral.unitPartition.mem_smul_span_iff.mp x.property.2
    choose a ha using hgrid
    let e : Exponent := Finsupp.equivFunOnFinite.symm (fun i => (a i).toNat)
    have he (i : Fin 4) : (e i : ℝ) / (n : ℝ) = x.val i := by
      have hz : (a i : ℝ) = (n : ℝ) * x.val i := ha i
      have haz : 0 ≤ a i := by exact_mod_cast (hz.symm ▸ mul_nonneg hn'.le (hx' i))
      have hr : (e i : ℝ) = (a i : ℝ) := by
        change ((a i).toNat : ℝ) = (a i : ℝ)
        exact_mod_cast Int.toNat_of_nonneg haz
      rw [hr, hz, mul_comm (n : ℝ), mul_div_cancel_right₀ _ hn'.ne']
    have hfun : (fun i => (e i : ℝ) / (n : ℝ)) = x.val := funext he
    have hem := (div_mem_padded s offset hn e).mp (hfun.symm ▸ hx)
    exact ⟨⟨e, hem⟩, Subtype.ext hfun⟩
  exact Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)
theorem padded_limit (s offset : Shape) :
    Tendsto (fun m : ℕ => (volume (padded s offset ((m : ℝ) + 1)⁻¹)).toReal)
      atTop (𝓝 (volume (cap s)).toReal) := by
  let r (m : ℕ) : ℝ := ((m : ℝ) + 1)⁻¹
  let E (m : ℕ) := padded s offset (r m)
  have hr : Tendsto r atTop (𝓝 0) := by
    simpa only [r, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hmono : Antitone E := by
    intro a b hab
    apply padded_mono
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  have hE : (⋂ m : ℕ, E m) = cap s := by
    ext x
    rw [Set.mem_iInter]
    constructor
    · intro hx
      have h (a : ℕ) : Tendsto (fun m => r m * (a : ℝ)) atTop (𝓝 0) := by
        simpa only [zero_mul] using hr.mul_const (a : ℝ)
      have hbound (a b : ℕ) :
          Tendsto (fun m => (a : ℝ) + r m * (b : ℝ)) atTop (𝓝 (a : ℝ)) := by
        simpa only [add_zero] using (h b).const_add (a : ℝ)
      exact ⟨(hx 0).1, ge_of_tendsto' (hbound s.b offset.b) (fun m => (hx m).2.1),
        ge_of_tendsto' (hbound s.j offset.j) (fun m => (hx m).2.2.1),
        ge_of_tendsto' (hbound s.t offset.t) (fun m => (hx m).2.2.2)⟩
    · intro hx m
      have h₀ : padded s offset 0 = cap s := by simp only [padded, realCap, cap, zero_mul, add_zero]
      exact padded_mono s offset (show 0 ≤ r m by positivity) (h₀.symm ▸ hx)
  have ht := tendsto_measure_iInter_atTop (μ := volume)
    (s := E) (fun m => (realCap_closed _ _ _).measurableSet.nullMeasurableSet)
    hmono ⟨0, (realCap_compact _ _ _).measure_ne_top⟩
  rw [hE] at ht
  have hfin : volume (cap s) ≠ ⊤ := (realCap_compact _ _ _).measure_ne_top
  exact (ENNReal.continuousAt_toReal hfin).tendsto.comp ht
theorem lattice_limit (s offset : Shape) :
    Tendsto (fun n : ℕ => ((lattice ((s.scale n).plus offset)).ncard : ℝ) / (n : ℝ)^4)
      atTop (𝓝 (volume (cap s)).toReal) := by
  let E := padded s offset
  have hpad : E 0 = cap s := by simp only [E, padded, realCap, cap, zero_mul, add_zero]
  have h (r : ℝ) : Tendsto (fun n : ℕ => ((E r ∩ grid n).ncard : ℝ) / (n : ℝ)^4)
      atTop (𝓝 (volume (E r)).toReal) := realCap_grid _ _ _
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hlow := (tendsto_order.mp (h 0)).1 a (by simpa only [hpad] using ha)
    filter_upwards [hlow, eventually_gt_atTop 0] with n hn hn'
    rw [count_grid s offset hn']
    refine hn.trans_le (div_le_div_of_nonneg_right ?_ (by positivity))
    exact_mod_cast Set.ncard_le_ncard
      (Set.inter_subset_inter_left _ (padded_mono s offset (by positivity : 0 ≤ (n : ℝ)⁻¹)))
      (grid_finite (realCap_compact _ _ _).isBounded hn')
  · intro a ha
    obtain ⟨m, hm⟩ := ((tendsto_order.mp (padded_limit s offset)).2 a ha).exists
    have hhigh := (tendsto_order.mp (h ((m : ℝ)+1)⁻¹)).2 a hm
    filter_upwards [hhigh, eventually_ge_atTop (m + 1)] with n hn hn'
    have hn0 : 0 < n := by omega
    rw [count_grid s offset hn0]
    refine (div_le_div_of_nonneg_right ?_ (by positivity)).trans_lt hn
    have hge : ((m : ℝ) + 1) ≤ n := by exact_mod_cast hn'
    exact_mod_cast Set.ncard_le_ncard
      (Set.inter_subset_inter_left _ (padded_mono s offset
        (inv_anti₀ (by positivity) hge)))
      (grid_finite (realCap_compact _ _ _).isBounded hn0)
theorem lattice_asymptotic (s offset : Shape) :
    Tendsto (fun m : ℕ => ((lattice ((s.scale (2 * m)).plus offset)).ncard : ℝ) /
      (2 * (m : ℝ))^4) atTop (𝓝 (volume (cap s)).toReal) := by
  have h : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact (eventually_ge_atTop b).mono (fun m hm => by omega)
  simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using (lattice_limit s offset).comp h
end
end K1_13_7_1_1_1
end
section
namespace K1_13_7_1_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_7_1 K1_13_7_1_1 MvPolynomial MeasureTheory Filter
open scoped Pointwise Topology
private def sumShape (S : Fin 4 → Shape) (w : Grades) : Shape :=
  ((((S 0).scale (w 0)).plus ((S 1).scale (w 1))).plus ((S 2).scale (w 2))).plus
    ((S 3).scale (w 3))
private theorem sum_chamber {S : Fin 4 → Shape} (hS : ∀ i, Chamber (S i)) (w : Grades) :
    Chamber (sumShape S w) :=
  chamber_plus (chamber_plus (chamber_plus (chamber_scale (hS 0) _) (chamber_scale (hS 1) _))
    (chamber_scale (hS 2) _)) (chamber_scale (hS 3) _)
private theorem sum_zero (S : Fin 4 → Shape) : sumShape S 0 = ⟨0, 0, 0⟩ := by
  apply shape_eq <;> simp [sumShape, Shape.plus, Shape.scale]
private theorem sum_shift (S : Fin 4 → Shape) (w : Grades) (i : Fin 4) :
    sumShape S (w + Pi.single i 1) = (sumShape S w).plus (S i) := by
  fin_cases i <;> apply shape_eq <;>
    simp [sumShape, Shape.plus, Shape.scale, Nat.add_mul] <;> ac_rfl
theorem graded_lattice {S : Fin 4 → Shape} (hS : ∀ i, Chamber (S i)) (b : ℕ) (w : Grades) :
    gradedExponents (fun i => lattice ((S i).scale 2)) (lattice (auxShape.scale 2)) b w =
      lattice (((auxShape.scale b).plus (sumShape S w)).scale 2) := by
  have hB := chamber_scale aux_chamber b
  have h0 := chamber_scale (hS 0) (w 0)
  have h1 := chamber_scale (hS 1) (w 1)
  have h2 := chamber_scale (hS 2) (w 2)
  have h3 := chamber_scale (hS 3) (w 3)
  simp only [gradedExponents]
  rw [lattice_nsmul aux_chamber, lattice_nsmul (hS 0), lattice_nsmul (hS 1),
    lattice_nsmul (hS 2), lattice_nsmul (hS 3),
    ← lattice_add hB h0, ← lattice_add (chamber_plus hB h0) h1,
    ← lattice_add (chamber_plus (chamber_plus hB h0) h1) h2,
    ← lattice_add (chamber_plus (chamber_plus (chamber_plus hB h0) h1) h2) h3]
  congr 2
  apply shape_eq <;> simp [sumShape, Shape.plus, add_assoc]
theorem graded_shape_shift (S : Fin 4 → Shape) (b m : ℕ) (w x : Grades) :
    ((auxShape.scale b).plus (sumShape S (x + m • w))).scale 2 =
      ((sumShape S w).scale (2 * m)).plus (((auxShape.scale b).plus (sumShape S x)).scale 2) := by
  apply shape_eq <;>
    simp [sumShape, Shape.plus, Shape.scale, Pi.add_apply, nsmul_eq_mul] <;>
    ring
theorem hilbert_bot {A : Fin 4 → Set Exponent} {B : Set Exponent} {b : ℕ} {w : Grades}
    (hfin : (gradedExponents A B b w).Finite) :
    hilbert A B ⊥ b w = ((gradedExponents A B b w).ncard : ℝ) := by
  let e := (AlgEquiv.quotientBot GeoField GeoJets).symm.toLinearEquiv
  have he : (Ideal.Quotient.mkₐ GeoField (⊥ : Ideal GeoJets)).toLinearMap = e.toLinearMap := by
    ext x
    rfl
  unfold hilbert
  rw [he, LinearEquiv.finrank_map_eq]
  let := hfin.fintype
  rw [Module.finrank_eq_card_basis (basisRestrictSupport GeoField _),
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
theorem cap_hilbert {S : Fin 4 → Shape} (hS : ∀ i, Chamber (S i)) (b : ℕ) (w : Grades) :
    hilbert (fun i => lattice ((S i).scale 2)) (lattice (auxShape.scale 2)) ⊥ b w =
      ((lattice (((auxShape.scale b).plus (sumShape S w)).scale 2)).ncard : ℝ) := by
  rw [hilbert_bot, graded_lattice hS]
  rw [graded_lattice hS]
  exact lattice_finite _
theorem shifted_grade (x w : Grades) (m : ℕ) (i : Fin 4) :
    (x + m • w) + Pi.single i m = x + m • (w + Pi.single i 1) := by
  have h : Pi.single i m = m • (Pi.single i 1 : Grades) := by
    funext j
    by_cases he : j = i <;> simp [Pi.smul_apply, he]
  rw [h, nsmul_add, add_assoc]
theorem tendsto_gradeDifferences (dirs : List (Fin 4)) (x : Grades)
    (F : ℕ → Grades → ℝ) (G : Grades → ℝ)
    (h : ∀ w : Grades, Tendsto (fun m : ℕ => F m (x + m • w) / (2 * (m : ℝ))^4)
      atTop (𝓝 (G w))) (w : Grades) :
    Tendsto (fun m : ℕ =>
      gradeDifferences dirs m (F m) (x + m • w) / (2 * (m : ℝ))^4)
      atTop (𝓝 (gradeDifferences dirs 1 G w)) := by
  induction dirs generalizing F G with
  | nil => exact h w
  | cons i dirs ih =>
      apply ih (fun m => gradeDifference (F m) i m) (gradeDifference G i 1)
      intro y
      simp only [gradeDifference, shifted_grade, sub_div]
      exact (h (y + Pi.single i 1)).sub (h y)
theorem cap_gradeDifferences {S : Fin 4 → Shape} (hS : ∀ i, Chamber (S i))
    (dirs : List (Fin 4)) (V : Set RealPoint → ℝ) (w : Grades) :
    gradeDifferences dirs 1 (fun x => V (cap (sumShape S x))) w =
      dirs.foldl (fun H i => bodyDifference H (cap (S i))) V (cap (sumShape S w)) := by
  induction dirs generalizing V with
  | nil => rfl
  | cons i dirs ih =>
      have h : gradeDifference (fun x => V (cap (sumShape S x))) i 1 =
          fun x => bodyDifference V (cap (S i)) (cap (sumShape S x)) := by
        funext x
        rw [gradeDifference, bodyDifference, sum_shift, cap_add (sum_chamber hS _) (hS i)]
      simp only [gradeDifferences, List.foldl_cons, h]
      exact ih _
theorem cap_mixedDegree {p h : Shape} (hp : Chamber p) (hh : Chamber h)
    {d : ℝ}
    (hd : IsMixedDegree (fun i => lattice ((![p, p, h, h] i).scale 2))
      (lattice (auxShape.scale 2)) ⊥ 0 d) :
    d / 16 = mixedVolume (cap p) (cap p) (cap h) (cap h) := by
  let S : Fin 4 → Shape := ![p, p, h, h]
  have hS : ∀ i, Chamber (S i) := by intro i; fin_cases i <;> assumption
  obtain ⟨N, hd⟩ := hd
  let x : Grades := fun _ => N
  let F : Grades → ℝ := hilbert (fun i => lattice ((S i).scale 2)) (lattice (auxShape.scale 2)) ⊥ N
  let V : Set RealPoint → ℝ := fun Q => (volume Q).toReal
  have hF (w : Grades) : Tendsto (fun m : ℕ => F (x + m • w) / (2 * (m : ℝ))^4)
      atTop (𝓝 (V (cap (sumShape S w)))) := by
    have ht := lattice_asymptotic (sumShape S w) (((auxShape.scale N).plus (sumShape S x)).scale 2)
    simpa only [F, V, cap_hilbert hS, graded_shape_shift] using ht
  have ht := tendsto_gradeDifferences (remainingDirections 0) x (fun _ => F)
    (fun w => V (cap (sumShape S w))) hF 0
  simp only [nsmul_zero, add_zero] at ht
  rw [cap_gradeDifferences hS, sum_zero, cap_zero] at ht
  change Tendsto _ atTop (𝓝 (mixedVolume (cap p) (cap p) (cap h) (cap h))) at ht
  have he : (fun m : ℕ => (d / 16 : ℝ)) =ᶠ[atTop]
      (fun m : ℕ => gradeDifferences (remainingDirections 0) m F x / (2 * (m : ℝ))^4) := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    rw [hd N x m le_rfl (fun _ => le_rfl)]
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' he) ht
end
end K1_13_7_1_1_1
end
section
namespace K1_13_7_1_1_1
noncomputable section
open K1_13_6 K1_13_7_1 MvPolynomial
private def prefixIdeal (F : Fin 4 → GeoJets) (k : ℕ) : Ideal GeoJets :=
  Ideal.span (F '' {i | i.val < k})
theorem prefix_succ (F : Fin 4 → GeoJets) (i : Fin 4) :
    prefixIdeal F (i.val + 1) = prefixIdeal F i.val ⊔ Ideal.span {F i} := by
  unfold prefixIdeal
  rw [← Ideal.span_union]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases h : j.val < i.val
    · exact Or.inl ⟨j, h, rfl⟩
    · have he : j = i := Fin.ext (by omega)
      exact Or.inr (congrArg F he)
  · rintro (⟨j, hj, rfl⟩ | rfl)
    · exact ⟨j, by omega, rfl⟩
    · exact ⟨i, by omega, rfl⟩
private theorem previous {F : Fin 4 → GeoJets} {i : Fin 4} {Q : Ideal GeoJets}
    (hQ : Q ∈ (prefixIdeal F (i.val + 1)).minimalPrimes) :
    ∃ P ∈ (prefixIdeal F i.val).minimalPrimes,
      Q ∈ (P ⊔ Ideal.span {F i}).minimalPrimes := by
  rw [prefix_succ] at hQ
  let := hQ.isPrime
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hQ.le)
  refine ⟨P, hP, ⟨⟨hQ.isPrime, sup_le hPQ (le_sup_right.trans hQ.le)⟩, ?_⟩⟩
  intro J hJ hJQ
  exact hQ.2 ⟨hJ.1, (sup_le_sup_right hP.le _).trans hJ.2⟩ hJQ
theorem cutDrop {P Q : Ideal GeoJets} (hP : P.IsPrime) {f : GeoJets}
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    affineDim P ≤ affineDim Q + 1 ∧ (affineDim Q + 1 = affineDim P → f ∉ P) := by
  let := hP
  by_cases hf : f ∈ P
  · have hle : Ideal.span {f} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hf
    rw [sup_eq_left.mpr hle] at hQ
    have hQP : Q = P := le_antisymm (hQ.2 ⟨hP, le_rfl⟩ hQ.le) hQ.le
    subst Q
    exact ⟨by omega, by omega⟩
  · have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hf hQ
    exact ⟨hd.symm.le, fun _ => hf⟩
theorem point_dim (y : GeoPoint) : affineDim (pointIdeal y) = 0 := by
  apply natDegree_affineHilbertPolynomial_eq_zero_iff.mpr
  let f : GeoJets →ₐ[GeoField] GeoField := aeval y
  have hf : Function.Surjective f := fun c => ⟨C c, by simp [f]⟩
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
theorem pointIdeal_injective : Function.Injective pointIdeal := by
  intro y z h
  funext i
  have hf : MvPolynomial.X i - MvPolynomial.C (y i) ∈ pointIdeal y := by
    simp [pointIdeal, RingHom.mem_ker]
  rw [h] at hf
  have hz : z i - y i = 0 := by simpa [pointIdeal, RingHom.mem_ker] using hf
  exact (sub_eq_zero.mp hz).symm
theorem proper_chain {f g u v : GeoJets} {y : GeoPoint} (hy : Isolated f g u v y) :
    ∃ P : Fin 5 → Ideal GeoJets, P 0 = ⊥ ∧ P 4 = pointIdeal y ∧
      (∀ i, (P i).IsPrime ∧ affineDim (P i) = 4 - i.val) ∧
      ∀ i : Fin 4, ![f, g, u, v] i ∉ P i.castSucc ∧
        P i.succ ∈ (P i.castSucc ⊔ Ideal.span {![f, g, u, v] i}).minimalPrimes := by
  classical
  let F : Fin 4 → GeoJets := ![f, g, u, v]
  have hF : prefixIdeal F 4 = Ideal.span ({f, g, u, v} : Set GeoJets) := by
    unfold prefixIdeal
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, _, rfl⟩
      fin_cases i <;> simp [F]
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
      · exact ⟨3, by decide, rfl⟩
  let q := pointIdeal y
  have hq : q ∈ (prefixIdeal F 4).minimalPrimes := hF.symm ▸ hy
  obtain ⟨p3, hp3, hc3⟩ := previous (i := 3) hq
  obtain ⟨p2, hp2, hc2⟩ := previous (i := 2) hp3
  obtain ⟨p1, hp1, hc1⟩ := previous (i := 1) hp2
  obtain ⟨p0, hp0, hc0⟩ := previous (i := 0) hp1
  have hbot : prefixIdeal F 0 = ⊥ := by simp [prefixIdeal]
  have hp0eq : p0 = ⊥ := by
    change p0 ∈ (prefixIdeal F 0).minimalPrimes at hp0
    rw [hbot] at hp0
    exact le_antisymm (hp0.2 ⟨Ideal.isPrime_bot, le_rfl⟩ bot_le) bot_le
  have hd0 : affineDim p0 = 4 := by rw [hp0eq, affineDim, natDegree_affineHilbertPolynomial_bot]; simp
  have hd4 : affineDim q = 0 := point_dim y
  have h0 := cutDrop hp0.isPrime hc0
  have h1 := cutDrop hp1.isPrime hc1
  have h2 := cutDrop hp2.isPrime hc2
  have h3 := cutDrop hp3.isPrime hc3
  have hd1 : affineDim p1 = 3 := by omega
  have hd2 : affineDim p2 = 2 := by omega
  have hd3 : affineDim p3 = 1 := by omega
  refine ⟨![p0,p1,p2,p3,q], hp0eq, rfl, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨hp0.isPrime, hd0⟩
    · exact ⟨hp1.isPrime, hd1⟩
    · exact ⟨hp2.isPrime, hd2⟩
    · exact ⟨hp3.isPrime, hd3⟩
    · exact ⟨hq.isPrime, hd4⟩
  · intro i
    fin_cases i
    · exact ⟨h0.2 (by omega), hc0⟩
    · exact ⟨h1.2 (by omega), hc1⟩
    · exact ⟨h2.2 (by omega), hc2⟩
    · exact ⟨h3.2 (by omega), hc3⟩
end
end K1_13_7_1_1_1
end
section
namespace K1_13_7_1_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_7_1 K1_13_7_1_1 MvPolynomial MeasureTheory Filter
open scoped Pointwise Topology BigOperators
def c1 : Prop :=
  ∀ (A : Fin 4 → Set Exponent) (B : Set Exponent), admissible A B →
    ∃ D : Fin 5 → Ideal GeoJets → ℝ,
      (∀ i P, P.IsPrime → affineDim P = 4 - i.val →
        0 ≤ D i P ∧ IsMixedDegree A B P i.val (D i P)) ∧
      ∀ y : GeoPoint, D 4 (pointIdeal y) = 1
def c2 : Prop :=
  ∀ (A : Fin 4 → Set Exponent) (B : Set Exponent), admissible A B →
    ∀ (i : Fin 4) (P : Ideal GeoJets), P.IsPrime → affineDim P = 4 - i.val →
      ∀ f : GeoJets, f ∉ P → ((f ^ 2).support : Set Exponent) ⊆ A i →
        ∀ Q : Finset (Ideal GeoJets),
          (∀ q ∈ Q, q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) →
          ∀ (d : ℝ) (e : Ideal GeoJets → ℝ), IsMixedDegree A B P i.val d →
            (∀ q ∈ Q, IsMixedDegree A B q (i.val + 1) (e q)) →
            2 * ∑ q ∈ Q, e q ≤ d
theorem sum_biUnion_le_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (C : α → Finset β) (w : β → ℝ)
    (hw : ∀ a ∈ S, ∀ b ∈ C a, 0 ≤ w b) :
    ∑ b ∈ S.biUnion C, w b ≤ ∑ a ∈ S, ∑ b ∈ C a, w b := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have ih' := ih (fun x hx => hw x (Finset.mem_insert_of_mem hx))
      have h := Finset.sum_union_inter (s₁ := C a) (s₂ := S.biUnion C) (f := w)
      have hz : 0 ≤ ∑ b ∈ C a ∩ S.biUnion C, w b :=
        Finset.sum_nonneg fun b hb => hw a (Finset.mem_insert_self a S) b
          (Finset.mem_inter.mp hb).1
      linarith
theorem count_paths (hcut : c2) {A : Fin 4 → Set Exponent} {B : Set Exponent}
    (hAB : admissible A B) (D : Fin 5 → Ideal GeoJets → ℝ)
    (hD : ∀ i P, P.IsPrime → affineDim P = 4 - i.val →
        0 ≤ D i P ∧ IsMixedDegree A B P i.val (D i P))
    (hpoint : ∀ y : GeoPoint, D 4 (pointIdeal y) = 1)
    {f g u v : GeoJets} (hs : ∀ i : Fin 4, ((![f,g,u,v] i ^ 2).support : Set Exponent) ⊆ A i)
    (points : Finset GeoPoint) (hpts : ∀ y ∈ points, Isolated f g u v y) :
    16 * (points.card : ℝ) ≤ D 0 ⊥ := by
  classical
  let P (y : points) := Classical.choose (proper_chain (hpts y.val y.property))
  have hP (y : points) : P y 0 = ⊥ ∧ P y 4 = pointIdeal y.val ∧
      (∀ i, (P y i).IsPrime ∧ affineDim (P y i) = 4 - i.val) ∧
      ∀ i : Fin 4, ![f, g, u, v] i ∉ P y i.castSucc ∧
        P y i.succ ∈ (P y i.castSucc ⊔ Ideal.span {![f, g, u, v] i}).minimalPrimes :=
    Classical.choose_spec (proper_chain (hpts y.val y.property))
  let L (k : Fin 5) : Finset (Ideal GeoJets) := points.attach.image (fun y => P y k)
  let total (k : Fin 5) : ℝ := ∑ q ∈ L k, D k q
  have hPrime (k : Fin 5) (q : Ideal GeoJets) (hq : q ∈ L k) :
      q.IsPrime ∧ affineDim q = 4 - k.val := by
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hq
    exact (hP y).2.2.1 k
  have hstep (i : Fin 4) : 2 * total i.succ ≤ total i.castSucc := by
    let C (q : Ideal GeoJets) :=
      (points.attach.filter (fun y => P y i.castSucc = q)).image (fun y => P y i.succ)
    have hu : (L i.castSucc).biUnion C = L i.succ := by
      ext q
      constructor
      · intro hq
        obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp hq
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
        exact Finset.mem_image.mpr ⟨y, (Finset.mem_filter.mp hy).1, rfl⟩
      · intro hq
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
        refine Finset.mem_biUnion.mpr ⟨P y i.castSucc, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
        exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, rfl⟩, rfl⟩
    have hchild (p q : Ideal GeoJets) (hq : q ∈ C p) :
        q ∈ (p ⊔ Ideal.span {![f,g,u,v] i}).minimalPrimes := by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
      have hy' := (Finset.mem_filter.mp hy).2
      simpa only [hy'] using ((hP y).2.2.2 i).2
    have hC (p q : Ideal GeoJets) (hq : q ∈ C p) :
        0 ≤ D i.succ q ∧ IsMixedDegree A B q (i.val + 1) (D i.succ q) := by
      have hqm : q ∈ L i.succ := by
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_image.mpr ⟨y, (Finset.mem_filter.mp hy).1, rfl⟩
      exact hD _ _ (hPrime _ _ hqm).1 (hPrime _ _ hqm).2
    have hbound (p : Ideal GeoJets) (hp : p ∈ L i.castSucc) :
        2 * ∑ q ∈ C p, D i.succ q ≤ D i.castSucc p := by
      have hn : ![f,g,u,v] i ∉ p := by
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hp
        exact ((hP y).2.2.2 i).1
      obtain ⟨hp', hd⟩ := hPrime _ _ hp
      exact hcut A B hAB i p hp' hd _ hn (hs i) (C p) (hchild p)
        _ _ (hD _ _ hp' hd).2 (fun q hq => (hC p q hq).2)
    calc
      2 * total i.succ ≤ 2 * ∑ p ∈ L i.castSucc, ∑ q ∈ C p, D i.succ q := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        unfold total
        rw [← hu]
        exact sum_biUnion_le_sum _ _ _ (fun p _ q hq => (hC p q hq).1)
      _ = ∑ p ∈ L i.castSucc, 2 * ∑ q ∈ C p, D i.succ q := by rw [Finset.mul_sum]
      _ ≤ total i.castSucc := Finset.sum_le_sum hbound
  have hrootDim : affineDim (⊥ : Ideal GeoJets) = 4 := by
    rw [affineDim, natDegree_affineHilbertPolynomial_bot]
    simp
  have hroot : total 0 ≤ D 0 ⊥ := by
    have hL : L 0 ⊆ {⊥} := by
      intro q hq
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hq
      simp [(hP y).1]
    unfold total
    calc
      ∑ q ∈ L 0, D 0 q ≤ ∑ q ∈ ({⊥} : Finset (Ideal GeoJets)), D 0 q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hL
        intro q hq _
        obtain rfl := Finset.mem_singleton.mp hq
        exact (hD 0 ⊥ Ideal.isPrime_bot hrootDim).1
      _ = D 0 ⊥ := Finset.sum_singleton _ _
  have hterm : total 4 = (points.card : ℝ) := by
    have hi : Function.Injective (fun (y : points) => P y 4) := by
      intro y z he
      apply Subtype.ext
      apply pointIdeal_injective
      simpa only [(hP y).2.1, (hP z).2.1] using he
    have hw (q : Ideal GeoJets) (hq : q ∈ L 4) : D 4 q = 1 := by
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hq
      rw [(hP y).2.1, hpoint]
    unfold total
    rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul, mul_one]
    change ((points.attach.image _).card : ℝ) = _
    rw [Finset.card_image_of_injective _ hi, Finset.card_attach]
  have h0 := hstep 0
  have h1 := hstep 1
  have h2 := hstep 2
  have h3 := hstep 3
  change 2 * total 1 ≤ total 0 at h0
  change 2 * total 2 ≤ total 1 at h1
  change 2 * total 3 ≤ total 2 at h2
  change 2 * total 4 ≤ total 3 at h3
  linarith
theorem of_children (h1 : c1) (h2 : c2) : K1_13_7_1_1.c1 := by
  intro p h hp hh f g u v hf hg hu hv points hpts
  let S : Fin 4 → Shape := ![p,p,h,h]
  let A := fun i => lattice ((S i).scale 2)
  let B := lattice (auxShape.scale 2)
  have hAB : admissible A B := cap_admissible S
  obtain ⟨D, hD, hpoint⟩ := h1 A B hAB
  have hs (i : Fin 4) : ((![f,g,u,v] i ^ 2).support : Set Exponent) ⊆ A i := by
    fin_cases i
    · exact square_support hf
    · exact square_support hg
    · exact square_support hu
    · exact square_support hv
  have hc := count_paths h2 hAB D hD hpoint hs points (fun y hy => (hpts y hy).1)
  have hd : affineDim (⊥ : Ideal GeoJets) = 4 := by
    rw [affineDim, natDegree_affineHilbertPolynomial_bot]
    simp
  rw [← cap_mixedDegree hp hh (hD 0 ⊥ Ideal.isPrime_bot hd).2]
  linarith
end
end K1_13_7_1_1_1
end
section
set_option autoImplicit false
namespace K1_13_7_1_1_1_1
noncomputable section
open K1_13_6 K1_13_7_1_1_1 MvPolynomial
open K1_13_6_2_4_1 (Grade slotWeight piece)
abbrev hilbertRank (A : Fin 4 → Set Exponent) (B : Set Exponent) (P : Ideal GeoJets)
    (b : ℕ) (w : Grades) : ℕ :=
  Module.finrank GeoField ((restrictSupport GeoField (gradedExponents A B b w)).map
    (Ideal.Quotient.mkₐ GeoField P).toLinearMap)
def slotSupport (A : Fin 4 → Set Exponent) (B : Set Exponent) : Fin 5 → Set Exponent :=
  Fin.lastCases B A
abbrev TaggedVar (A : Fin 4 → Set Exponent) (B : Set Exponent) :=
  (j : Fin 5) × slotSupport A B j
def tagSlot (A : Fin 4 → Set Exponent) (B : Set Exponent) : TaggedVar A B → Fin 5 :=
  Sigma.fst
def tagEval (A : Fin 4 → Set Exponent) (B : Set Exponent) :
    MvPolynomial (TaggedVar A B) GeoField →ₐ[GeoField] GeoJets :=
  aeval fun v => monomial v.2.val 1
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def tagIdeal (A : Fin 4 → Set Exponent) (B : Set Exponent) (P : Ideal GeoJets) :
    Ideal (MvPolynomial (TaggedVar A B) GeoField) :=
  ((P.comap (tagEval A B)).homogeneousCore (piece (tagSlot A B))).toIdeal
def grade (b : ℕ) (w : Grades) : Grade :=
  Finsupp.equivFunOnFinite.symm (Fin.lastCases b w)
@[simp] theorem grade_last (b : ℕ) (w : Grades) : grade b w (Fin.last 4) = b := by
  change Fin.lastCases b w (Fin.last 4) = b
  rw [Fin.lastCases_last]
@[simp] theorem grade_four (b : ℕ) (w : Grades) : grade b w 4 = b :=
  grade_last b w
@[simp] theorem grade_cut (b : ℕ) (w : Grades) (i : Fin 4) :
    grade b w i.castSucc = w i := by
  simp [grade]
end
end K1_13_7_1_1_1_1
end
section
set_option autoImplicit false
namespace K1_13_7_1_1_1_1
noncomputable section
open K1_13_6 K1_13_7_1 K1_13_7_1_1_1 MvPolynomial Filter
open K1_13_6_2_4_1 (Grade Form Represents line line_eval totalDegree_le_of_lines)
open scoped Pointwise
private def bounded (n : ℕ) : Set Exponent := {e | e.degree ≤ n}
private theorem bounded_add (m n : ℕ) : bounded m + bounded n ⊆ bounded (m + n) := by
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp he
  change (a + b).degree ≤ m + n
  rw [map_add]
  exact Nat.add_le_add ha hb
theorem bounded_nsmul (S : Set Exponent) {m : ℕ} (h : S ⊆ bounded m) (n : ℕ) :
    n • S ⊆ bounded (n * m) := by
  induction n with
  | zero => simp [bounded]
  | succ n ih =>
    rw [succ_nsmul, Nat.succ_mul]
    exact (Set.add_subset_add ih h).trans (bounded_add _ _)
theorem finite_bounded {S : Set Exponent} (h : S.Finite) : ∃ m, S ⊆ bounded m := by
  obtain ⟨m, hm⟩ := (h.image Finsupp.degree).bddAbove
  exact ⟨m, fun e he => hm (Set.mem_image_of_mem _ he)⟩
private theorem common_bound {A : Fin 4 → Set Exponent} {B : Set Exponent}
    (h : admissible A B) : ∃ m, B ⊆ bounded m ∧ ∀ i, A i ⊆ bounded m := by
  classical
  obtain ⟨n, hn⟩ := finite_bounded h.2.1
  choose f hf using fun i => finite_bounded (h.1 i).1
  refine ⟨max n (Finset.univ.sup f), ?_, ?_⟩
  · intro e he
    change e.degree ≤ max n (Finset.univ.sup f)
    exact (show e.degree ≤ n from hn he).trans (le_max_left _ _)
  · intro i e he
    change e.degree ≤ max n (Finset.univ.sup f)
    exact (show e.degree ≤ f i from hf i he).trans
      ((Finset.le_sup (f := f) (Finset.mem_univ i)).trans (le_max_right _ _))
theorem hilbertRank_le {A : Fin 4 → Set Exponent} {B : Set Exponent} {m : ℕ}
    (hB : B ⊆ bounded m) (hA : ∀ i, A i ⊆ bounded m) (P : Ideal GeoJets)
    (b : ℕ) (w : Grades) :
    hilbertRank A B P b w ≤ affineHilbertFunction P
      (b * m + w 0 * m + w 1 * m + w 2 * m + w 3 * m) := by
  have hAdd {S T : Set Exponent} {a b : ℕ} (ha : S ⊆ bounded a) (hb : T ⊆ bounded b) :
      S + T ⊆ bounded (a + b) := (Set.add_subset_add ha hb).trans (bounded_add a b)
  have he : gradedExponents A B b w ⊆
      bounded (b * m + w 0 * m + w 1 * m + w 2 * m + w 3 * m) :=
    hAdd (hAdd (hAdd (hAdd (bounded_nsmul B hB b) (bounded_nsmul _ (hA 0) (w 0)))
      (bounded_nsmul _ (hA 1) (w 1))) (bounded_nsmul _ (hA 2) (w 2)))
      (bounded_nsmul _ (hA 3) (w 3))
  apply Submodule.finrank_mono
  exact Submodule.map_mono (restrictSupport_mono GeoField he)
theorem polynomial_degree_bound {A : Fin 4 → Set Exponent} {B : Set Exponent}
    (hAB : admissible A B) (P : Ideal GeoJets) {p : Form}
    (hp : Represents p (fun t => (hilbertRank A B P (t 4) (fun i => t i.castSucc) : ℚ))) :
    p.totalDegree ≤ affineDim P := by
  obtain ⟨M, hB, hA⟩ := common_bound hAB
  obtain ⟨N, hN⟩ := hp
  apply totalDegree_le_of_lines
  intro t ht
  let L : ℕ := t 4 * M + t 0 * M + t 1 * M + t 2 * M + t 3 * M
  have hEval : ∀ᶠ n : ℕ in atTop, (line t p).eval (n : ℚ) =
      (hilbertRank A B P ((n • t) 4) (fun i => (n • t) i.castSucc) : ℚ) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [line_eval]
    exact hN _ (fun j => hn.trans (Nat.le_mul_of_pos_right n (ht j)))
  have hNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ (line t p).eval (n : ℚ) :=
    hEval.mono fun n hn => hn.symm ▸ Nat.cast_nonneg _
  have hUpper : ∀ᶠ n : ℕ in atTop, (line t p).eval (n : ℚ) ≤
      ((affineHilbertPolynomial P).comp (Polynomial.C ((L + 1 : ℕ) : ℚ) * Polynomial.X)).eval
        (n : ℚ) := by
    obtain ⟨N₁, hN₁⟩ := exists_eval_affineHilbertPolynomial P
    filter_upwards [hEval, eventually_ge_atTop N₁] with n hn hlarge
    have hnL : N₁ ≤ n * (L + 1) :=
      hlarge.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos L))
    rw [hn, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      mul_comm (((L + 1 : ℕ) : ℚ)), ← Nat.cast_mul, hN₁ _ hnL]
    have hb := hilbertRank_le hB hA P ((n • t) 4) (fun i => (n • t) i.castSucc)
    have hscale : (n • t) 4 * M + (n • t) 0 * M + (n • t) 1 * M +
        (n • t) 2 * M + (n • t) 3 * M = n * L := by
      simp only [Finsupp.smul_apply, smul_eq_mul, L]
      ring
    change hilbertRank A B P ((n • t) 4) (fun i => (n • t) i.castSucc) ≤
      affineHilbertFunction P _ at hb
    have hbound : hilbertRank A B P ((n • t) 4) (fun i => (n • t) i.castSucc) ≤
        affineHilbertFunction P (n * L) := by
      rw [← hscale]
      exact hb
    exact_mod_cast hbound.trans ((affineHilbertFunction_mono P)
      (Nat.mul_le_mul_left n (Nat.le_succ L)))
  have hDegree := (Polynomial.natDegree_le_of_eventually_eval_natCast_le hNonneg hUpper).1
  refine hDegree.trans (Polynomial.natDegree_comp_le.trans ?_)
  simpa only [mul_one, pow_one] using
    Nat.mul_le_mul_left (affineDim P) (Polynomial.natDegree_C_mul_X_pow_le ((L + 1 : ℕ) : ℚ) 1)
end
end K1_13_7_1_1_1_1
end
section
namespace K1_13_7_1_1_2
open K1_13 K1_13_7_1 K1_13_7_1_1 MeasureTheory Set
open scoped ENNReal
local notation "I₀" => Icc (0 : ℝ)
private theorem volume_slices {α : Type*} [MeasureSpace α]
    [SigmaFinite (volume : Measure α)] {S : Set (ℝ × α)} {C : Set α}
    {d : ℝ} {f : ℝ → ℝ} (hS : MeasurableSet S) (hC : volume C < ∞)
    (hSC : S ⊆ I₀ d ×ˢ C)
    (hvol : ∀ x ∈ I₀ d, (volume (Prod.mk x ⁻¹' S)).toReal = f x) :
    (volume S).toReal = ∫ x in I₀ d, f x := by
  have hm := measurable_measure_prodMk_left (ν := (volume : Measure α)) hS
  have hf : ∀ᵐ x ∂(volume : Measure ℝ), volume (Prod.mk x ⁻¹' S) < ∞ :=
    ae_of_all _ fun x => (measure_mono (fun y hy => (hSC (show (x, y) ∈ S from hy)).2)).trans_lt hC
  change (((volume : Measure ℝ).prod (volume : Measure α)) S).toReal = _
  rw [Measure.prod_apply hS, ← integral_toReal hm.aemeasurable hf,
    ← integral_indicator measurableSet_Icc]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ I₀ d
  · simpa only [indicator_of_mem hx] using hvol x hx
  · have he : Prod.mk x ⁻¹' S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hx (hSC (show (x, y) ∈ S from hy)).1
    simp [he, hx]
private theorem integral_affine (a b d : ℝ) (hd : 0 ≤ d) :
    (∫ x in I₀ d, a + b * x) = a * d + b * d ^ 2 / 2 := by
  have hconst : IntervalIntegrable (fun _ : ℝ => a) volume 0 d :=
    continuous_const.intervalIntegrable _ _
  have hlin : IntervalIntegrable (fun x : ℝ => b * x) volume 0 d :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hd]
  calc
    (∫ x in 0..d, a + b * x) = (∫ _ in 0..d, a) + (∫ x in 0..d, b * x) :=
      intervalIntegral.integral_add hconst hlin
    _ = _ := by
      rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul b (fun x => x),
        integral_id, smul_eq_mul]
      ring
private def strip (A U : ℝ) : Set (ℝ × ℝ) :=
  {v | 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ v.1 ≤ U ∧ v.2 + v.1 ≤ A}
theorem volume_strip (A U : ℝ) (hU : 0 ≤ U) (hUA : U ≤ A) :
    (volume (strip A U)).toReal = A * U - U ^ 2 / 2 := by
  have hS : IsClosed (strip A U) := by
    simp only [strip, ofPred_and]
    repeat' apply IsClosed.inter
    all_goals exact isClosed_le (by fun_prop) (by fun_prop)
  have hsub : strip A U ⊆ I₀ U ×ˢ I₀ A := by
    rintro ⟨u, x⟩ h
    obtain ⟨hu, hx, huU, hxu⟩ := h
    exact ⟨⟨hu, huU⟩, ⟨hx, by linarith⟩⟩
  calc
    (volume (strip A U)).toReal = ∫ u in I₀ U, A + (-1) * u := by
      apply volume_slices hS.measurableSet isCompact_Icc.measure_lt_top hsub
      intro u hu
      have he : Prod.mk u ⁻¹' strip A U = I₀ (A - u) := by
        ext x
        change (0 ≤ u ∧ 0 ≤ x ∧ u ≤ U ∧ x + u ≤ A) ↔ _
        exact ⟨fun h => ⟨h.2.1, by linarith [h.2.2.2]⟩,
          fun h => ⟨hu.1, h.1, hu.2, by linarith [h.2]⟩⟩
      rw [he, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal (sub_nonneg.mpr (hu.2.trans hUA))]
      ring
    _ = A * U - U ^ 2 / 2 := by rw [integral_affine _ _ _ hU]; ring
private def base (B J : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {v | 0 ≤ v.1 ∧ 0 ≤ v.2.1 ∧ 0 ≤ v.2.2 ∧
    v.2.1 + 2 * v.1 ≤ J ∧ v.2.2 + v.2.1 + v.1 ≤ B}
theorem volume_base (B J : ℝ) (hJ : 0 ≤ J) (hJB : J ≤ B) :
    (volume (base B J)).toReal = J ^ 2 * (2 * B - J) / 8 := by
  have hS : IsClosed (base B J) := by
    simp only [base, ofPred_and]
    repeat' apply IsClosed.inter
    all_goals exact isClosed_le (by fun_prop) (by fun_prop)
  have hsub : base B J ⊆ I₀ (J / 2) ×ˢ (I₀ B ×ˢ I₀ B) := by
    rintro ⟨r, u, x⟩ h
    obtain ⟨hr, hu, hx, hj, hb⟩ := h
    exact ⟨⟨hr, by linarith⟩, ⟨hu, by linarith⟩, ⟨hx, by linarith⟩⟩
  calc
    (volume (base B J)).toReal =
        ∫ r in I₀ (J / 2), (B * J - J ^ 2 / 2) + (J - 2 * B) * r := by
      apply volume_slices hS.measurableSet
        (isCompact_Icc.prod isCompact_Icc).measure_lt_top hsub
      intro r hr
      have he : Prod.mk r ⁻¹' base B J = strip (B - r) (J - 2 * r) := by
        ext ⟨u, x⟩
        change (0 ≤ r ∧ 0 ≤ u ∧ 0 ≤ x ∧ u + 2 * r ≤ J ∧ x + u + r ≤ B) ↔
          (0 ≤ u ∧ 0 ≤ x ∧ u ≤ J - 2 * r ∧ x + u ≤ B - r)
        constructor
        · rintro ⟨_, hu, hx, hj, hb⟩
          exact ⟨hu, hx, by linarith, by linarith⟩
        · rintro ⟨hu, hx, hj, hb⟩
          exact ⟨hr.1, hu, hx, by linarith, by linarith⟩
      rw [he, volume_strip _ _ (by linarith [hr.2]) (by linarith [hr.1])]
      ring
    _ = J ^ 2 * (2 * B - J) / 8 := by
      rw [integral_affine _ _ _ (by positivity)]
      ring
private def coordinates : RealPoint ≃ᵐ ℝ × ℝ × ℝ × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last 3)).trans
    ((MeasurableEquiv.refl ℝ).prodCongr
      ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last 2)).trans
        ((MeasurableEquiv.refl ℝ).prodCongr
          ((MeasurableEquiv.piFinTwo (fun _ => ℝ)).trans MeasurableEquiv.prodComm))))
theorem coordinates_preserving : MeasurePreserving coordinates volume volume := by
  have hswap : MeasurePreserving (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ)
      volume volume := Measure.measurePreserving_swap
  exact ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (((MeasurePreserving.id (volume : Measure ℝ)).prod
      (hswap.comp (volume_preserving_piFinTwo fun _ => ℝ))).comp
      (volume_preserving_piFinSuccAbove (fun _ => ℝ) (Fin.last 2)))).comp
    (volume_preserving_piFinSuccAbove (fun _ => ℝ) (Fin.last 3))
def body (b j t : ℝ) : Set (ℝ × ℝ × ℝ × ℝ) :=
  {v | 0 ≤ v.1 ∧ v.1 ≤ t ∧ 0 ≤ v.2.1 ∧ 0 ≤ v.2.2.1 ∧ 0 ≤ v.2.2.2 ∧
    v.2.2.1 + 2 * v.2.1 + 3 * v.1 ≤ j ∧ v.2.2.2 + v.2.2.1 + v.2.1 + v.1 ≤ b}
theorem cap_eq_preimage (p : Shape) :
    cap p = coordinates ⁻¹' body p.b p.j p.t := by
  ext x
  change ((∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 + x 3 ≤ p.b ∧
    x 1 + 2 * x 2 + 3 * x 3 ≤ p.j ∧ x 3 ≤ p.t) ↔
    (0 ≤ x 3 ∧ x 3 ≤ p.t ∧ 0 ≤ x 2 ∧ 0 ≤ x 1 ∧ 0 ≤ x 0 ∧
      x 1 + 2 * x 2 + 3 * x 3 ≤ p.j ∧ x 0 + x 1 + x 2 + x 3 ≤ p.b)
  constructor
  · rintro ⟨h, hb, hj, ht⟩
    exact ⟨h 3, ht, h 2, h 1, h 0, hj, hb⟩
  · rintro ⟨h3, ht, h2, h1, h0, hj, hb⟩
    exact ⟨by intro i; fin_cases i <;> assumption, hb, hj, ht⟩
theorem volume_body (b j t : ℝ) (hbj : j ≤ b) (hjt : 3 * t ≤ j) :
    (volume (body b j t)).toReal =
      ∫ s in I₀ t, (j - 3 * s) ^ 2 * (2 * b - j + s) / 8 := by
  have hS : IsClosed (body b j t) := by
    simp only [body, ofPred_and]
    repeat' apply IsClosed.inter
    all_goals exact isClosed_le (by fun_prop) (by fun_prop)
  have hsub : body b j t ⊆ I₀ t ×ˢ (I₀ b ×ˢ (I₀ b ×ˢ I₀ b)) := by
    rintro ⟨s, r, u, x⟩ h
    obtain ⟨hs, hst, hr, hu, hx, hj, hb⟩ := h
    exact ⟨⟨hs, hst⟩, ⟨hr, by linarith⟩, ⟨hu, by linarith⟩, ⟨hx, by linarith⟩⟩
  apply volume_slices hS.measurableSet
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).measure_lt_top hsub
  intro s hs
  have he : Prod.mk s ⁻¹' body b j t = base (b - s) (j - 3 * s) := by
    ext ⟨r, u, x⟩
    change (0 ≤ s ∧ s ≤ t ∧ 0 ≤ r ∧ 0 ≤ u ∧ 0 ≤ x ∧
      u + 2 * r + 3 * s ≤ j ∧ x + u + r + s ≤ b) ↔
      (0 ≤ r ∧ 0 ≤ u ∧ 0 ≤ x ∧ u + 2 * r ≤ j - 3 * s ∧ x + u + r ≤ b - s)
    constructor
    · rintro ⟨_, _, hr, hu, hx, hj, hb⟩
      exact ⟨hr, hu, hx, by linarith, by linarith⟩
    · rintro ⟨hr, hu, hx, hj, hb⟩
      exact ⟨hs.1, hs.2, hr, hu, hx, by linarith, by linarith⟩
  rw [he, volume_base _ _ (by linarith [hs.2]) (by linarith [hs.1])]
  ring
theorem proof : K1_13_7_1_1.c2 := by
  intro p hp
  let b : ℝ := p.b
  let j : ℝ := p.j
  let t : ℝ := p.t
  have hbj : j ≤ b := by
    dsimp [j, b]
    exact_mod_cast hp.1
  have hjt : 3 * t ≤ j := by
    dsimp [j, t]
    exact_mod_cast hp.2
  have ht : 0 ≤ t := Nat.cast_nonneg _
  rw [cap_eq_preimage, coordinates_preserving.measure_preimage_equiv,
    volume_body b j t hbj hjt, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht, ← intervalIntegral.integral_const_mul]
  let A := 8 * b * j ^ 2 - 4 * j ^ 3
  let B := -24 * b * j + 14 * j ^ 2
  let C := 24 * b - 20 * j
  let F := fun s : ℝ => A * s + B * s ^ 2 + C * s ^ 3 + 9 * s ^ 4
  have hF (s : ℝ) :
      HasDerivAt F (32 * ((j - 3 * s) ^ 2 * (2 * b - j + s) / 8)) s := by
    have hid := hasDerivAt_id s
    have h := (((hid.const_mul A).add ((hid.pow 2).const_mul B)).add
      ((hid.pow 3).const_mul C)).add ((hid.pow 4).const_mul (9 : ℝ))
    convert h using 1
    · funext y
      rfl
    · norm_num [A, B, C]
      ring
  have hc : Continuous (fun s : ℝ => 32 * ((j - 3 * s) ^ 2 * (2 * b - j + s) / 8)) := by
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s)
    (hc.intervalIntegrable _ _)]
  push_cast [volume32]
  dsimp [F, A, B, C, b, j, t]
  ring
end K1_13_7_1_1_2
end
section
set_option autoImplicit false
namespace K1_13_7_1_2
noncomputable section
open K1_13 K1_13_6 K1_13_7_1
open scoped BigOperators
abbrev TaylorRing := MvPolynomial TaylorIndex GeoField
abbrev TaylorIdeal := Ideal TaylorRing
abbrev TaylorPoint := TaylorIndex → GeoField
abbrev dimension (A : TaylorIdeal) := (MvPolynomial.affineHilbertPolynomial A).natDegree
def pairIdeal (f g : GeoJets) : Ideal GeoJets := Ideal.span {f, g}
def retained (f g : GeoJets) (C : TaylorChart) : Finset (Ideal GeoJets) :=
  (pairIdeal f g).retainedMinimalPrimes C.denom
def initialIndex (i : Fin 4) : TaylorIndex := i.castLE (by decide : 4 ≤ taylorLength)
def project (z : TaylorPoint) : GeoPoint := z ∘ initialIndex
def chartPoint (C : TaylorChart) (y : GeoPoint) : TaylorPoint :=
  fun i => MvPolynomial.eval y (C.numerator i) / MvPolynomial.eval y C.denom
def imageIdeal (C : TaylorChart) (P : Ideal GeoJets) : TaylorIdeal :=
  MvPolynomial.vanishingIdeal GeoField
    (chartPoint C '' {y | y ∈ MvPolynomial.zeroLocus GeoField P ∧
      MvPolynomial.eval y C.denom ≠ 0})
def imageDenom (C : TaylorChart) : TaylorRing := MvPolynomial.rename initialIndex C.denom
def formPolynomial (a : AffineForm) : TaylorRing :=
  MvPolynomial.C a.1 + ∑ i, MvPolynomial.C (a.2 i) * MvPolynomial.X i
end
end K1_13_7_1_2
end
