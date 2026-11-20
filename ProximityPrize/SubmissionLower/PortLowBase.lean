import ProximityPrize.SubmissionLower.Fast072
import ProximityPrize.SubmissionLower.PortBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_9
noncomputable section
open Polynomial
open P0 (I K k node agreement)
open K1_13 (Geom embed extend Row Shape shape InBox Fits Contact remaining
  chart liftedChart mixed32 ceilDiv)
open scoped BigOperators
abbrev physicalDegree : ℕ := k - 1 + P0.lowCutoff.toNat
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev incidenceGap : ℕ := agreement - physicalDegree
abbrev anchorCutoff : ℕ := 90 * agreement - 1
abbrev primaryCutoff : ℕ := 3000 * agreement - 1
abbrev primaryBox : Shape := ⟨4012, 1650, 550⟩
abbrev sourceRank : ℕ := 1274885048030345631
abbrev layerWidth : ℕ := incidenceGap + 3
abbrev layerNeed : ℕ := 27317599434965
def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val) * a) ≤ D
structure Messages (w : I → K) (Γ : Finset K) (s : K → K[X]) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, agreement ≤ T.card ∧
    ∀ i ∈ T, (s γ).eval (node i) = w i
structure PoleData (Γ : Finset K) (s : K → K[X]) where
  H : Geom[X]
  monic : H.Monic
  small : 1 ≤ H.natDegree ∧ H.natDegree ≤ P0.lowCutoff.toNat
  nodes : ∀ i, H.eval (embed (node i)) ≠ 0
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ k - 1 + H.natDegree
  z : K → Geom
  injective : Function.Injective z
  c : Geom[X]
  q : Geom[X]
  a₀ : Geom[X]
  a₁ : Geom[X]
  c_unit : IsCoprime c H
  q_unit : IsCoprime q H
  a₀_unit : IsCoprime a₀ H
  regular : ∀ γ ∈ Γ, IsCoprime (a₀ + C (z γ) * a₁) H
  residue : ∀ γ ∈ Γ, H ∣ c * (a₀ + C (z γ) * a₁) * extend (s γ) + C (z γ) * q
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0 < (shape f).t ∧ InBox (shape f) ⟨120, 48, 10⟩ ∧
    TrueWeightLE f anchorCutoff
def LowerRow (g : Row 3) : Prop :=
  g ≠ 0 ∧ g.totalDegree ≤ 120 ∧ K1_13.indexDegree g ≤ 48 ∧ TrueWeightLE g anchorCutoff
structure Cover {n : ℕ} (Γ : Finset K) (s : K → K[X])
    (g : Row 3) (f : Fin n → Row 4) : Prop where
  lower : LowerRow g
  factors : ∀ i, SmallFactor (f i)
  different : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)
  fits : Fits (fun i => shape (f i))
  covers : ∀ γ ∈ Γ, K1_13.atJet g (extend (s γ)) = 0 ∨
    ∃ i, K1_13.OnFactor (f i) (extend (s γ))
def PrimaryRank (w : I → K) : Prop :=
  ∃ e : Fin sourceRank → Row 4, LinearIndependent Geom e ∧
    ∀ i, InBox (shape (e i)) primaryBox ∧ TrueWeightLE (e i) primaryCutoff ∧ Contact w (e i)
def ProperCut (f : Row 4) (Γ : Finset K) (s : K → K[X]) (l : ℕ) : Prop :=
  ∃ Q : Row 4, (¬ f ∣ Q) ∧ InBox (shape Q) primaryBox ∧ TrueWeightLE Q primaryCutoff ∧
    ∀ γ ∈ Γ, K1_13.OrderAt Q (extend (s γ)) l
def LayerBudget {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Prop :=
  layerNeed ≤
    ∑ r ∈ Finset.range (1 + primaryCutoff / layerWidth),
      remaining (∑ i, (r + 1 - l i) * (a i).b) (∑ i, (r + 1 - l i) * (a i).j)
def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩
def surfaceNumerator32 (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L + 1) p
  let b := liftedChart (L + 2) p
  min (mixed32 p q (chart (L + 1) p) (chart (L + 2) p))
    (mixed32 p q a b + (L + 1) * mixed32 p q g b + (L + 2) * mixed32 p q g a)
def physicalPrice (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32 p q) 32 +
    ceilDiv ((P0.t + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (P0.t * curves + 2 * incidenceGap * points) (32 * incidenceGap)
def fatPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := if x.t = 1 then linearChart p else chart (taylorLength + 4) p
  let q : Shape := ⟨952630000, 322000000, 0⟩
  let big : Shape := ⟨6300 + q.b / 33184, 2403 + q.j / 33184, 0⟩
  let cut : Shape := ⟨max (max h.b big.b) (max h.j (big.j + 1)),
    max h.j (big.j + 1), max 1 h.t⟩
  let divisors := ceilDiv (P0.t * mixed32 p big cut h) (32 * incidenceGap) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b^2 + 5 * physicalDegree * p.b * h.b + 1
  let singular := if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b^2 + 1 else 0
  let curves := ceilDiv (P0.t * mixed32 p q q h + incidenceGap * mixed32 p q q p)
    (32 * incidenceGap * 293711590)
  let isolated := ceilDiv (3 * q.j^2 * (2 * q.b - q.j)) (4 * 41481 * (41481 - 33184 + 1) * 1037)
  divisors + singular + curves + isolated
end
end P0_9
end
section
namespace P0_9
noncomputable section
open Polynomial
open P0 (K I k node AnchorModel AnchoredFamily)
open K1_13 (Geom embed extend Row Shape shape Fits atJet OnFactor FatEquations FatEligible)
open scoped BigOperators
def c1 : Prop :=
  ∀ w Γ s, Messages w Γ s →
    ∃ (n : ℕ) (g : Row 3) (f : Fin n → Row 4), Cover Γ s g f
def c2 : Prop := ∀ w, PrimaryRank w
def c3 : Prop :=
  ∀ w Γ s, Messages w Γ s → PrimaryRank w →
    ∀ n (g : Row 3) (f : Fin n → Row 4), Cover Γ s g f →
      ∃ l : Fin n → ℕ, LayerBudget (fun i => shape (f i)) l ∧
        ∀ i, 0 < l i → ProperCut (f i) Γ s (l i)
def c4 : Prop :=
  ∀ w Γ s, Messages w Γ s → PoleData Γ s →
    ∃ (book : Finset K) (E : FatEquations), book.card ≤ 140000 ∧
      ∀ γ ∈ Γ, γ ∉ book → E.holds (extend (s γ))
def c5 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow g →
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ 18479565405033887
def c6 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → Γ.card ≤ physicalPrice (shape f) l
def c7 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) → FatEligible (shape f) →
    ∀ E : FatEquations, (∀ γ ∈ Γ, E.holds (extend (s γ))) → Γ.card ≤ fatPrice (shape f)
def c8 : Prop :=
  ∀ n (a : Fin n → Shape) (l cost : Fin n → ℕ), Fits a → LayerBudget a l →
    (∀ i, 0 < l i → cost i ≤ physicalPrice (a i) (l i)) →
    (∀ i, FatEligible (a i) → cost i ≤ fatPrice (a i)) →
    (∑ i, cost i) ≤ 211033041011743389
theorem degree_at_height {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (γ : K) (hγ : γ ∈ Γ) : (F.scalar γ).natDegree ≤ k - 1 + M.overhead.toNat := by
  rcases (F.mark γ hγ).scalar_degree with h | h
  · simp [h]
  · omega
theorem messages_of_anchor {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (hw : M.overhead ≤ P0.lowCutoff) : Messages M.word Γ F.scalar := by
  refine ⟨F.distinct, ?_, ?_⟩
  · intro γ hγ
    have overhead_le : M.overhead.toNat ≤ P0.lowCutoff.toNat := Int.toNat_le_toNat hw
    exact (degree_at_height M F γ hγ).trans (Nat.add_le_add_left overhead_le _)
  · intro γ hγ
    let m := F.mark γ hγ
    exact ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩
theorem pole_of_anchor {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ P0.lowCutoff) : Nonempty (PoleData Γ F.scalar) := by
  have hmax : M.overhead.toNat ≤ (extend M.E).natDegree := by
    rw [Polynomial.natDegree_map]
    unfold P0.AnchorModel.overhead
    omega
  obtain ⟨H, hm, hd, hdiv⟩ := K1_13.trim_divisor _ (M.E_monic.map embed) _ hmax
  let z := fun γ => embed (M.label γ)
  have unit {P : K[X]} (hp : IsCoprime P M.E) : IsCoprime (extend P) H :=
    (hp.map (Polynomial.mapRingHom embed)).of_isCoprime_of_dvd_right hdiv
  have amp (γ : K) : extend (M.amplitude γ) = extend M.A₀ + C (z γ) * extend M.A₁ := by
    simp [P0.AnchorModel.amplitude, z]
  refine ⟨⟨H, hm, ?_, ?_, ?_, z, ?_, extend M.factor, extend M.Q, extend M.A₀,
    extend M.A₁, unit M.coprime_factor.symm, unit M.offset_reduced,
    unit M.first_amplitude_unit, ?_, ?_⟩⟩
  · rw [hd]
    exact ⟨by omega, Int.toNat_le_toNat hi⟩
  · intro i hz
    obtain ⟨U, hU⟩ := hdiv
    have he : (extend M.E).eval (embed (node i)) ≠ 0 := by
      rw [Polynomial.eval_map_apply]
      exact (map_ne_zero embed).mpr (M.E_nodes i)
    apply he
    change (M.E.map embed).eval _ = 0
    rw [hU, Polynomial.eval_mul, hz, zero_mul]
  · intro γ hγ
    rw [hd]
    exact degree_at_height M F γ hγ
  · intro a b hab
    exact sub_left_inj.mp (embed.injective hab)
  · intro γ hγ
    rw [← amp]
    exact unit (F.mark γ hγ).pole_unit
  · intro γ hγ
    have eqn := (F.mark γ hγ).identity
    have orig : M.factor * M.amplitude γ * F.scalar γ + C (M.label γ) * M.Q =
        M.E * M.decoder (F.mark γ hγ).bad := by rw [← eqn]; ring
    have mapped := congrArg (Polynomial.map embed) orig
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at mapped
    rw [← amp]
    exact mapped ▸ hdiv.trans (dvd_mul_right _ _)
theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ ⊆ Γ) : Messages w Δ s :=
  ⟨h.distinct.mono hΔ, fun γ hγ => h.degree γ (hΔ hγ), fun γ hγ => h.hits γ (hΔ hγ)⟩
theorem ProperCut.mono {f Γ s l Δ} (h : ProperCut f Γ s l) (hΔ : Δ ⊆ Γ) :
    ProperCut f Δ s l := by
  obtain ⟨Q, hf, hbox, hw, hQ⟩ := h
  exact ⟨Q, hf, hbox, hw, fun γ hγ => hQ γ (hΔ hγ)⟩
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (h5 : c5) (h6 : c6) (h7 : c7) (h8 : c8) : P0.c9 := by
  classical
  intro u D M Γ F lo hi
  let s := F.scalar
  have hmsg : Messages M.word Γ s := messages_of_anchor M F hi
  obtain ⟨pole⟩ := pole_of_anchor M F lo hi
  obtain ⟨n, g, f, cover⟩ := h1 _ _ _ hmsg
  obtain ⟨l, layers, cut⟩ := h3 _ _ _ hmsg (h2 _) _ _ _ cover
  obtain ⟨book, E, booked, hE⟩ := h4 _ _ _ hmsg pole
  let low := Γ.filter (fun γ => atJet g (extend (s γ)) = 0)
  have low_bound : low.card ≤ 18479565405033887 :=
    h5 _ _ _ (hmsg.mono (Finset.filter_subset _ _)) _ cover.lower
      (fun _ h => (Finset.mem_filter.mp h).2)
  let pieces (i : Fin n) := Γ.filter (fun γ => γ ∉ book ∧ OnFactor (f i) (extend (s γ)))
  have part_sub (i) : pieces i ⊆ Γ := Finset.filter_subset _ _
  have on_part i : ∀ γ ∈ pieces i, OnFactor (f i) (extend (s γ)) :=
    fun _ h => (Finset.mem_filter.mp h).2.2
  have total := h8 n (fun i => shape (f i)) l (fun i => (pieces i).card) cover.fits layers
    (fun i h => h6 _ _ _ (hmsg.mono (part_sub i)) _ (cover.factors i) (on_part i) _ h
      ((cut i h).mono (part_sub i)))
    (fun i h => h7 _ _ _ (hmsg.mono (part_sub i)) _ (cover.factors i) (on_part i) h E
      (fun γ hγ => hE γ (part_sub i hγ) (Finset.mem_filter.mp hγ).2.1))
  have covers : Γ ⊆ book ∪ low ∪ Finset.univ.biUnion pieces := by
    intro γ hγ
    by_cases hb : γ ∈ book
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
    rcases cover.covers γ hγ with hg | ⟨i, hfi⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hg⟩))
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, hb, hfi⟩⟩
  calc
    Γ.card ≤ _ := Finset.card_le_card covers
    _ ≤ (book.card + low.card) + ∑ i, (pieces i).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le)
    _ ≤ _ := by omega
end
end P0_9
end
section
namespace P0_9_1
noncomputable section
open K1_13 (Geom)
open P0_9 (physicalDegree anchorCutoff)
open PolynomialDifferential ReedSolomon.HiddenDerivative
def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 120 ∧
    u.some.weight (fun i => i.val) ≤ 48 ∧
    u (some 3) ≤ 10 ∧
    u (some 1) + u (some 2) + u (some 3) ≤ 48 - (u.some.degree - 113 + 1) / 2 ∧
    u.weight (differentialWeight physicalDegree) ≤ anchorCutoff
def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}
def anchorLocal (center received : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 90 center received).domRestrict anchorSpace
end
end P0_9_1
end
section
namespace P0_9_1
noncomputable section
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open scoped BigOperators
open private exponent_le_of_mem_translation_monomial from ProximityPrize.SubmissionLower.Fast064
private def truncateX : DifferentialPolynomial Geom 3 →ₗ[Geom] DifferentialPolynomial Geom 3 :=
  filterSupport (fun u => u none < 90)
private theorem origin_monomial_zero (u : JetVariable 3 →₀ ℕ) (a : Geom)
    (hu : 90 ≤ u none) :
    localConstraintAt 90 0 0 (monomial u a) = 0 := by
  have hm : (MvPolynomial.X none ^ u none * monomial (u.erase none) a :
      DifferentialPolynomial Geom 3) = monomial u a := by
    rw [MvPolynomial.X_pow_eq_monomial, monomial_mul_monomial, one_mul, Finsupp.single_add_erase]
  rw [← hm]
  apply (satisfiesLocalConstraints_iff_coeff_eq_zero 90 0 0 _).mpr
  intro e he
  rw [map_mul, map_pow, unscaledLocalSubstitution, bind₁_X_right]
  simp only [unscaledLocalImage, C_0, zero_add, MvPolynomial.X_pow_eq_monomial]
  rw [coeff_monomial_mul', ite_eq_right]
  rw [Finsupp.single_le_iff]
  rw [localContactOrder_eq] at he
  change u none ≤ e (localT 3) → False
  omega
private theorem origin_truncateX (Q : DifferentialPolynomial Geom 3) :
    localConstraintAt 90 0 0 (truncateX Q) = localConstraintAt 90 0 0 Q := by
  rw [Q.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hfilter : truncateX (monomial u (Q.coeff u)) =
      if u none < 90 then monomial u (Q.coeff u) else 0 := by
    ext v
    rw [truncateX, coeff_filterSupport]
    by_cases h : u = v
    · subst v
      by_cases hx : u none < 90 <;> simp [hx]
    · by_cases hx : u none < 90 <;> simp [hx, coeff_monomial, h]
  rw [hfilter]
  split
  · rfl
  · rw [map_zero, origin_monomial_zero _ _ (by omega)]
private theorem centered_old_eligible {u v : JetVariable 3 →₀ ℕ}
    (h : v ≤ u) (hu : AnchorEligible u) (hx : v none < 90) :
    K1_13_1.AnchorEligible v := by
  have hd : v.some.degree ≤ u.some.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun j _ => h (some j)
  have hi : v.some.weight (fun i => i.val) ≤ u.some.weight (fun i => i.val) := by
    rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum]
    exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right j.val (h (some j))
  obtain ⟨hdeg, hidx, hf, htail, _⟩ := hu
  have hcap : 48 - (u.some.degree - 113 + 1) / 2 ≤ 48 - (v.some.degree - 113 + 1) / 2 := by
    omega
  refine ⟨hd.trans hdeg, hi.trans hidx, (h _).trans hf, ?_, ?_⟩
  · exact (add_le_add (add_le_add (h _) (h _)) (h _)).trans (htail.trans hcap)
  · have hw := Finsupp.weight_le_weight
      (w := fun j : Fin 4 => 133671 - j.val) (w' := fun _ => 133671)
      (fun j => Nat.sub_le _ _) v.some
    have he : v.some.weight (fun _ => 133671) = 133671 * v.some.degree := by
      simp only [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, smul_eq_mul,
        Finset.mul_sum, Nat.mul_comm]
    rw [he] at hw
    have hweight : differentialWeight (d := 3) 133671 =
        fun j => j.elim 1 (fun i => 133671 - i.val) := by
      funext j
      cases j <;> rfl
    rw [← Finsupp.optionElim_some v, hweight, Finsupp.weight_optionElim, one_mul]
    calc
      _ ≤ 89 + 133671 * 120 :=
        Nat.add_le_add (Nat.le_of_lt_succ hx)
          (hw.trans (Nat.mul_le_mul_left _ (hd.trans hdeg)))
      _ ≤ _ := by decide
private theorem centered_in_old_space (x y : Geom) (Q : anchorSpace) :
    truncateX (globalPointTranslation x y (Q : DifferentialPolynomial Geom 3)) ∈
      K1_13_1.anchorSpace := by
  classical
  rw [(Q : DifferentialPolynomial Geom 3).as_sum, map_sum, map_sum]
  refine Submodule.sum_mem _ fun u hu => ?_
  apply (mem_restrictSupport_iff Geom).mpr
  intro v hv
  have hn := mem_support_iff.mp hv
  rw [truncateX, coeff_filterSupport] at hn
  split at hn
  · exact centered_old_eligible
      (exponent_le_of_mem_translation_monomial x y u v _ (mem_support_iff.mpr hn))
      (Q.property hu) (by assumption)
  · exact (hn rfl).elim
private theorem old_rank : K1_13_1.c1 :=
  K1_13_1_1.of_children K1_13_1_1_1.proof K1_13_1_1_2.proof K1_13_1_1_3.proof
theorem rank_local (x y : Geom) :
    Module.finrank Geom (LinearMap.range (anchorLocal x y)) ≤ 9199626 := by
  have hpositive (j : JetVariable 3) : differentialWeight 133671 j ≠ 0 := by
    cases j with
    | none => decide
    | some j =>
      have hj := j.isLt
      change 133671 - j.val ≠ 0
      omega
  have : Module.Finite Geom K1_13_1.anchorSpace :=
    restrictSupport_finite <|
      (Finsupp.finite_of_nat_weight_le _ hpositive _).subset fun _ hu => hu.2.2.2.2
  let f : anchorSpace →ₗ[Geom] DifferentialPolynomial Geom 3 :=
    (truncateX.comp (globalPointTranslation x y).toLinearMap).domRestrict anchorSpace
  let tr : anchorSpace →ₗ[Geom] K1_13_1.anchorSpace :=
    f.codRestrict K1_13_1.anchorSpace (centered_in_old_space x y)
  have h : anchorLocal x y = (K1_13_1.anchorLocal 0 0).comp tr := by
    apply LinearMap.ext
    intro Q
    change localConstraintAt 90 x y (Q : DifferentialPolynomial Geom 3) =
      localConstraintAt 90 0 0 (truncateX (globalPointTranslation x y Q))
    rw [origin_truncateX, localConstraintAt_eq_zero_globalPointTranslation]
  rw [h]
  exact (LinearMap.finrank_range_comp_le_left (K1_13_1.anchorLocal 0 0) tr).trans (old_rank 0 0)
end
end P0_9_1
end
section
set_option autoImplicit false
set_option maxRecDepth 2000
namespace P0_9_1
open K1_13 (Geom)
open PolynomialDifferential
open scoped BigOperators
private abbrev Exponent := JetVariable 3 →₀ ℕ
private def indexWeight (a b c : ℕ) : ℕ := a + 2 * b + 3 * c
private def gradeCeiling (a b c : ℕ) : ℕ :=
  min 120 (113 + 2 * (48 - (a + b + c)))
private def gradeSlots (a b c : ℕ) : ℕ :=
  gradeCeiling a b c + 1 - (a + b + c)
private def firstWidth (a b c : ℕ) : ℕ :=
  90 * 180217 - 133551 * gradeCeiling a b c + indexWeight a b c
private def abscissaWidth (a b c j : ℕ) : ℕ := firstWidth a b c + 133551 * j
private noncomputable def exponent (x v a b c : ℕ) : Exponent :=
  (Finsupp.equivFunOnFinite.symm ![v, a, b, c]).optionElim x
@[simp] private theorem exponent_none (x v a b c : ℕ) : exponent x v a b c none = x := by
  simp [exponent]
@[simp] private theorem exponent_some (x v a b c : ℕ) (i : Fin 4) :
    exponent x v a b c (some i) = ![v, a, b, c] i := by
  simp [exponent]
private theorem exponent_coordinates (u : Exponent) :
    exponent (u none) (u (some 0)) (u (some 1)) (u (some 2)) (u (some 3)) = u := by
  ext i
  cases i with
  | none => simp
  | some i => fin_cases i <;> simp
private theorem jet_weight (m : Fin 4 →₀ ℕ) (w : Fin 4 → ℕ) :
    m.weight w = m 0 * w 0 + m 1 * w 1 + m 2 * w 2 + m 3 * w 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ, smul_eq_mul, add_assoc]
private theorem true_weight (x v a b c : ℕ) :
    (exponent x v a b c).weight (differentialWeight 133551) =
      x + (v * 133551 + a * 133550 + b * 133549 + c * 133548) := by
  have hw : differentialWeight (d := 3) 133551 = fun i =>
      i.elim 1 (fun k => 133551 - k.val) := by
    funext i
    cases i <;> rfl
  rw [hw, exponent, Finsupp.weight_optionElim, jet_weight]
  simp
private theorem eligible_exponent (x v a b c : ℕ) :
    AnchorEligible (exponent x v a b c) ↔
      c ≤ 10 ∧ indexWeight a b c ≤ 48 ∧ v + (a + b + c) ≤ gradeCeiling a b c ∧
        x + 133551 * (v + (a + b + c)) < 90 * 180217 + indexWeight a b c := by
  unfold AnchorEligible gradeCeiling indexWeight
  rw [show P0_9.physicalDegree = 133551 from rfl,
    Finsupp.degree_eq_weight_one, jet_weight, jet_weight, true_weight]
  simp only [mul_one, Finsupp.some_apply, exponent_some, Matrix.cons_val_zero, le_min_iff]
  change (v + a + b + c ≤ 120 ∧ v * 0 + a * 1 + b * 2 + c * 3 ≤ 48 ∧
    c ≤ 10 ∧ a + b + c ≤ 48 - (v + a + b + c - 113 + 1) / 2 ∧
    x + (v * 133551 + a * 133550 + b * 133549 + c * 133548) ≤ 90 * 180217 - 1) ↔ _
  by_cases h : a + b + c = 0 <;> omega
private theorem width_iff (a b c j x : ℕ) (hj : j ≤ gradeCeiling a b c) :
    x < abscissaWidth a b c j ↔
      x + 133551 * (gradeCeiling a b c - j) < 90 * 180217 + indexWeight a b c := by
  have hgrade : gradeCeiling a b c ≤ 120 := min_le_left _ _
  unfold abscissaWidth firstWidth
  omega
private abbrev Slot :=
  Σ c : Fin 11, Σ b : Fin ((48 - 3 * c.val) / 2 + 1),
    Σ a : Fin (48 - 3 * c.val - 2 * b.val + 1),
      Σ j : Fin (gradeSlots a.val b.val c.val),
        Fin (abscissaWidth a.val b.val c.val j.val)
private abbrev Eligible := {u : Exponent // AnchorEligible u}
private theorem slot_bounds (c b a j x : ℕ) :
    (c < 11 ∧ b < (48 - 3 * c) / 2 + 1 ∧ a < 48 - 3 * c - 2 * b + 1 ∧
      j < gradeSlots a b c ∧ x < abscissaWidth a b c j) ↔
    (c ≤ 10 ∧ indexWeight a b c ≤ 48 ∧ j + (a + b + c) ≤ gradeCeiling a b c ∧
      x < abscissaWidth a b c j) := by
  unfold indexWeight gradeSlots
  omega
private noncomputable def slotExponent (q : Slot) : Eligible := by
  rcases q with ⟨c, b, a, j, x⟩
  refine ⟨exponent x (gradeCeiling a b c - j - (a.val + b.val + c.val)) a b c, ?_⟩
  obtain ⟨hc, hi, hj, hx⟩ := (slot_bounds c b a j x).mp
    ⟨c.isLt, b.isLt, a.isLt, j.isLt, x.isLt⟩
  have hg : gradeCeiling a b c - j - (a.val + b.val + c.val) + (a.val + b.val + c.val) =
      gradeCeiling a b c - j := by omega
  rw [eligible_exponent, hg]
  exact ⟨hc, hi, by omega, (width_iff a b c j x (by omega)).mp hx⟩
private theorem slotExponent_injective : Function.Injective slotExponent := by
  rintro ⟨⟨c, hc⟩, ⟨b, hb⟩, ⟨a, ha⟩, ⟨j, hj⟩, ⟨x, hx⟩⟩
    ⟨⟨c', hc'⟩, ⟨b', hb'⟩, ⟨a', ha'⟩, ⟨j', hj'⟩, ⟨x', hx'⟩⟩ h
  have ec : c = c' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 3)) h
  have eb : b = b' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 2)) h
  have ea : a = a' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 1)) h
  have ex : x = x' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val none) h
  subst c'
  subst b'
  subst a'
  subst x'
  have ev : gradeCeiling a b c - j - (a + b + c) =
      gradeCeiling a b c - j' - (a + b + c) := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 0)) h
  have ej : j = j' := by
    change j < gradeSlots a b c at hj
    change j' < gradeSlots a b c at hj'
    unfold gradeSlots at hj hj'
    omega
  subst j'
  rfl
private theorem slotExponent_surjective : Function.Surjective slotExponent := by
  intro u
  let x := u.val none
  let v := u.val (some 0)
  let a := u.val (some 1)
  let b := u.val (some 2)
  let c := u.val (some 3)
  have he : exponent x v a b c = u.val := exponent_coordinates u.val
  obtain ⟨hc, hi, hg, hx⟩ := (eligible_exponent x v a b c).mp (he.symm ▸ u.property)
  let j := gradeCeiling a b c - (v + (a + b + c))
  have hj : j ≤ gradeCeiling a b c := Nat.sub_le _ _
  have hj' : gradeCeiling a b c - j = v + (a + b + c) := by
    dsimp [j]
    omega
  obtain ⟨hc', hb', ha', hj'', hx'⟩ := (slot_bounds c b a j x).mpr
    ⟨hc, hi, by dsimp [j]; omega, (width_iff a b c j x hj).mpr (hj'.symm ▸ hx)⟩
  refine ⟨⟨⟨c, hc'⟩, ⟨b, hb'⟩, ⟨a, ha'⟩, ⟨j, hj''⟩, ⟨x, hx'⟩⟩, Subtype.ext ?_⟩
  change exponent x (gradeCeiling a b c - j - (a + b + c)) a b c = u.val
  have hv : gradeCeiling a b c - j - (a + b + c) = v := by omega
  rwa [hv]
private def sumRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumRange f n + f n
private theorem sumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange, Finset.sum_range_succ, ih]
private theorem sumRange_eq_fin (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i : Fin n, f i := by
  rw [Fin.sum_univ_eq_sum_range, sumRange_eq]
private def tripleCount (a b c : ℕ) : ℕ :=
  let n := gradeSlots a b c
  n * firstWidth a b c + 133551 * (n * (n - 1) / 2)
private theorem sum_abscissaWidth (a b c : ℕ) :
    (∑ j : Fin (gradeSlots a b c), abscissaWidth a b c j) = tripleCount a b c := by
  rw [Fin.sum_univ_eq_sum_range (abscissaWidth a b c)]
  simp [abscissaWidth, tripleCount, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, Finset.sum_range_id]
private def rowCount (b c : ℕ) : ℕ :=
  sumRange (fun a => tripleCount a b c) (48 - 3 * c - 2 * b + 1)
private def sliceCount (c : ℕ) : ℕ :=
  sumRange (fun b => rowCount b c) ((48 - 3 * c) / 2 + 1)
private theorem slot_card : Fintype.card Slot = sumRange sliceCount 11 := by
  simp only [Slot, sliceCount, rowCount, Fintype.card_sigma, Fintype.card_fin, sumRange_eq_fin,
    sum_abscissaWidth]
private def rowTable : ℕ → List ℕ
  | 0 => [32035005198,30681091193,29331597631,27986791616,26646940252,25312370551,23983008873,22658588120,
      21338841194,20023500997,18712300431,17404972398,16101249800,14800865539,13503552517,12209043636,
      10917071798,9627369905,8339670859,7053707562,5769212916,4485919823,3203561185,1921869904,
      640578882]
  | 1 => [30308361331,28947469572,27591666011,26241277660,24896230879,23556258570,22221093635,20890468976,
      19564117495,18241772094,16923165675,15608031140,14296101391,12987109330,11680787859,10376869880,
      9075088295,7775176006,6476865915,5179890924,3883983935,2588877850,1294305571]
  | 2 => [28552344086,27186003537,25825138105,24469480692,23118764200,21772721531,20431085587,19093589270,
      17759965482,16429947125,15103267101,13779658312,12458853660,11140586047,9824588375,8510593546,
      7198334462,5887544025,4577955137,3269300700,1961313616,653726787]
  | 3 => [26769864100,25398388035,24031986438,22670392211,21313338256,19960557475,18611782770,17266747043,
      15925183196,14586824131,13251402750,11918651955,10588304648,9260093731,7933752106,6609012675,
      5285608340,3963272003,2641736566,1320734931]
  | 4 => [24960893898,23583614565,22211009051,20842810258,19478751088,18118564443,16761983225,15408740336,
      14058568678,12711201153,11366370663,10023810110,8683252396,7344430423,6007077093,4670925308,
      3335707970,2001157981,667008243]
  | 5 => [23124231521,21740481168,20361003985,18985532874,17613800737,16245540476,14880484993,13518367190,
      12158919969,10801876232,9446968881,8093930818,6742494945,5392394164,4043361377,2695129486,
      1347431393]
  | 6 => [21258675010,19867785885,18480769281,17097358100,15717285244,14340283615,12966086115,11594425646,
      10225035110,8857647409,7491995445,6127812120,4764830336,3402782995,2041402999,680423250]
  | 7 => [19363022406,17964326757,16569102980,15177083977,13788002650,12401591901,11017584632,9635713745,
      8255712142,6877312725,5500248396,4124252057,2749056610,1374394957]
  | 8 => [17436071750,16028901825,14624803123,13223508546,11824750996,10428263375,9033778585,7641029528,
      6249749106,4859670221,3470525775,2082048670,693971808]
  | 9 => [15476621083,14060309130,12646667751,11235429848,9826328323,8419096078,7013466015,5609171036,
      4205944043,2803517938,1401625623]
  | 10 => [13483468446,12057346713,10633494905,9211645924,7791532672,6372888051,4955444963,3538936310,
      2123094994,707653917]
  | _ => []
private theorem row0 (b : Fin 25) : rowCount b 0 = (rowTable 0)[b.val]! := by
  fin_cases b <;> decide
private theorem row1 (b : Fin 23) : rowCount b 1 = (rowTable 1)[b.val]! := by
  fin_cases b <;> decide
private theorem row2 (b : Fin 22) : rowCount b 2 = (rowTable 2)[b.val]! := by
  fin_cases b <;> decide
private theorem row3 (b : Fin 20) : rowCount b 3 = (rowTable 3)[b.val]! := by
  fin_cases b <;> decide
private theorem row4 (b : Fin 19) : rowCount b 4 = (rowTable 4)[b.val]! := by
  fin_cases b <;> decide
private theorem row5 (b : Fin 17) : rowCount b 5 = (rowTable 5)[b.val]! := by
  fin_cases b <;> decide
private theorem row6 (b : Fin 16) : rowCount b 6 = (rowTable 6)[b.val]! := by
  fin_cases b <;> decide
private theorem row7 (b : Fin 14) : rowCount b 7 = (rowTable 7)[b.val]! := by
  fin_cases b <;> decide
private theorem row8 (b : Fin 13) : rowCount b 8 = (rowTable 8)[b.val]! := by
  fin_cases b <;> decide
private theorem row9 (b : Fin 11) : rowCount b 9 = (rowTable 9)[b.val]! := by
  fin_cases b <;> decide
private theorem row10 (b : Fin 10) : rowCount b 10 = (rowTable 10)[b.val]! := by
  fin_cases b <;> decide
private theorem rowTable_correct (c : Fin 11) :
    ∀ b : Fin ((48 - 3 * c.val) / 2 + 1), rowCount b c = (rowTable c)[b.val]! := by
  fin_cases c
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
private def sliceTotals : List ℕ :=
  [404688682780,360604969994,319004761383,279307633360,242235876882,
    207191950209,174914598560,144797405935,117597073308,92698176868,
    70875506895]
private theorem sliceCount_eq (c : Fin 11) : sliceCount c = sliceTotals[c.val]! := by
  unfold sliceCount
  rw [sumRange_eq_fin]
  calc
    _ = ∑ b : Fin ((48 - 3 * c.val) / 2 + 1), (rowTable c)[b.val]! :=
      Finset.sum_congr rfl fun b _ => rowTable_correct c b
    _ = _ := by
      rw [← sumRange_eq_fin]
      fin_cases c <;> decide
private theorem totalCount : sumRange sliceCount 11 = 2413916636174 := by
  rw [sumRange_eq_fin]
  calc
    _ = ∑ c : Fin 11, sliceTotals[c.val]! :=
      Finset.sum_congr rfl fun c _ => sliceCount_eq c
    _ = _ := by rw [← sumRange_eq_fin]; decide
theorem anchor_finrank : Module.finrank Geom anchorSpace = 2413916636174 := by
  let e : Slot ≃ Eligible :=
    Equiv.ofBijective slotExponent ⟨slotExponent_injective, slotExponent_surjective⟩
  let b := MvPolynomial.basisRestrictSupport Geom {u : Exponent | AnchorEligible u}
  exact (Module.finrank_eq_card_basis (b.reindex e.symm)).trans (slot_card.trans totalCount)
end P0_9_1
end
section
namespace P0_9_2
noncomputable section
open K1_13 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open K1_13_2 (SourcePolynomial SourceExponent Local topWeight toRow)
open P0 (I K node)
open MvPolynomial (mem_support_iff)
def SourceEligible (e : SourceExponent) : Prop :=
  e.weight jetDegreeWeight ≤ 4012 ∧
  e.weight jetDerivativeWeight ≤ 1650 ∧
  e.weight topWeight ≤ 550 ∧
  e.weight (differentialWeight 133551) ≤ 3000 * 180217 - 1
def sourceExponents : Set SourceExponent := { e | SourceEligible e }
theorem sourceExponents_finite : sourceExponents.Finite := by
  refine (Finsupp.finite_of_nat_weight_le (differentialWeight (d := 3) 133551)
    ?_ (3000 * 180217 - 1)).subset (fun e he => he.2.2.2)
  intro v
  cases v with
  | none => decide
  | some j =>
    exact (differentialWeight_some_pos_of_order_lt_degree (by decide : 3 < 133551) j).ne'
def sourceColumns : Finset SourceExponent := sourceExponents_finite.toFinset
def SourceSpace : Submodule Geom SourcePolynomial :=
  MvPolynomial.restrictSupport Geom sourceExponents
instance : Module.Finite Geom SourceSpace :=
  MvPolynomial.restrictSupport_finite sourceExponents_finite
private theorem weight_eq_sum (m : Fin 4 →₀ ℕ) (weight : Fin 4 → ℕ) :
    m.weight weight = m.sum (fun i a => weight i * a) := by
  simp only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm]
theorem row_bounds (Q : SourceSpace) :
    InBox (shape (toRow Q.1)) ⟨4012, 1650, 550⟩ ∧
    P0_9.TrueWeightLE (toRow Q.1) (3000 * 180217 - 1) := by
  classical
  have h (m : Fin 4 →₀ ℕ) (hm : m ∈ (toRow Q.1).support) :
      m.sum (fun _ a => a) ≤ 4012 ∧
      m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
      ((toRow Q.1).coeff m).natDegree + m.sum (fun i a => (133551 - i.val) * a) ≤
        3000 * 180217 - 1 := by
    let n := ((toRow Q.1).coeff m).natDegree
    have hc : (Q.1).coeff (m.optionElim n) ≠ 0 := by
      rw [← MvPolynomial.optionEquivRight_coeff_coeff]
      change ((toRow Q.1).coeff m).coeff n ≠ 0
      rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
      exact mem_support_iff.mp hm
    have supportBound : ∀ e ∈ Q.1.support, SourceEligible e := Q.2
    obtain ⟨hb, hj, ht, hw⟩ := supportBound _ (mem_support_iff.mpr hc)
    have jb : jetDegreeWeight (d := 3) = (fun v => v.elim 0 (fun _ => 1)) := by
      funext v; cases v <;> rfl
    have ji : jetDerivativeWeight (d := 3) = (fun v => v.elim 0 (fun i => i.val)) := by
      funext v; cases v <;> rfl
    have jw : differentialWeight (d := 3) 133551 =
        (fun v => v.elim 1 (fun i => 133551 - i.val)) := by
      funext v; cases v <;> rfl
    rw [jb] at hb
    rw [ji] at hj
    rw [jw] at hw
    change (m.optionElim n).weight (fun v => v.elim 0 (Pi.single (3 : Fin 4) (1 : ℕ))) ≤ 550 at ht
    simp only [Finsupp.weight_optionElim, zero_mul, zero_add, one_mul] at hb hj ht hw
    rw [Finsupp.weight_single_one_apply] at ht
    rw [weight_eq_sum m (fun _ => 1)] at hb
    rw [weight_eq_sum m (fun i => i.val)] at hj
    rw [weight_eq_sum m (fun i => 133551 - i.val)] at hw
    exact ⟨by simpa only [one_mul] using hb, hj, ht, hw⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact Finset.sup_le fun m hm => (h m hm).1
  · exact Finset.sup_le fun m hm => (h m hm).2.1
  · exact MvPolynomial.degreeOf_le_iff.mpr fun m hm => (h m hm).2.2.1
  · exact fun m hm => (h m hm).2.2.2
theorem translate_mem_source (x y : Geom) (Q : SourceSpace) :
    globalPointTranslation x y Q.1 ∈ SourceSpace := by
  have preserve (wt : JetVariable 3 → ℕ) (B : ℕ)
      (h : ∀ e ∈ Q.1.support, e.weight wt ≤ B) :
      ∀ e ∈ (globalPointTranslation x y Q.1).support, e.weight wt ≤ B :=
    MvPolynomial.mem_restrictWeightAtMost.mp
      (globalPointTranslation_mem_restrictWeightAtMost (Nat.zero_le _) (Nat.zero_le _)
        x y (MvPolynomial.mem_restrictWeightAtMost.mpr h))
  have h : ∀ e ∈ Q.1.support, SourceEligible e :=
    Q.2
  exact fun e he =>
    ⟨preserve jetDegreeWeight 4012 (fun t ht => (h t ht).1) e he,
      preserve jetDerivativeWeight 1650 (fun t ht => (h t ht).2.1) e he,
      preserve topWeight 550 (fun t ht => (h t ht).2.2.1) e he,
      preserve (differentialWeight 133551) (3000 * 180217 - 1)
        (fun t ht => (h t ht).2.2.2) e he⟩
def nodeMap (x y : Geom) : SourceSpace →ₗ[Geom] Local :=
  (localConstraintAt 3000 x y).domRestrict SourceSpace
def wordMap (w : I → K) : SourceSpace →ₗ[Geom] (I → Local) :=
  LinearMap.pi fun i => nodeMap (embed (node i)) (embed (w i))
private theorem pointContact {m : ℕ} (x y : Geom) (Q : SourcePolynomial) (S : Geom[X])
    (hS : S.eval x = y) (hQ : SatisfiesLocalConstraints m x y Q) :
    (Polynomial.X - Polynomial.C x) ^ m ∣ differentialSpecialization Q S := by
  exact X_sub_C_pow_dvd_differentialSpecialization_of_contact Q S x y hS hQ
theorem contact_of_word_kernel (w : I → K) (Q : SourceSpace) (hQ : wordMap w Q = 0) :
    Contact w (toRow Q.1) := by
  intro i S hS
  rw [K1_13_2.atJet_toRow]
  have hi : SatisfiesLocalConstraints (d := 3) 3000 (embed (node i)) (embed (w i)) Q.1 := by
    exact congrFun hQ i
  have hd := pointContact (embed (node i)) (embed (w i)) Q.1 S hS hi
  with_reducible exact hd
theorem finrank_source : Module.finrank Geom SourceSpace = sourceColumns.card := by
  have h : (↑sourceColumns : Set SourceExponent) = sourceExponents :=
    Set.Finite.coe_toFinset sourceExponents_finite
  rw [SourceSpace, ← h]
  exact MvPolynomial.finrank_restrictSupport_finset (K := Geom) sourceColumns
end
end P0_9_2
end
section
namespace P0_9_2
noncomputable section
open K1_13_2 (SourceExponent topWeight)
open PolynomialDifferential ReedSolomon.HiddenDerivative Finset
open scoped BigOperators
private abbrev Column := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ
private def width (a b c f : ℕ) : ℕ :=
  540651000 + b + 2 * c + 3 * f - 133551 * (a + b + c + f)
private def tuples : Finset Column :=
  (range 551).sigma fun f =>
    (range ((1650 - 3 * f) / 2 + 1)).sigma fun c =>
      (range (1651 - 2 * c - 3 * f)).sigma fun b =>
        (range (4013 - b - c - f)).sigma fun a => range (width a b c f)
private def exponent : Column → SourceExponent
  | ⟨f, c, b, a, x⟩ => Finsupp.equivFunOnFinite.symm (fun v => v.elim x ![a, b, c, f])
private def coordinates (e : SourceExponent) : Column :=
  ⟨e (some 3), e (some 2), e (some 1), e (some 0), e none⟩
private theorem coordinates_exponent (t : Column) : coordinates (exponent t) = t := by
  rcases t with ⟨f, c, b, a, x⟩
  simp [coordinates, exponent]
private theorem exponent_coordinates (e : SourceExponent) : exponent (coordinates e) = e := by
  ext v
  cases v with
  | none => simp [coordinates, exponent]
  | some j => fin_cases j <;> simp [coordinates, exponent]
private theorem mem_columns (t : Column) :
    exponent t ∈ sourceColumns ↔ t ∈ tuples := by
  rcases t with ⟨f, c, b, a, x⟩
  change exponent ⟨f, c, b, a, x⟩ ∈ sourceExponents_finite.toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  change SourceEligible (exponent ⟨f, c, b, a, x⟩) ↔ _
  simp only [tuples, mem_sigma, mem_range, SourceEligible, Finsupp.weight_eq_sum,
    Fintype.sum_option, Fin.sum_univ_succ, Fin.sum_univ_zero, smul_eq_mul,
    jetDegreeWeight_none, jetDegreeWeight_some, jetDerivativeWeight, differentialWeight,
    topWeight, Option.elim_none, Option.elim_some, exponent, Finsupp.coe_equivFunOnFinite_symm]
  simp [width]
  omega
private theorem card_columns : sourceColumns.card = tuples.card := by
  let e : Column ≃ SourceExponent :=
    ⟨exponent, coordinates, coordinates_exponent, exponent_coordinates⟩
  exact (Finset.card_equiv e (fun t => (mem_columns t).symm)).symm
private def widthInt (a b c f : ℤ) : ℤ :=
  540651000 + b + 2 * c + 3 * f - 133551 * (a + b + c + f)
private theorem cast_width (a b c f : ℕ) (h : a + b + c + f ≤ 4012) :
    (width a b c f : ℤ) = widthInt a b c f := by
  have hpos : 133551 * (a + b + c + f) ≤ 540651000 + b + 2 * c + 3 * f := by omega
  simp [width, widthInt, Nat.cast_sub hpos]
private theorem scaled_sum (k : ℤ) (g p : ℤ → ℤ)
    (base : p 0 = 0) (step : ∀ t, p (t + 1) = p t + k * g t) (n : ℕ) :
    k * (∑ i ∈ range n, g i) = p n := by
  induction n with
  | zero => simpa using base.symm
  | succ n ih => rw [sum_range_succ, Nat.cast_succ, mul_add, ih, step]
private def prefixA (b c f n : ℤ) : ℤ :=
  n * (2 * widthInt 0 b c f - 133551 * (n - 1))
private def doubleA (b c f : ℤ) : ℤ :=
  prefixA b c f (4013 - b - c - f)
private def prefixB (c f n : ℤ) : ℤ :=
  let p := 4013 - c - f
  let q := 2 * widthInt 0 0 c f - 133551 * (p - 1)
  let r := 2 - 133551
  6 * n * p * q + 3 * n * (n - 1) * (p * r - q) - n * (n - 1) * (2 * n - 1) * r
private def twelveB (c f : ℤ) : ℤ :=
  prefixB c f (1651 - 2 * c - 3 * f)
private def prefixC (f n : ℤ) : ℤ :=
  let v₀ := twelveB 0 f
  let v₁ := twelveB 1 f
  let v₂ := twelveB 2 f
  let v₃ := twelveB 3 f
  24 * n * v₀ + 12 * n * (n - 1) * (v₁ - v₀) +
    4 * n * (n - 1) * (n - 2) * (v₂ - 2 * v₁ + v₀) +
    n * (n - 1) * (n - 2) * (n - 3) * (v₃ - 3 * v₂ + 3 * v₁ - v₀)
private def countA (b c f : ℕ) : ℤ :=
  ∑ a ∈ range (4013 - b - c - f), (width a b c f : ℤ)
private def countB (c f : ℕ) : ℤ :=
  ∑ b ∈ range (1651 - 2 * c - 3 * f), countA b c f
private def countC (f : ℕ) : ℤ :=
  ∑ c ∈ range ((1650 - 3 * f) / 2 + 1), countB c f
private theorem card_tuples_int : (tuples.card : ℤ) = ∑ f ∈ range 551, countC f := by
  simp only [tuples, card_sigma, card_range, Nat.cast_sum, countC, countB, countA]
private theorem countA_closed (b c f : ℕ) (h : b + 2 * c + 3 * f ≤ 1650) :
    2 * countA b c f = doubleA b c f := by
  have hsum : countA b c f =
      ∑ a ∈ range (4013 - b - c - f), widthInt a b c f := by
    apply sum_congr rfl
    intro a ha
    rw [mem_range] at ha
    exact cast_width a b c f (by omega)
  rw [hsum, scaled_sum 2 (fun a => widthInt a b c f) (prefixA b c f)
    (by simp [prefixA]) (by intro t; unfold prefixA widthInt; ring)]
  have hn : ((4013 - b - c - f : ℕ) : ℤ) = 4013 - b - c - f := by omega
  rw [hn, doubleA]
private theorem countB_closed (c f : ℕ) (h : 2 * c + 3 * f ≤ 1650) :
    12 * countB c f = twelveB c f := by
  calc
    12 * countB c f =
        ∑ b ∈ range (1651 - 2 * c - 3 * f), 6 * (2 * countA b c f) := by
      simp only [countB, ← mul_assoc, ← mul_sum, show (6 : ℤ) * 2 = 12 by decide]
    _ = 6 * ∑ b ∈ range (1651 - 2 * c - 3 * f), doubleA b c f := by
      rw [mul_sum]
      apply sum_congr rfl
      intro b hb
      rw [mem_range] at hb
      rw [countA_closed b c f (by omega)]
    _ = twelveB c f := by
      rw [scaled_sum 6 (fun b => doubleA b c f) (prefixB c f)
        (by simp [prefixB])
        (by intro t; unfold prefixB doubleA prefixA widthInt; ring)]
      have hn : ((1651 - 2 * c - 3 * f : ℕ) : ℤ) = 1651 - 2 * c - 3 * f := by omega
      rw [hn, twelveB]
private def closedC (f : ℕ) : ℤ :=
  prefixC f ((1650 - 3 * f) / 2 + 1 : ℕ)
private theorem countC_closed (f : ℕ) (hf : f < 551) :
    288 * countC f = closedC f := by
  calc
    288 * countC f =
        ∑ c ∈ range ((1650 - 3 * f) / 2 + 1), 24 * (12 * countB c f) := by
      simp only [countC, ← mul_assoc, ← mul_sum, show (24 : ℤ) * 12 = 288 by decide]
    _ = 24 * ∑ c ∈ range ((1650 - 3 * f) / 2 + 1), twelveB c f := by
      rw [mul_sum]
      apply sum_congr rfl
      intro c hc
      rw [mem_range] at hc
      rw [countB_closed c f (by omega)]
    _ = closedC f := by
      rw [scaled_sum 24 (fun c => twelveB c f) (prefixC f)
        (by simp [prefixC])
        (by intro t; unfold prefixC twelveB prefixB widthInt; ring)]
      rfl
private def pairPrefix (q : ℤ) : ℤ :=
  q * (33025892962946239768320 + (q - 1) * (-111062335503339043200 +
    (q - 2) * (105441619037425920 + (q - 3) * (44265756160800 +
      (q - 4) * 20769913728))))
private theorem pair_step (q : ℕ) (hq : q < 275) :
    pairPrefix (q + 1) = pairPrefix q + 120 * (closedC (2 * q) + closedC (2 * q + 1)) := by
  have he : (((1650 - 3 * (2 * q)) / 2 + 1 : ℕ) : ℤ) = 826 - 3 * q := by omega
  have ho : (((1650 - 3 * (2 * q + 1)) / 2 + 1 : ℕ) : ℤ) = 824 - 3 * q := by omega
  simp only [closedC, he, ho, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  unfold pairPrefix prefixC twelveB prefixB widthInt
  ring
private theorem pairs_sum (n : ℕ) (hn : n ≤ 275) :
    120 * (∑ f ∈ range (2 * n), closedC f) = pairPrefix n := by
  induction n with
  | zero => simp [pairPrefix]
  | succ n ih =>
    have hindex : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := Nat.cast_succ n
    rw [hindex, sum_range_succ, sum_range_succ, add_assoc,
      mul_add, ih (by omega), hcast, pair_step n (by omega)]
theorem sourceColumns_card : sourceColumns.card = 91485369007824320927 := by
  have h : 288 * (tuples.card : ℤ) = ∑ f ∈ range 551, closedC f := by
    rw [card_tuples_int, mul_sum]
    exact sum_congr rfl fun f hf => countC_closed f (mem_range.mp hf)
  have hprefix : pairPrefix 275 = 3161734324662895444108800 := by rfl
  have hlast : closedC 550 = 235395942392736 := by rfl
  have hsum : 120 * (∑ f ∈ range 550, closedC f) = pairPrefix 275 :=
    pairs_sum 275 (by decide)
  rw [show 551 = 2 * 275 + 1 by decide, sum_range_succ,
    show 2 * 275 = 550 by decide, hlast] at h
  rw [hprefix] at hsum
  rw [card_columns]
  omega
end
end P0_9_2
end
section
namespace P0_9_2
noncomputable section
open K1_13 PolynomialDifferential ReedSolomon.HiddenDerivative
open K1_13_2 (SourceExponent Local toRow)
open P0 (I K node)
open scoped BigOperators
private theorem high_monomial_vanishes (e : SourceExponent) (c : Geom) (he : 3000 ≤ e none) :
    localConstraintAt 3000 0 0 (MvPolynomial.monomial e c) = 0 := by
  change MvPolynomial.weightedTruncation (localContactWeight 3) 3000
    (MvPolynomial.bind₁ (unscaledLocalImage 3 0 0) (MvPolynomial.monomial e c)) = 0
  apply (MvPolynomial.weightedTruncation_eq_zero_iff _ _ _).mpr
  refine MvPolynomial.bind₁_mem_restrictWeightedOrder
    (w := fun v : JetVariable 3 => v.elim 1 (fun _ => 0)) ?_ ?_
  · intro v
    cases v with
    | none =>
      simpa only [unscaledLocalImage, map_zero, zero_add, Option.elim_none] using
        (MvPolynomial.X_mem_restrictWeightedOrder (R := Geom)
          (localContactWeight 3) (localT 3) (m := 1) (by rfl))
    | some j => simp
  · exact (MvPolynomial.monomial_mem_restrictWeightedOrder _ _ _ _).mpr
      (Or.inl (by simpa only [Finsupp.weight_elim_one_zero] using he))
private theorem old_eligible (e : SourceExponent) (he : SourceEligible e)
    (hx : e none < 3000) : K1_13_2.SourceEligible e := by
  have hw := weight_le_add_mul_totalJetDegree 133671 e
  change e.weight (differentialWeight 133671) ≤ e none + 133671 * e.weight jetDegreeWeight at hw
  refine ⟨he.1, he.2.1, he.2.2.1, ?_⟩
  have hb := he.1
  omega
private theorem node_range_le (x y : Geom) :
    LinearMap.range (nodeMap x y) ≤ LinearMap.range (K1_13_2.nodeMap 0 0) := by
  rintro _ ⟨Q, rfl⟩
  let R := globalPointTranslation x y Q.1
  have hR : R ∈ SourceSpace := translate_mem_source x y Q
  change localConstraintAt 3000 x y Q.1 ∈ _
  rw [localConstraintAt_eq_zero_globalPointTranslation]
  change localConstraintAt 3000 0 0 R ∈ _
  rw [congrArg (localConstraintAt 3000 0 0) R.as_sum, map_sum]
  refine Submodule.sum_mem _ fun e he => ?_
  by_cases hx : e none < 3000
  · have hOld : e ∈ K1_13_2.sourceExponents := old_eligible e (hR he) hx
    have hMono : MvPolynomial.monomial e (R.coeff e) ∈ K1_13_2.SourceSpace :=
      (MvPolynomial.monomial_mem_restrictSupport Geom).mpr (Or.inl hOld)
    exact ⟨⟨_, hMono⟩, rfl⟩
  · rw [high_monomial_vanishes _ _ (Nat.le_of_not_gt hx)]
    exact Submodule.zero_mem _
theorem word_rank_le (w : I → K) {b : ℕ}
    (h : Module.finrank Geom (LinearMap.range (K1_13_2.nodeMap 0 0)) ≤ b) :
    Module.finrank Geom (LinearMap.range (wordMap w)) ≤ 262144 * b := by
  let nmap (i : I) := nodeMap (embed (node i)) (embed (w i))
  let B (i : I) := LinearMap.range (nmap i)
  let f : SourceSpace →ₗ[Geom] (∀ i, B i) := LinearMap.pi fun i => (nmap i).rangeRestrict
  let g : (∀ i, B i) →ₗ[Geom] (I → Local) :=
    LinearMap.pi fun i => (B i).subtype.comp (LinearMap.proj i)
  have hw : wordMap w = g.comp f := rfl
  rw [hw]
  calc
    Module.finrank Geom (LinearMap.range (g.comp f)) ≤
        Module.finrank Geom (LinearMap.range g) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range f g)
    _ ≤ Module.finrank Geom (∀ i, B i) := g.finrank_range_le
    _ = ∑ i, Module.finrank Geom (B i) := Module.finrank_pi_fintype Geom
    _ ≤ ∑ _ : I, b := Finset.sum_le_sum fun i _ =>
      (Submodule.finrank_mono (node_range_le (embed (node i)) (embed (w i)))).trans h
    _ = 262144 * b := by simp [I, FrobeniusLocator.Native.I, ProximityPrize.Benchmark.IRSProfile.Index]
private theorem origin_rank :
    Module.finrank Geom (LinearMap.range (K1_13_2.nodeMap 0 0)) ≤ 344125686492134 := by
  have hBlock := K1_13_2_2.of_children K1_13_2_2_1.proof K1_13_2_2_2.proof K1_13_2_2_3.proof
    K1_13_2_2_4.proof K1_13_2_2_5.proof
  obtain ⟨power, hp⟩ := K1_13_2_3.of_children K1_13_2_3_1.proof K1_13_2_3_2.proof
    K1_13_2_3_3.proof K1_13_2_3_4.proof K1_13_2_3_5.proof K1_13_2_3_6.proof K1_13_2_3_7.proof
  exact (K1_13_2.origin_rank_le power hBlock).trans hp
private theorem surplus {r k n : ℕ}
    (hr : r ≤ 262144 * 344125686492134) (hn : n = 91485369007824320927)
    (he : r + k = n) : P0_9.sourceRank ≤ k := by
  change 1274885048030345631 ≤ k
  omega
private theorem map_independent_family {V W : Type*} [AddCommGroup V] [Module Geom V]
    [AddCommGroup W] [Module Geom W] {n : ℕ} (f : V →ₗ[Geom] W)
    (hf : Function.Injective f) (P : W → Prop) (hP : ∀ x, P (f x))
    (hn : n ≤ Module.finrank Geom V) :
    ∃ e : Fin n → W, LinearIndependent Geom e ∧ ∀ i, P (e i) := by
  obtain ⟨e, he⟩ := exists_linearIndependent_of_le_finrank hn
  exact ⟨f ∘ e, he.map' f (LinearMap.ker_eq_bot_of_injective hf), fun i => hP (e i)⟩
private theorem family_of_kernel (w : I → K) {n : ℕ}
    (hker : n ≤ Module.finrank Geom (LinearMap.ker (wordMap w))) :
    ∃ e : Fin n → Row 4, LinearIndependent Geom e ∧
      ∀ i, InBox (shape (e i)) P0_9.primaryBox ∧
        P0_9.TrueWeightLE (e i) P0_9.primaryCutoff ∧ Contact w (e i) := by
  let liftRow : LinearMap.ker (wordMap w) →ₗ[Geom] Row 4 :=
    toRow.toLinearMap.comp (SourceSpace.subtype.comp (LinearMap.ker (wordMap w)).subtype)
  have hinj : Function.Injective liftRow := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact toRow.injective hab
  let admissible (P : Row 4) := InBox (shape P) P0_9.primaryBox ∧
    P0_9.TrueWeightLE P P0_9.primaryCutoff ∧ Contact w P
  have hrows (Q : LinearMap.ker (wordMap w)) : admissible (liftRow Q) := by
    obtain ⟨hbox, hwt⟩ := row_bounds Q.1
    have hk : wordMap w Q.1 = 0 := (LinearMap.mem_ker (f := wordMap w)).mp Q.2
    have hcont := contact_of_word_kernel w Q.1 hk
    have happly : liftRow Q = toRow Q.1.1 := rfl
    rw [happly]
    exact ⟨hbox, hwt, hcont⟩
  have h := map_independent_family (V := LinearMap.ker (wordMap w)) (W := Row 4)
    (n := n) liftRow hinj admissible hrows hker
  simpa only [admissible] using h
theorem proof : P0_9.c2 := by
  intro w
  have hSource : Module.finrank Geom SourceSpace = 91485369007824320927 := by
    rw [finrank_source, sourceColumns_card]
  exact family_of_kernel w
    (surplus (word_rank_le w origin_rank) hSource (wordMap w).finrank_range_add_finrank_ker)
end
end P0_9_2
end
section
namespace P0_9_3
noncomputable section
open P0 (I K)
open P0_9 (TrueWeightLE primaryBox primaryCutoff layerWidth)
open K1_13 (Row InBox shape Contact)
def requiredOrder (T : ℕ) : ℕ :=
  (primaryCutoff - T) / layerWidth + 1
def BankRow (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) primaryBox ∧ TrueWeightLE P T ∧ Contact w P
end
end P0_9_3
end
section
namespace P0_9_3
noncomputable section
open Polynomial
open P0 (I K node)
open P0_9 (TrueWeightLE physicalDegree primaryBox primaryCutoff PrimaryRank sourceRank)
open K1_13 (Geom embed Row InBox shape indexDegree Contact jet atJet)
open K1_13_3 (Symbol symbolAt)
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
private abbrev Exponent := Fin 4 →₀ ℕ
private def jetWeight (m : Exponent) : ℕ :=
  m.sum (fun i a => (physicalDegree - i.val) * a)
private theorem bankRow_iff {w : I → K} {T : ℕ} {P : Row 4} :
    BankRow w T P ↔
      (∀ m ∈ P.support, m.sum (fun _ a => a) ≤ 4012 ∧
        m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
        (P.coeff m).natDegree + jetWeight m ≤ T) ∧ Contact w P := by
  simp only [BankRow, InBox, shape, indexDegree, MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_le_iff, Finset.sup_le_iff, TrueWeightLE]
  constructor
  · rintro ⟨⟨hb, hj, ht⟩, hT, hc⟩
    exact ⟨fun m hm => ⟨hb m hm, hj m hm, ht m hm, hT m hm⟩, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2.1, fun m hm => (h m hm).2.2.1⟩,
      fun m hm => (h m hm).2.2.2, hc⟩
private def jetEval (S : Geom[X]) : Row 4 →ₗ[Geom] Geom[X] :=
  (MvPolynomial.aeval (jet S)).toLinearMap.restrictScalars Geom
private theorem jetEval_apply (S : Geom[X]) (P : Row 4) : jetEval S P = atJet P S := by
  rfl
private theorem dvd_smul_poly (d P : Geom[X]) (c : Geom) (h : d ∣ P) :
    d ∣ c • P := by
  rw [Polynomial.smul_eq_C_mul]
  exact h.mul_left _
private def bank (w : I → K) (T : ℕ) : Submodule Geom (Row 4) where
  carrier := {P | BankRow w T P}
  zero_mem' := by
    apply bankRow_iff.mpr
    simp [Contact, atJet]
  add_mem' {P Q} hP hQ := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    obtain ⟨hQ, hq⟩ := bankRow_iff.mp hQ
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      have hor := Finset.mem_union.mp (MvPolynomial.support_add hm)
      have bounds :
          m.sum (fun _ a => a) ≤ 4012 ∧ m.sum (fun i a => i.val * a) ≤ 1650 ∧
            m 3 ≤ 550 ∧ jetWeight m ≤ T := by
        rcases hor with h | h
        · obtain ⟨hb, hj, ht, hw⟩ := hP m h
          exact ⟨hb, hj, ht, by omega⟩
        · obtain ⟨hb, hj, ht, hw⟩ := hQ m h
          exact ⟨hb, hj, ht, by omega⟩
      obtain ⟨hb, hj, ht, hw⟩ := bounds
      refine ⟨hb, hj, ht, ?_⟩
      have hsum : ((P + Q).coeff m).natDegree ≤
          max (P.coeff m).natDegree (Q.coeff m).natDegree := by
        change ((P.coeff m) + (Q.coeff m)).natDegree ≤ _
        exact natDegree_add_le _ _
      have hdegree (R : Row 4) (hR : m ∈ R.support → (R.coeff m).natDegree + jetWeight m ≤ T) :
          (R.coeff m).natDegree ≤ T - jetWeight m := by
        by_cases h : m ∈ R.support
        · have := hR h
          omega
        · have hz : R.coeff m = 0 := by
            by_contra hnz
            exact h (MvPolynomial.mem_support_iff.mpr hnz)
          rw [hz, natDegree_zero]
          exact Nat.zero_le _
      have hp' := hdegree P (fun h => (hP m h).2.2.2)
      have hq' := hdegree Q (fun h => (hQ m h).2.2.2)
      have := hsum.trans (max_le hp' hq')
      omega
    · intro i S hS
      rw [← jetEval_apply, map_add, jetEval_apply, jetEval_apply]
      exact dvd_add (hp i S hS) (hq i S hS)
  smul_mem' c P hP := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      obtain ⟨hb, hj, ht, hw⟩ := hP m (MvPolynomial.support_smul hm)
      refine ⟨hb, hj, ht, ?_⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h : jetEval S (c • P) = c • jetEval S P := (jetEval S).map_smul c P
      rw [jetEval_apply, jetEval_apply] at h
      rw [h]
      exact dvd_smul_poly _ _ c (hp i S hS)
private def coefficientArray (T : ℕ) :
    Row 4 →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
  LinearMap.pi fun u =>
    (Polynomial.lcoeff Geom u.2.val).comp
      ((MvPolynomial.lcoeff Geom[X] (Finsupp.equivFunOnFinite.symm (fun i => (u.1 i).val))
        : Row 4 →ₗ[Geom[X]] Geom[X]).restrictScalars Geom)
private instance finiteBank (w : I → K) (T : ℕ) : Module.Finite Geom (bank w T) := by
  classical
  let f : bank w T →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
    (coefficientArray T).comp (bank w T).subtype
  have hzero (Q : bank w T) (hQ : f Q = 0) : Q = 0 := by
    obtain ⟨P, hP⟩ := Q
    change BankRow w T P at hP
    apply Subtype.ext
    change P = 0
    apply MvPolynomial.ext
    intro m
    change _ = 0
    by_contra hnz
    have hm := MvPolynomial.mem_support_iff.mpr hnz
    have hT : (P.coeff m).natDegree ≤ T := (Nat.le_add_right _ _).trans (hP.2.1 m hm)
    let u : Fin 4 → Fin 4013 := fun i => ⟨m i, Nat.lt_succ_of_le <|
      (MvPolynomial.le_degreeOf_of_mem_support i hm).trans <|
        (P.degreeOf_le_totalDegree i).trans hP.1.1⟩
    apply hnz
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < T + 1
    · have hval := congrFun hQ (u, ⟨k, hk⟩)
      change (P.coeff (Finsupp.equivFunOnFinite.symm (fun i => (u i).val))).coeff k = 0 at hval
      have heq : Finsupp.equivFunOnFinite.symm (fun i => (u i).val) = m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro P Q h
  apply sub_eq_zero.mp
  have hz := f.map_sub P Q
  rw [h, sub_self] at hz
  exact hzero (P - Q) hz
private def symbolLinear (x : Geom) : Row 4 →ₗ[Geom] Symbol :=
  ({ symbolAt x with
      commutes' := by
        intro a
        change MvPolynomial.map (evalRingHom x) (MvPolynomial.C (Polynomial.C a)) =
          MvPolynomial.C a
        simp } : Row 4 →ₐ[Geom] Symbol).toLinearMap
private def bankEval (w : I → K) (x : Geom) (T : ℕ) : bank w T →ₗ[Geom] Symbol :=
  (symbolLinear x).comp (bank w T).subtype
private def linearFactor (x : Geom) : Geom[X] := (Polynomial.X : Geom[X]) - Polynomial.C x
private theorem linearFactor_ne (x : Geom) : linearFactor x ≠ 0 := X_sub_C_ne_zero x
private theorem linearFactor_degree (x : Geom) : (linearFactor x).natDegree = 1 :=
  natDegree_X_sub_C x
private theorem divide_specialization (P : Row 4) (x : Geom) (hP : symbolAt x P = 0) :
    ∃ Q : Row 4, MvPolynomial.C (linearFactor x) * Q = P := by
  let Q : Row 4 := AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange.linearMap (divByMonicHom (linearFactor x)) (AddMonoidAlgebra.coeff P))
  refine ⟨Q, MvPolynomial.ext _ _ fun m => ?_⟩
  have hroot : (P.coeff m).eval x = 0 := by
    have h := congrArg (fun B : Symbol => B.coeff m) hP
    change (symbolAt x P).coeff m = (0 : Symbol).coeff m at h
    rw [symbolAt, MvPolynomial.coeff_map] at h
    exact h
  rw [MvPolynomial.coeff_C_mul]
  change (linearFactor x) * ((P.coeff m) /ₘ (linearFactor x)) = P.coeff m
  exact mul_divByMonic_eq_iff_isRoot.mpr hroot
private theorem support_linear_mul (x : Geom) (P : Row 4) :
    (MvPolynomial.C (linearFactor x) * P).support = P.support := by
  ext m
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul]
  exact mul_ne_zero_iff.trans (and_iff_right (linearFactor_ne x))
private theorem mul_cutoff_iff (w : I → K) (x : Geom) (hx : ∀ i : I, x ≠ embed (node i))
    (T : ℕ) (P : Row 4) :
    BankRow w (T + 1) (MvPolynomial.C (linearFactor x) * P) ↔ BankRow w T P := by
  rw [bankRow_iff, bankRow_iff, support_linear_mul]
  apply and_congr
  · refine forall_congr' fun m => forall_congr' fun hm => ?_
    rw [MvPolynomial.coeff_C_mul, natDegree_mul (linearFactor_ne x)
      (MvPolynomial.mem_support_iff.mp hm), linearFactor_degree]
    omega
  · simp only [Contact, atJet, map_mul, MvPolynomial.eval_C]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro S
    apply forall_congr'
    intro hS
    generalize (3000 : ℕ) = m
    have hc : IsCoprime (linearFactor (embed (node i))) (linearFactor x) :=
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hx i).symm).isUnit
    have hd : IsCoprime (linearFactor (embed (node i)) ^ m) (linearFactor x) := hc.pow_left
    exact hd.dvd_mul_left_iff
private theorem zero_cutoff_kernel (w : I → K) (x : Geom) :
    LinearMap.ker (bankEval w x 0) = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro P hP
  change symbolAt x P.val = 0 at hP
  obtain ⟨Q, hQ⟩ := divide_specialization P.val x hP
  have hp : TrueWeightLE P.val 0 := P.property.2.1
  apply Subtype.ext
  change P.val = 0
  rw [← hQ]
  suffices Q = 0 by simp [this]
  apply MvPolynomial.ext
  intro m
  change _ = 0
  by_contra hnz
  have hm : m ∈ P.val.support := by
    rw [← hQ, support_linear_mul]
    exact MvPolynomial.mem_support_iff.mpr hnz
  have h := hp m hm
  rw [← hQ, MvPolynomial.coeff_C_mul, natDegree_mul (linearFactor_ne x) hnz,
    linearFactor_degree] at h
  omega
private theorem kernel_finrank (w : I → K) (x : Geom) (hx : ∀ i : I, x ≠ embed (node i))
    (T : ℕ) : Module.finrank Geom (LinearMap.ker (bankEval w x (T + 1))) =
      Module.finrank Geom (bank w T) := by
  let L : bank w T →ₗ[Geom] (LinearMap.ker (bankEval w x (T + 1))) :=
    LinearMap.codRestrict _ (LinearMap.codRestrict (bank w (T + 1))
      ((LinearMap.mulLeft Geom (MvPolynomial.C (linearFactor x))).comp (bank w T).subtype)
      (fun P => (mul_cutoff_iff w x hx T P.val).mpr P.property)) (fun P => by
        rw [LinearMap.mem_ker]
        change symbolAt x (MvPolynomial.C (linearFactor x) * P.val) = 0
        simp [symbolAt, linearFactor])
  have hL : Function.Bijective L := by
    have hnz : (MvPolynomial.C (linearFactor x) : Row 4) ≠ 0 := by
      simpa only [ne_eq, MvPolynomial.C_eq_zero] using linearFactor_ne x
    constructor
    · intro P Q h
      apply Subtype.ext
      have heq := congrArg (fun V : LinearMap.ker (bankEval w x (T + 1)) => V.val.val) h
      change MvPolynomial.C (linearFactor x) * P.val = MvPolynomial.C (linearFactor x) * Q.val at heq
      exact mul_left_cancel₀ hnz heq
    · intro P
      have h : symbolAt x P.val.val = 0 := LinearMap.mem_ker.mp P.property
      obtain ⟨Q, hQ⟩ := divide_specialization P.val.val x h
      have hmem : BankRow w (T + 1) (MvPolynomial.C (linearFactor x) * Q) := by
        rw [hQ]
        exact P.val.property
      refine ⟨⟨Q, (mul_cutoff_iff w x hx T Q).mp hmem⟩, Subtype.ext (Subtype.ext hQ)⟩
  exact (LinearEquiv.ofBijective L hL).finrank_eq.symm
theorem cutoff_rank (w : I → K) (x : Geom) (hr : PrimaryRank w)
    (hx : ∀ i : I, x ≠ embed (node i)) :
    ∃ r : ℕ → ℕ, sourceRank ≤ ∑ T ∈ Finset.range (primaryCutoff + 1), r T ∧
      ∀ T ≤ primaryCutoff, ∃ e : Fin (r T) → Row 4,
        (∀ i, BankRow w T (e i)) ∧
        LinearIndependent Geom (fun i => symbolAt x (e i)) := by
  classical
  let r (T : ℕ) := Module.finrank Geom (LinearMap.range (bankEval w x T))
  refine ⟨r, ?_, fun T _ => ?_⟩
  · have heq (T : ℕ) : Module.finrank Geom (bank w T) =
        ∑ V ∈ Finset.range (T + 1), r V := by
      induction T with
      | zero =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w 0) (V₂ := Symbol) (bankEval w x 0)
        rw [zero_cutoff_kernel, finrank_bot, Nat.add_zero] at h
        simpa only [Nat.zero_add, Finset.sum_range_one] using h.symm
      | succ T ih =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w (T + 1)) (V₂ := Symbol) (bankEval w x (T + 1))
        rw [kernel_finrank w x hx, ih, Nat.add_comm] at h
        rw [Finset.sum_range_succ]
        exact h.symm
    obtain ⟨e, he, hmem⟩ := hr
    have hi : LinearIndependent Geom (fun i => (⟨e i, hmem i⟩ : bank w primaryCutoff)) :=
      LinearIndependent.of_comp (bank w primaryCutoff).subtype he
    rw [← heq]
    simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank
  · let b := Module.finBasis Geom (LinearMap.range (bankEval w x T))
    choose e he using fun i : Fin (r T) => LinearMap.mem_range.mp (b i).property
    refine ⟨fun i => (e i).val, fun i => (e i).property, ?_⟩
    have h : LinearIndependent Geom (fun i => (b i).val) :=
      b.linearIndependent.map' (LinearMap.range (bankEval w x T)).subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have heq : (fun i => symbolAt x (e i).val) = fun i => (b i).val := funext he
    rwa [heq]
end
end P0_9_3
end
section
namespace P0_9_3
noncomputable section
open Polynomial
open P0 (I K node agreement)
open P0_9 (Messages SmallFactor ProperCut TrueWeightLE physicalDegree primaryBox
  primaryCutoff layerWidth layerNeed sourceRank)
open K1_13 (Geom embed extend Row shape InBox OrderAt indexDegree remaining)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open scoped BigOperators
def c1 : Prop :=
  ∀ (w : I → K) (T : ℕ) (P : Row 4), T ≤ primaryCutoff → BankRow w T P →
    ∀ S : Geom[X], S.natDegree ≤ physicalDegree →
      (∃ H : Finset I, agreement ≤ H.card ∧
        ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) →
      OrderAt P S (requiredOrder T)
def c2 : Prop :=
  ∀ (f P : Row 4) (Γ : Finset K) (s : K → K[X]) (d a : ℕ),
    SmallFactor f →
    InBox (shape P) primaryBox → TrueWeightLE P primaryCutoff →
    (∀ γ ∈ Γ, OrderAt P (extend (s γ)) d) →
    a < d → f ^ a ∣ P → (¬ f ^ (a + 1) ∣ P) →
    ProperCut f Γ s (d - a)
private theorem exists_fresh {n : ℕ} (f : Fin n → Row 4) :
    ∃ x : Geom, (∀ i : I, x ≠ embed (node i)) ∧
      ∀ i, (symbolAt x (f i)).support = (f i).support := by
  classical
  let nodes : Finset Geom := Finset.univ.image (fun i : I => embed (node i))
  let roots : Finset Geom := Finset.univ.biUnion (fun i : Fin n =>
    (f i).support.biUnion (fun m => ((f i).coeff m).roots.toFinset))
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (nodes ∪ roots)
  rw [Finset.mem_union, not_or] at hx
  refine ⟨x, ?_, fun i => Finset.Subset.antisymm (MvPolynomial.support_map_subset _ _) ?_⟩
  · intro i h
    exact hx.1 (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)
  · intro m hm
    rw [MvPolynomial.mem_support_iff] at ⊢
    change (MvPolynomial.map (evalRingHom x) (f i)).coeff m ≠ 0
    rw [MvPolynomial.coeff_map]
    intro heval
    have hroot : x ∈ ((f i).coeff m).roots :=
      (Polynomial.mem_roots (MvPolynomial.mem_support_iff.mp hm)).mpr heval
    exact hx.2 (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨m, hm, Multiset.mem_toFinset.mpr hroot⟩⟩)
private theorem specialization_bounds (x : Geom) (P : Row 4)
    (hP : InBox (shape P) primaryBox) :
    (symbolAt x P).totalDegree ≤ 4012 ∧ symbolIndex (symbolAt x P) ≤ 1650 := by
  have h : (symbolAt x P).support ⊆ P.support := MvPolynomial.support_map_subset _ _
  exact ⟨(Finset.sup_mono h).trans hP.1, (Finset.sup_mono h).trans hP.2.1⟩
private theorem exists_availability (hc : c1) (hd : c2)
    {w : I → K} {Γ : Finset K} {s : K → K[X]} (hm : Messages w Γ s)
    {f : Row 4} (hf : SmallFactor f) :
    ∃ l : ℕ, (∀ T ≤ primaryCutoff, ∀ P, BankRow w T P → f ^ (requiredOrder T - l) ∣ P) ∧
      (0 < l → ProperCut f Γ s l) := by
  classical
  let admissible (l : ℕ) : Prop :=
    ∀ T ≤ primaryCutoff, ∀ P, BankRow w T P → f ^ (requiredOrder T - l) ∣ P
  have hex : ∃ l, admissible l := by
    refine ⟨primaryCutoff / layerWidth + 1, fun T _ P _ => ?_⟩
    have hle : requiredOrder T ≤ primaryCutoff / layerWidth + 1 :=
      Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le _ _)) _
    rw [Nat.sub_eq_zero_of_le hle, pow_zero]
    exact one_dvd P
  let l := Nat.find hex
  have hl : admissible l := Nat.find_spec hex
  refine ⟨l, hl, fun hpos => ?_⟩
  have hbad : ¬ admissible (l - 1) := Nat.find_min hex (by omega)
  dsimp only [admissible] at hbad
  push Not at hbad
  obtain ⟨T, hT, P, hP, hnext⟩ := hbad
  have hle : l ≤ requiredOrder T := by
    by_contra! hlt
    have heq : requiredOrder T - (l - 1) = 0 := by omega
    exact hnext (by rw [heq, pow_zero]; exact one_dvd P)
  have hstep : requiredOrder T - (l - 1) = (requiredOrder T - l) + 1 := by omega
  have horder : ∀ γ ∈ Γ, OrderAt P (extend (s γ)) (requiredOrder T) := by
    intro γ hγ
    apply hc w T P hT hP
    · simpa only [extend, natDegree_map_eq_of_injective (RingHom.injective embed)] using
        hm.degree γ hγ
    · obtain ⟨H, hcard, hH⟩ := hm.hits γ hγ
      refine ⟨H, hcard, fun i hi => ?_⟩
      rw [extend, eval_map, eval₂_at_apply, hH i hi]
  have hweight : TrueWeightLE P primaryCutoff := fun m hm => (hP.2.1 m hm).trans hT
  have hcut := hd f P Γ s (requiredOrder T) (requiredOrder T - l) hf hP.1
    hweight horder (by omega) (hl T hT P hP) (by rwa [hstep] at hnext)
  have heq : requiredOrder T - (requiredOrder T - l) = l := by omega
  rwa [heq] at hcut
private theorem sum_by_layer (W E : ℕ) (hE : 0 < E) (cost : ℕ → ℕ) :
    (∑ T ∈ Finset.range (W + 1), cost ((W - T) / E)) ≤
      E * ∑ k ∈ Finset.range (1 + W / E), cost k := by
  let S := Finset.range (W + 1)
  let R := Finset.range (1 + W / E)
  let U := Finset.range E
  let pair (T : ℕ) : ℕ × ℕ := ((W - T) / E, (W - T) % E)
  have hmem : ∀ T ∈ S, pair T ∈ R ×ˢ U := by
    intro T _
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr (by
        change (W - T) / E < 1 + W / E
        have h : (W - T) / E ≤ W / E := Nat.div_le_div_right (Nat.sub_le W T)
        omega),
      Finset.mem_range.mpr (Nat.mod_lt _ hE)⟩
  have hinj : Set.InjOn pair (↑S : Set ℕ) := by
    intro T hT V hV h
    have hT' : T < W + 1 := Finset.mem_range.mp hT
    have hV' : V < W + 1 := Finset.mem_range.mp hV
    have he : W - T = W - V := by
      have ht := Nat.mod_add_div (W - T) E
      have hv := Nat.mod_add_div (W - V) E
      have hfst := congrArg Prod.fst h
      have hsnd := congrArg Prod.snd h
      change (W - T) / E = (W - V) / E at hfst
      change (W - T) % E = (W - V) % E at hsnd
      rw [hsnd, hfst, hv] at ht
      exact ht.symm
    omega
  calc
    _ ≤ ∑ p ∈ R ×ˢ U, cost p.1 := by
      refine Finset.sum_le_sum_of_injOn pair hinj ?_ (fun _ _ => le_rfl) (fun _ _ _ => Nat.zero_le _)
      intro p hp
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hp
      exact hmem T hT
    _ = _ := by rw [Finset.sum_product, Finset.mul_sum]; simp [U, R]
theorem of_children (h1 : c1) (h2 : c2) : P0_9.c3 := by
  classical
  intro w Γ s hm hr n g f hf
  choose l hl hcut using fun i => exists_availability h1 h2 hm (hf.factors i)
  obtain ⟨x, hx, hsup⟩ := exists_fresh f
  obtain ⟨r, hrank, hfamilies⟩ := cutoff_rank w x hr hx
  have hnz : ∀ i, symbolAt x (f i) ≠ 0 := by
    intro i hz
    have hzero := hsup i
    rw [hz, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at hzero
    exact (hf.factors i).1.ne_zero hzero
  let cost (k : ℕ) :=
    remaining (∑ i, (k + 1 - l i) * (shape (f i)).b)
      (∑ i, (k + 1 - l i) * (shape (f i)).j)
  have hcost : ∀ T ≤ primaryCutoff, r T ≤ cost ((primaryCutoff - T) / layerWidth) := by
    intro T hT
    obtain ⟨e, he, hei⟩ := hfamilies T hT
    let a (i : Fin n) := requiredOrder T - l i
    have hdiv (i : Fin (r T)) : (∏ j, f j ^ a j) ∣ e i := by
      apply Fintype.prod_dvd_of_isRelPrime
      · intro j k hjk
        have hj := (hf.factors j).1
        have hk := (hf.factors k).1
        exact (hj.isRelPrime_iff_not_dvd.mpr
          (fun h => hf.different j k hjk (hj.associated_of_dvd hk h))).pow
      · intro j
        exact hl j T hT (e i) (he i)
    have hbound := cofactor_rank n (fun i => symbolAt x (f i)) a hnz (r T)
      (fun i => symbolAt x (e i)) hei (fun i => by
        obtain ⟨hb, hj⟩ := specialization_bounds x (e i) (he i).1
        exact ⟨hb, hj, by simpa only [map_prod, map_pow] using map_dvd (symbolAt x) (hdiv i)⟩)
    have hb (i : Fin n) : (symbolAt x (f i)).totalDegree = (shape (f i)).b := by
      change (symbolAt x (f i)).totalDegree = (f i).totalDegree
      unfold MvPolynomial.totalDegree
      rw [hsup]
    have hj (i : Fin n) : symbolIndex (symbolAt x (f i)) = (shape (f i)).j := by
      change symbolIndex (symbolAt x (f i)) = indexDegree (f i)
      unfold symbolIndex indexDegree
      rw [hsup]
    simpa only [cost, a, requiredOrder, hb, hj] using hbound
  have hsum : sourceRank ≤ layerWidth * ∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k :=
    hrank.trans ((Finset.sum_le_sum fun T hT =>
      hcost T (Nat.le_of_lt_succ (Finset.mem_range.mp hT))).trans (sum_by_layer primaryCutoff layerWidth (by decide) cost))
  refine ⟨l, ?_, hcut⟩
  change layerNeed ≤ ∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k
  have hceil : layerWidth * (layerNeed - 1) < sourceRank := by decide
  by_contra! hsmall
  have hpred : (∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k) ≤
      layerNeed - 1 := by omega
  exact (not_le_of_gt hceil) (hsum.trans (Nat.mul_le_mul_left layerWidth hpred))
end
end P0_9_3
end
section
namespace P0_9_3_2
noncomputable section
open Polynomial
open P0_9 (SmallFactor ProperCut TrueWeightLE physicalDegree primaryBox primaryCutoff)
open K1_13 (Geom embed extend Row shape InBox OrderAt indexDegree shiftJet jet)
private abbrev Exponent := Fin 4 →₀ ℕ
private def translateTop : Row 4 →+* Polynomial (Row 4) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) fun i =>
    Polynomial.C (MvPolynomial.X i) + if i = 3 then Polynomial.X else 0
private def topHasse (a : ℕ) (P : Row 4) : Row 4 :=
  (translateTop P).coeff a
private theorem translate_independent (m : Exponent) (c : Geom[X]) (hm : m 3 = 0) :
    translateTop (MvPolynomial.monomial m c) = Polynomial.C (MvPolynomial.monomial m c) := by
  rw [translateTop, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq, map_mul]
  simp only [RingHom.comp_apply]
  congr 1
  unfold Finsupp.prod
  rw [map_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hne : i ≠ 3 := by
    intro he
    subst i
    exact (Finsupp.mem_support_iff.mp hi) hm
  simp [hne]
private theorem translate_top_pow_coeff (n a : ℕ) :
    ((Polynomial.C (MvPolynomial.X (3 : Fin 4) : Row 4) + Polynomial.X) ^ n).coeff a =
      MvPolynomial.C (↑(n.choose a) : Geom[X]) * MvPolynomial.X 3 ^ (n - a) := by
  rw [add_comm, ← Polynomial.taylor_X_pow, Polynomial.taylor_coeff,
    Polynomial.X_pow_eq_monomial, Polynomial.hasseDeriv_monomial]
  simp [Polynomial.eval_monomial]
private theorem erase_top_add (u : Exponent) :
    u.erase 3 + Finsupp.single 3 (u 3) = u := by
  ext i
  by_cases hi : i = 3
  · subst i
    simp
  · simp [Finsupp.erase_ne hi, Finsupp.single_eq_of_ne hi]
private theorem topHasse_monomial (a : ℕ) (u : Exponent) (c : Geom[X]) :
    topHasse a (MvPolynomial.monomial u c) =
      MvPolynomial.monomial (u.erase 3 + Finsupp.single 3 (u 3 - a)) (↑((u 3).choose a) * c) := by
  have hu : MvPolynomial.monomial u c =
      MvPolynomial.monomial (u.erase 3) c * MvPolynomial.X 3 ^ (u 3) := by
    rw [← MvPolynomial.monomial_add_single, erase_top_add]
  have hx : translateTop (MvPolynomial.X 3) =
      Polynomial.C (MvPolynomial.X 3) + Polynomial.X := by simp [translateTop]
  unfold topHasse
  rw [hu, map_mul, map_pow, translate_independent _ _ Finsupp.erase_same, hx,
    Polynomial.coeff_C_mul, translate_top_pow_coeff, ← mul_assoc]
  rw [mul_comm (MvPolynomial.monomial (u.erase 3) c), MvPolynomial.C_mul_monomial,
    ← MvPolynomial.monomial_add_single]
private theorem apply_add_top (m : Exponent) (a : ℕ) :
    (m + Finsupp.single 3 a : Exponent) 3 = m 3 + a := by simp
private theorem topHasse_coeff (a : ℕ) (P : Row 4) (m : Exponent) :
    (topHasse a P).coeff m =
      ↑((m 3 + a).choose a) * P.coeff (m + Finsupp.single 3 a) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [topHasse_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases ha : a ≤ u 3
    · have hcancel : (u.erase 3 + Finsupp.single 3 (u 3 - a)) + Finsupp.single 3 a = u := by
        rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel ha, erase_top_add]
      have heq : u.erase 3 + Finsupp.single 3 (u 3 - a) = m ↔
          u = m + Finsupp.single 3 a := by
        constructor
        · intro h
          rw [← h, hcancel]
        · intro h
          exact add_right_cancel (hcancel.trans h)
      simp only [heq]
      by_cases h : u = m + Finsupp.single 3 a
      · have h3 : u 3 = m 3 + a := by rw [h, apply_add_top]
        simp only [h3, ite_eq_left h]
      · simp [h]
    · have hne : u ≠ m + Finsupp.single 3 a := by
        intro h
        have h3 : u 3 = m 3 + a := by rw [h, apply_add_top]
        omega
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge ha)]
      simp [hne]
  | add P Q hP hQ =>
    simp only [topHasse, map_add, Polynomial.coeff_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply] at hP hQ ⊢
    rw [hP, hQ, mul_add]
private theorem source_support {a : ℕ} {P : Row 4} {m : Exponent}
    (hm : m ∈ (topHasse a P).support) : m + Finsupp.single 3 a ∈ P.support := by
  rw [MvPolynomial.mem_support_iff, topHasse_coeff] at hm
  exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hm)
private theorem sum_add_top (w : Fin 4 → ℕ) (m : Exponent) (a : ℕ) :
    (m + Finsupp.single 3 a).sum (fun i k => w i * k) =
      m.sum (fun i k => w i * k) + w 3 * a := by
  rw [Finsupp.sum_add_index' (fun i => Nat.mul_zero (w i)) (fun i b c => Nat.mul_add (w i) b c),
    Finsupp.sum_single_index (h := fun i k => w i * k) (Nat.mul_zero _)]
private theorem total_add_top (m : Exponent) (a : ℕ) :
    (m + Finsupp.single 3 a).sum (fun _ k => k) = m.sum (fun _ k => k) + a := by
  simpa only [one_mul] using sum_add_top (fun _ => 1) m a
private theorem topHasse_bounds (a : ℕ) (P : Row 4)
    (hb : InBox (shape P) primaryBox) (hw : TrueWeightLE P primaryCutoff) :
    InBox (shape (topHasse a P)) primaryBox ∧
      TrueWeightLE (topHasse a P) primaryCutoff := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change (topHasse a P).totalDegree ≤ 4012
    apply Finset.sup_le
    intro m hm
    have hp := (MvPolynomial.le_totalDegree (source_support hm)).trans hb.1
    rw [total_add_top] at hp
    change _ ≤ 4012 at hp
    omega
  · change indexDegree (topHasse a P) ≤ 1650
    apply Finset.sup_le
    intro m hm
    have hp := (Finset.le_sup (f := fun u : Exponent => u.sum (fun i k => i.val * k))
      (source_support hm)).trans hb.2.1
    rw [sum_add_top Fin.val] at hp
    change _ ≤ 1650 at hp
    omega
  · change (topHasse a P).degreeOf 3 ≤ 550
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have hp := (MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)).trans hb.2.2
    rw [apply_add_top] at hp
    change _ ≤ 550 at hp
    omega
  · intro m hm
    have hp := hw _ (source_support hm)
    rw [sum_add_top (fun i => physicalDegree - i.val)] at hp
    rw [topHasse_coeff]
    have hcoeff := Polynomial.natDegree_mul_le
      (p := (↑((m 3 + a).choose a) : Geom[X])) (q := P.coeff (m + Finsupp.single 3 a))
    rw [Polynomial.natDegree_natCast, zero_add] at hcoeff
    refine (Nat.add_le_add_right hcoeff _).trans (le_trans ?_ hp)
    exact Nat.add_le_add_left (Nat.le_add_right _ _) _
private def shiftHom (S : Geom[X]) : Row 4 →+* Row 4 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i))
private theorem translate_shift (S : Geom[X]) :
    translateTop.comp (shiftHom S) = (Polynomial.mapRingHom (shiftHom S)).comp translateTop := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [translateTop, shiftHom]
  · intro i
    simp only [RingHom.comp_apply, shiftHom, translateTop, MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_C, map_add, Polynomial.coe_mapRingHom, Polynomial.map_C]
    by_cases hi : i = 3
    · simp only [hi, ite_true, Polynomial.map_X]
      exact add_right_comm _ _ _
    · simp only [hi, ite_false, Polynomial.map_zero, add_zero]
private theorem topHasse_order (a d : ℕ) (P : Row 4) (S : Geom[X])
    (h : OrderAt P S d) : OrderAt (topHasse a P) S (d - a) := by
  have he := RingHom.congr_fun (translate_shift S) P
  change translateTop (shiftJet P S) = (translateTop P).map (shiftHom S) at he
  have hs : topHasse a (shiftJet P S) = shiftJet (topHasse a P) S := by
    change (translateTop (shiftJet P S)).coeff a =
      shiftHom S ((translateTop P).coeff a)
    rw [he, Polynomial.coeff_map]
  intro m hm
  rw [← hs] at hm
  have hd := h _ (source_support hm)
  rw [total_add_top] at hd
  omega
private theorem topHasse_one_not_dvd (f : Row 4) (hf : SmallFactor f) :
    ¬ f ∣ topHasse 1 f := by
  classical
  have hpos : 0 < f.degreeOf 3 := hf.2.1
  have hsmall : f.degreeOf 3 < K1.p :=
    (show f.degreeOf 3 ≤ 10 from hf.2.2.1.2.2).trans_lt (by decide)
  have hdeg : (topHasse 1 f).degreeOf 3 ≤ f.degreeOf 3 - 1 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have h := MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)
    rw [apply_add_top] at h
    omega
  have hnz : topHasse 1 f ≠ 0 := by
    have hsup : 0 < f.support.sup (fun m => m (3 : Fin 4)) := by
      rwa [← MvPolynomial.degreeOf_eq_sup]
    obtain ⟨u, hu, htop⟩ := (Finset.le_sup_iff hsup).mp (le_refl _)
    rw [← MvPolynomial.degreeOf_eq_sup] at htop
    have hupos : 0 < u 3 := hpos.trans_le htop
    have hult : u 3 < K1.p := (MvPolynomial.le_degreeOf_of_mem_support 3 hu).trans_lt hsmall
    let m := u.erase 3 + Finsupp.single 3 (u 3 - 1)
    have hsum : m + Finsupp.single 3 1 = u := by
      dsimp [m]
      rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel hupos, erase_top_add]
    have hm : m 3 + 1 = u 3 := by
      rw [← apply_add_top, hsum]
    have hc : (↑(u 3) : Geom[X]) ≠ 0 := by
      have : CharP Geom K1.p :=
        charP_of_injective_ringHom (RingHom.injective embed) K1.p
      intro hz
      have hz' : (↑(u 3) : Geom) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg (Polynomial.evalRingHom (0 : Geom)) hz
      exact (not_le_of_gt hult)
        (Nat.le_of_dvd hupos ((CharP.cast_eq_zero_iff Geom K1.p _).mp hz'))
    have hcoeff : (topHasse 1 f).coeff m ≠ 0 := by
      rw [topHasse_coeff, hm, hsum, Nat.choose_one_right]
      exact mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hu)
    intro hz
    exact hcoeff (by rw [hz]; rfl)
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro h
    exact hnz (by rw [hg, h, mul_zero])
  have h := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.1.ne_zero hg0
  rw [hg, h] at hdeg
  omega
private theorem topHasse_zero (P : Row 4) : topHasse 0 P = P := by
  ext m
  simp [topHasse_coeff]
private theorem coeff_X_mul_pow {R : Type*} [CommSemiring R]
    (V W : Polynomial R) (a : ℕ) :
    ((Polynomial.X * V) ^ a * W).coeff a = (V.coeff 0) ^ a * W.coeff 0 := by
  rw [mul_pow, mul_assoc]
  calc
    _ = (V ^ a * W).coeff 0 := by
      simpa only [zero_add] using Polynomial.coeff_X_pow_mul (V ^ a * W) a 0
    _ = _ := by
      change Polynomial.constantCoeff (V ^ a * W) =
        Polynomial.constantCoeff V ^ a * Polynomial.constantCoeff W
      rw [map_mul, map_pow]
private theorem exact_hasse_not_dvd {R : Type*} [CommRing R]
    (T : R →+* Polynomial R) (T0 : ∀ G, (T G).coeff 0 = G)
    (f P : R) (a : ℕ) (hf : Prime f) (hsep : ¬ f ∣ (T f).coeff 1)
    (hdiv : f ^ a ∣ P) (hexact : ¬ f ^ (a + 1) ∣ P) : ¬ f ∣ (T P).coeff a := by
  obtain ⟨U, rfl⟩ := hdiv
  have hu : ¬ f ∣ U := by
    rintro ⟨V, rfl⟩
    exact hexact ⟨V, by rw [pow_succ, mul_assoc]⟩
  let J := Ideal.span ({f} : Set R)
  have : J.IsPrime := Ideal.isPrime_span_singleton_of_prime hf
  let reduce := Ideal.Quotient.mk J
  let tr := (Polynomial.mapRingHom reduce).comp T
  have hzero (G : R) : reduce G = 0 ↔ f ∣ G :=
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hcoeff (G : R) (n : ℕ) : (tr G).coeff n = reduce ((T G).coeff n) :=
    Polynomial.coeff_map _ _
  have hconstant (G : R) : (tr G).coeff 0 = reduce G := by rw [hcoeff, T0]
  obtain ⟨V, hV⟩ := Polynomial.X_dvd_iff.mpr
    (show (tr f).coeff 0 = 0 by rw [hconstant]; exact (hzero _).mpr dvd_rfl)
  have hfirst : V.coeff 0 = reduce ((T f).coeff 1) := by
    rw [← hcoeff, hV]
    exact (Polynomial.coeff_X_mul V 0).symm
  have hr : reduce ((T (f ^ a * U)).coeff a) = reduce ((T f).coeff 1) ^ a * reduce U := by
    calc
      _ = (tr (f ^ a * U)).coeff a := (hcoeff _ _).symm
      _ = (V.coeff 0) ^ a * (tr U).coeff 0 := by
        rw [map_mul, map_pow, hV]
        exact coeff_X_mul_pow V (tr U) a
      _ = _ := by rw [hfirst, hconstant]
  intro h
  exact (mul_ne_zero (pow_ne_zero _ ((hzero _).not.mpr hsep))
    ((hzero _).not.mpr hu)) (hr.symm.trans ((hzero _).mpr h))
theorem proof : P0_9_3.c2 := by
  intro f P Γ s d a hf hb hw hord _ hdiv hexact
  obtain ⟨hbox, hweight⟩ := topHasse_bounds a P hb hw
  have hp : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hf.1
  have hproper : ¬ f ∣ topHasse a P :=
    exact_hasse_not_dvd translateTop topHasse_zero f P a hp (topHasse_one_not_dvd f hf) hdiv hexact
  exact ⟨topHasse a P, hproper, hbox, hweight, fun γ hγ =>
    topHasse_order a d P (extend (s γ)) (hord γ hγ)⟩
end
end P0_9_3_2
end
