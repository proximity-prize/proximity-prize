import ProximityPrize.SubmissionLower.Fast075
import ProximityPrize.SubmissionLower.Low27Common
set_option Elab.async false

section PackSource_P0_9Defs
set_option autoImplicit true
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
abbrev sourceRank : ℕ := 1176881727286216908
abbrev layerWidth : ℕ := incidenceGap + 3
abbrev layerNeed : ℕ := 25259851200580

/-- Physical weight uses the full Taylor space through the new low endpoint. -/
def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val) * a) ≤ D

structure Messages (w : I → K) (Γ : Finset K) (s : K → K[X]) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, agreement ≤ T.card ∧
    ∀ i ∈ T, (s γ).eval (node i) = w i

/-- The raw quotient on the actual one-pole divisor has degree at most k−1.
The residue identity holds modulo the entire divisor with multiplicity. -/
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
  lead_total : g.totalDegree ≤ 120 - ∑ i, (shape (f i)).t
  lead_index : K1_13.indexDegree g ≤ 48 - 3 * ∑ i, (shape (f i)).t
  covers : ∀ γ ∈ Γ, K1_13.atJet g (extend (s γ)) = 0 ∨
    ∃ i, K1_13.OnFactor (f i) (extend (s γ))

def PrimaryRank (w : I → K) : Prop :=
  ∃ e : Fin sourceRank → Row 4, LinearIndependent Geom e ∧
    ∀ i, InBox (shape (e i)) primaryBox ∧ TrueWeightLE (e i) primaryCutoff ∧ Contact w (e i)

def ProperCut (f : Row 4) (Γ : Finset K) (s : K → K[X]) (l : ℕ) : Prop :=
  ∃ Q : Row 4, (¬ f ∣ Q) ∧ InBox (shape Q) primaryBox ∧ TrueWeightLE Q primaryCutoff ∧
    ∀ γ ∈ Γ, K1_13.OrderAt Q (extend (s γ)) l

/-- Every layer spends the simultaneous powers of all the factors. Index
spend already enforces the top cap because 1650 = 3 * 550. -/
def LayerBudget {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Prop :=
  layerNeed ≤
    ∑ r ∈ Finset.range (1 + primaryCutoff / layerWidth),
      remaining (∑ i, (r + 1 - l i) * (a i).b) (∑ i, (r + 1 - l i) * (a i).j)

def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩

/-- The lifted graph contributes one term for each of its two segment slots. -/
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
end PackSource_P0_9Defs

section PackSource_P0_9Split
set_option autoImplicit true
namespace P0_9
noncomputable section

open Polynomial
open P0 (K I k node AnchorModel AnchoredFamily)
open K1_13 (Geom embed extend Row Shape shape Fits atJet OnFactor FatEquations FatEligible)
open scoped BigOperators

/-- Factor the small physical anchor into a lower equation and leading-unit charts. -/
def c1 : Prop :=
  ∀ w Γ s, Messages w Γ s →
    ∃ (n : ℕ) (g : Row 3) (f : Fin n → Row 4), Cover Γ s g f

/-- Source rank for the single full physical primary bank. -/
def c2 : Prop := ∀ w, PrimaryRank w

/-- The whole cutoff filtration supplies simultaneous layer spend and proper cuts. -/
def c3 : Prop :=
  ∀ w Γ s, Messages w Γ s → PrimaryRank w →
    ∀ n (g : Row 3) (f : Fin n → Row 4), Cover Γ s g f →
      ∃ l : Fin n → ℕ, LayerBudget (fun i => shape (f i)) l ∧
        ∀ i, 0 < l i → ProperCut (f i) Γ s (l i)

/-- The two one-pole sources give a common lower equation or a fat resultant. -/
def c4 : Prop :=
  ∀ w Γ s, Messages w Γ s → PoleData Γ s →
    ∃ (book : Finset K) (E : FatEquations), book.card ≤ 140000 ∧
      ∀ γ ∈ Γ, γ ∉ book → E.holds (extend (s γ))

/-- The fixed-chart mixed intersection fee is linear in the lower support. -/
def supportMixed (b j t : ℕ) : ℕ :=
  65983021807667 * b + 218189755673514 * j + 3388333121990 * t

def lowerPrice (g : Row 3) : ℕ :=
  supportMixed g.totalDegree (K1_13.indexDegree g) (K1_13.indexDegree g / 2) +
    4697034128334

def factorPrice (t : ℕ) : ℕ :=
  if t ≤ 7 then 222672674688503043 else if t ≤ 9 then 229472478411275283 else 229473781150506218

/-- Aggregate order-at-most-two count before the single seed book. -/
def c5 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow g →
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ lowerPrice g

/-- Proper physical cut on a single leading-unit factor at its actual order. -/
def c6 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → Γ.card ≤ physicalPrice (shape f) l

/-- Fat projected alternative on a single eligible factor, including singular sheets. -/
def c7 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) → FatEligible (shape f) →
    ∀ E : FatEquations, (∀ γ ∈ Γ, E.holds (extend (s γ))) → Γ.card ≤ fatPrice (shape f)

/-- The sum of factor fees through all retained and positive prefixes. -/
def c8 : Prop :=
  ∀ n (a : Fin n → Shape) (l cost : Fin n → ℕ), Fits a → LayerBudget a l →
    (∀ i, 0 < l i → cost i ≤ physicalPrice (a i) (l i)) →
    (∀ i, FatEligible (a i) → cost i ≤ fatPrice (a i)) →
    (∑ i, cost i) ≤ factorPrice (∑ i, (a i).t)

theorem degree_at_height {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (γ : K) (hγ : γ ∈ Γ) : (F.scalar γ).natDegree ≤ k - 1 + M.overhead.toNat := by
  rcases (F.mark γ hγ).scalar_degree with h | h
  · simp [h]
  · change (F.scalar γ).natDegree ≤ 131071 + M.overhead.toNat
    omega

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
    unfold K21.AnchorModel.overhead
    omega
  obtain ⟨H, hm, hd, hdiv⟩ := K1_13.trim_divisor _ (M.E_monic.map embed) _ hmax
  let z := fun γ => embed (M.label γ)
  have unit {P : K[X]} (hp : IsCoprime P M.E) : IsCoprime (extend P) H :=
    (hp.map (Polynomial.mapRingHom embed)).of_isCoprime_of_dvd_right hdiv
  have amp (γ : K) : extend (M.amplitude γ) = extend M.A₀ + C (z γ) * extend M.A₁ := by
    simp [K21.AnchorModel.amplitude, z]
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
  have low_bound : low.card ≤ lowerPrice g :=
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
  have hcost : lowerPrice g + factorPrice (∑ i, (shape (f i)).t) ≤
      242144488021490537 := by
    have hB := cover.lower.2.1
    have hJ := cover.lower.2.2.1
    have hb := cover.lead_total
    have hj := cover.lead_index
    unfold lowerPrice supportMixed factorPrice
    split_ifs <;> omega
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
end PackSource_P0_9Split

