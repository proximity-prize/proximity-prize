import ProximityPrize.SubmissionLower.Pack_K1DefsAt180255
import ProximityPrize.SubmissionLower.Retained762At180255
set_option Elab.async false

/-! K1_13 (overhead 1..2600) at the 6916 radius: A = 180255, e = 81889, D = A - 133671 = 46584,
layer width = (A + 3) - 133671 = 46587, terminal = 3000 * A - 1.

Port of `PackSource_K1_13Defs` / `PackSource_K1_13Split` (official Fast017.lean:12-418,
source 12b4b15df6ca7479274294f7e10aec177a3f2a9b) onto the `K1A` anchor definitions.

* A-free official definitions are reused verbatim through `open K1_13` (Geom, Row, jets, Shape,
  Fits, PoleData, OnFactor, Contact, FatEquations, symbols/remaining, chart geometry, trim_divisor).
* A-dependent definitions are re-stated here with the A' literals:
  `Messages` (180255 hits), `SmallFactor`/`LowerRow` (true weight < 90 A'), `PrimaryRank`
  (count and weight < 3000 A'), `ProperCut`, `LayerBudget` (need, layer count/width),
  `physicalPrice`/`fatPrice` (e = 81889, D = 46584, via `K1_13_8_R762.*At`).
* `of_children` is the official assembly; `c13_of` connects it to `K1A.c13 Bg`.

Constants (research/proximity-6916, all lightweight-checked in Python, NOT in Lean yet):
* rank 1206705973735705607 = cols' 91415523069168962567 - 262144 * blockSum 344119327909215,
  blockSum = official 344125686492134 - (c7 3319839881 + w3 1089925524 + w4 1948817514).
  The c6c7 patch proves only c7 + w3 (block sum ≤ 344121276726729); that gives need
  25891237961606 < cornerMass 57 = 25901955161916, i.e. order 57 and c8 FAILS. The w4 top
  certificate is therefore a hard prerequisite of `c2` below.
* need = ceilDiv rank 46587 = 25902203913876 (= `K1_13_8_R762.need6916`).
* c5 bound 18512791384214964 (c5_at_A.py), c8 bound 224203454802083722 (Bellman with
  threshold ⟨120,48,58⟩ + retained ⟨7,6,2⟩ branch, retained_762_branch.py).
* FatEquations keeps the official order 41481. If the c4 certificates are re-derived at A'
  with L + 3 = 49186 the arithmetic gives 41490 ≥ 41481, so the official field is the weaker
  (still sufficient) statement — provided firstOrder/secondOrder survive at A' (OPEN).

UNBUILT. No `sorry`; the eight children are hypotheses of `of_children`. -/

section PackSource_K1A_13Defs
set_option autoImplicit true
namespace K1A_13
noncomputable section
open Polynomial K1A
open K1_13 (Geom embed extend Row jet atJet shiftJet OrderAt TrueWeightLE indexDegree Shape shape
  InBox Fits PoleData topLead OnFactor Contact FatEquations symbols remaining
  FatEligible ceilDiv trim_divisor)
open scoped BigOperators

/-- Agreement A' = 180255 (official 180265). -/
abbrev agreement : ℕ := 180255
/-- (A' + 3) - 133671 (official 46597 = `K1_13_4.layerWidth`, Fast050.lean:8942). -/
abbrev layerWidth : ℕ := 46587
/-- 3000 A' - 1 (official `K1_13_4.terminal`, Fast050.lean:8941). -/
abbrev terminal : ℕ := 3000 * 180255 - 1
abbrev rank : ℕ := 1206705973735705607
abbrev need : ℕ := 25902203913876
abbrev c5Bound : ℕ := 18512791384214964
abbrev c8Bound : ℕ := 224203454802083722
abbrev bookBound : ℕ := 140000

structure Messages (w : I → K) (Γ : Finset K) (s : K → K[X]) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ 133671
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, 180255 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i

def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0 < (shape f).t ∧ InBox (shape f) ⟨120, 48, 10⟩ ∧
    TrueWeightLE f (90 * 180255 - 1)

def LowerRow (g : Row 3) : Prop :=
  g ≠ 0 ∧ g.totalDegree ≤ 120 ∧ indexDegree g ≤ 48 ∧ TrueWeightLE g (90 * 180255 - 1)

structure Cover {n : ℕ} (Γ : Finset K) (s : K → K[X])
    (g : Row 3) (f : Fin n → Row 4) : Prop where
  lower : LowerRow g
  factors : ∀ i, SmallFactor (f i)
  different : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)
  fits : Fits (fun i => shape (f i))
  covers : ∀ γ ∈ Γ, atJet g (extend (s γ)) = 0 ∨ ∃ i, OnFactor (f i) (extend (s γ))

def PrimaryRank (w : I → K) : Prop :=
  ∃ e : Fin 1206705973735705607 → Row 4, LinearIndependent Geom e ∧
    ∀ i, InBox (shape (e i)) ⟨4012, 1650, 550⟩ ∧
      TrueWeightLE (e i) (3000 * 180255 - 1) ∧ Contact w (e i)

def ProperCut (f : Row 4) (Γ : Finset K) (s : K → K[X]) (l : ℕ) : Prop :=
  ∃ Q : Row 4, (¬ f ∣ Q) ∧ InBox (shape Q) ⟨4012, 1650, 550⟩ ∧
    TrueWeightLE Q (3000 * 180255 - 1) ∧ ∀ γ ∈ Γ, OrderAt Q (extend (s γ)) l

def LayerBudget {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Prop :=
  25902203913876 ≤
    ∑ k ∈ Finset.range (1 + (3000 * 180255 - 1) / 46587),
      remaining (∑ i, (k + 1 - l i) * (a i).b) (∑ i, (k + 1 - l i) * (a i).j)

/-- `physicalPrice` with e = 262144 - A' and D = A' - 133671. -/
abbrev physicalPrice (x : Shape) (l : ℕ) : ℕ := K1_13_8_R762.physicalPriceAt 81889 46584 x l

abbrev fatPrice (x : Shape) : ℕ := K1_13_8_R762.fatPriceAt 81889 46584 x

theorem primary_layer_threshold : ceilDiv 1206705973735705607 46587 = 25902203913876 := by
  decide

theorem need_eq_retained : need = K1_13_8_R762.need6916 := rfl

theorem layer_count : 1 + (3000 * 180255 - 1) / 46587 = 11608 := by decide

/-- 6916 copy of the official `K1_13_2.surplus` (Fast017.lean:802-805): the A-free block budget
344119327909215 (`Asm.K1_13_2_3_strong`, w4 top rows included) and the A' source column count
91415523069168962567 give the primary rank. Without the w4 top rows (344121276726729) the same
arithmetic gives only 1206195102917315591 and `need` drops below cornerMass 57. -/
theorem rank_surplus {r k n : ℕ}
    (hr : r ≤ 262144 * 344119327909215) (hn : 91415523069168962567 ≤ n)
    (he : r + k = n) : 1206705973735705607 ≤ k := by
  omega

theorem rank_eq : 91415523069168962567 - 262144 * 344119327909215 = 1206705973735705607 := by
  decide

end
end K1A_13
end PackSource_K1A_13Defs

section PackSource_K1A_13Split
set_option autoImplicit true
namespace K1A_13
noncomputable section
open Polynomial K1A
open K1_13 (Geom embed extend Row jet atJet shiftJet OrderAt TrueWeightLE indexDegree Shape shape
  InBox Fits PoleData topLead OnFactor Contact FatEquations symbols remaining
  FatEligible ceilDiv trim_divisor)
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
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ 18512791384214964

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
    (∑ i, cost i) ≤ 224203454802083722

theorem degree_at_height {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (γ : K) (hγ : γ ∈ Γ) : (F.scalar γ).natDegree ≤ 131071 + M.overhead.toNat := by
  rcases (F.mark γ hγ).scalar_degree with h | h
  · simp [h]
  · omega

theorem messages_of_anchor {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (hw : M.overhead ≤ 2600) : Messages M.word Γ F.scalar := by
  refine ⟨F.distinct, ?_, ?_⟩
  · intro γ hγ
    have := degree_at_height M F γ hγ
    omega
  · intro γ hγ
    let m := F.mark γ hγ
    exact ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩

theorem pole_of_anchor {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2600) : Nonempty (PoleData Γ F.scalar) := by
  have hmax : M.overhead.toNat ≤ (extend M.E).natDegree := by
    rw [Polynomial.natDegree_map]
    unfold AnchorModel.overhead
    omega
  obtain ⟨H, hm, hd, hdiv⟩ := trim_divisor _ (M.E_monic.map embed) _ hmax
  let z := fun γ => embed (M.label γ)
  have unit {P : K[X]} (hp : IsCoprime P M.E) : IsCoprime (extend P) H :=
    (hp.map (Polynomial.mapRingHom embed)).of_isCoprime_of_dvd_right hdiv
  have amp (γ : K) : extend (M.amplitude γ) = extend M.A₀ + C (z γ) * extend M.A₁ := by
    simp [AnchorModel.amplitude, z]
  refine ⟨⟨H, hm, ?_, ?_, ?_, z, ?_, extend M.factor, extend M.Q, extend M.A₀,
    extend M.A₁, unit M.coprime_factor.symm, unit M.offset_reduced,
    unit M.first_amplitude_unit, ?_, ?_⟩⟩
  · rw [hd]
    omega
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

/-- Official `K1_13.of_children` (Fast017.lean:370-416) with the A' children and an explicit
budget field. The counting argument is literal-free. -/
theorem of_children {Bg : Budget} (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (h5 : c5) (h6 : c6) (h7 : c7) (h8 : c8)
    (hb : 140000 + 18512791384214964 + 224203454802083722 ≤ Bg.c13) : K1A.c13 Bg := by
  classical
  intro u D M Γ F lo hi
  let s := F.scalar
  have hmsg : Messages M.word Γ s := messages_of_anchor M F hi
  obtain ⟨pole⟩ := pole_of_anchor M F lo hi
  obtain ⟨n, g, f, cover⟩ := h1 _ _ _ hmsg
  obtain ⟨l, layers, cut⟩ := h3 _ _ _ hmsg (h2 _) _ _ _ cover
  obtain ⟨book, E, booked, hE⟩ := h4 _ _ _ hmsg pole
  let low := Γ.filter (fun γ => atJet g (extend (s γ)) = 0)
  have low_bound : low.card ≤ 18512791384214964 :=
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

/-- The value used in `budget_valid_check.json` (book offset 142720 as in the official
`K1.c13` constant 222142013343379695 + 18512789806143368). -/
abbrev c13Value : ℕ := 224203454802083722 + 18512791384214964 + 142720

theorem c13Value_eq : c13Value = 242716246186441406 := by decide

theorem c13_budget_room : 140000 + 18512791384214964 + 224203454802083722 ≤ c13Value := by decide

end
end K1A_13
end PackSource_K1A_13Split
