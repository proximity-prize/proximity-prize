import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Data.NNRat.Floor
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Pack_K1Defs
set_option Elab.async false

section PackSource_K1_13Defs
set_option autoImplicit true
namespace K1_13
noncomputable section
open Polynomial K1
open scoped BigOperators

abbrev Geom := AlgebraicClosure K
abbrev embed := algebraMap K Geom
abbrev extend (S : K[X]) := S.map embed
abbrev Row (n : ℕ) := MvPolynomial (Fin n) Geom[X]

/-- The same scalar polynomial at an indeterminate abscissa in every chart. -/
def jet (S : Geom[X]) {n : ℕ} (i : Fin n) : Geom[X] := hasseDeriv i.val S

def atJet {n : ℕ} (P : Row n) (S : Geom[X]) : Geom[X] :=
  MvPolynomial.eval (jet S) P

def shiftJet {n : ℕ} (P : Row n) (S : Geom[X]) : Row n :=
  MvPolynomial.eval₂ MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)) P

/-- Ordinary order in all jet directions with the abscissa held fixed. -/
def OrderAt {n : ℕ} (P : Row n) (S : Geom[X]) (d : ℕ) : Prop :=
  ∀ m ∈ (shiftJet P S).support, d ≤ m.sum (fun _ a => a)

/-- A physical upper bound also controls the degree in the abscissa. -/
def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (133671 - i.val) * a) ≤ D

def indexDegree {n : ℕ} (P : Row n) : ℕ :=
  P.support.sup (fun m => m.sum (fun i a => i.val * a))

structure Shape where
  b : ℕ
  j : ℕ
  t : ℕ
  deriving DecidableEq

def shape (P : Row 4) : Shape := ⟨P.totalDegree, indexDegree P, P.degreeOf 3⟩

def InBox (x y : Shape) : Prop := x.b ≤ y.b ∧ x.j ≤ y.j ∧ x.t ≤ y.t

def Fits {n : ℕ} (a : Fin n → Shape) : Prop :=
  (∀ i, 1 ≤ (a i).t ∧ 3 * (a i).t ≤ (a i).j ∧ (a i).j ≤ 3 * (a i).b) ∧
  (∑ i, (a i).b) ≤ 120 ∧ (∑ i, (a i).j) ≤ 48 ∧ (∑ i, (a i).t) ≤ 10

structure Messages (w : I → K) (Γ : Finset K) (s : K → K[X]) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ 133671
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, 180255 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i

/-- The projective residue equation is cleared only by factors which are units
modulo H. Its divisibility is in the polynomial ring, including repeated roots. -/
structure PoleData (Γ : Finset K) (s : K → K[X]) where
  H : Geom[X]
  monic : H.Monic
  small : 1 ≤ H.natDegree ∧ H.natDegree ≤ 2600
  nodes : ∀ i, H.eval (embed (node i)) ≠ 0
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ 131071 + H.natDegree
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
    TrueWeightLE f (90 * 180255 - 1)

/-- Substitute only the lower true jets and extract the original leading
coefficient in the highest jet. The nonzero test is at generic X. -/
def topLead (f : Row 4) (S : Geom[X]) : Geom[X] :=
  (MvPolynomial.eval₂ Polynomial.C
    (fun i : Fin 4 => if i = 3 then Polynomial.X else Polynomial.C (jet S i)) f).coeff (shape f).t

def OnFactor (f : Row 4) (S : Geom[X]) : Prop :=
  atJet f S = 0 ∧ topLead f S ≠ 0

def LowerRow (g : Row 3) : Prop :=
  g ≠ 0 ∧ g.totalDegree ≤ 120 ∧ indexDegree g ≤ 48 ∧ TrueWeightLE g (90 * 180255 - 1)

structure Cover {n : ℕ} (Γ : Finset K) (s : K → K[X])
    (g : Row 3) (f : Fin n → Row 4) : Prop where
  lower : LowerRow g
  factors : ∀ i, SmallFactor (f i)
  different : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)
  fits : Fits (fun i => shape (f i))
  covers : ∀ γ ∈ Γ, atJet g (extend (s γ)) = 0 ∨ ∃ i, OnFactor (f i) (extend (s γ))

/-- Vanishing at a node is tested on arbitrary polynomial paths through its
value. In particular a locator perturbation may exceed the declared degree. -/
def Contact (w : I → K) (P : Row 4) : Prop :=
  ∀ i (S : Geom[X]), S.eval (embed (node i)) = embed (w i) →
    (Polynomial.X - C (embed (node i))) ^ 3000 ∣ atJet P S

def PrimaryRank (w : I → K) : Prop :=
  ∃ e : Fin 1205039109374987271 → Row 4, LinearIndependent Geom e ∧
    ∀ i, InBox (shape (e i)) ⟨4012, 1650, 550⟩ ∧
      TrueWeightLE (e i) (3000 * 180255 - 1) ∧ Contact w (e i)

def ProperCut (f : Row 4) (Γ : Finset K) (s : K → K[X]) (l : ℕ) : Prop :=
  ∃ Q : Row 4, (¬ f ∣ Q) ∧ InBox (shape Q) ⟨4012, 1650, 550⟩ ∧
    TrueWeightLE Q (3000 * 180255 - 1) ∧ ∀ γ ∈ Γ, OrderAt Q (extend (s γ)) l

/-- Seed-independent equations in the three lower jets. Clearing a common
X-denominator preserves multiplicities at the indeterminate abscissa. -/
structure FatEquations where
  common : Row 3
  residual : Row 3
  common_ne : common ≠ 0
  residual_ne : residual ≠ 0
  common_total : common.totalDegree ≤ 6300
  common_index : indexDegree common ≤ 2403
  residual_total : residual.totalDegree ≤ 952630000
  residual_index : indexDegree residual ≤ 322000000

def FatEquations.holds (E : FatEquations) (S : Geom[X]) : Prop :=
  atJet E.common S = 0 ∨ OrderAt E.residual S 41481

/-- Count four jet exponents with bounded total and index. The innermost
summand counts the admissible exponents of Y₀. -/
def symbols (b j : ℕ) : ℕ :=
  ∑ z ∈ Finset.range (min b (j / 3) + 1),
  ∑ y ∈ Finset.range (min (b - z) ((j - 3*z) / 2) + 1),
  ∑ x ∈ Finset.range (min (b - z - y) (j - 3*z - 2*y) + 1), (b - z - y - x + 1)

def remaining (b j : ℕ) : ℕ :=
  if b ≤ 4012 ∧ j ≤ 1650 then symbols (4012 - b) (1650 - j) else 0

/-- Simultaneous powers of every factor consume the same symbol box. For
a spent product with index ≥ 3 times its top degree, the residual index bound
already imposes the residual top bound, since 1650 = 3 * 550. -/
def LayerBudget {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Prop :=
  25866424310967 ≤
    ∑ k ∈ Finset.range (1 + (3000 * 180255 - 1) / 46587),
      remaining (∑ i, (k + 1 - l i) * (a i).b) (∑ i, (k + 1 - l i) * (a i).j)

/- Full-space physical and fat factor prices from VERIFY-LOW L11–L16.
The polytopes below lie in the chamber b ≥ j ≥ 3t. -/

def Shape.plus (p q : Shape) : Shape := ⟨p.b + q.b, p.j + q.j, p.t + q.t⟩
def Shape.scale (p : Shape) (k : ℕ) : Shape := ⟨k*p.b, k*p.j, k*p.t⟩
def Shape.chamber (p : Shape) : Shape := ⟨max p.b p.j, p.j, p.t⟩

/-- Thirty-two times ordinary four-dimensional volume, integrated in the
highest exponent. Use signed arithmetic before taking the mixed difference. -/
def volume32 (p : Shape) : ℤ :=
  let b : ℤ := p.b
  let j : ℤ := p.j
  let t : ℤ := p.t
  8*b*j^2*t - 24*b*j*t^2 + 24*b*t^3 - 4*j^3*t + 14*j^2*t^2 - 20*j*t^3 + 9*t^4

def difference (h : Shape → ℤ) (a x : Shape) := h (x.plus a) - h x

def mixed32 (p q r s : Shape) : ℕ :=
  (difference (difference (difference (difference volume32 p) q) r) s ⟨0,0,0⟩).toNat

def ceilDiv (a b : ℕ) := (a + b - 1) / b

abbrev taylorLength : ℕ := 133672

def chart (L : ℕ) (p : Shape) : Shape :=
  let i := 2*L*(p.j - 3) + L + 3
  ⟨max (1 + 2*L*(p.b - 1)) i, i, min (2*L*(p.t - 1) + L + 1) (i / 3)⟩

def liftedChart (L : ℕ) (p : Shape) : Shape :=
  let i := 4 + (L - 5)*(p.j - 2)
  ⟨max (1 + (L - 5)*(p.b - 1)) i, i, min (2 + (L - 5)*p.t) (i / 3)⟩

def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength*(p.j - 2)
  ⟨max (1 + taylorLength*(p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩

/-- The lifted graph contributes three terms, one for each segment slot. -/
def surfaceNumerator32 (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L+1) p
  let b := liftedChart (L+2) p
  min (mixed32 p q (chart (L+1) p) (chart (L+2) p))
    (mixed32 p q a b + (L+1) * mixed32 p q g b + (L+2) * mixed32 p q g a)

def physicalPrice (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q : Shape := ⟨4013, 1650, 550⟩
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32 p q) 32 +
    ceilDiv ((81889 + 2*46584) * x.b * q.b * (chart (taylorLength+1) p).b) 46584
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2*x.t*mixed32 p p p h
  let points := mixed32 p q auxBox p + 2*x.t*mixed32 p p p p
  ceilDiv numerator l + 2*133671*x.b*q.b + ceilDiv (81889*curves + 2*46584*points) (32*46584)

def FatEligible (x : Shape) : Prop := x.b ≤ 60 ∧ x.j ≤ 32

def fatPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := if x.t = 1 then linearChart p else chart (taylorLength + 4) p
  let q : Shape := ⟨952630000, 322000000, 0⟩
  let big : Shape := ⟨35007, 12106, 0⟩
  let cut : Shape := ⟨max (max h.b big.b) (max h.j (big.j+1)), max h.j (big.j+1), max 1 h.t⟩
  let divisors := ceilDiv (81889 * mixed32 p big cut h) (32*46584) +
    ceilDiv (mixed32 p big cut p) 32 + 20*p.b*h.b^2 + 5*133671*p.b*h.b + 1
  let singular := if 1 < x.t then ceilDiv (4*x.t*mixed32 p p h h) 32 + x.t*x.b^2+1 else 0
  let curves := ceilDiv (81889*mixed32 p q q h + 46584*mixed32 p q q p) (32*46584*293711590)
  let isolated := ceilDiv (3*q.j^2*(2*q.b - q.j)) (4*41481*(41481 - 33184 + 1)*1037)
  divisors + singular + curves + isolated

theorem primary_layer_threshold :
    ceilDiv 1205039109374987271 46587 = 25866424310967 := by decide

theorem physical_price_corner :
    physicalPrice ⟨120,48,10⟩ 57 = 225965362921901696 := by decide

theorem fat_price_quadratic :
    fatPrice ⟨2,6,2⟩ = 96066881080577033 := by decide

end
end K1_13
end PackSource_K1_13Defs

section PackSource_K1_13Split
set_option autoImplicit true
namespace K1_13
noncomputable section
open Polynomial K1
open scoped BigOperators

/-- Factor the small physical anchor and collect all lower and leading terms. -/
def c1 : Prop :=
  ∀ w Γ s, Messages w Γ s →
    ∃ (n : ℕ) (g : Row 3) (f : Fin n → Row 4), Cover Γ s g f

/-- Full physical source at the single (4012,1650,550) primary bank. -/
def c2 : Prop := ∀ w, PrimaryRank w

/-- Availability from the whole cutoff filtration of this bank on one input. -/
def c3 : Prop :=
  ∀ w Γ s, Messages w Γ s → PrimaryRank w →
    ∀ n (g : Row 3) (f : Fin n → Row 4), Cover Γ s g f →
      ∃ l : Fin n → ℕ, LayerBudget (fun i => shape (f i)) l ∧
        ∀ i, 0 < l i → ProperCut (f i) Γ s (l i)

/-- A common lower-jet equation or a fat residual, after a single seed book. -/
def c4 : Prop :=
  ∀ w Γ s, Messages w Γ s → PoleData Γ s →
    ∃ (book : Finset K) (E : FatEquations), book.card ≤ 140000 ∧
      ∀ γ ∈ Γ, γ ∉ book → E.holds (extend (s γ))

/-- Aggregate order-at-most-two count, before parameter exceptions. -/
def c5 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow g →
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ 18512791384214964

/-- Proper physical cutter with full jet multiplicity on one leading-unit factor. -/
def c6 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → Γ.card ≤ physicalPrice (shape f) l

/-- Complete fat projected alternative, including singular sheets. -/
def c7 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) → FatEligible (shape f) →
    ∀ E : FatEquations, (∀ γ ∈ Γ, E.holds (extend (s γ))) → Γ.card ≤ fatPrice (shape f)

/-- Every factor has a nonnegative cost bounded by each applicable tariff. -/
def c8 : Prop :=
  ∀ n (a : Fin n → Shape) (l cost : Fin n → ℕ), Fits a → LayerBudget a l →
    (∀ i, 0 < l i → cost i ≤ physicalPrice (a i) (l i)) →
    (∀ i, FatEligible (a i) → cost i ≤ fatPrice (a i)) →
    (∑ i, cost i) ≤ 225965362921901696

theorem trim_divisor (P : Geom[X]) (hm : P.Monic) (h : ℕ) (hh : h ≤ P.natDegree) :
    ∃ H : Geom[X], H.Monic ∧ H.natDegree = h ∧ H ∣ P := by
  classical
  have hroots : h ≤ P.roots.card := hh.trans_eq (IsAlgClosed.splits P).natDegree_eq_card_roots
  have hpos : 0 < (P.roots.powersetCard h).card := by
    rw [Multiset.card_powersetCard]
    exact Nat.choose_pos hroots
  obtain ⟨t, ht⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  obtain ⟨htle, htcard⟩ := Multiset.mem_powersetCard.mp ht
  exact ⟨_, monic_multisetProd_X_sub_C t, (natDegree_multiset_prod_X_sub_C_eq_card t).trans htcard,
    (t.prod_X_sub_C_dvd_iff_le_roots hm.ne_zero).mpr htle⟩

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

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (h5 : c5) (h6 : c6) (h7 : c7) (h8 : c8) : K1.c13 := by
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

end
end K1_13
end PackSource_K1_13Split

section PackSource_K1_13_2Defs
set_option autoImplicit true
namespace K1_13_2

noncomputable section

open K1_13 PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

abbrev SourcePolynomial := DifferentialPolynomial Geom 3
abbrev SourceExponent := JetVariable 3 →₀ ℕ
abbrev Local := LocalPolynomial Geom 3

/-- Weight that counts only the highest jet exponent. -/
def topWeight (v : JetVariable 3) : ℕ :=
  v.elim 0 (Pi.single (3 : Fin 4) (1 : ℕ))

/-- The exact 4012 source, before any contact equations. -/
def SourceEligible (e : SourceExponent) : Prop :=
  e.weight jetDegreeWeight ≤ 4012 ∧
  e.weight jetDerivativeWeight ≤ 1650 ∧
  e.weight topWeight ≤ 550 ∧
  e.weight (differentialWeight 133671) ≤ 3000 * 180255 - 1

def sourceExponents : Set SourceExponent := { e | SourceEligible e }

theorem sourceExponents_finite : sourceExponents.Finite := by
  refine (Finsupp.finite_of_nat_weight_le (differentialWeight (d := 3) 133671)
    ?_ (3000 * 180255 - 1)).subset (fun e he => he.2.2.2)
  intro v
  cases v with
  | none => decide
  | some j =>
    exact (differentialWeight_some_pos_of_order_lt_degree (by decide : 3 < 133671) j).ne'

def sourceColumns : Finset SourceExponent := sourceExponents_finite.toFinset

def SourceSpace : Submodule Geom SourcePolynomial :=
  MvPolynomial.restrictSupport Geom sourceExponents

instance : Module.Finite Geom SourceSpace :=
  MvPolynomial.restrictSupport_finite sourceExponents_finite

/-- The first component is total jet degree. The second encodes the signed
difference between the abscissa exponent and the derivative index. -/
abbrev BlockIndex := Fin 4013 × Fin 4650

def offset (i : BlockIndex) : ℤ := (i.2.val : ℤ) - 1650

def blockExponents (i : BlockIndex) : Set SourceExponent :=
  { e | SourceEligible e ∧ e none < 3000 ∧
    e.weight jetDegreeWeight = i.1.val ∧ (e none : ℤ) - e.weight jetDerivativeWeight = offset i }

def BlockSpace (i : BlockIndex) : Submodule Geom SourcePolynomial :=
  MvPolynomial.restrictSupport Geom (blockExponents i)

instance (i : BlockIndex) : Module.Finite Geom (BlockSpace i) :=
  MvPolynomial.restrictSupport_finite
    (sourceExponents_finite.subset (fun _ h => h.1))

def originBlock (i : BlockIndex) : BlockSpace i →ₗ[Geom] Local :=
  (localConstraintAt 3000 0 0).domRestrict (BlockSpace i)

/-- Cumulative denominator coefficient for
    1 / ((1 - x)^2 (1 - x^2) (1 - x^3)).
    Grouping the weights by residue modulo 6 gives this cubic. -/
def denominator (u : ℤ) : ℤ :=
  if u < 0 then 0 else
    let q := u / 6
    let r := u % 6
    1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
      (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)

/-- Cumulative count of degree-d monomials with (0,1,2,3)-weight at most u. -/
def cumulative (d u : ℤ) : ℤ :=
  if d < 0 || u < 0 then 0 else
    let v := min u (3 * d)
    denominator v - denominator (v - d - 1) - denominator (v - d - 2) -
      denominator (v - d - 3) + denominator (v - 2 * d - 3) +
      denominator (v - 2 * d - 4) + denominator (v - 2 * d - 5) -
      denominator (v - 3 * d - 6)

/-- Also cap the exponent of the variable of weight 3. -/
def cappedCount (d u cap : ℤ) : ℤ :=
  if cap < 0 then 0 else cumulative d u - cumulative (d - cap - 1) (u - 3 * (cap + 1))

/-- Residual degree and bounds after stripping the forced value-variable power. -/
structure Flag where
  degree : ℤ
  lower : ℤ
  upper : ℤ
  cap : ℤ
  order : ℤ

/-- Valuations of the eleven test factors in PASCAL-CUBIC. In order these are
    Y₀, Y₁, Y₂, Y₃, Z, Y₀-Y₁, Y₀-Y₁+Y₂, and the four higher-degree forms. -/
def factorFlag (j : Fin 11) : Flag :=
  ![⟨1, 0, 0, 0, 0⟩, ⟨1, 1, 1, 0, 0⟩, ⟨1, 2, 2, 0, 1⟩, ⟨1, 3, 3, 1, 2⟩,
    ⟨1, 0, 3, 1, 3⟩, ⟨1, 0, 1, 0, 1⟩, ⟨1, 0, 2, 0, 2⟩, ⟨2, 1, 2, 0, 2⟩,
    ⟨2, 1, 3, 1, 3⟩, ⟨2, 2, 4, 1, 4⟩, ⟨3, 2, 3, 1, 3⟩] j

def initialFlag (i : BlockIndex) : Flag :=
  ⟨min i.1.val 1650, -offset i, 1650, 550, 3000 - (i.1.val : ℤ) - offset i⟩

def residualFlag (F : Flag) (power : Fin 11 → ℕ) : Flag where
  degree := F.degree - ∑ j, (power j : ℤ) * (factorFlag j).degree
  lower := F.lower - ∑ j, (power j : ℤ) * (factorFlag j).lower
  upper := F.upper - ∑ j, (power j : ℤ) * (factorFlag j).upper
  cap := F.cap - ∑ j, (power j : ℤ) * (factorFlag j).cap
  order := F.order - ∑ j, (power j : ℤ) * (factorFlag j).order

def oldCount (F : Flag) : ℤ :=
  cappedCount F.degree F.upper F.cap -
    cappedCount F.degree (min F.upper (F.lower - 1)) F.cap

/-- In (Z,Y₁,Y₂,Y₃) coordinates count target monomials of old index
at least `lower` and contact weight below `order`. -/
def targetCount (F : Flag) : ℤ :=
  let balance := F.order - 1 - F.lower + F.degree
  if balance < 0 then 0 else
    let removed := min F.degree (balance / 4) + 1
    cumulative F.degree (F.order - 1) - cumulative (F.degree - removed) (F.order - 1 - 3 * removed) -
      cumulative F.degree (F.lower - 1) + cumulative (F.degree - removed) (F.lower - 1)

/-- A signed dimension lower bound. Negative intermediate estimates are harmless. -/
def kernelLower (F : Flag) : ℤ :=
  if F.degree < 0 || F.upper < 0 || F.cap < 0 then 0 else oldCount F - targetCount F

/-- The possible contact rank of one block, using a single product of test factors. -/
def blockBound (i : BlockIndex) (power : Fin 11 → ℕ) : ℕ :=
  let F := initialFlag i
  if F.order ≤ 0 then 0 else
    let active := oldCount { F with upper := min F.upper (2999 - offset i) }
    let lower := max 0 (max (kernelLower F) (kernelLower (residualFlag F power)))
    (min active (oldCount F - lower)).toNat

end

end K1_13_2
end PackSource_K1_13_2Defs

section PackSource_K1_13_2AuxRows
set_option autoImplicit true
namespace K1_13_2

noncomputable section

open K1 K1_13 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
open MvPolynomial (mem_support_iff)

def toRow : SourcePolynomial ≃ₐ[Geom] Row 4 :=
  MvPolynomial.optionEquivRight Geom (Fin 4)

private theorem weight_eq_sum (m : Fin 4 →₀ ℕ) (weight : Fin 4 → ℕ) :
    m.weight weight = m.sum (fun i a => weight i * a) := by
  simp only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm]

/-- Extract the support test at the largest X exponent in a nonzero coefficient. -/
theorem row_bounds (Q : SourceSpace) :
    InBox (shape (toRow Q.1)) ⟨4012, 1650, 550⟩ ∧
    TrueWeightLE (toRow Q.1) (3000 * 180255 - 1) := by
  classical
  have h (m : Fin 4 →₀ ℕ) (hm : m ∈ (toRow Q.1).support) :
      m.sum (fun _ a => a) ≤ 4012 ∧
      m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
      ((toRow Q.1).coeff m).natDegree + m.sum (fun i a => (133671 - i.val) * a) ≤
        3000 * 180255 - 1 := by
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
    have jw : differentialWeight (d := 3) 133671 =
        (fun v => v.elim 1 (fun i => 133671 - i.val)) := by
      funext v; cases v <;> rfl
    rw [jb] at hb
    rw [ji] at hj
    rw [jw] at hw
    change (m.optionElim n).weight (fun v => v.elim 0 (Pi.single (3 : Fin 4) (1 : ℕ))) ≤ 550 at ht
    simp only [Finsupp.weight_optionElim, zero_mul, zero_add, one_mul] at hb hj ht hw
    rw [Finsupp.weight_single_one_apply] at ht
    rw [weight_eq_sum m (fun _ => 1)] at hb
    rw [weight_eq_sum m (fun i => i.val)] at hj
    rw [weight_eq_sum m (fun i => 133671 - i.val)] at hw
    exact ⟨by simpa only [one_mul] using hb, hj, ht, hw⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact Finset.sup_le fun m hm => (h m hm).1
  · exact Finset.sup_le fun m hm => (h m hm).2.1
  · exact MvPolynomial.degreeOf_le_iff.mpr fun m hm => (h m hm).2.2.1
  · exact fun m hm => (h m hm).2.2.2

theorem atJet_toRow (Q : SourcePolynomial) (S : Geom[X]) :
    atJet (toRow Q) S = differentialSpecialization Q S := by
  let values : Option (Fin 4) → Geom[X] := fun v => v.elim Polynomial.X (jet S)
  have h := MvPolynomial.aeval_map_optionEquivRight values Q
  have hx : values none = Polynomial.X := rfl
  have hid : (AlgHom.id Geom Geom[X]).toRingHom = RingHom.id Geom[X] := rfl
  rw [hx, Polynomial.aeval_X_left, hid, MvPolynomial.map_id, MvPolynomial.aeval_eq_eval] at h
  have hhom : MvPolynomial.aeval values = differentialSpecializationHom (d := 3) S := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [MvPolynomial.aeval_X]
    cases v with
    | none => exact (differentialSpecialization_x (d := 3) S).symm
    | some j => exact (differentialSpecialization_jet j S).symm
  rw [hhom] at h
  exact h

/-- Translate each independent coordinate weight and intersect the resulting bounds. -/
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
      preserve (differentialWeight 133671) (3000 * 180255 - 1)
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
  rw [atJet_toRow]
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

end K1_13_2
end PackSource_K1_13_2AuxRows

section PackSource_K1_13_2Split
set_option autoImplicit true
namespace K1_13_2

noncomputable section

open K1 K1_13 PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

/-- The monomial columns before the contact constraints. -/
def c1 : Prop := 91415523069168962567 ≤ sourceColumns.card

/-- A certified flag-product estimate for each origin block. -/
def c2 : Prop :=
  ∀ i : BlockIndex, ∀ power : Fin 11 → ℕ,
    Module.finrank Geom (LinearMap.range (originBlock i)) ≤ blockBound i power

/-- A choice of products for the pure integer rank calculation. -/
def c3 : Prop :=
  ∃ power : BlockIndex → Fin 11 → ℕ, (∑ i, blockBound i (power i)) ≤ 344125686492134

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

private theorem finrank_finset_sup_le {ι V : Type*} [AddCommGroup V] [Module Geom V]
    (p : ι → Submodule Geom V) [∀ i, Module.Finite Geom (p i)] (s : Finset ι) :
    Module.finrank Geom (s.sup p : Submodule Geom V) ≤ ∑ i ∈ s, Module.finrank Geom (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    exact (Submodule.finrank_add_le_finrank_add_finrank (p i) (s.sup p)).trans
      (Nat.add_le_add_left ih _)

private theorem finrank_of_column_cover {ι : Type*} [Fintype ι]
    (f : SourcePolynomial →ₗ[Geom] Local) (p : ι → Submodule Geom Local)
    [∀ i, Module.Finite Geom (p i)] (bound : ι → ℕ)
    (hcol : ∀ e ∈ sourceExponents, ∀ c, f (MvPolynomial.monomial e c) = 0 ∨
      ∃ i, f (MvPolynomial.monomial e c) ∈ p i)
    (hbound : ∀ i, Module.finrank Geom (p i) ≤ bound i) :
    Module.finrank Geom (LinearMap.range (f.domRestrict SourceSpace)) ≤ ∑ i, bound i := by
  have cover : LinearMap.range (f.domRestrict SourceSpace) ≤ Finset.univ.sup p := by
    intro L hL
    obtain ⟨Q, hQ⟩ := LinearMap.mem_range.mp hL
    rw [← hQ]
    change f Q.1 ∈ Finset.univ.sup p
    have expand := congrArg f Q.1.as_sum
    rw [map_sum] at expand
    rw [expand]
    refine Submodule.sum_mem _ fun e he => ?_
    rcases hcol e (Q.2 he) (Q.1.coeff e) with hzero | ⟨i, hi⟩
    · rw [hzero]
      exact Submodule.zero_mem _
    · exact (Finset.le_sup (f := p) (Finset.mem_univ i)) hi
  exact (Submodule.finrank_mono cover).trans
    ((finrank_finset_sup_le p _).trans (Finset.sum_le_sum fun i _ => hbound i))

/-- Every column surviving the local truncation belongs to a grade/offset block. -/
theorem origin_rank_le (power : BlockIndex → Fin 11 → ℕ) (h : c2) :
    Module.finrank Geom (LinearMap.range (nodeMap 0 0)) ≤ ∑ i, blockBound i (power i) := by
  classical
  let ranges : BlockIndex → Submodule Geom Local := fun i => LinearMap.range (originBlock i)
  refine finrank_of_column_cover (localConstraintAt 3000 0 0) ranges
    (fun i => blockBound i (power i)) ?_ (fun i => h i (power i))
  intro e he c
  by_cases hx : e none < 3000
  · have he' : SourceEligible e := he
    let grade := e.weight jetDegreeWeight
    let idx := e.weight jetDerivativeWeight
    have hb : grade ≤ 4012 := he'.1
    have hj : idx ≤ 1650 := he'.2.1
    let i : BlockIndex := (⟨grade, by omega⟩, ⟨e none + (1650 - idx), by omega⟩)
    have hi : e ∈ blockExponents i := by
      refine ⟨he', hx, rfl, ?_⟩
      change (e none : ℤ) - idx = ((e none + (1650 - idx) : ℕ) : ℤ) - 1650
      omega
    refine Or.inr ⟨i, ?_⟩
    have hm : MvPolynomial.monomial e c ∈ BlockSpace i := by
      unfold BlockSpace
      exact (MvPolynomial.monomial_mem_restrictSupport Geom).mpr (Or.inl hi)
    exact ⟨⟨MvPolynomial.monomial e c, hm⟩, rfl⟩
  · exact Or.inl (high_monomial_vanishes e _ (Nat.le_of_not_gt hx))

/-- Translation puts every node map inside the range of the origin map. -/
theorem node_range_le (x y : Geom) :
    LinearMap.range (nodeMap x y) ≤ LinearMap.range (nodeMap 0 0) := by
  rintro _ ⟨Q, rfl⟩
  refine ⟨⟨globalPointTranslation x y Q.1, translate_mem_source x y Q⟩, ?_⟩
  exact (localConstraintAt_eq_zero_globalPointTranslation (m := 3000) x y Q.1).symm

/-- Sum the individual rank bounds by factoring through the product of the node ranges. -/
theorem word_rank_le (w : I → K) {b : ℕ}
    (h : Module.finrank Geom (LinearMap.range (nodeMap 0 0)) ≤ b) :
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

private theorem surplus {r k n : ℕ}
    (hr : r ≤ 262144 * 344125686492134) (hn : 91415523069168962567 ≤ n)
    (he : r + k = n) : 1205039109374987271 ≤ k := by
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
      ∀ i, InBox (shape (e i)) ⟨4012, 1650, 550⟩ ∧
        TrueWeightLE (e i) (3000 * 180255 - 1) ∧ Contact w (e i) := by
  let liftRow : LinearMap.ker (wordMap w) →ₗ[Geom] Row 4 :=
    toRow.toLinearMap.comp (SourceSpace.subtype.comp (LinearMap.ker (wordMap w)).subtype)
  have hinj : Function.Injective liftRow := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact toRow.injective hab
  let admissible (P : Row 4) := InBox (shape P) ⟨4012, 1650, 550⟩ ∧
    TrueWeightLE P (3000 * 180255 - 1) ∧ Contact w P
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

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13.c2 := by
  intro w
  obtain ⟨power, hpower⟩ := h3
  have hlocal := (origin_rank_le power h2).trans hpower
  have hglobal := word_rank_le w hlocal
  have hsource : 91415523069168962567 ≤ Module.finrank Geom SourceSpace := by
    rw [finrank_source]
    exact h1
  exact family_of_kernel w (surplus hglobal hsource (wordMap w).finrank_range_add_finrank_ker)

end

end K1_13_2
end PackSource_K1_13_2Split
