import ProximityPrize.SubmissionLower.GoldBranch6N7
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
abbrev physicalDegree : ℕ := k - 1 + P1.lowCutoff.toNat
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev incidenceGap : ℕ := agreement - physicalDegree
abbrev layerWidth : ℕ := incidenceGap + 3
abbrev anchorBox : Shape := ⟨121, 49, 14⟩
abbrev anchorCutoff : ℕ := 90 * agreement - 1
abbrev parameterCap : ℕ := 60000
abbrev lowCap : ℕ := 259967560664163328 + 1010930246923036
structure Messages (w : I → K) (Γ : Finset K) (s : K → K[X]) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, agreement ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i
  word_fixed : ∀ i, P1.twist (w i) = w i
  scalar_fixed : ∀ γ ∈ Γ, (s γ).map P1.twist = s γ
def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val) * a) ≤ D
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0 < (shape f).t ∧ InBox (shape f) anchorBox ∧ TrueWeightLE f anchorCutoff
def LowerRow (topSpend : ℕ) (g : Row 3) : Prop :=
  g ≠ 0 ∧ g.totalDegree + topSpend ≤ anchorBox.b ∧
    indexDegree g + 3 * topSpend ≤ anchorBox.j ∧ TrueWeightLE g anchorCutoff
def spend {ι : Type*} (a : ι → Shape) (T : Finset ι) : Shape :=
  ⟨∑ i ∈ T, (a i).b, ∑ i ∈ T, (a i).j, ∑ i ∈ T, (a i).t⟩
abbrev Valid := K1_13_8.Valid
abbrev zeroShape := K1_13_8.zeroShape
structure Cover {n : ℕ} (Γ : Finset K) (s : K → K[X])
    (g : Row 3) (f : Fin n → Row 4) : Prop where
  lower : LowerRow (spend (fun i => shape (f i)) Finset.univ).t g
  factors : ∀ i, SmallFactor (f i)
  different : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)
  valid : ∀ i, Valid (shape (f i))
  fits : InBox (spend (fun i => shape (f i)) Finset.univ) anchorBox
  covers : ∀ γ ∈ Γ, atJet g (extend (s γ)) = 0 ∨ ∃ i, OnFactor (f i) (extend (s γ))
inductive Bank where
  | primary
  | secondary
  deriving DecidableEq
def Bank.m : Bank → ℕ
  | .primary => 2320
  | .secondary => 3600
def Bank.box : Bank → Shape
  | .primary => ⟨3096, 1295, 378⟩
  | .secondary => ⟨4788, 2052, 595⟩
def Bank.surplus : Bank → ℕ
  | .primary => 302231627979257906
  | .secondary => 2940647283380376514
def Bank.cutoff (b : Bank) : ℕ := b.m * agreement - 1
def Contact (b : Bank) (w : I → K) (P : Row 4) : Prop :=
  ∀ i (S : Geom[X]), S.eval (embed (node i)) = embed (w i) →
    (Polynomial.X - C (embed (node i))) ^ b.m ∣ atJet P S
def BankRank (b : Bank) (w : I → K) : Prop :=
  ∃ e : Fin b.surplus → Row 4, LinearIndependent Geom e ∧
    ∀ i, InBox (shape (e i)) b.box ∧ TrueWeightLE (e i) b.cutoff ∧ Contact b w (e i)
def ProperCut (b : Bank) (f : Row 4) (Γ : Finset K) (s : K → K[X]) (l : ℕ) : Prop :=
  ∃ Q : Row 4, (¬ f ∣ Q) ∧ InBox (shape Q) b.box ∧ TrueWeightLE Q b.cutoff ∧
    ∀ γ ∈ Γ, OrderAt Q (extend (s γ)) l
def symbols (c : Shape) : ℕ :=
  ∑ z ∈ Finset.range (min c.t (min c.b (c.j / 3)) + 1),
    ∑ y ∈ Finset.range (min (c.b - z) ((c.j - 3*z) / 2) + 1),
      ∑ x ∈ Finset.range (min (c.b - z - y) (c.j - 3*z - 2*y) + 1),
        (c.b - z - y - x + 1)
def remaining (box used : Shape) : ℕ :=
  if used.b ≤ box.b ∧ used.j ≤ box.j ∧ used.t ≤ box.t then
    symbols ⟨box.b - used.b, box.j - used.j, box.t - used.t⟩
  else 0
def orderBound (b : Bank) (used : Shape) : ℕ :=
  let tail := ∑ r ∈ Finset.range b.box.t, remaining b.box (used.scale (r + 1))
  ceilDiv (b.surplus - layerWidth * tail) (layerWidth * symbols b.box)
structure FatEquations where
  common : Row 3
  residual : Row 3
  common_ne : common ≠ 0
  residual_ne : residual ≠ 0
  common_total : common.totalDegree ≤ 3284
  common_index : indexDegree common ≤ 1120
  residual_total : residual.totalDegree ≤ 409200000
  residual_index : indexDegree residual ≤ 129000000
def FatEquations.holds (E : FatEquations) (S : Geom[X]) : Prop :=
  atJet E.common S = 0 ∨ OrderAt E.residual S 40517
def signedMixed32 (p q r s : Shape) : ℤ :=
  let Δ := K1_13.difference
  Δ (Δ (Δ (Δ K1_13.volume32 p) q) r) s zeroShape
def surfaceNumerator32 (p q : Shape) : ℕ :=
  let M := taylorLength
  let u := M + 1
  let v := M + 2
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart u p
  let b := liftedChart v p
  let ordinary := mixed32 p q (chart u p) (chart v p)
  let base := mixed32 p q a b + u * mixed32 p q g b + v * mixed32 p q g a
  if 3 * (p.t + 1) ≤ p.j + 1 ∧ 2 ≤ p.t + 1 ∧
      3 * (2 + (u - 5) * p.t) ≤ a.j ∧ 3 * (2 + (v - 5) * p.t) ≤ b.j ∧
      2 * u ≤ a.t ∧ 2 * v ≤ b.t then
    let s : Shape := ⟨1, 4, 2⟩
    let removed : ℤ := (u : ℤ) * signedMixed32 p q s b + (v : ℤ) * signedMixed32 p q s a +
      (u : ℤ) * (v : ℤ) * (signedMixed32 p q s g - signedMixed32 p q s s)
    min ordinary (min base ((base : ℤ) - removed).toNat)
  else min ordinary base
def physicalPrice (b : Bank) (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := b.box
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32 p q) 32 +
    ceilDiv ((P1.t + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (P1.t * curves + 2 * incidenceGap * points) (32 * incidenceGap)
def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩
def fatPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := if x.t = 1 then linearChart p else chart (taylorLength + 4) p
  let q : Shape := ⟨409200000, 129000000, 0⟩
  let big : Shape := ⟨3284 + q.b / 32413, 1120 + q.j / 32413, 0⟩
  let cut : Shape := ⟨max (max h.b big.b) (max h.j (big.j + 1)),
    max h.j (big.j + 1), max 1 h.t⟩
  let divisors := ceilDiv (P1.t * mixed32 p big cut h) (32 * incidenceGap) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b^2 + 5 * physicalDegree * p.b * h.b + 1
  let singular := if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b^2 + 1 else 0
  let length := (40517 - 1012 + 1) * (40517 - 32413 + 2 - 1012)
  let curves := ceilDiv (P1.t * mixed32 p q q h + incidenceGap * mixed32 p q q p)
    (32 * incidenceGap * length)
  let isolated := ceilDiv (3 * q.j^2 * (2 * q.b - q.j)) (4 * 40517 * (40517 - 32413 + 1) * 1012)
  divisors + singular + curves + isolated
def lowerBox (topSpend : ℕ) : Shape :=
  let j := anchorBox.j - 3 * topSpend
  ⟨max (anchorBox.b - topSpend) (j + 3), j, j / 2⟩
def lowerLift (L : ℕ) (p : Shape) : Shape :=
  let j := 2 + (L - 4) * (p.j + 2)
  ⟨1 + (L - 4) * p.b, j, min (1 + (L - 4) * (p.t + 2)) (j / 2)⟩
def lowerPrice (topSpend : ℕ) : ℕ :=
  let p := lowerBox topSpend
  let M := taylorLength
  let g : Shape := ⟨p.b, p.j + 1, min (p.t + 1) ((p.j + 1) / 2)⟩
  let x := lowerLift (M + 1) p
  let y := lowerLift (M + 2) p
  let mixed := K1_13_5.mixed3 p x y + (M - 1) * K1_13_5.mixed3 p g y +
    M * K1_13_5.mixed3 p g x
  let H := max p.b ((2 * p.t - 1) * p.b - p.t^2)
  let J := max p.j ((2 * p.t - 1) * p.j - 2 * p.t^2)
  let exponent := 2 * M - 5
  let a := 1 + exponent * (H - 1)
  let d := min a (exponent * (J - 1) + M - 1)
  let r := H * d + J * (a - d)
  let initial := 1 + exponent * (p.b - 1)
  let extra := (P1.t + 2 * incidenceGap) * p.b * initial + P1.t * (physicalDegree * p.b + r)
  mixed + ceilDiv extra incidenceGap + p.b + H^2
def Charges (prior edge : Shape) (cost : ℕ) : Prop :=
  (0 < orderBound .primary (prior.plus edge) →
    cost ≤ physicalPrice .primary edge (orderBound .primary (prior.plus edge))) ∧
  (0 < orderBound .secondary edge →
    cost ≤ physicalPrice .secondary edge (orderBound .secondary edge)) ∧
  (K1_13.FatEligible edge → cost ≤ fatPrice edge)
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
theorem degree_at_height {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (γ : K) (hγ : γ ∈ Γ) : (F.scalar γ).natDegree ≤ k - 1 + M.overhead.toNat := by
  rcases (F.mark γ hγ).scalar_degree with h | h
  · simp [h]
  · change (F.scalar γ).natDegree ≤ k - 1 + (P1.ModelAt.overhead M).toNat
    omega
theorem messages_of_anchor {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (hw : M.overhead ≤ P1.lowCutoff) : Messages M.word Γ F.scalar := by
  refine ⟨F.distinct, ?_, ?_, M.word_fixed, fun γ hγ => (F.mark γ hγ).scalar_fixed⟩
  · intro γ hγ
    have overhead_le : M.overhead.toNat ≤ P1.lowCutoff.toNat := Int.toNat_le_toNat hw
    exact (degree_at_height M F γ hγ).trans (Nat.add_le_add_left overhead_le _)
  · intro γ hγ
    let m := F.mark γ hγ
    exact ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩
theorem pole_of_anchor {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ P1.lowCutoff) :
    ∃ P : PoleData Γ F.scalar, P.H.natDegree ≤ P1.lowCutoff.toNat := by
  have hmax : M.overhead.toNat ≤ (extend M.E).natDegree := by
    rw [Polynomial.natDegree_map]
    change M.overhead.toNat ≤ M.E.natDegree
    unfold P1.AnchorModel.overhead P1.ModelAt.overhead
    omega
  obtain ⟨H, hm, hd, hdiv⟩ := K1_13.trim_divisor _ (M.E_monic.map embed) _ hmax
  let z := fun γ => embed (M.label γ)
  have unit {P : K[X]} (hp : IsCoprime P M.E) : IsCoprime (extend P) H :=
    (hp.map (Polynomial.mapRingHom embed)).of_isCoprime_of_dvd_right hdiv
  have amp (γ : K) : extend (M.amplitude γ) = extend M.A₀ + C (z γ) * extend M.A₁ := by
    simp [P1.AnchorModel.amplitude, P1.ModelAt.amplitude, z]
  have hsmall : H.natDegree ≤ P1.lowCutoff.toNat := hd.le.trans (Int.toNat_le_toNat hi)
  refine ⟨⟨H, hm, ?_, ?_, ?_, z, ?_, extend M.factor, extend M.Q, extend M.A₀,
    extend M.A₁, unit M.coprime_factor.symm, unit M.offset_reduced,
    unit M.first_amplitude_unit, ?_, ?_⟩, hsmall⟩
  · rw [hd]
    exact ⟨by omega, (Int.toNat_le_toNat hi).trans (by decide)⟩
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
  ⟨h.distinct.mono hΔ, fun γ hγ => h.degree γ (hΔ hγ), fun γ hγ => h.hits γ (hΔ hγ),
    h.word_fixed, fun γ hγ => h.scalar_fixed γ (hΔ hγ)⟩
theorem ProperCut.mono {b f Γ s l Δ} (h : ProperCut b f Γ s l) (hΔ : Δ ⊆ Γ) :
    ProperCut b f Δ s l := by
  obtain ⟨Q, hf, hbox, hw, hQ⟩ := h
  exact ⟨Q, hf, hbox, hw, fun γ hγ => hQ γ (hΔ hγ)⟩
end
end P1_6
end
