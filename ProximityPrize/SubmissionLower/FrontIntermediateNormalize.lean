import ProximityPrize.SubmissionLower.FrontRank582268
import ProximityPrize.SubmissionLower.AgreementLift

set_option Elab.async false
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

namespace FrontIntermediate
noncomputable section

open Polynomial Finset FrobeniusLocator ProximityPrize.Benchmark Front82268
open Front82268Direction (Regular excluded excluded_card_le cross_lift)
open private Front82268_5.same_scalar_label from ProximityPrize.SubmissionLower.FrontRank582268

/-- Forget only the agreement lower bound of a mark. -/
def weakenMark {A : ℕ} {u : Words} {γ : K} (ha : agreement ≤ A) (B : P1.BadMarkAt A u γ) :
    BadMark u γ :=
  { B with agreement := ha.trans B.agreement }

/-- Restore the original mark after the normalization has used the weaker rank parameters. -/
private def restoreMark {A : ℕ} {u : Words} {deleted : Finset I} {γ : K} {S : K[X]}
    {M : AnchorModel u deleted} {ha : agreement ≤ A} {B : P1.BadMarkAt A u γ}
    (m : AnchorMark M γ S) (hm : m.bad = weakenMark ha B) : P1.MarkAt (A := A) M γ S where
  bad := B
  avoids_deleted := by simpa only [hm, weakenMark] using m.avoids_deleted
  scalar_fixed := m.scalar_fixed
  scalar_degree := m.scalar_degree
  scalar_hits := by simpa only [hm, weakenMark] using m.scalar_hits
  pole_unit := m.pole_unit
  identity := by simpa only [hm, weakenMark, P1.ModelAt.decoder] using m.identity

def StrongFamily (A : ℕ) (u : Words) (Γ : Finset K) : Prop :=
  ∀ γ ∈ Γ, Nonempty (P1.BadMarkAt A u γ)

/-- The old cheap rank cases can use the stronger marks at the weaker radius. -/
theorem weak_bad_family {A : ℕ} {u : Words} {Γ : Finset K} (ha : agreement ≤ A)
    (hΓ : StrongFamily A u Γ) : BadFamily u Γ := by
  intro γ hγ
  obtain ⟨B⟩ := hΓ γ hγ
  apply AgreementLift.bad_of_mark (weakenMark ha B)
  rw [IRSProfile.card_index]
  change 262144 * (1 - ProtocolTarget82268.radius) ≤ 179876
  norm_num [ProtocolTarget82268.radius, ProtocolTarget82268.queryRadius, claimedRadius]

/-- The positive-strength version of the parallel, unit-norm rank case. -/
theorem coherent_anchors {A : ℕ} (ha : agreement ≤ A) (u : Words) (hu : FrontRemainder u)
    (T : TwoActive u) (R : Relation T) (D : Reduction u T R) (B : RankThree u T R D)
    (par : Parallel B) (unit : UnitNorm B) (Γ : Finset K) (bad : StrongFamily A u Γ)
    (normal : ∀ γ ∈ Γ, Normal u γ) :
    Γ.card ≤ anchorFee ∨
      ∃ book : Finset K, book ⊆ Γ ∧ book.card ≤ anchorFee ∧
        ∃ M : AnchorModel u (fixedNodes R), Nonempty (P1.FamilyAt A M (Γ \ book)) := by
  classical
  by_cases hsmall : Γ.card ≤ anchorFee
  · exact Or.inl hsmall
  right
  obtain ⟨F, height⟩ := Front82268_5.direction_of_rankThree hu B par unit
  let book := excluded F Γ
  have hbook : book ⊆ Γ := filter_subset _ _
  have hcard : book.card ≤ (p + 1) * F.s + F.U.natDegree + blockLength + 1 :=
    excluded_card_le F Γ
  have hbudget : book.card + 1 ≤ anchorFee := by
    have hprod := Nat.mul_le_mul_left p (show F.s ≤ heightCap by omega)
    rw [Nat.add_mul, one_mul] at hcard
    rw [← anchor_fee_exact]
    omega
  let Δ := Γ \ book
  have hbig : 1 < Δ.card := by
    have hpart := card_sdiff_add_card_eq_card hbook
    change Δ.card + book.card = Γ.card at hpart
    omega
  have regular (δ : K) (hd : δ ∈ Δ) : Regular F δ := by
    obtain ⟨hin, hout⟩ := mem_sdiff.mp hd
    by_contra h
    exact hout (mem_filter.mpr ⟨hin, h⟩)
  let original (g : Δ) := Classical.choice (bad g.val (mem_sdiff.mp g.property).1)
  let m (g : Δ) := weakenMark ha (original g)
  have avoid (g : Δ) : Disjoint (m g).support (fixedNodes R) := by
    apply disjoint_left.mpr
    intro i hi hid
    exact (D.deleted_error g.val (normal g.val (mem_sdiff.mp g.property).1) (m g) i hid)
      ((m g).hits i hi)
  obtain ⟨η, hη, ζ, hζ, hne⟩ := one_lt_card.mp hbig
  let a : Δ := ⟨η, hη⟩
  let b : Δ := ⟨ζ, hζ⟩
  obtain ⟨lift⟩ := cross_lift F
  obtain ⟨O⟩ := Front82268Direction.offset_of_anchor F lift (m a) (avoid a) (regular η hη)
  obtain ⟨M, S, marks, same⟩ := Front82268_5.normalize F height Δ regular m avoid a b hne.symm O
  let scalar (γ : K) : K[X] := if h : γ ∈ Δ then S ⟨γ, h⟩ else 0
  have weak (γ : K) (hγ : γ ∈ Δ) : AnchorMark M γ (scalar γ) := by
    simpa only [scalar, dite_eq_left hγ] using marks ⟨γ, hγ⟩
  refine ⟨book, hbook, by omega, M, ⟨⟨scalar, ?_, ?_⟩⟩⟩
  · intro γ hγ
    rw [show scalar γ = S ⟨γ, hγ⟩ from dite_eq_left hγ]
    exact restoreMark (marks ⟨γ, hγ⟩) (same ⟨γ, hγ⟩)
  · intro γ hγ δ hδ he
    exact Front82268_5.same_scalar_label (weak γ hγ) (he ▸ weak δ hδ)

theorem strong_family_of_bad_slopes {A : ℕ} {u : Words} {Γ : Finset K}
    (h : ∀ γ ∈ Γ, Principal.BadSlope node (u 0) (u 1) k A γ) : StrongFamily A u Γ := by
  intro γ hγ
  obtain ⟨S, hS, ⟨P, hP, he⟩, hn⟩ := h γ hγ
  exact ⟨⟨S, P, hS, hP, he, hn⟩⟩

#print axioms weak_bad_family
#print axioms coherent_anchors
end
end FrontIntermediate
