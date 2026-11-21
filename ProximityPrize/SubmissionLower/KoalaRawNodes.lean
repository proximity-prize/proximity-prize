import ProximityPrize.SubmissionLower.KoalaRawBounds
import ProximityPrize.SubmissionLower.KoalaBoxLift

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace SplitCut.Raw
noncomputable section
open P1 (K I node)
open K1_14 (FX seedEmbedding)
open K1_14_6 (Biform rootPoint)
open K1_14_6_1 (flatten separant markEval)
open HighCore82229Upper HighCore82229Upper_3 HighCore82229Upper_3_3
open MvPolynomial SplitCut.BoxDegree
open HighCore82229Upper_3_3_1
open scoped BigOperators
open private HighCore82229Upper_3_3_1.mark_biform HighCore82229Upper_3.seedBiform_image from ProximityPrize.SubmissionLower.HighCore82229UpperGeometry

abbrev ev (J : Input) (γ : K) : Biform →+* FX := markEval (J.model.label γ) (J.family.scalar γ)
abbrev sepF (J : Input) := separant (flatten J.f)
abbrev rawRes {J : Input} (B : ResidueLift J) (r : ℕ) (x : I) :=
  seedBiform (residueAtNode B x)*sepF J^(2*r-1)
abbrev rawJet {J : Input} (B : ResidueLift J) (r j : ℕ) :=
  sepF J^((2*r-1)-(2*j-1))*quotientNumerator J B j

def nodeCut {J : Input} (B : ResidueLift J) (s : Finset I) (x : I)
    (b : I → FX) (a : Fin (prefixLength J s) → FX) : Biform :=
  let r := J.ell-s.card
  let D := quotientDenominator J B r
  (rawRes B r x - wordAt J x • D) +
    (∑ i ∈ s, b i • (wordAt J i • D - rawRes B r i)) +
    ∑ j, a j • rawJet B r j.val

theorem node_fit {J : Input} (B : ResidueLift J) (s : Finset I) (x : I)
    (b : I → FX) (a : Fin (prefixLength J s) → FX) {v w : ℕ}
    (hf : flatten J.f ∈ space FX J.e v w) :
    let r := J.ell-s.card
    nodeCut B s x b a ∈ space FX (1+(2*r-1)*(J.e-1)) ((2*r-1)*v+2*J.w) ((2*r-1)*w+2*J.w) := by
  let r := J.ell-s.card
  let V := space FX (1+(2*r-1)*(J.e-1)) ((2*r-1)*v+2*J.w) ((2*r-1)*w+2*J.w)
  have hden : quotientDenominator J B r ∈ V :=
    grow (show (2*r-1)*(J.e-1) ≤ 1+(2*r-1)*(J.e-1) by omega) le_rfl le_rfl (den B hf r)
  have hres (i : I) : rawRes B r i ∈ V :=
    grow (show (2*r-1)*(J.e-1) ≤ 1+(2*r-1)*(J.e-1) by omega) le_rfl le_rfl (residue B hf r i)
  apply V.add_mem
  · apply V.add_mem
    · exact V.sub_mem (hres x) (V.smul_mem _ hden)
    · exact V.sum_mem (fun i _ => V.smul_mem _ (V.sub_mem (V.smul_mem _ hden) (hres i)))
  · apply V.sum_mem
    intro j _
    exact V.smul_mem _ (padded_num B hf (j := j.val) (r := r)
      (show j.val≤r by have := (sectionIndex J s j).isLt; exact Nat.lt_succ_iff.mp this))

private theorem eval_seed (J : Input) (γ : K) (t : SeedConstants) :
    ev J γ (seedBiform t) = markPoint J γ (seedInJet t) := by
  rw [← HighCore82229Upper_3_3_1.mark_biform, HighCore82229Upper_3.seedBiform_image]
  rfl

theorem den_ne {J : Input} (B : ResidueLift J) {γ : K} (hγ : γ ∈ J.marks) (r : ℕ) :
    ev J γ (quotientDenominator J B r) ≠ 0 := by
  have hδ : ev J γ (seedBiform B.denominator) ≠ 0 := by
    rw [eval_seed]
    have h := (HighCore82229Upper_3_3_1.proof J B γ hγ).1
    rw [openFactor,map_mul,mul_ne_zero_iff] at h
    exact h.1
  have hsep : ev J γ (sepF J) ≠ 0 := by
    rw [K1_14_6_1.eval_separant]
    exact (J.regular γ hγ).2.2
  unfold quotientDenominator
  rw [map_mul,map_pow]
  exact mul_ne_zero hδ (pow_ne_zero _ hsep)

private theorem normalize_rawres {J : Input} (B : ResidueLift J) {γ : K} (hγ : γ ∈ J.marks)
    (r : ℕ) (x : I) :
    ev J γ (rawRes B r x) / ev J γ (quotientDenominator J B r) =
      residueValue (markPoint J γ) B x := by
  have hδ := den_ne B hγ 0
  have hsep : ev J γ (sepF J) ≠ 0 := by
    rw [K1_14_6_1.eval_separant]
    exact (J.regular γ hγ).2.2
  simp only [quotientDenominator, Nat.mul_zero, Nat.zero_sub, pow_zero, mul_one] at hδ
  unfold rawRes quotientDenominator residueValue
  rw [map_mul,map_mul,map_pow,← eval_seed,show residueInJet B = seedInJet B.denominator from rfl,
    ← eval_seed]
  field_simp

private theorem normalize_rawjet {J : Input} (B : ResidueLift J) {γ : K} (hγ : γ ∈ J.marks)
    (s : Finset I) (j : Fin (prefixLength J s)) :
    let r := J.ell-s.card
    ev J γ (rawJet B r j.val) / ev J γ (quotientDenominator J B r) =
      canonicalJet (markPoint J γ) J B (prefixIndex J s j) := by
  let r := J.ell-s.card
  have hj : j.val ≤ r := Nat.lt_succ_iff.mp (sectionIndex J s j).isLt
  have hj' : 2*j.val-1 ≤ 2*r-1 := by omega
  change _ = (markPoint J γ (oldNumerator J B j.val)) / (markPoint J γ (oldDenominator J B j.val))
  rw [oldNumerator,oldDenominator,HighCore82229Upper_3_3_1.mark_biform,HighCore82229Upper_3_3_1.mark_biform]
  apply (div_eq_div_iff (den_ne B hγ r) (den_ne B hγ j.val)).2
  unfold rawJet quotientDenominator
  simp only [map_mul,map_pow]
  let u := ev J γ (sepF J)
  let A := 2*r-1
  let C := 2*j.val-1
  let z := ev J γ (quotientNumerator J B j.val)
  let v := ev J γ (seedBiform B.denominator)
  change (u^(A-C)*z)*(v*u^C) = z*(v*u^A)
  calc
    _ = (u^(A-C)*u^C)*(z*v) := by ring
    _ = _ := by rw [← pow_add,Nat.sub_add_cancel hj']; ring

theorem node_eval {J : Input} (B : ResidueLift J) (s : Finset I) (x : I)
    (b : I → FX) (a : Fin (prefixLength J s) → FX) (hw : FixedWeights J s x b a)
    {γ : K} (hγ : γ ∈ J.marks)
    (hs : ∀ i ∈ s, (J.family.scalar γ).eval (node i) = J.model.word i) :
    ev J γ (nodeCut B s x b a) = 0 ↔ (J.family.scalar γ).eval (node x) = J.model.word x := by
  let φ := markPoint J γ
  let r := J.ell-s.card
  have hspec := (HighCore82229Upper_3_3_1.proof J B γ hγ).2
  have hfixed : ∀ i ∈ s, reconstructedValue J (residueValue φ B) (canonicalJet φ J B) i =
      algebraMap FX FX (wordAt J i) := by
    intro i hi
    change curveValue φ J B i = _
    rw [hspec,hs i hi]
    rfl
  have W := hw FX (residueValue φ B) (canonicalJet φ J B) hfixed
  have hD := den_ne B hγ r
  have heval (z : FX) (q : Biform) : ev J γ (z • q) = z*ev J γ q := by
    change MvPolynomial.eval _ (z • q) = _
    simp [MvPolynomial.smul_eq_C_mul]
  have hc : ev J γ (nodeCut B s x b a) / ev J γ (quotientDenominator J B r) =
      seedEmbedding ((J.family.scalar γ).eval (node x)) - seedEmbedding (J.model.word x) := by
    rw [← hspec]
    change _ = reconstructedValue J (residueValue φ B) (canonicalJet φ J B) x -
      algebraMap FX FX (wordAt J x)
    rw [W]
    unfold nodeCut
    dsimp only [r,φ] at hD ⊢
    simp only [map_add,map_sub,map_sum,heval,add_div,sub_div,Finset.sum_div,mul_div_assoc,
      div_self hD,mul_one,normalize_rawres B hγ,normalize_rawjet B hγ s,Algebra.algebraMap_self,RingHom.id_apply]
  calc
    _ ↔ ev J γ (nodeCut B s x b a) / ev J γ (quotientDenominator J B r) = 0 := by
      rw [div_eq_zero_iff, or_iff_left hD]
    _ ↔ _ := by rw [hc, sub_eq_zero]; exact seedEmbedding.injective.eq_iff
end
end SplitCut.Raw
