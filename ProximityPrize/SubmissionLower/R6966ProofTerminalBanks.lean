import ProximityPrize.SubmissionLower.R6960HelperPrefix
import ProximityPrize.SubmissionLower.R6966ProofTerminalProjection

set_option Elab.async false

namespace Research6966.TerminalBanks
open Polynomial
open K1 (I K)
open K1_14 (Shape L Jet liftPoly jetAt)
open K1_14_1 (CRTLift PoleData MarkResidues nodeL evaluated evaluated_shape evaluated_mono)
open K1_14_3 (Surface Parent OrderAt RowCaps)
open scoped Polynomial
noncomputable section

/-- All full-cutoff banks inside one paid geometric shape. The multiplier
is allowed to vary because it does not enter the geometric cutter charge. -/
def inside (s E : Shape) : Prop :=
    0<s.m ∧ s.B≤E.B ∧ s.J≤E.J ∧ s.U≤E.U

def Pass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (A : ℕ) (E : Shape) (q : Surface) : Prop :=
    ∀ s : Shape, inside s E → ∀ F∈evaluated Crt word s (s.m*A-1), F∈q.asIdeal

/-- Failure supplies a single proper cutter of the original paid shape,
vanishing for every marked scalar with the given agreement. -/
theorem failed_cutter {h A : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (positive : 0<A) (regular : ∀ i j,(D.block i).eval (nodeL j) ≠ 0)
    {E : Shape} {q : Surface} (failed : ¬Pass Crt word A E q) :
    ∃ F : Jet, RowCaps F E ∧ F∉q.asIdeal ∧
      ∀ z S, MarkResidues D z S → (liftPoly S).natDegree≤131071+h →
        ∀ T : Finset I, A≤T.card → (∀ i∈T,(liftPoly S).eval (nodeL i)=word i) →
        jetAt F z S=0 := by
  classical
  unfold Pass at failed
  push Not at failed
  obtain ⟨s, ⟨sm,b,j,u⟩, F, mem, proper⟩ := failed
  refine ⟨F,?_,proper,?_⟩
  · intro v y c
    obtain ⟨b₀,j₀,u₀⟩:=evaluated_shape Crt word mem v y c
    exact ⟨b₀.trans b,j₀.trans j,u₀.trans u⟩
  · intro z S res deg T count agree
    exact P0_10_1.contact_vanish Crt word regular z S res deg T count agree s _
      (Nat.sub_lt (Nat.mul_pos sm positive) (by decide)) F mem

/-- A retained parent supplies the whole reserved order for every admissible
row. Both seed shifts may be taken before invoking the original parent theorem. -/
theorem retained_order {h A : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {E s : Shape} {q : Surface} (geo : Parent q) (pass : Pass Crt word A E q)
    (fits : inside s E) {W r : ℕ} (small : r+1<K1.p) (cut : W+2*h*r<s.m*A)
    {F : Jet} (mem : F∈evaluated Crt word s W) : OrderAt q F (r+1) := by
  apply K1_14_3R_1.proof q F (r+1) geo small
  intro i j ij
  have limit := Nat.mul_le_mul_left (2*h) (show i+j≤r by omega)
  rw [Nat.mul_add] at limit
  have f := P0_10_1.evaluated_shift Crt word mem 0 i
  have g := P0_10_1.evaluated_shift Crt word f 1 j
  apply pass s fits
  exact evaluated_mono Crt word rfl rfl rfl le_rfl (by omega) g

/-- One native buffered row controls the joint ordinate product of all its
on-graph sheets. The order uses the actual source pass and actual fibre ideal. -/
theorem product_of_retained {h A : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {E s : Shape} {W r : ℕ} (fits : inside s E) (small : r+1<K1.p)
    (cut : W+2*h*r<s.m*A) {F : Jet} (mem : F∈evaluated Crt word s W)
    (ys : Finset K1_14_3.SeedClosure) (v : K1_14_3.SeedClosure → K1_14_3.SeedClosure)
    (G₁ G₀ : K1_14_3.SeedClosure[X])
    (sheets : ∀ y∈ys, ∃ q : Surface, Parent q ∧ Pass Crt word A E q ∧
      K1_14_3.OnSeedFibre q y (v y) ∧ G₁.eval y≠0 ∧ G₁.eval y*v y=G₀.eval y)
    (J : ℕ) (bound : (K1_14_3.fibreRow F).natDegree ≤ J) :
    (∏ y∈ys,(Polynomial.X (R:=K1_14_3.SeedClosure)-Polynomial.C y))^(r+1) ∣
      TerminalProjection.cleared G₁ G₀ (K1_14_3.fibreRow F) J := by
  apply TerminalProjection.all_sheets G₁ G₀ _ ys v _ _ bound
  intro y hy
  obtain ⟨q,geo,pass,fiber,reg,onG⟩:=sheets y hy
  exact ⟨reg,onG,retained_order Crt word geo pass fits small cut mem y (v y) fiber⟩

#print axioms failed_cutter
#print axioms retained_order
#print axioms product_of_retained
end
end Research6966.TerminalBanks
