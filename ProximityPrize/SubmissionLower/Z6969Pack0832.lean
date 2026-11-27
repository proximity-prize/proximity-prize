import ProximityPrize.SubmissionLower.Wide50EulerPrimaryFamily
import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.Low6966Order
import ProximityPrize.SubmissionLower.Low6966Retained
import ProximityPrize.SubmissionLower.R6960Anchor6966Local
import ProximityPrize.SubmissionLower.Low50Euler2367JetDegree
import ProximityPrize.SubmissionLower.R6960Low6960SurfaceLinearFour
import ProximityPrize.SubmissionLower.GoldBranch6N8
import ProximityPrize.SubmissionLower.Final50Price
import ProximityPrize.SubmissionLower.KoalaRetainedCut
import ProximityPrize.SubmissionLower.UpperBranch5
import ProximityPrize.SubmissionLower.RingHomShortcuts

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969Primary
section Z6969Source2261
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000

namespace Research6969.Low6969Primary

open Polynomial
open P3 (I K node)
open K1_13 (Geom Row shape InBox Contact)
open Wide50EulerPrimary (primary_family sourceRank layerNeed)

abbrev agreement : ℕ := 179740
abbrev degree : ℕ := 133363
abbrev cutoff : ℕ := 3000 * agreement - 1
abbrev rank : ℕ := sourceRank agreement degree
abbrev need : ℕ := layerNeed agreement degree

structure Messages (w : I → K) (Γ : Finset K) (s : K → Polynomial K) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ Low6969Primary.degree
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, agreement ≤ T.card ∧
    ∀ i ∈ T, (s γ).eval (node i) = w i

theorem messages_of_family {cap u deleted Γ} (M : P1.ModelAt cap u deleted)
    (F : P1.FamilyAt agreement M Γ) (hi : M.overhead ≤ 2292) :
    Messages M.word Γ F.scalar := by
  refine ⟨F.distinct, ?_, ?_⟩
  · intro γ hγ
    obtain hzero | h := (F.mark γ hγ).scalar_degree
    · simp [hzero]
    · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at h
      change (F.scalar γ).natDegree ≤ 133363
      omega
  · intro γ hγ
    let mark := F.mark γ hγ
    exact ⟨mark.bad.support, mark.bad.agreement, mark.scalar_hits⟩



/-- The actual production primary row bank at the low-height cutoff. -/
theorem primary_at_endpoint (w : I → K) :
    ∃ e : Fin rank → Row 4, LinearIndependent Geom e ∧
      ∀ i, InBox (shape (e i)) PrimaryTaper.primaryBox ∧
        PrimaryTaper.TrueWeightLE degree (e i) cutoff ∧
        PrimaryTaper.JetsBounded (e i) ∧ Contact w (e i) :=
  primary_family agreement degree (by decide) (by decide) (by decide +kernel) w le_rfl


end Research6969.Low6969Primary
end Z6969Source2261

-- Source: ProximityPrize.SubmissionLower.Low6969Order
section Z6969Source2262
set_option autoImplicit true
set_option Elab.async false

section Merged_Low6969Order

-- merged module R6960Low6966Profile
section Merged_R6960Low6966Profile

set_option Elab.async false

namespace LowProfile6969
open P3 (I K node)
open K1_13 (Row Shape InBox shape OrderAt extend)
open scoped Polynomial BigOperators

abbrev agreement := Research6969.Low6969Primary.agreement
abbrev physicalDegree := Research6969.Low6969Primary.degree
abbrev primaryCutoff := Research6969.Low6969Primary.cutoff
abbrev need := Research6969.Low6969Primary.need
abbrev layerWidth : ℕ := agreement-physicalDegree+3
abbrev layerCount : ℕ := 1+primaryCutoff/layerWidth
abbrev TrueWeightLE {n : ℕ} (P : Row n) (T : ℕ) := PrimaryTaper.TrueWeightLE physicalDegree P T

abbrev Messages := Research6969.Low6969Primary.Messages

def ProperCut (f : Row 4) (Γ : Finset K) (s : K→(Polynomial K)) (l : ℕ) : Prop :=
  ∃ Q : Row 4, (¬f∣Q) ∧ InBox (shape Q) PrimaryTaper.primaryBox ∧ TrueWeightLE Q primaryCutoff ∧
    Final50Price.ActiveFits Q 5164 ∧ ∀ γ∈Γ,OrderAt Q (extend (s γ)) l

def LayerBudget {n : ℕ} (a : Fin n→Shape) (l : Fin n→ℕ) : Prop :=
  need ≤ ∑ r∈Finset.range layerCount,
    Final50Price.remaining (∑ i,(r+1-l i)*(a i).b) (∑ i,(r+1-l i)*(a i).j)
end LowProfile6969

end Merged_R6960Low6966Profile

-- merged module R6960Low6969Order
section Merged_R6960Low6969Order
set_option Elab.async false
namespace Low6969Order
noncomputable section
open K1_13 (Geom Row shape InBox Contact)
open P3 (I K)
abbrev TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) := LowProfile6969.TrueWeightLE P D
abbrev physicalDegree := LowProfile6969.physicalDegree
abbrev agreement := LowProfile6969.agreement
abbrev primaryBox := PrimaryTaper.primaryBox
abbrev primaryCutoff := LowProfile6969.primaryCutoff
abbrev sourceRank := Wide50EulerPrimary.sourceRank agreement physicalDegree
abbrev layerWidth := LowProfile6969.layerWidth
abbrev layerNeed := LowProfile6969.need
abbrev Messages := LowProfile6969.Messages


theorem certified_layers : sourceRank / layerWidth + 1 = 20089989785677 := by decide
def PrimaryRank (w : I → K) : Prop :=
  ∃ e : Fin sourceRank → Row 4, LinearIndependent Geom e ∧
    ∀ i, InBox (shape (e i)) primaryBox ∧ TrueWeightLE (e i) primaryCutoff ∧
      PrimaryTaper.JetsBounded (e i) ∧ Contact w (e i)
end
end Low6969Order
section
namespace Low6969OrderProof
noncomputable section
open P3 (I K)
open Low6969Order (TrueWeightLE primaryBox primaryCutoff layerWidth)
open K1_13 (Row InBox shape Contact)
def requiredOrder (T : ℕ) : ℕ :=
  (primaryCutoff - T) / layerWidth + 1
def BankRow (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) primaryBox ∧ TrueWeightLE P T ∧
    PrimaryTaper.JetsBounded P ∧ Contact w P
end
end Low6969OrderProof
end
section
namespace Low6969OrderProof
noncomputable section
open Polynomial
open P3 (I K node)
open Low6969Order (agreement)
open Low6969Order (Messages TrueWeightLE physicalDegree primaryBox PrimaryRank primaryCutoff layerWidth layerNeed sourceRank)

open K1_13 (Geom embed extend Row shape InBox OrderAt indexDegree)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open scoped BigOperators
open P0_9_3 (exists_fresh specialization_bounds sum_by_layer)














def c3 : Prop :=
  ∀ (w : I → K) (x : Geom), PrimaryRank w →
    (∀ i : I, x ≠ embed (node i)) →
    ∃ r : ℕ → ℕ, sourceRank ≤ ∑ T ∈ Finset.range (primaryCutoff + 1), r T ∧
      ∀ T ≤ primaryCutoff, ∃ e : Fin (r T) → Row 4,
        (∀ i, BankRow w T (e i)) ∧
        LinearIndependent Geom (fun i => symbolAt x (e i))




































































































end
end Low6969OrderProof
end
section
set_option maxRecDepth 12000
namespace Low6969OrderProof_1
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P3 (I K node)
open Low6969Order (agreement)
open Low6969Order (TrueWeightLE physicalDegree primaryCutoff layerWidth)
open Low6969OrderProof (BankRow requiredOrder)
open K1_13 (Geom embed Row jet Contact)
open K1_13_3_1 (line)
open scoped BigOperators
open K1_13_3_1 (eval_line line_contacts_zero)
open K1_13_3_1 (order_of_locator_lines)
private def Bounded (Q : Polynomial (Polynomial Geom)) (b : ℕ) : Prop :=
  ∀ j, (Q.coeff j).natDegree ≤ b + layerWidth * j
private theorem bounded_mul {F G : Polynomial (Polynomial Geom)} {a b : ℕ}
    (hF : Bounded F a) (hG : Bounded G b) : Bounded (F * G) (a + b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum, Nat.mul_add]
  omega
private theorem bounded_C (f : (Polynomial Geom)) {a : ℕ} (hf : f.natDegree ≤ a) :
    Bounded (Polynomial.C f) a := by
  intro j
  by_cases h : j = 0
  · simpa [h] using hf
  · simp [Polynomial.coeff_C, h]
private theorem bounded_prod {ι : Type*} (A : Finset ι)
    (f : ι → Polynomial (Polynomial Geom)) (b : ι → ℕ) (hf : ∀ i ∈ A, Bounded (f i) (b i)) :
    Bounded (∏ i ∈ A, f i) (∑ i ∈ A, b i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using bounded_C (1 : (Polynomial Geom)) (a := 0) (by simp)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact bounded_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
private theorem bounded_pow {f : Polynomial (Polynomial Geom)} {b : ℕ} (hf : Bounded f b) (n : ℕ) :
    Bounded (f ^ n) (b * n) := by
  induction n with
  | zero => simpa using bounded_C (1 : (Polynomial Geom)) (a := 0) (by simp)
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact bounded_mul ih hf
private theorem line_degree (P : Row 4) (S U : (Polynomial Geom)) (T : ℕ)
    (hP : TrueWeightLE P T) (hS : S.natDegree ≤ physicalDegree)
    (hU : U.natDegree ≤ agreement + 3) (j : ℕ) :
    ((line P S U).coeff j).natDegree ≤ T + layerWidth * j := by
  let b (i : Fin 4) : ℕ := physicalDegree - i.val
  let F (i : Fin 4) : Polynomial (Polynomial Geom) :=
    Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 4) : Bounded (F i) (b i) := by
    intro k
    have hs : (jet S i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le S i.val).trans (Nat.sub_le_sub_right hS _)
    have hu : (jet U i).natDegree ≤ b i + layerWidth := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi : i.val ≤ physicalDegree := (Nat.le_of_lt_succ i.isLt).trans (by decide)
      have hwidth : agreement + 3 = layerWidth + physicalDegree := by decide
      change agreement + 3 - i.val ≤ (physicalDegree - i.val) + layerWidth
      rw [hwidth, Nat.add_sub_assoc hi, Nat.add_comm layerWidth]
    change ((Polynomial.C (jet S i) + Polynomial.C (jet U i) *
      Polynomial.X).coeff k).natDegree ≤ b i + layerWidth * k
    rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
    by_cases h0 : k = 0
    · simpa [h0] using hs
    · by_cases h1 : k = 1
      · simpa [h1] using hu
      · simp [h0, h1]
  unfold line
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  have hterm := bounded_mul (bounded_C (P.coeff m) le_rfl)
    (bounded_prod m.support (fun i => F i ^ m i) (fun i => b i * m i)
      (fun i _ => bounded_pow (hF i) (m i))) j
  exact hterm.trans (Nat.add_le_add_right (hP m hm) _)
private theorem line_coeff_zero (w : I → K) (T : ℕ) (P : Row 4) (S : (Polynomial Geom))
    (hw : TrueWeightLE P T) (hc : Contact w P) (hS : S.natDegree ≤ physicalDegree)
    (A : Finset I) (hA : A.card = agreement)
    (hhit : ∀ i ∈ A, S.eval (embed (node i)) = embed (w i))
    (V : (Polynomial Geom)) (hV : V.natDegree ≤ 3) (j : ℕ)
    (hj : T + layerWidth * j ≤ primaryCutoff) :
    (line P S (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ agreement + 3 := by
    exact natDegree_mul_le.trans (by rw [locator_natDegree, hA]; exact Nat.add_le_add_left hV _)
  let Q := line P S U
  have hcontact (i : I) (hi : i ∈ A) (c : Geom) :
      (Polynomial.X - C (x i)) ^ 3000 ∣ Q.eval (C c) := by
    rw [show Q = line P S U from rfl, eval_line]
    apply hc
    have hL : L.eval (x i) = 0 := locator_eval_zero x A i hi
    have hU0 : U.eval (x i) = 0 := by simp [U, hL]
    simpa [x, eval_smul, hU0] using hhit i hi
  have hx : Function.Injective x :=
    (RingHom.injective embed).comp IRSProfile.domain.injective
  have hb := (line_degree P S U T hw hS hU j).trans hj
  have hdegree : (Q.coeff j).natDegree < 3000 * A.card := by
    rw [hA]
    exact hb.trans_lt (Nat.sub_lt (Nat.mul_pos (by decide) (by decide)) (by decide))
  exact line_contacts_zero Q A x hx 3000 hcontact j hdegree
theorem order_of_contact (w : I → K) (P : Row 4) {T : ℕ} (hT : T ≤ primaryCutoff)
    (hw : TrueWeightLE P T) (hc : Contact w P) {S : (Polynomial Geom)} (hS : S.natDegree ≤ physicalDegree)
    {H : Finset I} (hH : agreement ≤ H.card)
    (hits : ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) :
    K1_13.OrderAt P S (requiredOrder T) := by
  obtain ⟨A, hAH, hA⟩ := Finset.exists_subset_card_eq hH
  let x (i : I) := embed (node i)
  apply order_of_locator_lines P S (locator x A) (locator_monic x A).ne_zero
  intro V hV j hj
  apply line_coeff_zero w T P S hw hc hS A hA (fun i hi => hits i (hAH hi)) V hV j
  have hj' : j ≤ (primaryCutoff - T) / layerWidth := Nat.lt_succ_iff.mp hj
  have hq := Nat.div_mul_le_self (primaryCutoff - T) layerWidth
  rw [Nat.mul_comm _ layerWidth] at hq
  calc
    T + layerWidth * j ≤ T + layerWidth * ((primaryCutoff - T) / layerWidth) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left layerWidth hj') T
    _ ≤ T + (primaryCutoff - T) := Nat.add_le_add_left hq T
    _ = primaryCutoff := Nat.add_sub_of_le hT




end
end Low6969OrderProof_1
end
section
namespace Low6969OrderProof_2
noncomputable section
open Polynomial
open Low6969Order (TrueWeightLE physicalDegree primaryBox primaryCutoff)
open K1_13 (Geom embed extend Row Shape shape InBox indexDegree)
open P0_9_3_2 (translateTop topHasse topHasse_coeff source_support sum_add_top total_add_top apply_add_top erase_top_add topHasse_order topHasse_zero exact_hasse_not_dvd)























































































end
end Low6969OrderProof_2
end
section
namespace Low6969OrderProof_3
noncomputable section
open Polynomial
open P3 (I K node)
open Low6969Order (TrueWeightLE physicalDegree primaryCutoff)
open Low6969OrderProof (BankRow)
open K1_13 (Geom embed Row InBox shape indexDegree Contact atJet)
open K1_13_3 (Symbol symbolAt)
open P0_9_3 (jetEval jetEval_apply dvd_smul_poly coefficientArray symbolLinear linearFactor linearFactor_ne linearFactor_degree divide_specialization support_linear_mul)
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
        (P.coeff m).natDegree + jetWeight m ≤ T ∧ m ∈ TaperColumns.jetExponents) ∧ Contact w P := by
  simp only [BankRow, InBox, shape, indexDegree, MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_le_iff, Finset.sup_le_iff, TrueWeightLE, PrimaryTaper.JetsBounded]
  constructor
  · rintro ⟨⟨hb, hj, ht⟩, hT, hs, hc⟩
    exact ⟨fun m hm => ⟨hb m hm, hj m hm, ht m hm, hT m hm, hs m hm⟩, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2.1, fun m hm => (h m hm).2.2.1⟩,
      fun m hm => (h m hm).2.2.2.1, fun m hm => (h m hm).2.2.2.2, hc⟩
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
            m 3 ≤ 550 ∧ jetWeight m ≤ T ∧ m ∈ TaperColumns.jetExponents := by
        rcases hor with h | h
        · obtain ⟨hb, hj, ht, hw, hjets⟩ := hP m h
          exact ⟨hb, hj, ht, by omega, hjets⟩
        · obtain ⟨hb, hj, ht, hw, hjets⟩ := hQ m h
          exact ⟨hb, hj, ht, by omega, hjets⟩
      obtain ⟨hb, hj, ht, hw, hjets⟩ := bounds
      refine ⟨hb, hj, ht, ?_, hjets⟩
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
      have hp' := hdegree P (fun h => (hP m h).2.2.2.1)
      have hq' := hdegree Q (fun h => (hQ m h).2.2.2.1)
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
      obtain ⟨hb, hj, ht, hw, hjets⟩ := hP m (MvPolynomial.support_smul hm)
      refine ⟨hb, hj, ht, ?_, hjets⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h : jetEval S (c • P) = c • jetEval S P := (jetEval S).map_smul c P
      rw [jetEval_apply, jetEval_apply] at h
      rw [h]
      exact dvd_smul_poly _ _ c (hp i S hS)
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
private def bankEval (w : I → K) (x : Geom) (T : ℕ) : bank w T →ₗ[Geom] Symbol :=
  (symbolLinear x).comp (bank w T).subtype
private theorem mul_cutoff_iff (w : I → K) (x : Geom) (hx : ∀ i : I, x ≠ embed (node i))
    (T : ℕ) (P : Row 4) :
    BankRow w (T + 1) (MvPolynomial.C (linearFactor x) * P) ↔ BankRow w T P := by
  rw [bankRow_iff, bankRow_iff, support_linear_mul]
  apply and_congr
  · refine forall_congr' fun m => forall_congr' fun hm => ?_
    rw [MvPolynomial.coeff_C_mul, natDegree_mul (linearFactor_ne x)
      (MvPolynomial.mem_support_iff.mp hm), linearFactor_degree]
    constructor <;> rintro ⟨hb, hj, ht, hw, hJets⟩ <;>
      exact ⟨hb, hj, ht, by omega, hJets⟩
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
        simp only [bankEval, LinearMap.comp_apply, Submodule.subtype_apply,
          LinearMap.codRestrict_apply, LinearMap.mulLeft_apply]
        change symbolAt x (MvPolynomial.C (linearFactor x) * P.val) = 0
        have h0 : symbolAt x (MvPolynomial.C (linearFactor x)) = 0 := by
          simp only [symbolAt, linearFactor, MvPolynomial.map_C, Polynomial.coe_evalRingHom,
            Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, map_zero]
        rw [RingHom.map_mul, h0, zero_mul])
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
theorem proof : Low6969OrderProof.c3 := by
  classical
  intro w x hr hx
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
end Low6969OrderProof_3
end
namespace Low6969Order
noncomputable section
open K1_13 (Row shape)
open P3 (K)
open scoped Polynomial
export Low6969OrderProof (BankRow requiredOrder)
export Low6969OrderProof_1 (order_of_contact)
theorem messages_of_family {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt agreement M Γ) (hh : M.overhead ≤ 2292) :
    Messages M.word Γ F.scalar :=
  Research6969.Low6969Primary.messages_of_family M F hh










theorem primary_rank (w : P3.I → K) : PrimaryRank w :=
  Research6969.Low6969Primary.primary_at_endpoint w
theorem symbol_families : Low6969OrderProof.c3 := Low6969OrderProof_3.proof








end
end Low6969Order

end Merged_R6960Low6969Order

end Merged_Low6969Order

end Z6969Source2262

-- Source: ProximityPrize.SubmissionLower.Low6969Retained
section Z6969Source2263
set_option autoImplicit true
set_option Elab.async false

-- merged module R6960Low6969Retained
section Merged_R6960Low6969Retained

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace Low6969Retained
open K1_13 (Shape InBox)
open K1_13_8 (Valid zeroShape zeroMass)
open P0_9_8 (symbol_count)
open LowProfile6969 (layerCount)
local notation "layerNeed" => LowProfile6969.need
open Final50PriceLayer (layerTerm)
open scoped BigOperators
open P3_6_8 (shapeSum shapeSum_empty shapeSum_valid_or_empty spend_le)
open P3_6_8_1 (sumBelow term mass_eq extend)


def Box (a : Shape) : Prop :=
  a.b ≤ 27 ∧ a.j ≤ 8 ∧ (4 ≤ a.j → a.b ≤ 25) ∧ (5 ≤ a.j → a.b ≤ 22) ∧
  (6 ≤ a.j → a.b ≤ 19) ∧ (7 ≤ a.j → a.b ≤ 14) ∧ (8 ≤ a.j → a.b ≤ 6)
def combined {n : ℕ} (a : Fin n → Shape) (z : Finset (Fin n)) := P3_6_8.shapeSum a z

local notation "row!" h "," len "," nxt "," v "," z =>
  P3_6_8_1.extend (n := len) (N := nxt) (y := v) (total := z) h rfl rfl rfl

private theorem reject3 : zeroMass 28 3 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 28) (j := 3) (m := 143) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 28 3) 0 = 0 := rfl
  have r1 := row! r0,12,12,4487333727686,4487333727686
  have r2 := row! r1,12,24,3762659771402,8249993499088
  have r3 := row! r2,12,36,3108192642446,11358186141534
  have r4 := row! r3,12,48,2519763922706,13877950064240
  have r5 := row! r4,12,60,1993324446806,15871274511046
  have r6 := row! r5,12,72,1524944302106,17396218813152
  have r7 := row! r6,12,84,1110812828702,18507031641854
  have r8 := row! r7,12,96,747238668280,19254270310134
  have r9 := row! r8,12,108,431539940145,19685810250279
  have r10 := row! r9,12,120,176240195865,19862050446144
  have r11 := row! r10,12,132,30699448338,19892749894482
  have r12 := row! r11,11,143,773590642,19893523485124
  rw [r12]
  decide

private theorem reject4 : zeroMass 26 4 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 26) (j := 4) (m := 154) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 26 4) 0 = 0 := rfl
  have r1 := row! r0,12,12,4457924221828,4457924221828
  have r2 := row! r1,12,24,3694139357412,8152063579240
  have r3 := row! r2,12,36,3020291191620,11172354770860
  have r4 := row! r3,12,48,2429554428580,13601909199440
  have r5 := row! r4,12,60,1915360345860,15517269545300
  have r6 := row! r5,12,72,1471396794468,16988666339768
  have r7 := row! r6,12,84,1091608198852,18080274538620
  have r8 := row! r7,12,96,770195556900,18850470095520
  have r9 := row! r8,12,108,501616440976,19352086536496
  have r10 := row! r9,12,120,280971568492,19633058104988
  have r11 := row! r10,12,132,111555751260,19744613856248
  have r12 := row! r11,12,144,18384312204,19762998168452
  have r13 := row! r12,10,154,359753742,19763357922194
  rw [r13]
  decide

private theorem reject5 : zeroMass 23 5 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 23) (j := 5) (m := 174) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 23 5) 0 = 0 := rfl
  have r1 := row! r0,12,12,4437425025303,4437425025303
  have r2 := row! r1,12,24,3647721777551,8085146802854
  have r3 := row! r2,12,36,2963031374519,11048178177373
  have r4 := row! r3,12,48,2373948326607,13422126503980
  have r5 := row! r4,12,60,1871496552215,15293623056195
  have r6 := row! r5,12,72,1447129377743,16740752433938
  have r7 := row! r6,12,84,1092729537591,17833481971529
  have r8 := row! r7,12,96,800609174159,18634091145688
  have r9 := row! r8,12,108,563509837847,19197600983535
  have r10 := row! r9,12,120,374602487055,19572203470590
  have r11 := row! r10,12,132,227487489219,19799690959809
  have r12 := row! r11,12,144,116378050133,19916069009942
  have r13 := row! r12,12,156,39557489286,19955626499228
  have r14 := row! r13,12,168,4378437247,19960004936475
  have r15 := row! r14,6,174,18369367,19960023305842
  rw [r15]
  decide

private theorem reject6 : zeroMass 20 6 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 20) (j := 6) (m := 200) (by decide) (Or.inl (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 20 6) 0 = 0 := rfl
  have r1 := row! r0,12,12,4416491788049,4416491788049
  have r2 := row! r1,12,24,3598518638333,8015010426382
  have r3 := row! r2,12,36,2898523609481,10913534035863
  have r4 := row! r3,12,48,2304691473845,13218225509708
  have r5 := row! r4,12,60,1805825102465,15024050612173
  have r6 := row! r5,12,72,1391345465069,16415396077242
  have r7 := row! r6,12,84,1051291630073,17466687707315
  have r8 := row! r7,12,96,776320764581,18243008471896
  have r9 := row! r8,12,108,557708134385,18800716606281
  have r10 := row! r9,12,120,387347103965,19188063710246
  have r11 := row! r10,12,132,257749136489,19445812846735
  have r12 := row! r11,12,144,162043793813,19607856640548
  have r13 := row! r12,12,156,93978736481,19701835377029
  have r14 := row! r13,12,168,47919723725,19749755100754
  have r15 := row! r14,12,180,18887896997,19768642997751
  have r16 := row! r15,12,192,3562975968,19772205973719
  have r17 := row! r16,8,200,49565740,19772255539459
  rw [r17]
  decide

private theorem reject7 : zeroMass 15 7 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 15) (j := 7) (m := 235) (by decide) (Or.inr (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 15 7) 0 = 0 := rfl
  have r1 := row! r0,12,12,4412735849268,4412735849268
  have r2 := row! r1,12,24,3590013950096,8002749799364
  have r3 := row! r2,12,36,2887936043876,10890685843240
  have r4 := row! r3,12,48,2294106149808,13184791993048
  have r5 := row! r4,12,60,1796799228020,14981591221068
  have r6 := row! r5,12,72,1384961179568,16366552400636
  have r7 := row! r6,12,84,1048208846436,17414761247072
  have r8 := row! r7,12,96,776830011536,18191591258608
  have r9 := row! r8,12,108,561783398708,18753374657316
  have r10 := row! r9,12,120,394698672720,19148073330036
  have r11 := row! r10,12,132,267876439268,19415949769304
  have r12 := row! r11,12,144,174288244976,19590238014280
  have r13 := row! r12,12,156,107576577396,19697814591676
  have r14 := row! r13,12,168,62054865008,19759869456684
  have r15 := row! r14,12,180,32707477220,19792576933904
  have r16 := row! r15,12,192,15189724368,19807766658272
  have r17 := row! r16,12,204,5827857716,19813594515988
  have r18 := row! r17,12,216,1619069456,19815213585444
  have r19 := row! r18,12,228,231492708,19815445078152
  have r20 := row! r19,7,235,4535960,19815449614112
  rw [r20]
  decide

private theorem reject8 : zeroMass 7 8 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 7) (j := 8) (m := 206) (by decide) (Or.inr (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 7 8) 0 = 0 := rfl
  have r1 := row! r0,12,12,4434018990758,4434018990758
  have r2 := row! r1,12,24,3638417588822,8072436579580
  have r3 := row! r2,12,36,2948917116678,11021353696258
  have r4 := row! r3,12,48,2356675780790,13378029477048
  have r5 := row! r4,12,60,1853134903142,15231164380190
  have r6 := row! r5,12,72,1430018921238,16661183301428
  have r7 := row! r6,12,84,1079335388102,17740518689530
  have r8 := row! r7,12,96,793374972278,18533893661808
  have r9 := row! r8,12,108,564711457830,19098605119638
  have r10 := row! r9,12,120,386201744342,19484806863980
  have r11 := row! r10,12,132,250985846918,19735792710898
  have r12 := row! r11,12,144,152486896182,19888279607080
  have r13 := row! r12,12,156,84411138278,19972690745358
  have r14 := row! r13,12,168,40747934870,20013438680228
  have r15 := row! r14,12,180,15769763142,20029208443370
  have r16 := row! r15,12,192,4032215798,20033240659168
  have r17 := row! r16,12,204,374001062,20033614660230
  have r18 := row! r17,2,206,182693,20033614842923
  rw [r18]
  decide

private theorem reject9 : zeroMass 3 9 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b := 3) (j := 9) (m := 183) (by decide) (Or.inr (by decide))]
  have r0 : P3_6_8_1.sumBelow (P3_6_8_1.term 3 9) 0 = 0 := rfl
  have r1 := row! r0,12,12,4419454632432,4419454632432
  have r2 := row! r1,12,24,3596534841372,8015989473804
  have r3 := row! r2,12,36,2880841206984,10896830680788
  have r4 := row! r3,12,48,2265453291444,13162283972232
  have r5 := row! r4,12,60,1743314608032,14905598580264
  have r6 := row! r5,12,72,1307232621132,16212831201396
  have r7 := row! r6,12,84,949878746232,17162709947628
  have r8 := row! r7,12,96,663788349924,17826498297552
  have r9 := row! r8,12,108,441360749904,18267859047456
  have r10 := row! r9,12,120,274859214972,18542718262428
  have r11 := row! r10,12,132,156410965032,18699129227460
  have r12 := row! r11,12,144,78007171092,18777136398552
  have r13 := row! r12,12,156,31502955264,18808639353816
  have r14 := row! r13,12,168,8617390764,18817256744580
  have r15 := row! r14,12,180,933501912,18818190246492
  have r16 := row! r15,3,183,1782176,18818192028668
  rw [r16]
  decide

theorem mass_le {n : ℕ} {a : Fin n → Shape} {l : Fin n → ℕ}
    (hlayers : LowProfile6969.LayerBudget a l) {z s : Finset (Fin n)} {q : Shape} {L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L)
    (hdisj : Disjoint z s) (hq : InBox q (P3_6_8.shapeSum a z)) :
    LowProfile6969.need ≤ ∑ k ∈ Finset.range layerCount, layerTerm q (P3_6_8.shapeSum a s) L k := by
  refine hlayers.trans (Finset.sum_le_sum fun k _ => Final50PriceLayer.remaining_anti ?_ ?_)
  · exact P3_6_8.spend_le (fun i => (a i).b) hz hs hdisj hq.1
  · exact P3_6_8.spend_le (fun i => (a i).j) hz hs hdisj hq.2.1
private theorem zeroMass_upper {b j : ℕ} (hj : 0 < j) :
    (∑ k ∈ Finset.range layerCount, K1_13.remaining ((k + 1) * b) ((k + 1) * j)) ≤
      zeroMass b j := by
  unfold zeroMass
  simp only [symbol_count]
  rw [K1_13_8.sum_range_min layerCount (1650 / j)
    (fun k hk => K1_13_8.fastRemaining_zero (K1_13_8.index_over hj hk))]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (min_le_right _ _))

private theorem retained_bound {r : Shape} (hr : Valid r)
    (hmass : layerNeed ≤ ∑ k ∈ Finset.range layerCount,
      K1_13.remaining ((k + 1) * r.b) ((k + 1) * r.j)) : Box r := by
  have reject {b j : ℕ} (hb : b ≤ r.b) (hj : j ≤ r.j) (hjpos : 0 < j)
      (hsmall : zeroMass b j < layerNeed) : False := by
    have hle : layerNeed ≤ zeroMass b j := hmass.trans <|
      (Finset.sum_le_sum fun k _ => K1_13_8.remaining_anti
        (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_left _ hj)).trans
        (zeroMass_upper hjpos)
    exact (not_lt_of_ge hle) hsmall
  obtain ⟨ht, hjt, hjb⟩ := hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra! h; exact reject (by omega) (by omega) (by decide) reject3
  · by_contra! h; exact reject (by omega) (by omega) (by decide) reject9
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject4
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject5
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject6
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject7
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) reject8

/-- The factors that receive no proper cut have total top degree at most two. -/
theorem no_cut_shape {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ)
    (ha : ∀ i, Valid (a i)) (hl : LowProfile6969.LayerBudget a l)
    (z : Finset (Fin n)) (hz : ∀ i ∈ z, l i = 0) :
    z = ∅ ∨ (Box (combined a z) ∧ 1 ≤ (combined a z).t ∧ (combined a z).t ≤ 2) := by
  rcases P3_6_8.shapeSum_valid_or_empty ha z with h | hr
  · exact Or.inl h
  · right
    let r := P3_6_8.shapeSum a z
    have hb := mass_le hl (s := ∅) (q := r) (L := 0) hz (by simp) (by simp)
      (show InBox r r from ⟨le_rfl, le_rfl, le_rfl⟩)
    have hbox : Box r := retained_bound hr (by
      have hcost : layerNeed ≤ ∑ k ∈ Finset.range layerCount, layerTerm r zeroShape 0 k := by
        simpa only [P3_6_8.shapeSum_empty] using hb
      refine hcost.trans (Finset.sum_le_sum fun k _ => ?_)
      simp only [layerTerm, zeroShape, Nat.mul_zero, Nat.add_zero, Final50Price.remaining]
      exact min_le_right _ _)
    refine ⟨hbox, hr.1, ?_⟩
    have hjet := hr.2.1
    have hj := hbox.2.1
    change 3*r.t ≤ r.j at hjet
    change (r.t ≤ 2)
    omega

end Low6969Retained

end Merged_R6960Low6969Retained
end Z6969Source2263

-- Source: ProximityPrize.SubmissionLower.LowAnchor6969Local
section Z6969Source2264
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

namespace LowAnchor6969Local
noncomputable section
open K1 K1_13 K1_13_1_1 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open A6966FinalAnchorSpace (gradeLimit gradeLimit_antitone cap_of_grade cap_active AnchorEligible anchorLocal anchorSpace)
open scoped BigOperators
open K1_13_1 (atJet_unflatten)
open K1_13_1_1 (exponent_le_of_mem_translation_monomial)

def WideEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 142 ∧ u.some.weight (fun i => i.val) ≤ 58 ∧ u (some 3) ≤ 15 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133363) ≤ 106 * 179740 - 1 + 58

def wideSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | WideEligible u}

def wideLocal (x y : Geom) : wideSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 106 x y).domRestrict _

section
open MvPolynomial

private def truncateX : DifferentialPolynomial Geom 3 →ₗ[Geom] DifferentialPolynomial Geom 3 :=
  filterSupport (fun u => u none < 106)
private theorem origin_monomial_zero (u : JetVariable 3 →₀ ℕ) (a : Geom)
    (hu : 106 ≤ u none) :
    localConstraintAt 106 0 0 (monomial u a) = 0 := by
  have hm : (MvPolynomial.X none ^ u none * monomial (u.erase none) a :
      DifferentialPolynomial Geom 3) = monomial u a := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, one_mul, Finsupp.single_add_erase]
  rw [← hm]
  apply (satisfiesLocalConstraints_iff_coeff_eq_zero 106 0 0 _).mpr
  intro e he
  rw [map_mul, map_pow, unscaledLocalSubstitution, bind₁_X_right]
  simp only [unscaledLocalImage, MvPolynomial.C_0, zero_add, MvPolynomial.X_pow_eq_monomial]
  rw [coeff_monomial_mul', ite_eq_right]
  rw [Finsupp.single_le_iff]
  rw [localContactOrder_eq] at he
  change u none ≤ e (localT 3) → False
  omega
private theorem origin_truncateX (Q : DifferentialPolynomial Geom 3) :
    localConstraintAt 106 0 0 (truncateX Q) = localConstraintAt 106 0 0 Q := by
  rw [Q.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hfilter : truncateX (monomial u (Q.coeff u)) =
      if u none < 106 then monomial u (Q.coeff u) else 0 := by
    ext v
    rw [truncateX, coeff_filterSupport]
    by_cases h : u = v
    · subst v
      by_cases hx : u none < 106 <;> simp [hx]
    · by_cases hx : u none < 106 <;> simp [hx, MvPolynomial.coeff_monomial, h]
  rw [hfilter]
  split
  · rfl
  · rw [map_zero, origin_monomial_zero _ _ (by omega)]

private theorem centered {u v : JetVariable 3 →₀ ℕ}
    (h : v ≤ u) (hu : WideEligible u) (hx : v none < 106) :
    AnchorEligible v := by
  have hd : v.some.degree ≤ u.some.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun j _ => h (some j)
  have hi : v.some.weight (fun i => i.val) ≤ u.some.weight (fun i => i.val) := by
    rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum]
    exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right j.val (h (some j))
  obtain ⟨hdeg,hidx,ht,htail,_⟩ := hu
  have hsum := add_le_add (add_le_add (h (some 1)) (h (some 2))) (h (some 3))
  refine ⟨hd.trans hdeg,hi.trans hidx,(h _).trans ht,hd.trans (htail.trans (gradeLimit_antitone hsum)),?_⟩
  have hw := Finsupp.weight_le_weight
    (w := fun j : Fin 4 => 133484 - j.val) (w' := fun _ => 133484)
    (fun j => Nat.sub_le _ _) v.some
  have he : v.some.weight (fun _ => 133484) = 133484 * v.some.degree := by
    simp only [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, smul_eq_mul,
      Finset.mul_sum, Nat.mul_comm]
  rw [he] at hw
  have hweight : differentialWeight (d := 3) 133484 =
      fun j => j.elim 1 (fun i => 133484 - i.val) := by
    funext j
    cases j <;> rfl
  rw [← Finsupp.optionElim_some v, hweight, Finsupp.weight_optionElim, one_mul]
  calc
    _ ≤ 105 + 133484 * 142 :=
      Nat.add_le_add (Nat.le_of_lt_succ hx)
        (hw.trans (Nat.mul_le_mul_left _ (hd.trans hdeg)))
    _ ≤ _ := by decide
private theorem centered_in_space (x y : Geom) (Q : wideSpace) :
    truncateX (globalPointTranslation x y (Q : DifferentialPolynomial Geom 3)) ∈
      anchorSpace := by
  classical
  rw [(Q : DifferentialPolynomial Geom 3).as_sum, map_sum, map_sum]
  refine Submodule.sum_mem _ fun u hu => ?_
  apply (mem_restrictSupport_iff Geom).mpr
  intro v hv
  have hn := mem_support_iff.mp hv
  rw [truncateX, coeff_filterSupport] at hn
  split at hn
  · exact centered
      (exponent_le_of_mem_translation_monomial x y u v _ (mem_support_iff.mpr hn))
      (Q.property hu) (by assumption)
  · exact (hn rfl).elim
theorem rank_at_point_le_origin (x y : Geom) :
    Module.finrank Geom (LinearMap.range (wideLocal x y)) ≤
      Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) := by
  have hpositive (j : JetVariable 3) : differentialWeight 133484 j ≠ 0 := by
    cases j with
    | none => decide
    | some j =>
      have hj := j.isLt
      change 133484 - j.val ≠ 0
      omega
  have : Module.Finite Geom anchorSpace :=
    restrictSupport_finite <|
      (Finsupp.finite_of_nat_weight_le _ hpositive _).subset fun _ hu => hu.2.2.2.2
  let f : wideSpace →ₗ[Geom] DifferentialPolynomial Geom 3 :=
    (truncateX.comp (globalPointTranslation x y).toLinearMap).domRestrict wideSpace
  let tr : wideSpace →ₗ[Geom] anchorSpace := f.codRestrict _ fun Q =>
    centered_in_space x y Q
  have he : wideLocal x y = (anchorLocal 0 0).comp tr := by
    apply LinearMap.ext
    intro Q
    change localConstraintAt 106 x y (Q : DifferentialPolynomial Geom 3) =
      localConstraintAt 106 0 0 (truncateX (globalPointTranslation x y Q))
    rw [origin_truncateX,localConstraintAt_eq_zero_globalPointTranslation]
  rw [he]
  exact LinearMap.finrank_range_comp_le_left _ _

end

theorem per_position (x y : Geom) :
    Module.finrank Geom (LinearMap.range (wideLocal x y)) ≤ 22239546 :=
  (rank_at_point_le_origin x y).trans A6966FinalRank.origin_rank

theorem finiteWide : Module.Finite Geom wideSpace := by
  have hpositive (j : JetVariable 3) : differentialWeight 133363 j ≠ 0 := by
    cases j with
    | none => decide
    | some j =>
      have hj := j.isLt
      change 133363 - j.val ≠ 0
      omega
  exact MvPolynomial.restrictSupport_finite <|
    (Finsupp.finite_of_nat_weight_le _ hpositive _).subset fun _ hu => hu.2.2.2.2

theorem shape_bound (Q : wideSpace) :
    InBox (shape (MvPolynomial.optionEquivRight Geom (Fin 4) Q)) ⟨142, 58, 15⟩ := by
  classical
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  have hQ := (MvPolynomial.mem_restrictSupport_iff Geom).mp Q.property
  have hm (m : Fin 4 →₀ ℕ) (h : m ∈ P.support) : ∃ i, WideEligible (m.optionElim i) := by
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp h)
    refine ⟨i, hQ ?_⟩
    exact MvPolynomial.mem_support_iff.mpr (by
      rwa [← MvPolynomial.optionEquivRight_coeff_coeff, ← Polynomial.mem_support_iff])
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.degree_apply, Finsupp.sum] using hi.1
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hi.2.1
  · change P.degreeOf 3 ≤ 15
    rw [MvPolynomial.degreeOf_eq_sup]
    apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.optionElim_apply_some] using hi.2.2.1

theorem active_bound (Q : wideSpace) :
    A6966LowBase.ActiveFits (MvPolynomial.optionEquivRight Geom (Fin 4) Q) 178 := by
  classical
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  intro m hm
  obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp hm)
  have hQ := (MvPolynomial.mem_restrictSupport_iff Geom).mp Q.property
  have h : WideEligible (m.optionElim i) := hQ (MvPolynomial.mem_support_iff.mpr (by
    rwa [← MvPolynomial.optionEquivRight_coeff_coeff, ← Polynomial.mem_support_iff]))
  have hd := h.1
  have hl := h.2.2.2.1
  have hw := h.2.1
  simp only [Finsupp.optionElim_apply_some] at hl
  rw [Finsupp.some_optionElim] at hd hw
  have hdeg : m.degree = m 0 + m 1 + m 2 + m 3 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_four]
  have hweight : m.weight (fun i : Fin 4 => i.val) = m 1 + 2 * m 2 + 3 * m 3 := by
    rw [Finsupp.weight_eq_sum, Fin.sum_univ_four]
    simp [Nat.mul_comm, Nat.add_assoc]
  change m.weight (fun i : Fin 4 => i.val) ≤ 58 at hw
  rw [hweight] at hw
  have hc := cap_of_grade (s := m.degree) (t := m 1 + m 2 + m 3)
    (by omega) (by omega) (by simpa [Finsupp.some_optionElim] using hl)
  have hb := cap_active _ hd
  omega

theorem rawWeight (Q : wideSpace) :
    differentialWeightedDegree 133363 (Q : DifferentialPolynomial Geom 3) ≤
      106 * 179740 - 1 + 58 := by
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  exact fun m hm => (Q.property hm).2.2.2.2


end
end LowAnchor6969Local
end Z6969Source2264

-- Source: ProximityPrize.SubmissionLower.LowAnchor6969Columns
section Z6969Source2265
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

open K1 K1_13 K1_13_1_1 PolynomialDifferential ReedSolomon.HiddenDerivative
open MvPolynomial
open scoped BigOperators Polynomial

namespace LowAnchor6969Columns
noncomputable section

abbrev Ex := JetVariable 3 →₀ ℕ
abbrev DP := DifferentialPolynomial Geom 3

def jidx (u : Ex) : ℕ := u.some.weight Fin.val
def jdeg (u : Ex) : ℕ := u.some.degree
def jdiff (u : Ex) : ℕ := u (some 1) + u (some 2) + u (some 3)

@[simp] theorem jidx_add (u v : Ex) : jidx (u + v) = jidx u + jidx v := by
  simp [jidx, Finsupp.some_add]
@[simp] theorem jdeg_add (u v : Ex) : jdeg (u + v) = jdeg u + jdeg v := by
  simp [jdeg, Finsupp.some_add]
@[simp] theorem jdiff_add (u v : Ex) : jdiff (u + v) = jdiff u + jdiff v := by
  unfold jdiff
  simp only [Finsupp.add_apply]
  omega

def top (u : Ex) : Ex := u + Finsupp.single none (jidx u)

@[simp] theorem top_add (u v : Ex) : top (u + v) = top u + top v := by
  rw [top, jidx_add, Finsupp.single_add]
  unfold top
  abel

def Related (u v : Ex) : Prop :=
  jdeg v = jdeg u ∧ jidx v ≤ jidx u ∧ jdiff v ≤ jdiff u ∧
    v (some 3) ≤ u (some 3) ∧ v none = u none + jidx v

theorem Related.add {u v a b : Ex} (h : Related u a) (k : Related v b) :
    Related (u+v) (a+b) := by
  obtain ⟨hd,hi,hf,ht,hx⟩ := h
  obtain ⟨kd,ki,kf,kt,kx⟩ := k
  unfold Related
  simp only [jdeg_add, jidx_add, jdiff_add, Finsupp.add_apply]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem top_related (u : Ex) : Related u (top u) := by
  unfold top Related jdeg jidx jdiff
  simp [Finsupp.some_add, Finsupp.some_single_none]

def Bounded (u : Ex) (P : DP) : Prop :=
  ∀ v ∈ P.support, Related u v ∧ jidx v < jidx u

def HasTop (u : Ex) (a : Geom) (P : DP) : Prop :=
  ∃ L, P = monomial (top u) a + L ∧ Bounded u L

private theorem bounded_add {u : Ex} {P Q : DP} (h : Bounded u P) (k : Bounded u Q) :
    Bounded u (P+Q) := by
  intro v hv
  exact (Finset.mem_union.mp (support_add hv)).elim (h v) (k v)

private theorem monomial_related {u : Ex} {a : Geom} {v : Ex}
    (h : v ∈ (monomial (top u) a).support) : Related u v := by
  have hv := Finset.mem_singleton.mp (support_monomial_subset h)
  simpa only [hv] using top_related u

private theorem top_idx (u : Ex) : jidx (top u) = jidx u := by
  unfold jidx top
  simp [Finsupp.some_add, Finsupp.some_single_none]

private theorem bounded_mul_left {u v : Ex} {P Q : DP} (h : Bounded u P)
    (k : ∀ a ∈ Q.support, Related v a) : Bounded (u+v) (P*Q) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hz)
  obtain ⟨hr, hi⟩ := h a ha
  have hk := k b hb
  exact ⟨hr.add hk, by simpa using Nat.add_lt_add_of_lt_of_le hi hk.2.1⟩

private theorem bounded_mul_right {u v : Ex} {P Q : DP} (h : ∀ a ∈ P.support, Related u a)
    (k : Bounded v Q) : Bounded (u+v) (P*Q) := by
  rw [add_comm, mul_comm]
  exact bounded_mul_left k h

theorem HasTop.mul {u v : Ex} {a b : Geom} {P Q : DP} (h : HasTop u a P)
    (k : HasTop v b Q) : HasTop (u+v) (a*b) (P*Q) := by
  obtain ⟨L, rfl, hL⟩ := h
  obtain ⟨M, rfl, hM⟩ := k
  refine ⟨monomial (top u) a * M + L * monomial (top v) b + L*M, ?_, ?_⟩
  · rw [top_add, ← monomial_mul_monomial]
    ring
  · refine bounded_add (bounded_add ?_ ?_) ?_
    · exact bounded_mul_right (fun b hb => monomial_related hb) hM
    · exact bounded_mul_left hL (fun b hb => monomial_related hb)
    · exact bounded_mul_left hL (fun b hb => (hM b hb).1)

theorem HasTop.support {u : Ex} {a : Geom} {P : DP} (h : HasTop u a P) :
    ∀ v ∈ P.support, Related u v := by
  obtain ⟨L,rfl,hL⟩ := h
  intro v hv
  exact (Finset.mem_union.mp (support_add hv)).elim (fun h => monomial_related h) (fun h => (hL v h).1)

theorem HasTop.lower {u : Ex} {a : Geom} {P : DP} (h : HasTop u a P) :
    ∀ v ∈ P.support, v = top u ∨ jidx v < jidx u := by
  obtain ⟨L,rfl,hL⟩ := h
  intro v hv
  exact (Finset.mem_union.mp (support_add hv)).elim
    (fun h => Or.inl (Finset.mem_singleton.mp (support_monomial_subset h))) (fun h => Or.inr (hL v h).2)

theorem HasTop.coeff {u : Ex} {a : Geom} {P : DP} (h : HasTop u a P) :
    P.coeff (top u) = a := by
  obtain ⟨L,rfl,hL⟩ := h
  have hzero : L.coeff (top u) = 0 := by
    apply notMem_support_iff.mp
    intro hz
    have hh := (hL _ hz).2
    rw [top_idx] at hh
    exact (lt_irrefl _) hh
  simp [hzero]

theorem HasTop.pow {u : Ex} {a : Geom} {P : DP} (h : HasTop u a P) (n : ℕ) :
    HasTop (n • u) (a^n) (P^n) := by
  induction n with
  | zero =>
    refine ⟨0, ?_, by simp [Bounded]⟩
    simp [top,jidx,monomial_zero']
  | succ n ih =>
    rw [pow_succ, pow_succ, succ_nsmul]
    exact ih.mul h

private def eulTerm (i k : ℕ) (hk : k < 4) : DP :=
  monomial (Finsupp.single none k + Finsupp.single (some ⟨k,hk⟩) 1)
    ((-1 : Geom)^k * (133363-k).choose (i-k))

def eul (i : Fin 4) : DP :=
  ∑ k : Fin (i.val+1), eulTerm i.val k.val (by omega)

private theorem eulTerm_related (i k : Fin 4) (h : k ≤ i) :
    Related (Finsupp.single (some i) 1)
      (Finsupp.single none k.val + Finsupp.single (some k) 1) := by
  have hval : k.val ≤ i.val := h
  simp only [Related, jdeg, jidx, jdiff, Finsupp.some_add, Finsupp.some_single_none,
    zero_add, Finsupp.some_single_some, Finsupp.degree_single, Finsupp.weight_single,
    nsmul_eq_mul, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Option.some.injEq]
  fin_cases k <;> fin_cases i <;> (first | contradiction | decide)


theorem eul_top (i : Fin 4) : HasTop (Finsupp.single (some i) 1) ((-1 : Geom)^i.val) (eul i) := by
  rw [eul, Fin.sum_univ_castSucc]
  let L := ∑ k : Fin i.val, eulTerm i.val k.val (by omega)
  have he : eulTerm i.val i.val i.isLt =
      monomial (top (Finsupp.single (some i) 1)) ((-1 : Geom)^i.val) := by
    simp [eulTerm,top,jidx,Finsupp.some_single_some, Finsupp.weight_single,add_comm]
  refine ⟨L, ?_, ?_⟩
  · rw [add_comm]
    congr 1
  · intro v hv
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp (support_sum hv)
    have hv' := Finset.mem_singleton.mp (support_monomial_subset hk)
    subst v
    refine ⟨eulTerm_related i ⟨k,by omega⟩ (by exact k.isLt.le), ?_⟩
    simp [jidx,Finsupp.some_add,Finsupp.some_single_none,Finsupp.some_single_some,Finsupp.weight_single, k.isLt]


def ColumnEligible (u : Ex) : Prop :=
  jdeg u ≤ 142 ∧ jidx u ≤ 58 ∧ u (some 3) ≤ 15 ∧
    jdeg u ≤ A6966FinalAnchorSpace.gradeLimit (jdiff u) ∧
    u none + 133363*jdeg u < 106*179740 + 2*jidx u

private def orth (u : Ex) : DP :=
  eul 0 ^ u (some 0) * eul 1 ^ u (some 1) *
    eul 2 ^ u (some 2) * eul 3 ^ u (some 3)

private def jetOnly (u : Ex) : Ex := u.some.optionElim 0

private theorem normalized_jet (u : Ex) :
    u (some 0) • Finsupp.single (some (0 : Fin 4)) 1 +
      u (some 1) • Finsupp.single (some (1 : Fin 4)) 1 +
      u (some 2) • Finsupp.single (some (2 : Fin 4)) 1 +
      u (some 3) • Finsupp.single (some (3 : Fin 4)) 1 = jetOnly u := by
  ext k
  cases k with
  | none => simp [jetOnly]
  | some k => fin_cases k <;> simp [jetOnly]

private def sign (u : Ex) : Geom :=
  ((-1 : Geom)^0) ^ u (some 0) * ((-1 : Geom)^1) ^ u (some 1) *
    ((-1 : Geom)^2) ^ u (some 2) * ((-1 : Geom)^3) ^ u (some 3)

private theorem sign_ne_zero (u : Ex) : sign u ≠ 0 := by simp [sign]

private theorem orth_top (u : Ex) : HasTop (jetOnly u) (sign u) (orth u) := by
  rw [← normalized_jet]
  exact ((((eul_top 0).pow _).mul ((eul_top 1).pow _)).mul ((eul_top 2).pow _)).mul ((eul_top 3).pow _)

private theorem single_top (x : ℕ) : HasTop (Finsupp.single none x) 1
    (monomial (Finsupp.single none x) 1) := by
  refine ⟨0, ?_, by simp [Bounded]⟩
  simp [top,jidx,Finsupp.some_single_none]

private def adjusted (u : Ex) : Ex :=
  Finsupp.single none (u none - jidx u) + jetOnly u

private theorem adjusted_idx (u : Ex) : jidx (adjusted u) = jidx u := by
  rw [adjusted,jidx,Finsupp.some_add,Finsupp.some_single_none,zero_add,jetOnly,Finsupp.some_optionElim]
  rfl

private theorem adjusted_top (u : Ex) (h : jidx u ≤ u none) : top (adjusted u) = u := by
  rw [top,adjusted_idx]
  ext k
  cases k with
  | none => simp [adjusted,jetOnly,Nat.sub_add_cancel h]
  | some k => simp [adjusted,jetOnly]

def column (u : Ex) : DP :=
  if u none < jidx u then monomial u 1 else
    monomial (Finsupp.single none (u none - jidx u)) 1 * orth u

private theorem column_hasTop (u : Ex) (h : ¬ u none < jidx u) :
    HasTop (adjusted u) (sign u) (column u) := by
  simpa only [column, ite_eq_right h, one_mul, adjusted] using (single_top _).mul (orth_top u)

theorem column_coeff (u : Ex) : (column u).coeff u ≠ 0 := by
  by_cases h : u none < jidx u
  · simp [column,h]
  · have he := (column_hasTop u h).coeff
    rw [adjusted_top u (Nat.le_of_not_gt h)] at he
    rw [he]
    exact sign_ne_zero u

theorem column_lower (u v : Ex) (h : v ≠ u) (hle : jidx u ≤ jidx v) :
    (column u).coeff v = 0 := by
  apply notMem_support_iff.mp
  intro hv
  by_cases hcut : u none < jidx u
  · rw [column,ite_eq_left hcut] at hv
    exact h (Finset.mem_singleton.mp (support_monomial_subset hv))
  · obtain he | hl := (column_hasTop u hcut).lower v hv
    · exact h (he.trans (adjusted_top u (Nat.le_of_not_gt hcut)))
    · rw [adjusted_idx] at hl
      omega

private theorem jet_weight (m : Fin 4 →₀ ℕ) (w : Fin 4 → ℕ) :
    m.weight w = m 0 * w 0 + m 1 * w 1 + m 2 * w 2 + m 3 * w 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ, smul_eq_mul, add_assoc]

private theorem weight_formula (u : Ex) :
    u.weight (differentialWeight 133363) + jidx u = u none + 133363*jdeg u := by
  have he : differentialWeight (d := 3) 133363 = fun i =>
      i.elim 1 (fun k => 133363 - k.val) := by
    funext i
    cases i <;> rfl
  conv_lhs => enter [1]; rw [← Finsupp.optionElim_some u,he,Finsupp.weight_optionElim,one_mul]
  unfold jidx jdeg
  rw [Finsupp.degree_eq_weight_one, jet_weight, jet_weight, jet_weight]
  change u none + (u.some 0*133363 + u.some 1*133362 + u.some 2*133361 + u.some 3*133360) +
      (u.some 0*0 + u.some 1*1 + u.some 2*2 + u.some 3*3) =
    u none + 133363 * (u.some 0*1 + u.some 1*1 + u.some 2*1 + u.some 3*1)
  omega

private theorem adjusted_shape (u : Ex) :
    jdeg (adjusted u) = jdeg u ∧ jdiff (adjusted u) = jdiff u ∧
      adjusted u (some 3) = u (some 3) ∧ adjusted u none = u none - jidx u := by
  have he : (adjusted u).some = u.some := by
    rw [adjusted,Finsupp.some_add,Finsupp.some_single_none,zero_add,jetOnly,Finsupp.some_optionElim]
  change (adjusted u).some.degree = u.some.degree ∧ _ ∧ _ ∧ _
  rw [he]
  simp [adjusted,jetOnly,jdiff]

theorem column_wide {u : Ex} (h : ColumnEligible u) :
    column u ∈ LowAnchor6969Local.wideSpace := by
  apply (MvPolynomial.mem_restrictSupport_iff Geom).mpr
  intro v hv
  obtain ⟨hd,hi,ht,hf,hw⟩ := h
  have hvw := weight_formula v
  by_cases hcut : u none < jidx u
  · rw [column,ite_eq_left hcut] at hv
    have he := Finset.mem_singleton.mp (support_monomial_subset hv)
    subst v
    refine ⟨hd,hi,ht,hf,?_⟩
    omega
  · obtain ⟨hvd,hvi,hvf,hvt,hvx⟩ := (column_hasTop u hcut).support v hv
    obtain ⟨had,haf,hat,hax⟩ := adjusted_shape u
    rw [had] at hvd
    rw [adjusted_idx] at hvi
    rw [haf] at hvf
    rw [hat] at hvt
    rw [hax] at hvx
    refine ⟨hvd.le.trans hd,hvi.trans hi,hvt.trans ht,?_ ,?_⟩
    · exact hvd.le.trans (hf.trans (A6966FinalAnchorSpace.gradeLimit_antitone hvf))
    · omega



private theorem spec_eul (S : (Polynomial Geom)) (i : Fin 4) :
    differentialSpecializationHom S (eul i) = EulerJetDegree.euler 133363 i.val S := by
  rw [eul, map_sum, EulerJetDegree.euler, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold eulTerm
  rw [monomial_add_single, pow_one, ← MvPolynomial.C_mul_X_pow_eq_monomial,
    map_mul, map_mul, map_pow]
  simp [differentialSpecializationHom, mul_assoc]

private theorem natDegree_prod_bound (S : (Polynomial Geom)) (u : Ex) (hS : S.natDegree ≤ 133363) :
    (differentialSpecializationHom S (orth u)).natDegree ≤ 133363*jdeg u - jidx u := by
  rw [orth,map_mul,map_mul,map_mul,map_pow,map_pow,map_pow,map_pow,spec_eul,spec_eul,spec_eul,spec_eul]
  have hh (i : Fin 4) := (Polynomial.natDegree_pow_le
    (p := EulerJetDegree.euler 133363 i.val S) (n := u (some i))).trans
      (Nat.mul_le_mul_left _ (EulerJetDegree.natDegree_euler_le_sub (i := i.val) hS))
  have ha := Polynomial.natDegree_mul_le.trans (Nat.add_le_add
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add
      (Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hh 0) (hh 1))) (hh 2))) (hh 3))
  refine ha.trans ?_
  rw [jdeg, Finsupp.degree_eq_weight_one, jidx, jet_weight, jet_weight]
  change (u (some 0)*133363 + u (some 1)*133362 + u (some 2)*133361 + u (some 3)*133360) ≤
    133363 * (u (some 0)*1+u (some 1)*1+u (some 2)*1+u (some 3)*1) -
    (u (some 0)*0+u (some 1)*1+u (some 2)*2+u (some 3)*3)
  omega

theorem column_eval_degree (S : (Polynomial Geom)) {u : Ex} (h : ColumnEligible u)
    (hs : S.natDegree ≤ 133363) :
    (differentialSpecialization (column u) S).natDegree ≤ 106 * 179740 - 1 := by
  obtain ⟨hd,hi,_,_,hw⟩ := h
  by_cases hcut : u none < jidx u
  · rw [column,ite_eq_left hcut]
    apply (natDegree_differentialSpecialization_le _ _ hs).trans
    rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
    intro v hv
    have he := Finset.mem_singleton.mp (support_monomial_subset hv)
    subst v
    have hf := weight_formula u
    omega
  · change (differentialSpecializationHom S (column u)).natDegree ≤ _
    rw [column,ite_eq_right hcut,map_mul,← MvPolynomial.X_pow_eq_monomial,map_pow]
    have hx : differentialSpecializationHom S (MvPolynomial.X none : DP) = Polynomial.X := by
      simp [differentialSpecializationHom]
    rw [hx]
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_X_pow]
    · have hrel := natDegree_prod_bound S u hs
      have hz : jidx u ≤ 133363*jdeg u := by
        have hh := weight_formula u
        have hwnd : u none ≤ u.weight (differentialWeight 133363) := by
          have he : differentialWeight (d := 3) 133363 = fun i =>
              i.elim 1 (fun k => 133363 - k.val) := by
            funext i
            cases i <;> rfl
          rw [← Finsupp.optionElim_some u,he,Finsupp.weight_optionElim,one_mul]
          simp
        omega
      omega

end
end LowAnchor6969Columns
end Z6969Source2265

-- Source: ProximityPrize.SubmissionLower.LowAnchor6969Dimension
section Z6969Source2266
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

namespace LowAnchor6969Dimension
open A6966FinalAnchorSpace LowAnchor6969Columns
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

/- Count the abscissa powers using the monomial parametrization in P0_9_1. -/
private abbrev Exponent := JetVariable 3 →₀ ℕ
private def indexWeight (a b c : ℕ) : ℕ := a + 2 * b + 3 * c
private def gradeCeiling (a b c : ℕ) : ℕ :=
  min 142 (gradeLimit (a + b + c))
private def gradeSlots (a b c : ℕ) : ℕ :=
  gradeCeiling a b c + 1 - (a + b + c)
private def firstWidth (a b c : ℕ) : ℕ :=
  106 * 179740 - 133363 * gradeCeiling a b c + 2 * indexWeight a b c
private def abscissaWidth (a b c j : ℕ) : ℕ := firstWidth a b c + 133363 * j
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
private theorem eligible_exponent (x v a b c : ℕ) :
    ColumnEligible (exponent x v a b c) ↔
      c ≤ 15 ∧ indexWeight a b c ≤ 58 ∧ v + (a + b + c) ≤ gradeCeiling a b c ∧
        x + 133363 * (v + (a + b + c)) < 106 * 179740 + 2 * indexWeight a b c := by
  unfold ColumnEligible jdeg jidx jdiff gradeCeiling indexWeight
  rw [Finsupp.degree_eq_weight_one, jet_weight, jet_weight]
  simp only [mul_one, Finsupp.some_apply, exponent_some, Matrix.cons_val_zero, le_min_iff]
  simp only [exponent_none, Matrix.cons_val_one]
  have ht : ![v,a,b,c] (2 : Fin 4) = b := rfl
  have hf : ![v,a,b,c] (3 : Fin 4) = c := rfl
  rw [ht,hf,show ![a,b,c] (0 : Fin 3) = a by rfl]
  change (v + a + b + c ≤ 142 ∧ v * 0 + a * 1 + b * 2 + c * 3 ≤ 58 ∧
    c ≤ 15 ∧ v + a + b + c ≤ gradeLimit (a + b + c) ∧
    x + 133363 * (v + a + b + c) < 106 * 179740 + 2 * (v * 0 + a * 1 + b * 2 + c * 3)) ↔ _
  omega
private theorem width_iff (a b c j x : ℕ) (hj : j ≤ gradeCeiling a b c) :
    x < abscissaWidth a b c j ↔
      x + 133363 * (gradeCeiling a b c - j) < 106 * 179740 + 2 * indexWeight a b c := by
  have hgrade : gradeCeiling a b c ≤ 142 := min_le_left _ _
  unfold abscissaWidth firstWidth
  omega
private abbrev Slot :=
  Σ c : Fin 16, Σ b : Fin ((58 - 3 * c.val) / 2 + 1),
    Σ a : Fin (58 - 3 * c.val - 2 * b.val + 1),
      Σ j : Fin (gradeSlots a.val b.val c.val),
        Fin (abscissaWidth a.val b.val c.val j.val)
private abbrev Eligible := {u : Exponent // ColumnEligible u}
private theorem slot_bounds (c b a j x : ℕ) :
    (c < 16 ∧ b < (58 - 3 * c) / 2 + 1 ∧ a < 58 - 3 * c - 2 * b + 1 ∧
      j < gradeSlots a b c ∧ x < abscissaWidth a b c j) ↔
    (c ≤ 15 ∧ indexWeight a b c ≤ 58 ∧ j + (a + b + c) ≤ gradeCeiling a b c ∧
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
  n * firstWidth a b c + 133363 * (n * (n - 1) / 2)
private theorem sum_abscissaWidth (a b c : ℕ) :
    (∑ j : Fin (gradeSlots a b c), abscissaWidth a b c j) = tripleCount a b c := by
  rw [Fin.sum_univ_eq_sum_range (abscissaWidth a b c)]
  simp [abscissaWidth, tripleCount, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, Finset.sum_range_id]
private def rowCount (b c : ℕ) : ℕ :=
  sumRange (fun a => tripleCount a b c) (58 - 3 * c - 2 * b + 1)
private def sliceCount (c : ℕ) : ℕ :=
  sumRange (fun b => rowCount b c) ((58 - 3 * c) / 2 + 1)
private theorem slot_card : Fintype.card Slot = sumRange sliceCount 16 := by
  simp only [Slot, sliceCount, rowCount, Fintype.card_sigma, Fintype.card_fin, sumRange_eq_fin,
    sum_abscissaWidth]
private def totals : List ℕ := [792229856789, 720519587459, 652047384834, 586021710405, 523426000532, 463453531767, 407103459043, 353553740610, 303819383337, 257062893809, 214315264194, 174723416049, 139334460204, 107279806590, 79624565202, 55487968368]

private theorem slice_value (i : Fin 16) : sliceCount i = totals[i.val]! := by
  fin_cases i <;> decide +kernel

private theorem totalCount : sumRange sliceCount 16 = 5830003029192 := by
  rw [sumRange_eq_fin]
  calc
    _ = ∑ c : Fin 16, totals[c.val]! := Finset.sum_congr rfl fun c _ => slice_value c
    _ = _ := by rw [← sumRange_eq_fin]; decide +kernel


theorem eligible_card : Nonempty (Eligible ≃ Fin 5830003029192) := by
  let e : Slot ≃ Eligible :=
    Equiv.ofBijective slotExponent ⟨slotExponent_injective, slotExponent_surjective⟩
  exact ⟨e.symm.trans ((Fintype.equivFin Slot).trans (finCongr (slot_card.trans totalCount)))⟩

end LowAnchor6969Dimension
end Z6969Source2266

-- Source: ProximityPrize.SubmissionLower.LowAnchor6969
section Z6969Source2267
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option linter.style.haveILetI false
set_option maxRecDepth 10000

namespace LowAnchor6969
noncomputable section
open K1 K1_13 K1_13_1_1 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open LowAnchor6969Columns LowAnchor6969Local
open scoped BigOperators
open K1_13_1 (atJet_unflatten)

private abbrev Slot := {u : Ex // ColumnEligible u}

private theorem independent_dp : LinearIndependent Geom (fun u : Slot => column u.val) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c he i hi
  by_contra hn
  let F := s.filter (fun i => c i ≠ 0)
  have hF : F.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hn⟩⟩
  obtain ⟨j, hj, hm⟩ := F.exists_max_image (fun u => jidx u.val) hF
  have hj' := Finset.mem_filter.mp hj
  have hcoeff := congrArg (fun p : DP => p.coeff j.val) he
  change (∑ i ∈ s, c i • column i.val).coeff j.val = (0 : DP).coeff j.val at hcoeff
  rw [MvPolynomial.coeff_sum, AddMonoidAlgebra.coeff_zero,
    Finset.sum_eq_single_of_mem j hj'.1] at hcoeff
  · rw [MvPolynomial.coeff_smul, smul_eq_mul] at hcoeff
    exact (mul_ne_zero hj'.2 (column_coeff j.val)) hcoeff
  · intro k hk hkj
    rw [MvPolynomial.coeff_smul]
    by_cases hc : c k = 0
    · simp [hc]
    · have hne : j.val ≠ k.val := fun h => hkj (Subtype.ext h.symm)
      have hi := hm k (Finset.mem_filter.mpr ⟨hk,hc⟩)
      simp [column_lower k.val j.val hne hi]

private def source : Submodule Geom DP := Submodule.span Geom
    (Set.range fun u : Slot => column u.val)

private theorem source_le_wide : source ≤ wideSpace := by
  apply Submodule.span_le.mpr
  rintro _ ⟨u,rfl⟩
  exact column_wide u.property

private theorem dim_source : Module.finrank Geom source = 5830003029192 := by
  classical
  obtain ⟨e⟩ := LowAnchor6969Dimension.eligible_card
  letI : Fintype Slot := Fintype.ofEquiv _ e.symm
  rw [source,finrank_span_eq_card independent_dp,Fintype.card_congr e,Fintype.card_fin]

private theorem source_eval (Q : source) (S : (Polynomial Geom)) (hs : S.natDegree ≤ 133363) :
    (differentialSpecialization (Q.val : DP) S).natDegree ≤ 106*179740-1 := by
  change (differentialSpecializationHom S Q.val).natDegree ≤ _
  let f := (differentialSpecializationHom (d := 3) S).toLinearMap
  change (f Q.val).natDegree ≤ _
  have hq : Q.val ∈ Submodule.span Geom (Set.range fun u : Slot => column u.val) := Q.property
  refine Submodule.span_induction (p := fun p _ => (f p).natDegree ≤ 106 * 179740 - 1) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨u,rfl⟩
    exact column_eval_degree S u.property hs
  · rw [map_zero]
    simp
  · intro a b _ _ ha hb
    rw [map_add]
    exact (Polynomial.natDegree_add_le (f a) (f b)).trans (max_le ha hb)
  · intro a p _ hp
    rw [map_smul]
    exact (Polynomial.natDegree_smul_le _ _).trans hp

private def row (w : I → K) (i : I) : source →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 106 (embed (node i)) (embed (w i))).domRestrict _

private theorem row_rank (w : I → K) (i : I) :
    Module.finrank Geom (LinearMap.range (row w i)) ≤ 22239546 := by
  letI : Module.Finite Geom wideSpace := finiteWide
  let L := wideLocal (embed (node i)) (embed (w i))
  have hle : LinearMap.range (row w i) ≤ LinearMap.range L := by
    rintro _ ⟨Q,rfl⟩
    exact ⟨⟨Q.val,source_le_wide Q.property⟩,rfl⟩
  have hfin : Module.finrank Geom (LinearMap.range (row w i)) ≤
      Module.finrank Geom (LinearMap.range L) := Submodule.finrank_mono hle
  exact hfin.trans (per_position (embed (node i)) (embed (w i)))

private theorem exists_local (w : I → K) :
    ∃ Q : source, Q ≠ 0 ∧ ∀ i, row w i Q = 0 := by
  have hr : (∑ i, Module.finrank Geom (LinearMap.range (row w i))) ≤ 262144 * 22239546 := calc
    _ ≤ ∑ _ : I, (22239546 : ℕ) := Finset.sum_le_sum fun i _ => row_rank w i
    _ = _ := by simp
  have hroom : 262144 * 22239546 < Module.finrank Geom source := by
    rw [dim_source]
    decide
  exact LinearMap.exists_ne_zero_of_sum_finrank_range_lt (row w) (hr.trans_lt hroom)

/-- The Euler anchor at the actual low endpoint, using the published local-rank witnesses. -/
theorem exists_anchor (w : I → K) :
    ∃ P : Row 4, P ≠ 0 ∧ InBox (shape P) ⟨142,58,15⟩ ∧ A6966LowBase.ActiveFits P 178 ∧
      differentialWeightedDegree 133363 ((MvPolynomial.optionEquivRight Geom (Fin 4)).symm P) ≤
        106 * 179740 - 1 + 58 ∧
      ∀ (S : (Polynomial K)) (T : Finset I), S.natDegree ≤ 133363 → 179740 ≤ T.card →
        (∀ i ∈ T, S.eval (node i) = w i) → atJet P (extend S) = 0 := by
  classical
  obtain ⟨Q,hQ,hloc⟩ := exists_local w
  let V : wideSpace := ⟨Q.val, source_le_wide Q.property⟩
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q.val
  have hP : P ≠ 0 := by
    intro h
    exact hQ (Subtype.ext ((MvPolynomial.optionEquivRight Geom (Fin 4)).injective
      (h.trans (map_zero _).symm)))
  refine ⟨P,hP,shape_bound V,active_bound V,?_,?_⟩
  · simpa only [P,AlgEquiv.symm_apply_apply] using rawWeight V
  · intro S T hd hT hits
    rw [atJet_unflatten]
    have hS : (extend S).natDegree ≤ 133363 := Polynomial.natDegree_map_le.trans hd
    have hdeg := (source_eval Q (extend S) hS).trans_lt (by decide : 106*179740-1 < 106*179740)
    have heval (i : I) (hi : i ∈ T) : (extend S).eval (embed (node i)) = embed (w i) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, hits i hi]
    exact eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
      (fun i => embed (node i)) T 106 179740
      ((RingHom.injective embed).comp node.injective).injOn hT
      (fun i hi => X_sub_C_pow_dvd_differentialSpecialization_of_contact
        Q.val (extend S) (embed (node i)) (embed (w i)) (heval i hi) (hloc i)) hdeg

/-- The actual low-band model and marks supply the same single anchor. -/
theorem anchor_of_family {cap u del Γ} (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179740 M Γ)
    (hi : M.overhead ≤ 2292) :
    ∃ P : Row 4, P ≠ 0 ∧ InBox (shape P) ⟨142,58,15⟩ ∧ A6966LowBase.ActiveFits P 178 ∧
      differentialWeightedDegree 133363 ((MvPolynomial.optionEquivRight Geom (Fin 4)).symm P) ≤
        106*179740-1+58 ∧ ∀ γ∈Γ,atJet P (extend (F.scalar γ))=0 := by
  obtain ⟨P,nz,box,active,weight,zero⟩ := exists_anchor M.word
  refine ⟨P,nz,box,active,weight,?_⟩
  intro γ hγ
  let mark := F.mark γ hγ
  have degree : (F.scalar γ).natDegree ≤ 133363 := by
    rcases mark.scalar_degree with z | h
    · simp [z]
    · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at h
      omega
  exact zero _ mark.bad.support degree mark.bad.agreement mark.scalar_hits

end
end LowAnchor6969
end Z6969Source2267

-- Source: ProximityPrize.SubmissionLower.Low6969Inventory
section Z6969Source2268
set_option autoImplicit true
set_option Elab.async false

set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
namespace LowProfile6969
noncomputable section
open Finset Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K I node)
open K1_13 (Geom extend Row Shape shape InBox atJet indexDegree OnFactor)
open K1_13_1 (anchorLead anchorLead_ne indexDegree_eq)
open Final50Price (ActiveFits)
open Final50GeoCover (activeDegree activeFits_iff)
open K1_13_1 (coeff_flatten anchorLead_term index_bounds)
open scoped BigOperators Polynomial Classical
abbrev anchorCutoff : ℕ := 106*agreement-1+58
def fullCap (top : ℕ) : Shape := ⟨142, 58, top⟩
def Fits (top : ℕ) {n : ℕ} (a : Fin n → Shape) : Prop :=
  (∀ i, K1_13_8.Valid (a i)) ∧ (∑ i, (a i).b) ≤ 142 ∧ (∑ i, (a i).j) ≤ 58 ∧
    (∑ i, (a i).t) ≤ top
def LowerRow (top : ℕ) (g : Row 3) : Prop :=
  g≠0 ∧ g.totalDegree≤142-top ∧ indexDegree g≤58-3*top ∧ TrueWeightLE g anchorCutoff
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0<(shape f).t ∧ InBox (shape f) (fullCap 15) ∧ TrueWeightLE f anchorCutoff
theorem trueWeight_iff {n D : ℕ} (P : Row n) :
    TrueWeightLE P D ↔
      ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).weightedTotalDegree
        (fun v => v.elim 1 (fun i => physicalDegree - i.val)) ≤ D := by
  classical
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  constructor
  · intro h u hu
    have hc : (P.coeff u.some).coeff (u none) ≠ 0 := by
      rw [← coeff_flatten, Finsupp.optionElim_some]
      exact MvPolynomial.mem_support_iff.mp hu
    have hm : u.some ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr (fun hz => hc (by simp [hz]))
    have hi := Polynomial.le_natDegree_of_ne_zero hc
    rw [← Finsupp.optionElim_some u, Finsupp.weight_optionElim, one_mul]
    apply (Nat.add_le_add_right hi _).trans
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using h _ hm
  · intro h m hm
    let d := (P.coeff m).natDegree
    have hc : (P.coeff m).coeff d ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    have hu : m.optionElim d ∈ ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).support :=
      MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten])
    have hb := h _ hu
    rw [Finsupp.weight_optionElim, one_mul] at hb
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hb
theorem differentialWeight_eq : differentialWeight (d := 3) physicalDegree =
    fun v => v.elim 1 (fun i => physicalDegree - i.val) := by
  funext v
  cases v <;> rfl
section FactorCover
open MvPolynomial UniqueFactorizationMonoid
theorem lower_of_anchor (P : Row 4) (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨142, 58, 15⟩) (hw : TrueWeightLE P anchorCutoff) :
    LowerRow (shape P).t (anchorLead P) := by
  refine ⟨anchorLead_ne hP, ?_, ?_, ?_⟩
  · have hb := (Euler50GeoLead.lead_degree P hP).trans hbox.1
    change (anchorLead P).totalDegree + (shape P).t ≤ 142 at hb
    change (anchorLead P).totalDegree ≤ 142 - (shape P).t
    omega
  · have hj := (Euler50GeoLead.lead_index P hP).trans hbox.2.1
    change indexDegree (anchorLead P) + 3 * (shape P).t ≤ 58 at hj
    change indexDegree (anchorLead P) ≤ 58 - 3 * (shape P).t
    omega
  · intro m hm
    obtain ⟨u, hu, hc, h⟩ := anchorLead_term P m hm
    have hle := h (fun i => physicalDegree - i.val)
    rw [← hc]
    apply (Nat.add_le_add_left _ _).trans (hw u hu)
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm, Fin.val_castSucc] using hle
theorem factor_small {P f : Row 4} (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨142, 58, 15⟩) (hw : TrueWeightLE P anchorCutoff)
    (hf : Irreducible f) (ht : 0 < (shape f).t) (hd : f ∣ P) : SmallFactor f := by
  refine ⟨hf, ht, ⟨?_, ?_, ?_⟩, ?_⟩
  · have h := weightedTotalDegree_le_of_dvd (1 : Fin 4 → ℕ) hd hP
    rw [weightedTotalDegree_one, weightedTotalDegree_one] at h
    exact h.trans hbox.1
  · have h := weightedTotalDegree_le_of_dvd (fun i => i.val) hd hP
    rw [← indexDegree_eq, ← indexDegree_eq] at h
    exact h.trans hbox.2.1
  · have h := weightedTotalDegree_le_of_dvd (Pi.single (3 : Fin 4) 1) hd hP
    simp only [weightedTotalDegree_piSingle] at h
    exact h.trans hbox.2.2
  · let e := MvPolynomial.optionEquivRight Geom (Fin 4)
    have hd' : e.symm f ∣ e.symm P := _root_.map_dvd e.symm hd
    have hP' : e.symm P ≠ 0 := fun h => hP (e.symm.injective (h.trans (map_zero _).symm))
    exact (trueWeight_iff f).mpr
      ((weightedTotalDegree_le_of_dvd _ hd' hP').trans ((trueWeight_iff P).mp hw))
end FactorCover






























































end
end LowProfile6969
end Z6969Source2268

-- Source: ProximityPrize.SubmissionLower.Low6969FatDefs
section Z6969Source2269
set_option autoImplicit true
set_option Elab.async false

-- merged module R6960Low6969FatDefs
section Merged_R6960Low6969FatDefs

set_option Elab.async false
section
namespace Low6969Fat
noncomputable section
open K1 (I K)
open K1_13 (Geom)
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
abbrev firstOrder : ℕ := 4009322
abbrev secondOrder : ℕ := 1775283
abbrev firstCut : ℕ := 5000 * 179740 - firstOrder
abbrev secondCut : ℕ := 5000 * 179740 - secondOrder
abbrev bankRank : ℕ := 633745210731502346258
def mixedWeight (a : SeedVar →₀ ℕ) : ℕ :=
  6876 * a none + 48671 * a.some.degree
theorem mixedWeight_add (a b : SeedVar →₀ ℕ) :
    mixedWeight (a + b) = mixedWeight a + mixedWeight b := by
  simp only [mixedWeight, Finsupp.add_apply, Finsupp.some_add, map_add, Nat.mul_add]
  ac_rfl
/-- The low fat chain works with rows whose seed degree is at most 24,000 in the first bank and 32,000 in the second. -/
abbrev seedCap (a : K1_13.Shape) : ℕ := if a.b = 6789 then 24000 else 32000
def Caps27 {R : Type*} [CommSemiring R] (a : K1_13.Shape) (F : SeedRow R) : Prop :=
  Caps a F ∧ seedDegree F ≤ seedCap a
def Source27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t : ℕ) (F : PhysicalRow) : Prop :=
  Source w P L a t F ∧ seedDegree F ≤ seedCap a
def HasRank27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t n : ℕ) : Prop :=
  ∃ e : Fin n → PhysicalRow, LinearIndependent Geom e ∧ ∀ i, Source27 w P L a t (e i)
abbrev commonBox : K1_13.Shape := ⟨2947, 955, 0⟩
abbrev resultantBox : K1_13.Shape := ⟨380928000, 128800000, 0⟩
structure FatEquations where
  common : K1_13.Row 3
  residual : K1_13.Row 3
  common_ne : common ≠ 0
  residual_ne : residual ≠ 0
  common_total : common.totalDegree ≤ commonBox.b
  common_index : K1_13.indexDegree common ≤ commonBox.j
  residual_total : residual.totalDegree ≤ resultantBox.b
  residual_index : K1_13.indexDegree residual ≤ resultantBox.j
structure CommonPair (F G : GenericRow) where
  fixed : Finset GenericRow
  moving : Finset GenericRow
  pure : (Polynomial GenericX)
  exponent : GenericRow → ℕ
  left : GenericRow
  right : GenericRow
  pure_ne : pure ≠ 0
  pure_degree : pure.natDegree ≤ 56000
  fixed_kind : ∀ f ∈ fixed, Irreducible f ∧ 0 < jetTotal f ∧ seedDegree f = 0
  moving_kind : ∀ f ∈ moving, Irreducible f ∧ 0 < jetTotal f ∧
    0 < seedDegree f ∧ f.degreeOf (some 2) = 0
  fixed_total : jetTotal (∏ f ∈ fixed, f) ≤ 125
  fixed_index : jetIndex (∏ f ∈ fixed, f) ≤ 42
  moving_total : jetTotal (∏ f ∈ moving, f) ≤ 17
  moving_index : jetIndex (∏ f ∈ moving, f) ≤ 5
  moving_seed : seedDegree (∏ f ∈ moving, f) ≤ 83
  left_eq : F = (pureSeed pure * (∏ f ∈ fixed, f ^ exponent f) *
    (∏ f ∈ moving, f ^ exponent f)) * left
  right_eq : G = (pureSeed pure * (∏ f ∈ fixed, f ^ exponent f) *
    (∏ f ∈ moving, f ^ exponent f)) * right
  left_ne : left ≠ 0
  right_ne : right ≠ 0
  proper : IsRelPrime left right
  left_caps : Caps27 firstBox left
  right_caps : Caps27 secondBox right
def Necessary {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P) :
    Submodule Geom PhysicalRow :=
  Submodule.span Geom {Q | ∃ t F a, Source27 w P L secondBox t F ∧
    t + mixedWeight a ≤ secondCut ∧ Q = mixedHasse a F}
def MixedOrder (F : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) (d : ℕ) : Prop :=
  ∀ a ∈ (translate (atPoint z y) F).support, d ≤ mixedWeight a
def PairOrders (F G : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) : Prop :=
  MixedOrder F z y firstOrder ∧ MixedOrder G z y secondOrder
end
end Low6969Fat
end
section
namespace Low6969Fat
noncomputable section
open K1 K1_13
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open P0_9_4 (clear_denominators)
open scoped Polynomial BigOperators
structure Messages (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) : Prop where
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, 179740 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i
def c1 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2292 →
    (∃ F, F ≠ 0 ∧ Source27 w P L firstBox firstCut F) ∧
    HasRank27 w P L secondBox secondCut bankRank
def c2 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P) (F : PhysicalRow),
    F ≠ 0 → Caps27 firstBox F → HasRank27 w P L secondBox secondCut bankRank →
    ∃ G, G ∈ Necessary w P L ∧ Nonempty (CommonPair (toGeneric F) (toGeneric G))
def c3 : Prop :=
  ∀ w Γ s, Messages w Γ s →
    ∀ (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2292 →
      (∀ F, Source27 w P L firstBox firstCut F → ∀ γ ∈ Γ,
        MixedOrder (toGeneric F) (inclConst (P.z γ)) (trajectory (extend (s γ))) firstOrder) ∧
      (∀ G ∈ Necessary w P L, ∀ γ ∈ Γ,
        MixedOrder (toGeneric G) (inclConst (P.z γ)) (trajectory (extend (s γ))) secondOrder)

abbrev fatOrder : ℕ := 21269
def Holds (E : FatEquations) (S : (Polynomial K1_13.Geom)) : Prop :=
  K1_13.atJet E.common S = 0 ∨ K1_13.OrderAt E.residual S fatOrder

def Equations : Prop :=
  ∀ (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)),
    (∀ γ ∈ Γ, (s γ).natDegree ≤ 133363) →
    (∀ γ ∈ Γ, ∃ T : Finset I, 179740 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i) →
    ∀ P : K1_13.PoleData Γ s, P.H.natDegree ≤ 2292 →
    ∃ (book : Finset K1.K) (E : FatEquations), book.card ≤ 56000 ∧
      ∀ γ ∈ Γ, γ ∉ book → Holds E (K1_13.extend (s γ))
end
end Low6969Fat
end

end Merged_R6960Low6969FatDefs
end Z6969Source2269
