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

abbrev agreement : ℕ := 179730
abbrev degree : ℕ := 133378
abbrev cutoff : ℕ := 3000 * agreement - 1
abbrev rank : ℕ := sourceRank agreement degree
abbrev need : ℕ := layerNeed agreement degree

structure Messages (w : I → K) (Γ : Finset K) (s : K → Polynomial K) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ Low6969Primary.degree
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, agreement ≤ T.card ∧
    ∀ i ∈ T, (s γ).eval (node i) = w i

theorem messages_of_family {cap u deleted Γ} (M : P1.ModelAt cap u deleted)
    (F : P1.FamilyAt agreement M Γ) (hi : M.overhead ≤ 2307) :
    Messages M.word Γ F.scalar := by
  refine ⟨F.distinct, ?_, ?_⟩
  · intro γ hγ
    obtain hzero | h := (F.mark γ hγ).scalar_degree
    · simp [hzero]
    · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at h
      change (F.scalar γ).natDegree ≤ 133378
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
    (F : P1.FamilyAt agreement M Γ) (hh : M.overhead ≤ 2307) :
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
  a.b ≤ 28 ∧ a.j ≤ 8 ∧ (4 ≤ a.j → a.b ≤ 26) ∧ (5 ≤ a.j → a.b ≤ 23) ∧
  (6 ≤ a.j → a.b ≤ 20) ∧ (7 ≤ a.j → a.b ≤ 15) ∧ (8 ≤ a.j → a.b ≤ 8)
def combined {n : ℕ} (a : Fin n → Shape) (z : Finset (Fin n)) := P3_6_8.shapeSum a z

local notation "row!" h "," len "," nxt "," v "," z =>
  P3_6_8_1.extend (n := len) (N := nxt) (y := v) (total := z) h rfl rfl rfl

private theorem reject3 : zeroMass 29 3 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b:=29) (j:=3) (m:=138) (by decide) (Or.inl (by decide))]
  have r0 : sumBelow (term 29 3) 0 = 0 := rfl
  have r1 := extend (n:=12) (N:=12) (y:=4477975520787) (total:=4477975520787) r0 rfl rfl rfl
  have r2 := extend (n:=12) (N:=24) (y:=3737583866259) (total:=8215559387046) r1 rfl rfl rfl
  have r3 := extend (n:=12) (N:=36) (y:=3069529283115) (total:=11285088670161) r2 rfl rfl rfl
  have r4 := extend (n:=12) (N:=48) (y:=2469498206427) (total:=13754586876588) r3 rfl rfl rfl
  have r5 := extend (n:=12) (N:=60) (y:=1933300802979) (total:=15687887679567) r4 rfl rfl rfl
  have r6 := extend (n:=12) (N:=72) (y:=1456870971267) (total:=17144758650834) r5 rfl rfl rfl
  have r7 := extend (n:=12) (N:=84) (y:=1036266341499) (total:=18181024992333) r6 rfl rfl rfl
  have r8 := extend (n:=12) (N:=96) (y:=667679360644) (total:=18848704352977) r7 rfl rfl rfl
  have r9 := extend (n:=12) (N:=108) (y:=350662584629) (total:=19199366937606) r8 rfl rfl rfl
  have r10 := extend (n:=12) (N:=120) (y:=112409380647) (total:=19311776318253) r9 rfl rfl rfl
  have r11 := extend (n:=12) (N:=132) (y:=10847697500) (total:=19322624015753) r10 rfl rfl rfl
  have r12 := extend (n:=6) (N:=138) (y:=42232007) (total:=19322666247760) r11 rfl rfl rfl
  rw [r12]
  decide

private theorem reject4 : zeroMass 27 4 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b:=27) (j:=4) (m:=148) (by decide) (Or.inl (by decide))]
  have r0 : sumBelow (term 27 4) 0 = 0 := rfl
  have r1 := extend (n:=12) (N:=12) (y:=4448708304028) (total:=4448708304028) r0 rfl rfl rfl
  have r2 := extend (n:=12) (N:=24) (y:=3669952574668) (total:=8118660878696) r1 rfl rfl rfl
  have r3 := extend (n:=12) (N:=36) (y:=2983874250236) (total:=11102535128932) r2 rfl rfl rfl
  have r4 := extend (n:=12) (N:=48) (y:=2383395415084) (total:=13485930544016) r3 rfl rfl rfl
  have r5 := extend (n:=12) (N:=60) (y:=1861705343836) (total:=15347635887852) r4 rfl rfl rfl
  have r6 := extend (n:=12) (N:=72) (y:=1412260501388) (total:=16759896389240) r5 rfl rfl rfl
  have r7 := extend (n:=12) (N:=84) (y:=1028784542908) (total:=17788680932148) r6 rfl rfl rfl
  have r8 := extend (n:=12) (N:=96) (y:=705268313836) (total:=18493949245984) r7 rfl rfl rfl
  have r9 := extend (n:=12) (N:=108) (y:=435977627600) (total:=18929926873584) r8 rfl rfl rfl
  have r10 := extend (n:=12) (N:=120) (y:=217512667936) (total:=19147439541520) r9 rfl rfl rfl
  have r11 := extend (n:=12) (N:=132) (y:=63845620505) (total:=19211285162025) r10 rfl rfl rfl
  have r12 := extend (n:=12) (N:=144) (y:=4896470558) (total:=19216181632583) r11 rfl rfl rfl
  have r13 := extend (n:=4) (N:=148) (y:=5416761) (total:=19216187049344) r12 rfl rfl rfl
  rw [r13]
  decide

private theorem reject5 : zeroMass 24 5 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b:=24) (j:=5) (m:=167) (by decide) (Or.inl (by decide))]
  have r0 : sumBelow (term 24 5) 0 = 0 := rfl
  have r1 := extend (n:=12) (N:=12) (y:=4428349760428) (total:=4428349760428) r0 rfl rfl rfl
  have r2 := extend (n:=12) (N:=24) (y:=3624402126232) (total:=8052751886660) r1 rfl rfl rfl
  have r3 := extend (n:=12) (N:=36) (y:=2928770873996) (total:=10981522760656) r2 rfl rfl rfl
  have r4 := extend (n:=12) (N:=48) (y:=2331664262920) (total:=13313187023576) r3 rfl rfl rfl
  have r5 := extend (n:=12) (N:=60) (y:=1823740696204) (total:=15136927719780) r4 rfl rfl rfl
  have r6 := extend (n:=12) (N:=72) (y:=1396108721048) (total:=16533036440828) r5 rfl rfl rfl
  have r7 := extend (n:=12) (N:=84) (y:=1040327028652) (total:=17573363469480) r6 rfl rfl rfl
  have r8 := extend (n:=12) (N:=96) (y:=748404454216) (total:=18321767923696) r7 rfl rfl rfl
  have r9 := extend (n:=12) (N:=108) (y:=512799976940) (total:=18834567900636) r8 rfl rfl rfl
  have r10 := extend (n:=12) (N:=120) (y:=326422720024) (total:=19160990620660) r9 rfl rfl rfl
  have r11 := extend (n:=12) (N:=132) (y:=182652280504) (total:=19343642901164) r10 rfl rfl rfl
  have r12 := extend (n:=12) (N:=144) (y:=77055882718) (total:=19420698783882) r11 rfl rfl rfl
  have r13 := extend (n:=12) (N:=156) (y:=15281570442) (total:=19435980354324) r12 rfl rfl rfl
  have r14 := extend (n:=11) (N:=167) (y:=397884432) (total:=19436378238756) r13 rfl rfl rfl
  rw [r14]
  decide

private theorem reject6 : zeroMass 21 6 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b:=21) (j:=6) (m:=191) (by decide) (Or.inl (by decide))]
  have r0 : sumBelow (term 21 6) 0 = 0 := rfl
  have r1 := extend (n:=12) (N:=12) (y:=4407555550024) (total:=4407555550024) r0 rfl rfl rfl
  have r2 := extend (n:=12) (N:=24) (y:=3576044411128) (total:=7983599961152) r1 rfl rfl rfl
  have r3 := extend (n:=12) (N:=36) (y:=2866331436904) (total:=10849931398056) r2 rfl rfl rfl
  have r4 := extend (n:=12) (N:=48) (y:=2266057390744) (total:=13115988788800) r3 rfl rfl rfl
  have r5 := extend (n:=12) (N:=60) (y:=1763516966536) (total:=14879505755336) r4 rfl rfl rfl
  have r6 := extend (n:=12) (N:=72) (y:=1347658788664) (total:=16227164544000) r5 rfl rfl rfl
  have r7 := extend (n:=12) (N:=84) (y:=1008085412008) (total:=17235249956008) r6 rfl rfl rfl
  have r8 := extend (n:=12) (N:=96) (y:=735053321944) (total:=17970303277952) r7 rfl rfl rfl
  have r9 := extend (n:=12) (N:=108) (y:=519472934344) (total:=18489776212296) r8 rfl rfl rfl
  have r10 := extend (n:=12) (N:=120) (y:=352908595576) (total:=18842684807872) r9 rfl rfl rfl
  have r11 := extend (n:=12) (N:=132) (y:=227578582504) (total:=19070263390376) r10 rfl rfl rfl
  have r12 := extend (n:=12) (N:=144) (y:=136355102488) (total:=19206618492864) r11 rfl rfl rfl
  have r13 := extend (n:=12) (N:=156) (y:=72764293384) (total:=19279382786248) r12 rfl rfl rfl
  have r14 := extend (n:=12) (N:=168) (y:=31021519144) (total:=19310404305392) r13 rfl rfl rfl
  have r15 := extend (n:=12) (N:=180) (y:=7203309307) (total:=19317607614699) r14 rfl rfl rfl
  have r16 := extend (n:=11) (N:=191) (y:=222068622) (total:=19317829683321) r15 rfl rfl rfl
  rw [r16]
  decide

private theorem reject7 : zeroMass 16 7 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b:=16) (j:=7) (m:=235) (by decide) (Or.inr rfl)]
  have r0 : sumBelow (term 16 7) 0 = 0 := rfl
  have r1 := extend (n:=12) (N:=12) (y:=4403937022179) (total:=4403937022179) r0 rfl rfl rfl
  have r2 := extend (n:=12) (N:=24) (y:=3568363723539) (total:=7972300745718) r1 rfl rfl rfl
  have r3 := extend (n:=12) (N:=36) (y:=2857725950803) (total:=10830026696521) r2 rfl rfl rfl
  have r4 := extend (n:=12) (N:=48) (y:=2258903862243) (total:=13088930558764) r3 rfl rfl rfl
  have r5 := extend (n:=12) (N:=60) (y:=1759505456643) (total:=14848436015407) r4 rfl rfl rfl
  have r6 := extend (n:=12) (N:=72) (y:=1347866573299) (total:=16196302588706) r5 rfl rfl rfl
  have r7 := extend (n:=12) (N:=84) (y:=1013050892019) (total:=17209353480725) r6 rfl rfl rfl
  have r8 := extend (n:=12) (N:=96) (y:=744849933123) (total:=17954203413848) r7 rfl rfl rfl
  have r9 := extend (n:=12) (N:=108) (y:=533783057443) (total:=18487986471291) r8 rfl rfl rfl
  have r10 := extend (n:=12) (N:=120) (y:=371097466323) (total:=18859083937614) r9 rfl rfl rfl
  have r11 := extend (n:=12) (N:=132) (y:=248768201619) (total:=19107852139233) r10 rfl rfl rfl
  have r12 := extend (n:=12) (N:=144) (y:=159498145699) (total:=19267350284932) r11 rfl rfl rfl
  have r13 := extend (n:=12) (N:=156) (y:=96718021443) (total:=19364068306375) r12 rfl rfl rfl
  have r14 := extend (n:=12) (N:=168) (y:=54586392243) (total:=19418654698618) r13 rfl rfl rfl
  have r15 := extend (n:=12) (N:=180) (y:=27989662003) (total:=19446644360621) r14 rfl rfl rfl
  have r16 := extend (n:=12) (N:=192) (y:=12542075139) (total:=19459186435760) r15 rfl rfl rfl
  have r17 := extend (n:=12) (N:=204) (y:=4585716579) (total:=19463772152339) r16 rfl rfl rfl
  have r18 := extend (n:=12) (N:=216) (y:=1190511763) (total:=19464962664102) r17 rfl rfl rfl
  have r19 := extend (n:=12) (N:=228) (y:=154226643) (total:=19465116890745) r18 rfl rfl rfl
  have r20 := extend (n:=7) (N:=235) (y:=2616445) (total:=19465119507190) r19 rfl rfl rfl
  rw [r20]
  decide

private theorem reject8 : zeroMass 9 8 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b:=9) (j:=8) (m:=206) (by decide) (Or.inr rfl)]
  have r0 : sumBelow (term 9 8) 0 = 0 := rfl
  have r1 := extend (n:=12) (N:=12) (y:=4416692946778) (total:=4416692946778) r0 rfl rfl rfl
  have r2 := extend (n:=12) (N:=24) (y:=3596722857258) (total:=8013415804036) r1 rfl rfl rfl
  have r3 := extend (n:=12) (N:=36) (y:=2892292320762) (total:=10905708124798) r2 rfl rfl rfl
  have r4 := extend (n:=12) (N:=48) (y:=2292711993802) (total:=13198420118600) r3 rfl rfl rfl
  have r5 := extend (n:=12) (N:=60) (y:=1787745517722) (total:=14986165636322) r4 rfl rfl rfl
  have r6 := extend (n:=12) (N:=72) (y:=1367609518698) (total:=16353775155020) r5 rfl rfl rfl
  have r7 := extend (n:=12) (N:=84) (y:=1022973607738) (total:=17376748762758) r6 rfl rfl rfl
  have r8 := extend (n:=12) (N:=96) (y:=744960380682) (total:=18121709143440) r7 rfl rfl rfl
  have r9 := extend (n:=12) (N:=108) (y:=525145418202) (total:=18646854561642) r8 rfl rfl rfl
  have r10 := extend (n:=12) (N:=120) (y:=355557285802) (total:=19002411847444) r9 rfl rfl rfl
  have r11 := extend (n:=12) (N:=132) (y:=228677533818) (total:=19231089381262) r10 rfl rfl rfl
  have r12 := extend (n:=12) (N:=144) (y:=137440697418) (total:=19368530078680) r11 rfl rfl rfl
  have r13 := extend (n:=12) (N:=156) (y:=75234296602) (total:=19443764375282) r12 rfl rfl rfl
  have r14 := extend (n:=12) (N:=168) (y:=35898836202) (total:=19479663211484) r13 rfl rfl rfl
  have r15 := extend (n:=12) (N:=180) (y:=13727805882) (total:=19493391017366) r14 rfl rfl rfl
  have r16 := extend (n:=12) (N:=192) (y:=3467680138) (total:=19496858697504) r15 rfl rfl rfl
  have r17 := extend (n:=12) (N:=204) (y:=317918298) (total:=19497176615802) r16 rfl rfl rfl
  have r18 := extend (n:=2) (N:=206) (y:=153575) (total:=19497176769377) r17 rfl rfl rfl
  rw [r18]
  decide

private theorem reject9 : zeroMass 3 9 < layerNeed := by
  rw [P3_6_8_1.mass_eq (b:=3) (j:=9) (m:=183) (by decide) (Or.inr rfl)]
  have r0 : sumBelow (term 3 9) 0 = 0 := rfl
  have r1 := extend (n:=12) (N:=12) (y:=4419454632432) (total:=4419454632432) r0 rfl rfl rfl
  have r2 := extend (n:=12) (N:=24) (y:=3596534841372) (total:=8015989473804) r1 rfl rfl rfl
  have r3 := extend (n:=12) (N:=36) (y:=2880841206984) (total:=10896830680788) r2 rfl rfl rfl
  have r4 := extend (n:=12) (N:=48) (y:=2265453291444) (total:=13162283972232) r3 rfl rfl rfl
  have r5 := extend (n:=12) (N:=60) (y:=1743314608032) (total:=14905598580264) r4 rfl rfl rfl
  have r6 := extend (n:=12) (N:=72) (y:=1307232621132) (total:=16212831201396) r5 rfl rfl rfl
  have r7 := extend (n:=12) (N:=84) (y:=949878746232) (total:=17162709947628) r6 rfl rfl rfl
  have r8 := extend (n:=12) (N:=96) (y:=663788349924) (total:=17826498297552) r7 rfl rfl rfl
  have r9 := extend (n:=12) (N:=108) (y:=441360749904) (total:=18267859047456) r8 rfl rfl rfl
  have r10 := extend (n:=12) (N:=120) (y:=274859214972) (total:=18542718262428) r9 rfl rfl rfl
  have r11 := extend (n:=12) (N:=132) (y:=156410965032) (total:=18699129227460) r10 rfl rfl rfl
  have r12 := extend (n:=12) (N:=144) (y:=78007171092) (total:=18777136398552) r11 rfl rfl rfl
  have r13 := extend (n:=12) (N:=156) (y:=31502955264) (total:=18808639353816) r12 rfl rfl rfl
  have r14 := extend (n:=12) (N:=168) (y:=8617390764) (total:=18817256744580) r13 rfl rfl rfl
  have r15 := extend (n:=12) (N:=180) (y:=933501912) (total:=18818190246492) r14 rfl rfl rfl
  have r16 := extend (n:=3) (N:=183) (y:=1782176) (total:=18818192028668) r15 rfl rfl rfl
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
abbrev anchorCutoff : ℕ := 107*agreement-1+60
def fullCap (top : ℕ) : Shape := ⟨143, 60, top⟩
def Fits (top : ℕ) {n : ℕ} (a : Fin n → Shape) : Prop :=
  (∀ i, K1_13_8.Valid (a i)) ∧ (∑ i, (a i).b) ≤ 143 ∧ (∑ i, (a i).j) ≤ 60 ∧
    (∑ i, (a i).t) ≤ top
def LowerRow (top : ℕ) (g : Row 3) : Prop :=
  g≠0 ∧ g.totalDegree≤143-top ∧ indexDegree g≤60-3*top ∧ TrueWeightLE g anchorCutoff
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0<(shape f).t ∧ InBox (shape f) (fullCap 16) ∧ TrueWeightLE f anchorCutoff
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
    (hbox : InBox (shape P) ⟨143, 60, 16⟩) (hw : TrueWeightLE P anchorCutoff) :
    LowerRow (shape P).t (anchorLead P) := by
  refine ⟨anchorLead_ne hP, ?_, ?_, ?_⟩
  · have hb := (Euler50GeoLead.lead_degree P hP).trans hbox.1
    change (anchorLead P).totalDegree + (shape P).t ≤ 143 at hb
    change (anchorLead P).totalDegree ≤ 143 - (shape P).t
    omega
  · have hj := (Euler50GeoLead.lead_index P hP).trans hbox.2.1
    change indexDegree (anchorLead P) + 3 * (shape P).t ≤ 60 at hj
    change indexDegree (anchorLead P) ≤ 60 - 3 * (shape P).t
    omega
  · intro m hm
    obtain ⟨u, hu, hc, h⟩ := anchorLead_term P m hm
    have hle := h (fun i => physicalDegree - i.val)
    rw [← hc]
    apply (Nat.add_le_add_left _ _).trans (hw u hu)
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm, Fin.val_castSucc] using hle
theorem factor_small {P f : Row 4} (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨143, 60, 16⟩) (hw : TrueWeightLE P anchorCutoff)
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
abbrev firstOrder : ℕ := 3975818
abbrev secondOrder : ℕ := 1815862
abbrev firstCut : ℕ := 5000 * 179730 - firstOrder
abbrev secondCut : ℕ := 5000 * 179730 - secondOrder
abbrev bankRank : ℕ := 701329375673955677026
def mixedWeight (a : SeedVar →₀ ℕ) : ℕ :=
  6921 * a none + 48661 * a.some.degree
theorem mixedWeight_add (a b : SeedVar →₀ ℕ) :
    mixedWeight (a + b) = mixedWeight a + mixedWeight b := by
  simp only [mixedWeight, Finsupp.add_apply, Finsupp.some_add, map_add, Nat.mul_add]
  ac_rfl
/-- The low fat chain works with rows whose seed degree is at most 24,000 in the first bank and 32,000 in the second. -/
abbrev seedCap (a : K1_13.Shape) : ℕ := if a.b = 6789 then 24400 else 35200
def Caps27 {R : Type*} [CommSemiring R] (a : K1_13.Shape) (F : SeedRow R) : Prop :=
  Caps a F ∧ seedDegree F ≤ seedCap a
def Source27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t : ℕ) (F : PhysicalRow) : Prop :=
  Source w P L a t F ∧ seedDegree F ≤ seedCap a
def HasRank27 {Γ s} (w : I → K) (P : K1_13.PoleData Γ s) (L : ResidueChart P)
    (a : K1_13.Shape) (t n : ℕ) : Prop :=
  ∃ e : Fin n → PhysicalRow, LinearIndependent Geom e ∧ ∀ i, Source27 w P L a t (e i)
abbrev commonBox : K1_13.Shape := ⟨682, 239, 0⟩
abbrev resultantBox : K1_13.Shape := ⟨405380800, 137080000, 0⟩
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
  pure_degree : pure.natDegree ≤ 59600
  fixed_kind : ∀ f ∈ fixed, Irreducible f ∧ 0 < jetTotal f ∧ seedDegree f = 0
  moving_kind : ∀ f ∈ moving, Irreducible f ∧ 0 < jetTotal f ∧
    0 < seedDegree f ∧ f.degreeOf (some 2) = 0
  fixed_total : jetTotal (∏ f ∈ fixed, f) ≤ 52
  fixed_index : jetIndex (∏ f ∈ fixed, f) ≤ 14
  moving_total : jetTotal (∏ f ∈ moving, f) ≤ 7
  moving_index : jetIndex (∏ f ∈ moving, f) ≤ 2
  moving_seed : seedDegree (∏ f ∈ moving, f) ≤ 45
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
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, 179730 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i
def c1 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2307 →
    (∃ F, F ≠ 0 ∧ Source27 w P L firstBox firstCut F) ∧
    HasRank27 w P L secondBox secondCut bankRank
def c2 : Prop :=
  ∀ w Γ s (P : PoleData Γ s) (L : ResidueChart P) (F : PhysicalRow),
    F ≠ 0 → Caps27 firstBox F → HasRank27 w P L secondBox secondCut bankRank →
    ∃ G, G ∈ Necessary w P L ∧ Nonempty (CommonPair (toGeneric F) (toGeneric G))
def c3 : Prop :=
  ∀ w Γ s, Messages w Γ s →
    ∀ (P : PoleData Γ s) (L : ResidueChart P), P.H.natDegree ≤ 2307 →
      (∀ F, Source27 w P L firstBox firstCut F → ∀ γ ∈ Γ,
        MixedOrder (toGeneric F) (inclConst (P.z γ)) (trajectory (extend (s γ))) firstOrder) ∧
      (∀ G ∈ Necessary w P L, ∀ γ ∈ Γ,
        MixedOrder (toGeneric G) (inclConst (P.z γ)) (trajectory (extend (s γ))) secondOrder)

abbrev fatOrder : ℕ := 21437
def Holds (E : FatEquations) (S : (Polynomial K1_13.Geom)) : Prop :=
  K1_13.atJet E.common S = 0 ∨ K1_13.OrderAt E.residual S fatOrder

def Equations : Prop :=
  ∀ (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)),
    (∀ γ ∈ Γ, (s γ).natDegree ≤ 133378) →
    (∀ γ ∈ Γ, ∃ T : Finset I, 179730 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i) →
    ∀ P : K1_13.PoleData Γ s, P.H.natDegree ≤ 2307 →
    ∃ (book : Finset K1.K) (E : FatEquations), book.card ≤ 59600 ∧
      ∀ γ ∈ Γ, γ ∉ book → Holds E (K1_13.extend (s γ))
end
end Low6969Fat
end

end Merged_R6960Low6969FatDefs
end Z6969Source2269
