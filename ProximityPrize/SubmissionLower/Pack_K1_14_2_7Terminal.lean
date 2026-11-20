import Mathlib.Algebra.Polynomial.Monic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.MvPolynomial.Basic
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast029
set_option Elab.async false

section PackSource_K1_14_2_7Cutoffs
set_option autoImplicit true
namespace K1_14_2_7

noncomputable section

open K1_14 K1_14_2 Polynomial Finset
open scoped BigOperators

def top : ℕ := full.m * 180236

def width (h q j : ℕ) : ℕ := top + j - q * (131071 - h)

/-- With `k` distinct Y ordinates the forced V order of a row is at most one `k`-th of its
inner grade, so each grade costs `j + (q-j)/k` contact steps. -/
def contactBudget (k q j : ℕ) : ℕ := j + (q - j) / k

def loss (k h q j : ℕ) : ℕ := width h q j - 2*h*contactBudget k q j

private def eligible (k h W q j : ℕ) : Prop :=
  q * (131071-h) ≤ W+j ∧ top ≤ W+2*h*contactBudget k q j

private instance (k h W q j : ℕ) : Decidable (eligible k h W q j) := by
  unfold eligible
  infer_instance

private def positions (k h W : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  ((range (full.B+1)).sigma (fun q => range (min q full.J+1))).filter
    (fun a => eligible k h W a.1 a.2)

private theorem mem_positions (k h W q j : ℕ) :
    (⟨q,j⟩ : Σ _ : ℕ, ℕ) ∈ positions k h W ↔
      q ≤ full.B ∧ j ≤ min q full.J ∧ eligible k h W q j := by
  simp [positions, and_assoc]

private theorem seed_finrank (U : ℕ) :
    Module.finrank FX (MvPolynomial.restrictTotalDegree (Fin 2) FX U) = triangle U := by
  rw [MvPolynomial.restrictTotalDegree,
    Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport FX _),
    Nat.card_coe_set_eq]
  change {e : Fin 2 →₀ ℕ | e.degree ≤ U}.ncard = triangle U
  rw [Finsupp.ncard_setOf_degree_le]
  simp [triangle, Nat.choose_two_right, Nat.mul_comm (U+2)]

private theorem forced_at_full (w : ℤ) (hw : w ≤ 3554) (W j : ℕ) :
    forcedPower w W j = 1 + (top-1-W)/(2*w.toNat)-j := by
  have hm : (band w).multiplicity = full.m := by
    unfold band
    split_ifs <;> rfl
  unfold forcedPower top
  rw [hm]

set_option maxRecDepth 12000 in
/-- Projection to eligible coefficient positions is injective because every
nonzero row has its leading position in the projection. -/
private theorem cutoff_rank_le (k : ℕ) (hk : 0 < k) (w : ℤ) (hlo : 1 ≤ w) (hhi : w ≤ 3554)
    (W : ℕ) (hW : W < top) (V : Submodule FX Jet)
    {f : Equation} (hf : k ≤ f.natDegree)
    (hshape : ∀ P ∈ V, ∀ j i, (P.coeff j).coeff i ≠ 0 →
      i+j ≤ full.B ∧ j ≤ full.J ∧ ((P.coeff j).coeff i).totalDegree ≤ full.U)
    (hwidth : ∀ P ∈ V, P ≠ 0 →
      (P.leadingCoeff.natDegree + P.natDegree) * (131071-w.toNat) ≤ W+P.natDegree)
    (hdiv : ∀ P ∈ V, P ≠ 0 → f ^ forcedPower w W P.natDegree ∣ P.leadingCoeff) :
    Module.finrank FX V ≤ (positions k w.toNat W).card * triangle full.U := by
  classical
  let S := positions k w.toNat W
  let T := MvPolynomial.restrictTotalDegree (Fin 2) FX full.U
  let coord (a : S) : V →ₗ[FX] Seeds :=
    (((lcoeff Seeds (a.1.1-a.1.2)).restrictScalars FX).comp
      ((lcoeff Equation a.1.2).restrictScalars FX)).comp V.subtype
  let proj : V →ₗ[FX] S → T := LinearMap.pi fun a => (coord a).codRestrict T (by
    intro P
    change (P.1.coeff a.1.2).coeff (a.1.1-a.1.2) ∈ T
    apply (MvPolynomial.mem_restrictTotalDegree _ _ _).2
    by_cases hz : (P.1.coeff a.1.2).coeff (a.1.1-a.1.2) = 0
    · simp [hz]
    · exact (hshape P.1 P.2 _ _ hz).2.2)
  have hzero : ∀ P : V, proj P = 0 → P = 0 := by
    intro P hP
    apply Subtype.ext
    by_contra hne
    let j := P.1.natDegree
    let i := P.1.leadingCoeff.natDegree
    have hcoef : (P.1.coeff j).coeff i ≠ 0 :=
      leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hne)
    obtain ⟨hB, hJ, _⟩ := hshape P.1 P.2 j i hcoef
    have hdvd := hdiv P.1 P.2 hne
    -- Specialize the exponent before taking degrees to keep kernel replay small.
    rw [forced_at_full w hhi W] at hdvd
    have hd := natDegree_le_of_dvd hdvd (leadingCoeff_ne_zero.mpr hne)
    rw [natDegree_pow] at hd
    have hpower : 1 + (top-1-W)/(2*w.toNat)-j ≤ i/k := by
      apply (Nat.le_div_iff_mul_le hk).2
      exact (Nat.mul_le_mul_left _ hf).trans hd
    have hstep : 0 < 2*w.toNat := by omega
    have hcontact : top ≤ W+2*w.toNat*(j+i/k) := by
      by_contra! hc
      have hh := (Nat.le_div_iff_mul_le hstep).2
        (show (j+i/k)*(2*w.toNat) ≤ top-1-W by
          rw [mul_comm]
          omega)
      omega
    have hb : eligible k w.toNat W (i+j) j := by
      refine ⟨hwidth P.1 P.2 hne, ?_⟩
      unfold contactBudget
      rw [Nat.add_sub_cancel]
      exact hcontact
    have hjq : j ≤ i+j := Nat.le_add_left j i
    have ha : (⟨i+j,j⟩ : Σ _ : ℕ, ℕ) ∈ S := by
      change (⟨i+j,j⟩ : Σ _ : ℕ, ℕ) ∈ positions k w.toNat W
      rw [mem_positions]
      exact ⟨hB, le_min hjq hJ, hb⟩
    let a : S := ⟨⟨i+j,j⟩, ha⟩
    have hz := congrArg (fun v : S → T => (v a : Seeds)) hP
    change (P.1.coeff j).coeff (i+j-j) = 0 at hz
    exact hcoef (by simpa using hz)
  have hinj : Function.Injective proj := by
    intro P Q heq
    let D : V := P + (-1 : FX) • Q
    have hD : proj D = 0 := calc
      _ = proj P + (-1 : FX) • proj Q := by
        change proj (P + (-1 : FX) • Q) = _
        rw [map_add, map_smul]
      _ = ((1 : FX) + -1) • proj Q := by rw [add_smul, one_smul, heq]
      _ = 0 := by rw [add_neg_cancel, zero_smul]
    have h := congrArg Subtype.val (hzero D hD)
    change P.1 + (-1 : FX) • Q.1 = (0 : Jet) at h
    have hneg : Q.1 + (-1 : FX) • Q.1 = 0 := calc
      _ = ((1 : FX) + -1) • Q.1 := by rw [add_smul, one_smul]
      _ = 0 := by rw [add_neg_cancel, zero_smul]
    have he := congrArg (fun r : Jet => r + Q.1) h
    rw [add_assoc, add_comm ((-1 : FX) • Q.1), hneg, add_zero, zero_add] at he
    exact Subtype.ext he
  calc
    _ ≤ Module.finrank FX (S → T) := LinearMap.finrank_le_finrank_of_injective hinj
    _ = _ := by
      let : Module.Free FX T := Module.Free.of_basis (MvPolynomial.basisRestrictSupport FX _)
      rw [Module.finrank_pi_fintype FX (M := fun _ : S => T)]
      simp [T, S, seed_finrank]

private theorem positions_card (k h W : ℕ) :
    (positions k h W).card = shapeSum full (fun q j => if eligible k h W q j then 1 else 0) := by
  unfold positions shapeSum
  rw [card_filter, sum_sigma]

private theorem position_count (k h q j : ℕ) (hj : j ≤ q * (131071-h)) :
    (∑ W ∈ range top, if eligible k h W q j then 1 else 0) + loss k h q j = width h q j := by
  let t := q * (131071-h)
  let d := 2*h*contactBudget k q j
  have hI : (range top).filter (fun W => eligible k h W q j) =
      Ico (max (t-j) (top-d)) top := by
    apply Finset.ext
    intro W
    rw [Finset.mem_filter, mem_range, mem_Ico, max_le_iff]
    change (W < top ∧ t ≤ W+j ∧ top ≤ W+d) ↔
      ((t-j ≤ W ∧ top-d ≤ W) ∧ W < top)
    have ht : j ≤ t := hj
    omega
  rw [← card_filter, hI, Nat.card_Ico]
  change top - max (t-j) (top-d) + (top+j-t-d) = top+j-t
  omega

/-- The telescope loses the early cutoff interval at each eligible jet position. -/
theorem rank_add_loss_le (k : ℕ) (hk : 0 < k) (w : ℤ) (hlo : 1 ≤ w) (hhi : w ≤ 3554)
    {u del} {M : K1.AnchorModel u del} {Γ} {F : K1.AnchoredFamily M Γ}
    (hw : M.overhead = w) {rows : Banks} (hr : JetSource M F rows)
    (hs : full ∈ scheduled w) {f : Equation} (hf : k ≤ f.natDegree)
    (hd : FullDivisibility w rows f) :
    (∑ W ∈ range top, Module.finrank FX (rows full W)) +
        triangle full.U * shapeSum full (loss k w.toNat) ≤
      triangle full.U * shapeSum full (width w.toNat) := by
  have hceil :
      (∑ W ∈ range top, Module.finrank FX (rows full W)) ≤
        ∑ W ∈ range top, (positions k w.toNat W).card * triangle full.U := by
    apply sum_le_sum
    intro W hW
    have hscheduled : full ∈ scheduled M.overhead := by simpa only [hw] using hs
    exact cutoff_rank_le k hk w hlo hhi W (mem_range.mp hW) _ hf
      (hr.shape full hscheduled W) (by simpa only [hw] using hr.leading full hscheduled W)
      (hd W (mem_range.mp hW))
  apply (Nat.add_le_add_right hceil _).trans
  simp_rw [positions_card]
  rw [← sum_mul, mul_comm _ (triangle full.U), ← mul_add]
  apply Nat.mul_le_mul_left
  have hswap (g : ℕ → ℕ → ℕ → ℕ) :
      (∑ W ∈ range top, shapeSum full (g W)) =
        shapeSum full (fun q j => ∑ W ∈ range top, g W q j) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  rw [hswap]
  unfold shapeSum
  simp only [← sum_add_distrib]
  apply sum_le_sum
  intro q _
  apply sum_le_sum
  intro j hj
  have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
  have hk' : 1 ≤ 131071-w.toNat := by omega
  have hjk : j ≤ q*(131071-w.toNat) := hjq.trans (by
    simpa using Nat.mul_le_mul_left q hk')
  exact (position_count k w.toNat q j hjk).le

end
end K1_14_2_7
end PackSource_K1_14_2_7Cutoffs

section PackSource_K1_14_2_7Arithmetic
set_option autoImplicit true
namespace K1_14_2_7

open K1_14 K1_14_2 Finset
open scoped BigOperators

private theorem sum_progression (n : ℕ) (a d : ℤ) :
    (∑ j ∈ range n, (a-2*d*(j : ℤ))) = (n : ℤ)*(a-d*((n : ℤ)-1)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, Nat.cast_succ]; ring

/-- `k` times the lost width, with the floor in the contact budget replaced by its
rational upper bound `(q + (k-1) j)/k`. -/
private def signedWidth (k : ℕ) (h : ℤ) (q j : ℕ) : ℤ :=
  (k : ℤ)*((top : ℤ)+j-131071*(q : ℤ)) + h*(((k : ℤ)-2)*(q : ℤ)-2*((k : ℤ)-1)*(j : ℤ))

private theorem signed_le_loss (k h q j : ℕ) (hh : h ≤ 131071) (hj : j ≤ q) :
    signedWidth k h q j ≤ (k : ℤ)*(loss k h q j : ℤ) := by
  have cast_sub_le (a b : ℕ) : (a : ℤ) - b ≤ ((a-b : ℕ) : ℤ) := by omega
  have hraw := cast_sub_le (top+j) (q*(131071-h))
  have hloss := cast_sub_le (width h q j) (2*h*contactBudget k q j)
  have hdiv : k*((q-j)/k) ≤ q-j := Nat.mul_div_le _ _
  have hbudget : (k : ℤ)*(contactBudget k q j : ℤ) ≤ ((k : ℤ)-1)*(j : ℤ)+(q : ℤ) := by
    unfold contactBudget
    generalize (q - j) / k = m at hdiv ⊢
    have h := Int.ofNat_le.mpr hdiv
    push_cast [Nat.cast_sub hj] at h ⊢
    linarith only [h]
  have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  have hh0 : (0 : ℤ) ≤ 2*(h : ℤ) := by positivity
  push_cast [Nat.cast_sub hh] at hraw hloss
  change _ ≤ (width h q j : ℤ) at hraw
  change _ ≤ (loss k h q j : ℤ) at hloss
  have e1 := mul_le_mul_of_nonneg_left hraw hk0
  have e2 := mul_le_mul_of_nonneg_left hloss hk0
  have e3 := mul_le_mul_of_nonneg_left hbudget hh0
  unfold signedWidth
  linarith only [e1, e2, e3]

/-- The number of grades at each `q` whose signed width is kept: those positive at the base
height `b` (any choice is sound; this one maximises the base value). -/
private def supportCount (k b q : ℕ) : ℕ :=
  min (min q full.J+1)
    ((k*top + (2*(k-1)*b-k) - 1 - (k*131071-(k-2)*b)*q)/(2*(k-1)*b-k))

private def block (k : ℕ) (h : ℤ) (b q : ℕ) : ℤ :=
  let n : ℤ := supportCount k b q
  n*(2*signedWidth k h q 0 - (2*((k : ℤ)-1)*h-k)*(n-1))

private def blockSlope (k b q : ℕ) : ℤ :=
  let n : ℤ := supportCount k b q
  n*(2*((k : ℤ)-2)*(q : ℤ)-2*((k : ℤ)-1)*(n-1))

private def supportBase (k b : ℕ) : ℤ := ∑ q ∈ range (full.B+1), block k b b q

private def supportSlope (k b : ℕ) : ℤ := ∑ q ∈ range (full.B+1), blockSlope k b q

private theorem block_eq_sum (k : ℕ) (h : ℤ) (b q : ℕ) :
    block k h b q = ∑ j ∈ range (supportCount k b q), 2*signedWidth k h q j := by
  calc
    _ = ∑ j ∈ range (supportCount k b q),
      (2*signedWidth k h q 0 - 2*(2*((k : ℤ)-1)*h-k)*(j : ℤ)) := by
      rw [sum_progression]
      rfl
    _ = _ := by
      apply sum_congr rfl
      intro j _
      unfold signedWidth
      ring

private theorem support_le_loss (k b h : ℕ) (hh : h ≤ 131071) :
    supportBase k b + ((h : ℤ)-b)*supportSlope k b ≤
      2*(k : ℤ)*(shapeSum full (loss k h) : ℤ) := by
  have haffine (q : ℕ) : block k b b q + ((h : ℤ)-b)*blockSlope k b q = block k h b q := by
    unfold block blockSlope signedWidth
    ring
  unfold supportBase supportSlope shapeSum
  push_cast
  simp only [mul_sum, ← sum_add_distrib, haffine]
  apply sum_le_sum
  intro q _
  rw [block_eq_sum]
  have hsub : range (supportCount k b q) ⊆ range (min q full.J+1) :=
    range_mono (min_le_left _ _)
  calc
    _ ≤ ∑ j ∈ range (supportCount k b q), 2*(k : ℤ)*(loss k h q j : ℤ) := by
      apply sum_le_sum
      intro j hj
      have hjq : j ≤ q := by
        have hj' := mem_range.mp (hsub hj)
        omega
      have hs := signed_le_loss k h q j hh hjq
      linarith only [hs]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)

private def nodeRow (k d : ℕ) : ℕ :=
  let n := min k ((d+1)/2)
  n*(d+1-n)

private theorem node_row (k d : ℕ) : (∑ i ∈ range k, (d-2*i)) = nodeRow k d := by
  unfold nodeRow
  let n := min k ((d+1)/2)
  have hnk : n ≤ k := min_le_left _ _
  have hnd : n ≤ (d+1)/2 := min_le_right _ _
  have hreduce : (∑ i ∈ range k, (d-2*i)) = ∑ i ∈ range n, (d-2*i) := by
    symm
    apply sum_subset (range_mono hnk)
    intro i hi hni
    simp only [mem_range, not_lt] at hi hni
    have hi' : (d+1)/2 ≤ i := by unfold n at hni; omega
    omega
  have hcast : ((∑ i ∈ range n, (d-2*i) : ℕ) : ℤ) =
      ∑ i ∈ range n, ((d : ℤ)-2*(i : ℤ)) := by
    rw [Nat.cast_sum]
    apply sum_congr rfl
    intro i hi
    have hit := mem_range.mp hi
    rw [Nat.cast_sub (by omega : 2*i ≤ d)]
    push_cast
    rfl
  have hc := sum_progression n (d : ℤ) 1
  simp only [mul_one, one_mul] at hc
  have hn : n ≤ d+1 := by omega
  apply Int.ofNat_inj.mp
  rw [hreduce, hcast, hc]
  change _ = (↑(n*(d+1-n)) : ℤ)
  push_cast [Nat.cast_sub hn]
  ring

private def physicalDebit : ℕ :=
  triangle full.U * 262144 * ∑ q ∈ range (full.B+1),
    nodeRow (min q full.J+1) (full.m+min q full.J-q)

private def poleDebitSlope : ℕ :=
  2*(full.U+1) * ∑ q ∈ range (full.B+1), (min q full.J+1)*((full.B+full.J-q)*(full.B-q))

private theorem debit_eq (h : ℕ) :
    sourceDebit h full = physicalDebit + h*poleDebitSlope := by
  have hnode : shapeSum full (fun q i => full.m+min q full.J-(q+2*i)) =
      ∑ q ∈ range (full.B+1),
        nodeRow (min q full.J+1) (full.m+min q full.J-q) := by
    unfold shapeSum
    apply sum_congr rfl
    intro q _
    simpa only [Nat.sub_sub] using node_row (min q full.J+1) (full.m+min q full.J-q)
  have hpole : shapeSum full (fun q _ => (full.B+full.J-q)*(full.B-q)) =
      ∑ q ∈ range (full.B+1), (min q full.J+1)*((full.B+full.J-q)*(full.B-q)) := by
    unfold shapeSum
    simp only [sum_const, card_range, Nat.nsmul_eq_mul]
  unfold sourceDebit physicalDebit poleDebitSlope
  rw [hnode, hpole, ← Nat.mul_assoc h (2*(full.U+1)), ← Nat.mul_assoc h 2, Nat.mul_comm h 2]

/-- The kernel-checked supporting line of the `k`-ordinate loss at base height `b`. -/
def SupportCheck (k b : ℕ) : Prop :=
  2*(k : ℤ)*((physicalDebit : ℤ)+b*(poleDebitSlope : ℤ)) <
      (triangle full.U : ℤ)*supportBase k b ∧
    2*(k : ℤ)*(poleDebitSlope : ℤ) ≤ (triangle full.U : ℤ)*supportSlope k b

/-- The `k`-ordinate loss exceeds the actual source debits from the base height up. -/
theorem debit_lt_loss (k b : ℕ) (hk : 0 < k) (hc : SupportCheck k b) (h : ℕ) (hlo : b ≤ h)
    (hhi : h ≤ 131071) :
    sourceDebit h full < triangle full.U * shapeSum full (loss k h) := by
  rw [debit_eq]
  have hs := mul_le_mul_of_nonneg_left (support_le_loss k b h hhi)
    (show 0 ≤ (triangle full.U : ℤ) by positivity)
  have hi := mul_le_mul_of_nonneg_left hc.2
    (show 0 ≤ (h : ℤ)-b by omega)
  have hk2 : (0 : ℤ) < 2*(k : ℤ) := by omega
  have hz : 2*(k : ℤ)*((physicalDebit + h*poleDebitSlope : ℕ) : ℤ) <
      2*(k : ℤ)*((↑(triangle full.U * shapeSum full (loss k h)) : ℤ)) := by
    push_cast
    nlinarith only [hs, hi, hc.1]
  exact_mod_cast lt_of_mul_lt_mul_left hz hk2.le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Band 0, [2564, 2600]: seven distinct Y values. -/
theorem support_check_seven : SupportCheck 7 2564 := by
  unfold SupportCheck
  constructor <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Band 1, [2601, 3554]: six distinct Y values. -/
theorem support_check_six : SupportCheck 6 2601 := by
  unfold SupportCheck
  constructor <;> decide +kernel

end K1_14_2_7
end PackSource_K1_14_2_7Arithmetic

section PackSource_K1_14_2_7Proof
set_option autoImplicit true
namespace K1_14_2_7

open K1_14 K1_14_2 Finset
open scoped BigOperators

/-- A full terminal bank with the source floor cannot support a projected equation of
Y-degree at least `k` with all the forced leading-coefficient divisibilities, from any
base height `b` whose supporting line is checked. -/
theorem degree_lt (k b : ℕ) (hk : 0 < k) (hc : SupportCheck k b) (hb : 1 ≤ b)
    (hguard : full.B * (131071 - b) ≤ top)
    {u del} {M : K1.AnchorModel u del} {Γ} {F : K1.AnchoredFamily M Γ}
    (hlo : (b : ℤ) ≤ M.overhead) (hhi : M.overhead ≤ 3554)
    {rows : Banks} (hr : JetSource M F rows) {f : Equation}
    (hd : FullDivisibility M.overhead rows f) : f.natDegree < k := by
  by_contra! hlarge
  have hs : full ∈ scheduled M.overhead := by simp [scheduled, full, hhi]
  have htop : 0 < top := by decide
  have hcut : top-1+1 = top := by omega
  have hfloor := hr.floor_bound full hs (top-1) (by
    change top-1 < top
    omega) (by
      intro q hq j _
      rw [hcut]
      have hw : 131071-M.overhead.toNat ≤ 131071-b := by omega
      exact ((Nat.mul_le_mul hq hw).trans hguard).trans (Nat.le_add_right _ _))
  rw [hcut] at hfloor
  have hrank := rank_add_loss_le k hk M.overhead (by omega) hhi rfl hr hs hlarge hd
  have hloss := debit_lt_loss k b hk hc M.overhead.toNat (by omega) (by omega)
  change triangle full.U * shapeSum full (width M.overhead.toNat) ≤
      sourceDebit M.overhead.toNat full + ∑ W ∈ range top, Module.finrank FX (rows full W) at hfloor
  omega

/-- The projected equation has at most the band's Y-degree: six below 2601 (seven
ordinates), five from 2601 (six ordinates). -/
theorem proof : K1_14_2.c7 := by
  intro u del M Γ F hlo hhi rows hr f _ hd
  by_cases h0 : M.overhead ≤ 2600
  · have hy : (band M.overhead).yBound = 6 := by simp [band, h0]
    rw [hy]
    exact Nat.le_of_lt_succ (degree_lt 7 2564 (by decide) support_check_seven (by decide)
      (by decide) (by omega) hhi hr hd)
  · have hy : (band M.overhead).yBound = 5 := by simp [band, h0, hhi]
    rw [hy]
    exact Nat.le_of_lt_succ (degree_lt 6 2601 (by decide) support_check_six (by decide)
      (by decide) (by omega) hhi hr hd)

end K1_14_2_7
end PackSource_K1_14_2_7Proof
