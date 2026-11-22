import ProximityPrize.SubmissionLower.PuncturedCompactPrimary

set_option Elab.async false
set_option maxRecDepth 12000
namespace PuncturedCompactPrimary
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P3 (I K node)
open K1_13 (Geom embed Row jet extend atJet)
open K1_13_3_1 (line)
open scoped BigOperators Polynomial
open private eval_line line_contacts_zero order_of_locator_lines from ProximityPrize.SubmissionLower.Fast074

def cutoff (A : ℕ) : ℕ := 3000 * A - 1

def layerWidth (A D : ℕ) : ℕ := A + 3 - D

def requiredOrder (A D T : ℕ) : ℕ := (cutoff A - T) / layerWidth A D + 1

private def Bounded (W : ℕ) (Q : Polynomial Geom[X]) (b : ℕ) : Prop :=
  ∀ j, (Q.coeff j).natDegree ≤ b + W * j
private theorem bounded_mul {W : ℕ} {F G : Polynomial Geom[X]} {a b : ℕ}
    (hF : Bounded W F a) (hG : Bounded W G b) : Bounded W (F * G) (a + b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum, Nat.mul_add]
  omega
private theorem bounded_C {W : ℕ} (f : Geom[X]) {a : ℕ} (hf : f.natDegree ≤ a) :
    Bounded W (Polynomial.C f) a := by
  intro j
  by_cases h : j = 0
  · simpa [h] using hf
  · simp [Polynomial.coeff_C, h]
private theorem bounded_prod {W : ℕ} {ι : Type*} (A : Finset ι)
    (f : ι → Polynomial Geom[X]) (b : ι → ℕ) (hf : ∀ i ∈ A, Bounded W (f i) (b i)) :
    Bounded W (∏ i ∈ A, f i) (∑ i ∈ A, b i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using bounded_C (1 : Geom[X]) (a := 0) (by simp)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact bounded_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
private theorem bounded_pow {W : ℕ} {f : Polynomial Geom[X]} {b : ℕ} (hf : Bounded W f b) (n : ℕ) :
    Bounded W (f ^ n) (b * n) := by
  induction n with
  | zero => simpa using bounded_C (1 : Geom[X]) (a := 0) (by simp)
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact bounded_mul ih hf
private theorem line_degree {a D : ℕ} (hD : 3 < D) (hgap : D ≤ a + 3) (P : Row 4) (S U : Geom[X]) (T : ℕ)
    (hP : PrimaryTaper.TrueWeightLE D P T) (hS : S.natDegree ≤ D)
    (hU : U.natDegree ≤ a + 3) (j : ℕ) :
    ((line P S U).coeff j).natDegree ≤ T + layerWidth a D * j := by
  let b (i : Fin 4) : ℕ := D - i.val
  let F (i : Fin 4) : Polynomial Geom[X] :=
    Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 4) : Bounded (layerWidth a D) (F i) (b i) := by
    intro k
    have hs : (jet S i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le S i.val).trans (Nat.sub_le_sub_right hS _)
    have hu : (jet U i).natDegree ≤ b i + layerWidth a D := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi : i.val ≤ D := (Nat.le_of_lt_succ i.isLt).trans (by omega)
      have hwidth : a + 3 = layerWidth a D + D := (Nat.sub_add_cancel hgap).symm
      change a + 3 - i.val ≤ (D - i.val) + layerWidth a D
      rw [hwidth, Nat.add_sub_assoc hi, Nat.add_comm (layerWidth a D)]
    change ((Polynomial.C (jet S i) + Polynomial.C (jet U i) *
      Polynomial.X).coeff k).natDegree ≤ b i + layerWidth a D * k
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
private theorem line_coeff_zero {a D : ℕ} (ha : 0 < a) (hD : 3 < D)
    (hgap : D ≤ a + 3) (w : I → K) (deleted : Finset I) (T : ℕ)
    (P : Row 4) (S : Geom[X]) (hw : PrimaryTaper.TrueWeightLE D P T) (hc : Contact w deleted P) (hS : S.natDegree ≤ D)
    (A : Finset I) (hA : A.card = a) (apart : Disjoint A deleted)
    (hhit : ∀ i ∈ A, S.eval (embed (node i)) = embed (w i))
    (V : Geom[X]) (hV : V.natDegree ≤ 3) (j : ℕ)
    (hj : T + layerWidth a D * j ≤ (cutoff a)) :
    (line P S (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ a + 3 := by
    exact natDegree_mul_le.trans (by rw [locator_natDegree, hA]; exact Nat.add_le_add_left hV _)
  let Q := line P S U
  have hcontact (i : I) (hi : i ∈ A) (c : Geom) :
      (Polynomial.X - C (x i)) ^ 3000 ∣ Q.eval (C c) := by
    rw [show Q = line P S U from rfl, eval_line]
    apply hc i (fun hd => Finset.disjoint_left.mp apart hi hd)
    have hL : L.eval (x i) = 0 := locator_eval_zero x A i hi
    have hU0 : U.eval (x i) = 0 := by simp [U, hL]
    simpa [x, eval_smul, hU0] using hhit i hi
  have hx : Function.Injective x :=
    (RingHom.injective embed).comp IRSProfile.domain.injective
  have hb := (line_degree (a := a) hD hgap P S U T hw hS hU j).trans hj
  have hdegree : (Q.coeff j).natDegree < 3000 * A.card := by
    rw [hA]
    exact hb.trans_lt (Nat.sub_lt (Nat.mul_pos (by decide) ha) (by decide))
  exact line_contacts_zero Q A x hx 3000 hcontact j hdegree
/-- The contacts on a disjoint agreement set give the order required by the primary layers. -/
theorem order_of_contact {a D : ℕ} (ha : 0 < a) (hD : 3 < D)
    (hgap : D ≤ a + 3) (w : I → K) (deleted : Finset I) (P : Row 4) {T : ℕ}
    (hT : T ≤ (cutoff a)) (hw : PrimaryTaper.TrueWeightLE D P T) (hc : Contact w deleted P)
    {S : Geom[X]} (hS : S.natDegree ≤ D)
    {H : Finset I} (hH : a ≤ H.card) (apart : Disjoint H deleted)
    (hits : ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) :
    K1_13.OrderAt P S (requiredOrder a D T) := by
  obtain ⟨A, hAH, hA⟩ := Finset.exists_subset_card_eq hH
  let x (i : I) := embed (node i)
  apply order_of_locator_lines P S (locator x A) (locator_monic x A).ne_zero
  intro V hV j hj
  have hAapart : Disjoint A deleted := apart.mono_left hAH
  apply line_coeff_zero ha hD hgap w deleted T P S hw hc hS A hA hAapart (fun i hi => hits i (hAH hi)) V hV j
  have hj' : j ≤ ((cutoff a) - T) / layerWidth a D := Nat.lt_succ_iff.mp hj
  have hq := Nat.div_mul_le_self ((cutoff a) - T) (layerWidth a D)
  rw [Nat.mul_comm _ (layerWidth a D)] at hq
  calc
    T + layerWidth a D * j ≤ T + layerWidth a D * (((cutoff a) - T) / layerWidth a D) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left (layerWidth a D) hj') T
    _ ≤ T + ((cutoff a) - T) := Nat.add_le_add_left hq T
    _ = (cutoff a) := Nat.add_sub_of_le hT

theorem vanishes_of_contact {a D : ℕ} (ha : 0 < a) (hD : 3 < D)
    (hgap : D ≤ a + 3) (w : I → K) (deleted : Finset I) (P : Row 4)
    (hw : PrimaryTaper.TrueWeightLE D P (cutoff a)) (hc : Contact w deleted P) (S : K[X])
    (hS : S.natDegree ≤ D) (H : Finset I) (hH : a ≤ H.card)
    (apart : Disjoint H deleted) (hits : ∀ i ∈ H, S.eval (node i) = w i) :
    atJet P (extend S) = 0 := by
  apply K1_13_6_1.orderAt_vanishes (show 0 < requiredOrder a D (cutoff a) by simp [requiredOrder])
  have hdeg : (extend S).natDegree ≤ D := Polynomial.natDegree_map_le.trans hS
  refine order_of_contact ha hD hgap w deleted P le_rfl hw hc hdeg hH apart ?_
  intro i hi
  change (S.map embed).eval (embed (node i)) = embed (w i)
  rw [Polynomial.eval_map, Polynomial.eval₂_hom, hits i hi]

#print axioms order_of_contact
#print axioms vanishes_of_contact
end
end PuncturedCompactPrimary
