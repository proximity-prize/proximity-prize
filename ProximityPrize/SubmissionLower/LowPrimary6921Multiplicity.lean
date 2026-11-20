import ProximityPrize.SubmissionLower.LowPrimary6921Source
import ProximityPrize.SubmissionLower.LowPrice6921Relaxed

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

namespace LowPrimary6921

noncomputable section

open Polynomial K1 K1_13 FrobeniusLocator ProximityPrize.Benchmark
open K1_13_3 (Symbol symbolAt)
open K1_13_3_1 (line)
open scoped BigOperators Polynomial

def requiredOrder (T : ℕ) : ℕ := (terminal - T) / layerWidth + 1

def BankRow (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) ⟨4012, 1650, 550⟩ ∧ WeightLE P T ∧ Contact w P

private def Bounded (Q : Polynomial Geom[X]) (b : ℕ) : Prop :=
  ∀ j, (Q.coeff j).natDegree ≤ b + layerWidth * j

private theorem bounded_mul {F G : Polynomial Geom[X]} {a b : ℕ}
    (hF : Bounded F a) (hG : Bounded G b) : Bounded (F * G) (a + b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum, Nat.mul_add]
  omega

private theorem bounded_C (f : Geom[X]) {a : ℕ} (hf : f.natDegree ≤ a) :
    Bounded (Polynomial.C f) a := by
  intro j
  by_cases h : j = 0
  · simpa [h] using hf
  · simp [Polynomial.coeff_C, h]

private theorem bounded_prod {ι : Type*} (A : Finset ι)
    (f : ι → Polynomial Geom[X]) (b : ι → ℕ) (hf : ∀ i ∈ A, Bounded (f i) (b i)) :
    Bounded (∏ i ∈ A, f i) (∑ i ∈ A, b i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using bounded_C (1 : Geom[X]) (a := 0) (by simp)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact bounded_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

private theorem bounded_pow {f : Polynomial Geom[X]} {b : ℕ} (hf : Bounded f b) (n : ℕ) :
    Bounded (f ^ n) (b * n) := by
  induction n with
  | zero => simpa using bounded_C (1 : Geom[X]) (a := 0) (by simp)
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact bounded_mul ih hf

private theorem line_degree (P : Row 4) (S U : Geom[X]) (T : ℕ)
    (hP : WeightLE P T) (hS : S.natDegree ≤ 133518) (hU : U.natDegree ≤ 180172)
    (j : ℕ) : ((line P S U).coeff j).natDegree ≤ T + layerWidth * j := by
  let b (i : Fin 4) : ℕ := 133518 - i.val
  let F (i : Fin 4) : Polynomial Geom[X] :=
    Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 4) : Bounded (F i) (b i) := by
    intro k
    have hs : (jet S i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le S i.val).trans (Nat.sub_le_sub_right hS _)
    have hu : (jet U i).natDegree ≤ b i + layerWidth := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi := i.isLt
      change 180172 - i.val ≤ (133518 - i.val) + 46654
      omega
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

private theorem eval_line (P : Row 4) (S U : Geom[X]) (c : Geom) :
    (line P S U).eval (Polynomial.C c) = atJet P (S + c • U) := by
  change (evalRingHom (Polynomial.C c))
    (MvPolynomial.eval₂ Polynomial.C
      (fun i => Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X) P) = _
  rw [MvPolynomial.hom_eval₂]
  have hC : (evalRingHom (C c)).comp C = RingHom.id Geom[X] := RingHom.ext fun f => by simp
  rw [hC]
  change MvPolynomial.eval _ P = MvPolynomial.eval (jet (S + c • U)) P
  have heq : (fun i : Fin 4 => (evalRingHom (C c))
      (Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X)) =
      jet (S + c • U) := by
    funext i
    simp only [coe_evalRingHom, eval_mul, eval_C, eval_X, jet, map_add]
    rw [(hasseDeriv i.val).map_smul, Algebra.smul_def, algebraMap_eq, mul_comm]
  rw [heq]

private theorem swapped_coeff (Q : Polynomial Geom[X]) (i j : ℕ) :
    ((Bivariate.swap Q).coeff i).coeff j = (Q.coeff j).coeff i := by
  induction Q using Polynomial.induction_on' with
  | add P Q hp hq => simp [hp, hq]
  | monomial n P =>
    induction P using Polynomial.induction_on' with
    | add P Q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
    | monomial m c =>
      rw [Bivariate.swap_monomial_monomial]
      by_cases hi : m = i <;> by_cases hj : n = j <;> simp [Polynomial.coeff_monomial, hi, hj]

private theorem eval_swap (Q : Polynomial Geom[X]) (c : Geom) :
    (Bivariate.swap Q).map (evalRingHom c) = Q.eval (Polynomial.C c) := by
  simpa [Polynomial.aeval_def]
    using (Bivariate.aveal_eq_map_swap c Q).symm

/-- Contact at all constant values of the line parameter holds coefficientwise. -/
private theorem coeff_contact (Q : Polynomial Geom[X]) (x : Geom) (r : ℕ)
    (h : ∀ c : Geom, (Polynomial.X - C x) ^ r ∣ Q.eval (C c)) (j : ℕ) :
    (Polynomial.X - C x) ^ r ∣ Q.coeff j := by
  let f : Geom[X] →+* Geom[X] := (taylorAlgHom x).toRingHom
  let A := Q.map f
  have heval (c : Geom) : A.eval (C c) = taylor x (Q.eval (C c)) := by
    change (Q.map f).eval (C c) = f (Q.eval (C c))
    have hC : f (C c) = C c := taylor_C _ _
    rw [← hC, eval_map, eval₂_at_apply]
    rw [hC]
  have hzero (i : ℕ) (hi : i < r) : (Bivariate.swap A).coeff i = 0 := by
    apply eq_zero_of_infinite_isRoot
    have hz (c : Geom) : ((Bivariate.swap A).coeff i).eval c = 0 := by
      change evalRingHom c ((Bivariate.swap A).coeff i) = 0
      rw [← Polynomial.coeff_map, eval_swap, heval]
      exact X_pow_dvd_iff.mp ((X_pow_dvd_taylor_iff_X_sub_C_pow_dvd _ _ _).mpr (h c)) i hi
    simpa [IsRoot, hz] using (Set.infinite_univ : (Set.univ : Set Geom).Infinite)
  apply (X_pow_dvd_taylor_iff_X_sub_C_pow_dvd _ _ _).mp
  apply X_pow_dvd_iff.mpr
  intro i hi
  change (f (Q.coeff j)).coeff i = 0
  rw [← Polynomial.coeff_map, ← swapped_coeff, hzero i hi, Polynomial.coeff_zero]

private theorem line_contacts_zero (Q : Polynomial Geom[X]) (A : Finset I)
    (x : I → Geom) (hx : Function.Injective x) (r : ℕ)
    (h : ∀ i ∈ A, ∀ c : Geom, (Polynomial.X - C (x i)) ^ r ∣ Q.eval (C c))
    (j : ℕ) (hdeg : (Q.coeff j).natDegree < r * A.card) : Q.coeff j = 0 := by
  exact K1_11.eq_zero_of_many_contacts A x hx r (Q.coeff j)
    (fun i hi => coeff_contact Q (x i) r (h i hi) j) hdeg

/-- The reserve makes every low coefficient of every locator line vanish. -/
theorem line_coeff_zero (w : I → K) (T : ℕ) (P : Row 4) (S : Geom[X])
    (hP : BankRow w T P) (hS : S.natDegree ≤ 133518)
    (A : Finset I) (hA : A.card = 180169)
    (hhit : ∀ i ∈ A, S.eval (embed (node i)) = embed (w i))
    (V : Geom[X]) (hV : V.natDegree ≤ 3) (j : ℕ) (hj : T + layerWidth * j ≤ terminal) :
    (line P S (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ 180172 := by
    exact natDegree_mul_le.trans (by rw [locator_natDegree, hA]; omega)
  let Q := line P S U
  have hcontact (i : I) (hi : i ∈ A) (c : Geom) :
      (Polynomial.X - C (x i)) ^ 3000 ∣ Q.eval (C c) := by
    rw [show Q = line P S U from rfl, eval_line]
    apply hP.2.2
    have hL : L.eval (x i) = 0 := locator_eval_zero x A i hi
    have hU0 : U.eval (x i) = 0 := by simp [U, hL]
    simpa [x, eval_smul, hU0] using hhit i hi
  have hx : Function.Injective x :=
    (RingHom.injective embed).comp IRSProfile.domain.injective
  have hb := (line_degree P S U T hP.2.1 hS hU j).trans hj
  have hdegree : (Q.coeff j).natDegree < 3000 * A.card := by
    rw [hA]
    exact hb.trans_lt (by decide)
  exact line_contacts_zero Q A x hx 3000 hcontact j hdegree

private theorem exists_direction (L : Geom[X]) (x : Geom) (hx : L.eval x ≠ 0)
    (v : Fin 4 → Geom) :
    ∃ V : Geom[X], V.natDegree ≤ 3 ∧ ∀ i : Fin 4, (jet (L * V) i).eval x = v i := by
  classical
  let B := (Polynomial.X - C x) ^ 4
  have hB : B.Monic := (monic_X_sub_C x).pow _
  have hdeg : B.natDegree = 4 := by simp [B, natDegree_pow]
  have hcop : IsCoprime L B := by
    apply (irreducible_X_sub_C x).coprime_pow_of_not_dvd
    simpa [dvd_iff_isRoot, IsRoot] using hx
  obtain ⟨a, b, hab⟩ := hcop
  let F := taylor (-x) (ofFn 4 v)
  let V := (a * F) %ₘ B
  have hdiv : B ∣ L * V - F := by
    refine ⟨-(b * F + L * ((a * F) /ₘ B)), ?_⟩
    dsimp only [V]
    rw [modByMonic_eq_sub_mul_div]
    linear_combination F * hab
  have hjet := (X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero (L * V - F) x 4).mp hdiv
  refine ⟨V, ?_, fun i => ?_⟩
  · have hne : B ≠ 1 := by
      intro h
      rw [h, natDegree_one] at hdeg
      omega
    have hsmall := natDegree_modByMonic_lt (a * F) hB hne
    rw [hdeg] at hsmall
    exact Nat.le_of_lt_succ hsmall
  · have h := hjet i.val i.isLt
    rw [map_sub, eval_sub, sub_eq_zero] at h
    change (hasseDeriv i.val (L * V)).eval x = v i
    rw [h, ← taylor_coeff, show F = taylor (-x) (ofFn 4 v) from rfl, taylor_taylor,
      add_neg_cancel, taylor_zero, ofFn_coeff_eq_val_of_lt v i.isLt]

/-- Along a scalar line through the origin, the coefficient at degree j
is the degree-j homogeneous component evaluated at the direction. -/
private theorem coeff_line_through_zero (P : Symbol) (v : Fin 4 → Geom) (j : ℕ) :
    (MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (v i) * Polynomial.X) P).coeff j =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent j P) := by
  classical
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff, MvPolynomial.homogeneousComponent_apply]
  change _ = MvPolynomial.eval₂Hom (RingHom.id _) v _
  rw [map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.eval₂Hom_monomial]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← map_pow Polynomial.C,
    ← map_prod Polynomial.C, ← map_mul Polynomial.C, ← mul_assoc, Finset.prod_pow_eq_pow_sum,
    Polynomial.coeff_C_mul_X_pow, RingHom.id_apply, Finsupp.degree_apply]
  split_ifs <;> simp_all

private theorem line_at_abscissa (P : Row 4) (S U : Geom[X]) (x : Geom) :
    (line P S U).map (evalRingHom x) =
      MvPolynomial.eval₂ Polynomial.C (fun i : Fin 4 => Polynomial.C ((jet U i).eval x) *
        Polynomial.X) (symbolAt x (shiftJet P S)) := by
  let f := evalRingHom x
  let g (i : Fin 4) : Geom[X] := Polynomial.C (f (jet U i)) * Polynomial.X
  change (mapRingHom f) (MvPolynomial.eval₂ Polynomial.C
    (fun i : Fin 4 => Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X) P) =
    MvPolynomial.eval₂Hom Polynomial.C g
      (MvPolynomial.map f (MvPolynomial.eval₂ MvPolynomial.C
        (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)) P))
  rw [MvPolynomial.hom_eval₂, MvPolynomial.eval₂Hom_map_hom]
  change _ = MvPolynomial.eval₂Hom (Polynomial.C.comp f) g
    (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)) P)
  rw [MvPolynomial.map_eval₂Hom]
  have hl : (mapRingHom f).comp Polynomial.C = Polynomial.C.comp f := RingHom.ext fun p => by simp
  have hr : (MvPolynomial.eval₂Hom (Polynomial.C.comp f) g).comp MvPolynomial.C =
      Polynomial.C.comp f := RingHom.ext fun p => by simp
  rw [hl, hr]
  congr 1
  funext i
  simp [g, add_comm]

private theorem order_of_locator_lines (P : Row 4) (S L : Geom[X]) (hL : L ≠ 0) (d : ℕ)
    (h : ∀ (V : Geom[X]), V.natDegree ≤ 3 → ∀ j < d, (line P S (L * V)).coeff j = 0) :
    OrderAt P S d := by
  intro m hm
  change d ≤ m.degree
  by_contra! hlt
  have hz (x : Geom) (hx : L.eval x ≠ 0) : ((shiftJet P S).coeff m).eval x = 0 := by
    let A := symbolAt x (shiftJet P S)
    let Q := MvPolynomial.homogeneousComponent m.degree A
    have hQ : Q = 0 := by
      apply (MvPolynomial.homogeneousComponent_isHomogeneous _ _).eq_zero_of_forall_eval_eq_zero
      intro v
      obtain ⟨V, hV, hv⟩ := exists_direction L x hx v
      have heval := congrArg (evalRingHom x) (h V hV m.degree hlt)
      rw [map_zero, ← Polynomial.coeff_map, line_at_abscissa] at heval
      let along (u : Fin 4 → Geom) :=
        (MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (u i) * Polynomial.X) A).coeff
          m.degree
      have hdir := congrArg along (funext hv)
      have hvanish : along v = 0 := hdir.symm.trans heval
      simpa only [along, coeff_line_through_zero] using hvanish
    have hcoeff := congrArg (fun F : Symbol => F.coeff m) hQ
    simpa [Q, MvPolynomial.coeff_homogeneousComponent, A, symbolAt, MvPolynomial.coeff_map]
      using hcoeff
  have hzero : (shiftJet P S).coeff m = 0 := by
    apply eq_zero_of_infinite_isRoot
    refine (finite_setOfPred_isRoot hL).infinite_compl.mono ?_
    intro x hx
    exact hz x hx
  exact MvPolynomial.mem_support_iff.mp hm hzero

theorem contact_order (w : I → K) (T : ℕ) (P : Row 4)
    (hT : T ≤ terminal) (hP : BankRow w T P) (S : Geom[X])
    (hS : S.natDegree ≤ degreeBound)
    (hits : ∃ H : Finset I, agreement ≤ H.card ∧
      ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) :
    OrderAt P S (requiredOrder T) := by
  obtain ⟨H, hH, hhits⟩ := hits
  obtain ⟨A, hAH, hA⟩ := Finset.exists_subset_card_eq hH
  let x (i : I) := embed (node i)
  apply order_of_locator_lines P S (locator x A) (locator_monic x A).ne_zero
  intro V hV j hj
  apply line_coeff_zero w T P S hP hS A hA (fun i hi => hhits i (hAH hi)) V hV j
  have hj' : j ≤ (terminal - T) / layerWidth := Nat.lt_succ_iff.mp hj
  have hd := Nat.mul_le_mul_left layerWidth hj'
  have hq := Nat.div_mul_le_self (terminal - T) layerWidth
  rw [Nat.mul_comm _ layerWidth] at hq
  omega

private abbrev Exponent := Fin 4 →₀ ℕ

/-- Translate the top jet by a formal parameter, holding all coefficients
and the other jets fixed. -/
private def translateTop : Row 4 →+* Polynomial (Row 4) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) fun i =>
    Polynomial.C (MvPolynomial.X i) + if i = 3 then Polynomial.X else 0

private def topHasse (a : ℕ) (P : Row 4) : Row 4 :=
  (translateTop P).coeff a

private theorem translate_independent (m : Exponent) (c : Geom[X]) (hm : m 3 = 0) :
    translateTop (MvPolynomial.monomial m c) = Polynomial.C (MvPolynomial.monomial m c) := by
  rw [translateTop, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq, map_mul]
  simp only [RingHom.comp_apply]
  congr 1
  unfold Finsupp.prod
  rw [map_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hne : i ≠ 3 := by
    intro he
    subst i
    exact (Finsupp.mem_support_iff.mp hi) hm
  simp [hne]

private theorem translate_top_pow_coeff (n a : ℕ) :
    ((Polynomial.C (MvPolynomial.X (3 : Fin 4) : Row 4) + Polynomial.X) ^ n).coeff a =
      MvPolynomial.C (↑(n.choose a) : Geom[X]) * MvPolynomial.X 3 ^ (n - a) := by
  rw [add_comm, ← Polynomial.taylor_X_pow, Polynomial.taylor_coeff,
    Polynomial.X_pow_eq_monomial, Polynomial.hasseDeriv_monomial]
  simp [Polynomial.eval_monomial]

private theorem erase_top_add (u : Exponent) :
    u.erase 3 + Finsupp.single 3 (u 3) = u := by
  ext i
  by_cases hi : i = 3
  · subst i
    simp
  · simp [Finsupp.erase_ne hi, Finsupp.single_eq_of_ne hi]

private theorem topHasse_monomial (a : ℕ) (u : Exponent) (c : Geom[X]) :
    topHasse a (MvPolynomial.monomial u c) =
      MvPolynomial.monomial (u.erase 3 + Finsupp.single 3 (u 3 - a)) (↑((u 3).choose a) * c) := by
  have hu : MvPolynomial.monomial u c =
      MvPolynomial.monomial (u.erase 3) c * MvPolynomial.X 3 ^ (u 3) := by
    rw [← MvPolynomial.monomial_add_single, erase_top_add]
  have hx : translateTop (MvPolynomial.X 3) =
      Polynomial.C (MvPolynomial.X 3) + Polynomial.X := by simp [translateTop]
  unfold topHasse
  rw [hu, map_mul, map_pow, translate_independent _ _ Finsupp.erase_same, hx,
    Polynomial.coeff_C_mul, translate_top_pow_coeff, ← mul_assoc]
  rw [mul_comm (MvPolynomial.monomial (u.erase 3) c), MvPolynomial.C_mul_monomial,
    ← MvPolynomial.monomial_add_single]

private theorem apply_add_top (m : Exponent) (a : ℕ) :
    (m + Finsupp.single 3 a : Exponent) 3 = m 3 + a := by simp

private theorem topHasse_coeff (a : ℕ) (P : Row 4) (m : Exponent) :
    (topHasse a P).coeff m =
      ↑((m 3 + a).choose a) * P.coeff (m + Finsupp.single 3 a) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [topHasse_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases ha : a ≤ u 3
    · have hcancel : (u.erase 3 + Finsupp.single 3 (u 3 - a)) + Finsupp.single 3 a = u := by
        rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel ha, erase_top_add]
      have heq : u.erase 3 + Finsupp.single 3 (u 3 - a) = m ↔
          u = m + Finsupp.single 3 a := by
        constructor
        · intro h
          rw [← h, hcancel]
        · intro h
          exact add_right_cancel (hcancel.trans h)
      simp only [heq]
      by_cases h : u = m + Finsupp.single 3 a
      · have h3 : u 3 = m 3 + a := by rw [h, apply_add_top]
        simp only [h3, ite_eq_left h]
      · simp [h]
    · have hne : u ≠ m + Finsupp.single 3 a := by
        intro h
        have h3 : u 3 = m 3 + a := by rw [h, apply_add_top]
        omega
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge ha)]
      simp [hne]
  | add P Q hP hQ =>
    simp only [topHasse, map_add, Polynomial.coeff_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply] at hP hQ ⊢
    rw [hP, hQ, mul_add]

private theorem source_support {a : ℕ} {P : Row 4} {m : Exponent}
    (hm : m ∈ (topHasse a P).support) : m + Finsupp.single 3 a ∈ P.support := by
  rw [MvPolynomial.mem_support_iff, topHasse_coeff] at hm
  exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hm)

private theorem sum_add_top (w : Fin 4 → ℕ) (m : Exponent) (a : ℕ) :
    (m + Finsupp.single 3 a).sum (fun i k => w i * k) =
      m.sum (fun i k => w i * k) + w 3 * a := by
  rw [Finsupp.sum_add_index' (fun i => Nat.mul_zero (w i)) (fun i b c => Nat.mul_add (w i) b c),
    Finsupp.sum_single_index (h := fun i k => w i * k) (Nat.mul_zero _)]

private theorem total_add_top (m : Exponent) (a : ℕ) :
    (m + Finsupp.single 3 a).sum (fun _ k => k) = m.sum (fun _ k => k) + a := by
  simpa only [one_mul] using sum_add_top (fun _ => 1) m a

private theorem topHasse_bounds (a : ℕ) (P : Row 4)
    (hb : InBox (shape P) ⟨4012, 1650, 550⟩) (hw : WeightLE P terminal) :
    InBox (shape (topHasse a P)) ⟨4012, 1650, 550⟩ ∧ WeightLE (topHasse a P) terminal := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change (topHasse a P).totalDegree ≤ 4012
    apply Finset.sup_le
    intro m hm
    have hp := (MvPolynomial.le_totalDegree (source_support hm)).trans hb.1
    rw [total_add_top] at hp
    change _ ≤ 4012 at hp
    omega
  · change indexDegree (topHasse a P) ≤ 1650
    apply Finset.sup_le
    intro m hm
    have hp := (Finset.le_sup (f := fun u : Exponent => u.sum (fun i k => i.val * k))
      (source_support hm)).trans hb.2.1
    rw [sum_add_top Fin.val] at hp
    change _ ≤ 1650 at hp
    omega
  · change (topHasse a P).degreeOf 3 ≤ 550
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have hp := (MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)).trans hb.2.2
    rw [apply_add_top] at hp
    change _ ≤ 550 at hp
    omega
  · intro m hm
    have hp := hw _ (source_support hm)
    rw [sum_add_top (fun i => degreeBound - i.val)] at hp
    rw [topHasse_coeff]
    have hcoeff := Polynomial.natDegree_mul_le
      (p := (↑((m 3 + a).choose a) : Geom[X])) (q := P.coeff (m + Finsupp.single 3 a))
    rw [Polynomial.natDegree_natCast, zero_add] at hcoeff
    omega

private def shiftHom (S : Geom[X]) : Row 4 →+* Row 4 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i))

private theorem translate_shift (S : Geom[X]) :
    translateTop.comp (shiftHom S) = (Polynomial.mapRingHom (shiftHom S)).comp translateTop := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [translateTop, shiftHom]
  · intro i
    simp only [RingHom.comp_apply, shiftHom, translateTop, MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_C, map_add, Polynomial.coe_mapRingHom, Polynomial.map_C]
    by_cases hi : i = 3
    · simp only [hi, ite_true, Polynomial.map_X]
      exact add_right_comm _ _ _
    · simp only [hi, ite_false, Polynomial.map_zero, add_zero]

private theorem topHasse_order (a d : ℕ) (P : Row 4) (S : Geom[X])
    (h : OrderAt P S d) : OrderAt (topHasse a P) S (d - a) := by
  have he := RingHom.congr_fun (translate_shift S) P
  change translateTop (shiftJet P S) = (translateTop P).map (shiftHom S) at he
  have hs : topHasse a (shiftJet P S) = shiftJet (topHasse a P) S := by
    change (translateTop (shiftJet P S)).coeff a =
      shiftHom S ((translateTop P).coeff a)
    rw [he, Polynomial.coeff_map]
  intro m hm
  rw [← hs] at hm
  have hd := h _ (source_support hm)
  rw [total_add_top] at hd
  omega

private theorem topHasse_one_not_dvd (f : Row 4) (hf : SmallFactor f) :
    ¬ f ∣ topHasse 1 f := by
  classical
  have hpos : 0 < f.degreeOf 3 := hf.2.1
  have hsmall : f.degreeOf 3 < K1.p :=
    (show f.degreeOf 3 ≤ 10 from hf.2.2.1.2.2).trans_lt (by decide)
  have hdeg : (topHasse 1 f).degreeOf 3 ≤ f.degreeOf 3 - 1 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have h := MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)
    rw [apply_add_top] at h
    omega
  have hnz : topHasse 1 f ≠ 0 := by
    have hsup : 0 < f.support.sup (fun m => m (3 : Fin 4)) := by
      rwa [← MvPolynomial.degreeOf_eq_sup]
    obtain ⟨u, hu, htop⟩ := (Finset.le_sup_iff hsup).mp (le_refl _)
    rw [← MvPolynomial.degreeOf_eq_sup] at htop
    have hupos : 0 < u 3 := hpos.trans_le htop
    have hult : u 3 < K1.p := (MvPolynomial.le_degreeOf_of_mem_support 3 hu).trans_lt hsmall
    let m := u.erase 3 + Finsupp.single 3 (u 3 - 1)
    have hsum : m + Finsupp.single 3 1 = u := by
      dsimp [m]
      rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel hupos, erase_top_add]
    have hm : m 3 + 1 = u 3 := by
      rw [← apply_add_top, hsum]
    have hc : (↑(u 3) : Geom[X]) ≠ 0 := by
      have : CharP Geom K1.p :=
        charP_of_injective_ringHom (RingHom.injective embed) K1.p
      intro hz
      have hz' : (↑(u 3) : Geom) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg (Polynomial.evalRingHom (0 : Geom)) hz
      exact (not_le_of_gt hult)
        (Nat.le_of_dvd hupos ((CharP.cast_eq_zero_iff Geom K1.p _).mp hz'))
    have hcoeff : (topHasse 1 f).coeff m ≠ 0 := by
      rw [topHasse_coeff, hm, hsum, Nat.choose_one_right]
      exact mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hu)
    intro hz
    exact hcoeff (by rw [hz]; rfl)
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro h
    exact hnz (by rw [hg, h, mul_zero])
  have h := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.1.ne_zero hg0
  rw [hg, h] at hdeg
  omega

private theorem topHasse_zero (P : Row 4) : topHasse 0 P = P := by
  ext m
  simp [topHasse_coeff]

/-- The first possible coefficient after extracting one parameter from
each of the a factors. -/
private theorem coeff_X_mul_pow {R : Type*} [CommSemiring R]
    (V W : Polynomial R) (a : ℕ) :
    ((Polynomial.X * V) ^ a * W).coeff a = (V.coeff 0) ^ a * W.coeff 0 := by
  rw [mul_pow, mul_assoc]
  calc
    _ = (V ^ a * W).coeff 0 := by
      simpa only [zero_add] using Polynomial.coeff_X_pow_mul (V ^ a * W) a 0
    _ = _ := by
      change Polynomial.constantCoeff (V ^ a * W) =
        Polynomial.constantCoeff V ^ a * Polynomial.constantCoeff W
      rw [map_mul, map_pow]

/-- In the quotient by the prime factor, the constant term of its translate
vanishes and the first coefficient survives. -/
private theorem exact_hasse_not_dvd {R : Type*} [CommRing R]
    (T : R →+* Polynomial R) (T0 : ∀ G, (T G).coeff 0 = G)
    (f P : R) (a : ℕ) (hf : Prime f) (hsep : ¬ f ∣ (T f).coeff 1)
    (hdiv : f ^ a ∣ P) (hexact : ¬ f ^ (a + 1) ∣ P) : ¬ f ∣ (T P).coeff a := by
  obtain ⟨U, rfl⟩ := hdiv
  have hu : ¬ f ∣ U := by
    rintro ⟨V, rfl⟩
    exact hexact ⟨V, by rw [pow_succ, mul_assoc]⟩
  let J := Ideal.span ({f} : Set R)
  have : J.IsPrime := Ideal.isPrime_span_singleton_of_prime hf
  let reduce := Ideal.Quotient.mk J
  let tr := (Polynomial.mapRingHom reduce).comp T
  have hzero (G : R) : reduce G = 0 ↔ f ∣ G :=
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hcoeff (G : R) (n : ℕ) : (tr G).coeff n = reduce ((T G).coeff n) :=
    Polynomial.coeff_map _ _
  have hconstant (G : R) : (tr G).coeff 0 = reduce G := by rw [hcoeff, T0]
  obtain ⟨V, hV⟩ := Polynomial.X_dvd_iff.mpr
    (show (tr f).coeff 0 = 0 by rw [hconstant]; exact (hzero _).mpr dvd_rfl)
  have hfirst : V.coeff 0 = reduce ((T f).coeff 1) := by
    rw [← hcoeff, hV]
    exact (Polynomial.coeff_X_mul V 0).symm
  have hr : reduce ((T (f ^ a * U)).coeff a) = reduce ((T f).coeff 1) ^ a * reduce U := by
    calc
      _ = (tr (f ^ a * U)).coeff a := (hcoeff _ _).symm
      _ = (V.coeff 0) ^ a * (tr U).coeff 0 := by
        rw [map_mul, map_pow, hV]
        exact coeff_X_mul_pow V (tr U) a
      _ = _ := by rw [hfirst, hconstant]
  intro h
  exact (mul_ne_zero (pow_ne_zero _ ((hzero _).not.mpr hsep))
    ((hzero _).not.mpr hu)) (hr.symm.trans ((hzero _).mpr h))

/-- The Hasse partial at the exact exponent is a proper cutter of the factor. -/
theorem proper_cut (f P : Row 4) (Γ : Finset K) (s : K → K[X]) (d a : ℕ)
    (hf : SmallFactor f) (hb : InBox (shape P) ⟨4012, 1650, 550⟩)
    (hw : WeightLE P terminal)
    (hord : ∀ γ ∈ Γ, OrderAt P (extend (s γ)) d)
    (_ : a < d) (hdiv : f ^ a ∣ P) (hexact : ¬ f ^ (a + 1) ∣ P) :
    LowPrice6921.RelaxedProperCut f Γ s (d - a) := by
  obtain ⟨hbox, hweight⟩ := topHasse_bounds a P hb hw
  have hp : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hf.1
  have hproper : ¬ f ∣ topHasse a P :=
    exact_hasse_not_dvd translateTop topHasse_zero f P a hp (topHasse_one_not_dvd f hf) hdiv hexact
  exact ⟨topHasse a P, hproper, hbox,
    LowPrice6921.cutter_weight_of_new_degree _ hbox hweight, fun γ hγ =>
    topHasse_order a d P (extend (s γ)) (hord γ hγ)⟩

end
end LowPrimary6921
