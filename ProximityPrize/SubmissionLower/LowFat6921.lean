import ProximityPrize.SubmissionLower.LowFat6921Rank
import ProximityPrize.SubmissionLower.Fast076
set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

namespace LowFat6921

noncomputable section

open Polynomial K1 K1_13 K1_13_4 K1_13_4_3 K1_13_4_5
open FrobeniusLocator ProximityPrize.Benchmark
open scoped Polynomial BigOperators

structure Messages (w : I → K) (Γ : Finset K) (s : K → K[X]) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ 133518
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, 180169 ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i

def NewPairOrders (F G : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) : Prop :=
  MixedOrder F z y firstMixedOrder ∧ MixedOrder G z y secondMixedOrder

open K1_13_4_3_3 (line)
private def RawLocator : Prop :=
  ∀ (w : I → K) (H res T : Geom[X]) (t k : ℕ) (Q : Row 3),
    T.natDegree ≤ 131071 →
    (∃ A : Finset I, 180169 ≤ A.card ∧
      ∀ i ∈ A, (H * T + res).eval (embed (node i)) = embed (w i)) →
    RawContact 5000 w H res Q → RawCut t Q →
    t + 49196 * k < 5000 * 180169 →
    LowerOrder (MvPolynomial.map inclX Q) (trajectory T) (k + 1)

private def Bounded (F : Polynomial Geom[X]) (b : ℕ) : Prop :=
  ∀ j, (F.coeff j).natDegree ≤ b + 49196 * j

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

private theorem line_degree (Q : Row 3) (T U : Geom[X]) (t : ℕ)
    (hQ : RawCut t Q) (hT : T.natDegree ≤ 131071) (hU : U.natDegree ≤ 180267)
    (j : ℕ) : ((line Q T U).coeff j).natDegree ≤ t + 49196 * j := by
  let b (i : Fin 3) : ℕ := 131071 - i.val
  let F (i : Fin 3) : Polynomial Geom[X] :=
    Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 3) : Bounded (F i) (b i) := by
    intro k
    have ht : (jet T i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le T i.val).trans (Nat.sub_le_sub_right hT _)
    have hu : (jet U i).natDegree ≤ b i + 49196 := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi := i.isLt
      change 180267 - i.val ≤ (131071 - i.val) + 49196
      omega
    change ((F i).coeff k).natDegree ≤ b i + 49196 * k
    rw [show F i = _ from rfl, Polynomial.coeff_add, Polynomial.coeff_C,
      Polynomial.coeff_C_mul_X]
    by_cases h0 : k = 0
    · simpa [h0] using ht
    · by_cases h1 : k = 1
      · simpa [h1] using hu
      · simp [h0, h1]
  unfold line
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro a ha
  have hterm := bounded_mul (bounded_C (Q.coeff a) le_rfl)
    (bounded_prod a.support (fun i => F i ^ a i) (fun i => b i * a i)
      (fun i _ => bounded_pow (hF i) (a i))) j
  exact hterm.trans (Nat.add_le_add_right (hQ a ha) _)

private theorem eval_line (Q : Row 3) (T U : Geom[X]) (c : Geom) :
    (line Q T U).eval (Polynomial.C c) = atJet Q (T + c • U) := by
  change (evalRingHom (Polynomial.C c))
    (MvPolynomial.eval₂ Polynomial.C
      (fun i => Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X) Q) = _
  rw [MvPolynomial.hom_eval₂]
  have hC : (evalRingHom (C c)).comp C = RingHom.id Geom[X] := RingHom.ext fun p => by simp
  rw [hC]
  change MvPolynomial.eval _ Q = MvPolynomial.eval (jet (T + c • U)) Q
  have heq : (fun i : Fin 3 => (evalRingHom (C c))
      (Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X)) =
      jet (T + c • U) := by
    funext i
    simp only [coe_evalRingHom, eval_mul, eval_C, eval_X, jet, map_add]
    rw [(hasseDeriv i.val).map_smul, Algebra.smul_def, algebraMap_eq, mul_comm]
  rw [heq]

private theorem swapped_coeff (F : Polynomial Geom[X]) (i j : ℕ) :
    ((Bivariate.swap F).coeff i).coeff j = (F.coeff j).coeff i := by
  induction F using Polynomial.induction_on' with
  | add P Q hp hq => simp [hp, hq]
  | monomial n P =>
    induction P using Polynomial.induction_on' with
    | add P Q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
    | monomial m c =>
      rw [Bivariate.swap_monomial_monomial]
      by_cases hi : m = i <;> by_cases hj : n = j <;> simp [Polynomial.coeff_monomial, hi, hj]

/-- Taylor coefficients below the contact order vanish as parameter polynomials. -/
private theorem coeff_contact (F : Polynomial Geom[X]) (x : Geom) (r : ℕ)
    (h : ∀ c : Geom, (Polynomial.X - C x) ^ r ∣ F.eval (C c)) (j : ℕ) :
    (Polynomial.X - C x) ^ r ∣ F.coeff j := by
  let f : Geom[X] →+* Geom[X] := (taylorAlgHom x).toRingHom
  let A := F.map f
  have heval (c : Geom) : A.eval (C c) = taylor x (F.eval (C c)) := by
    change (F.map f).eval (C c) = f (F.eval (C c))
    have hC : f (C c) = C c := taylor_C _ _
    rw [← hC, eval_map, eval₂_at_apply]
    rw [hC]
  have hzero (i : ℕ) (hi : i < r) : (Bivariate.swap A).coeff i = 0 := by
    apply eq_zero_of_infinite_isRoot
    have hz (c : Geom) : ((Bivariate.swap A).coeff i).eval c = 0 := by
      have hs : (Bivariate.swap A).map (evalRingHom c) = A.eval (C c) := by
        simpa [Polynomial.aeval_def] using (Bivariate.aveal_eq_map_swap c A).symm
      change evalRingHom c ((Bivariate.swap A).coeff i) = 0
      rw [← Polynomial.coeff_map, hs, heval]
      exact X_pow_dvd_iff.mp ((X_pow_dvd_taylor_iff_X_sub_C_pow_dvd _ _ _).mpr (h c)) i hi
    simpa [IsRoot, hz] using (Set.infinite_univ : (Set.univ : Set Geom).Infinite)
  apply (X_pow_dvd_taylor_iff_X_sub_C_pow_dvd _ _ _).mp
  apply X_pow_dvd_iff.mpr
  intro i hi
  change (f (F.coeff j)).coeff i = 0
  rw [← Polynomial.coeff_map, ← swapped_coeff, hzero i hi, Polynomial.coeff_zero]

/-- Each surviving parameter coefficient must vanish by contact at the selected hits. -/
theorem line_coeff_zero (w : I → K) (H res T : Geom[X]) (t r : ℕ) (Q : Row 3)
    (hT : T.natDegree ≤ 131071) (hQ : RawCut t Q) (hcontact : RawContact r w H res Q)
    (A : Finset I) (hA : A.card = 180169)
    (hhit : ∀ i ∈ A, (H * T + res).eval (embed (node i)) = embed (w i))
    (V : Geom[X]) (hV : V.natDegree ≤ 2) (j : ℕ) (hj : t + 49196 * j < r * 180169) :
    (line Q T (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ 180267 :=
    natDegree_mul_le.trans (by rw [locator_natDegree, hA]; omega)
  have hc (i : I) (hi : i ∈ A) (c : Geom) :
      (Polynomial.X - C (x i)) ^ r ∣ (line Q T U).eval (C c) := by
    rw [eval_line]
    apply hcontact i
    have hL : L.eval (x i) = 0 := locator_eval_zero x A i hi
    have hU0 : U.eval (x i) = 0 := by simp [U, hL]
    have ht : (T + c • U).eval (x i) = T.eval (x i) := by simp [eval_smul, hU0]
    change (H * (T + c • U) + res).eval (x i) = _
    rw [eval_add, eval_mul, ht, ← eval_mul, ← eval_add]
    exact hhit i hi
  have hx : Function.Injective x :=
    (RingHom.injective embed).comp IRSProfile.domain.injective
  apply K1_11.eq_zero_of_many_contacts A x hx r
  · exact fun i hi => coeff_contact _ _ _ (hc i hi) j
  · rw [hA]
    exact (line_degree Q T U t hQ hT hU j).trans_lt hj

private theorem exists_direction (L : Geom[X]) (x : Geom) (hx : L.eval x ≠ 0)
    (v : Fin 3 → Geom) :
    ∃ V : Geom[X], V.natDegree ≤ 2 ∧ ∀ i : Fin 3, (jet (L * V) i).eval x = v i := by
  classical
  let B := (Polynomial.X - C x) ^ 3
  have hB : B.Monic := (monic_X_sub_C x).pow _
  have hdeg : B.natDegree = 3 := by simp [B, natDegree_pow]
  have hcop : IsCoprime L B := by
    apply (irreducible_X_sub_C x).coprime_pow_of_not_dvd
    simpa [dvd_iff_isRoot, IsRoot] using hx
  obtain ⟨a, b, hab⟩ := hcop
  let F := taylor (-x) (ofFn 3 v)
  let V := (a * F) %ₘ B
  have hdiv : B ∣ L * V - F := by
    refine ⟨-(b * F + L * ((a * F) /ₘ B)), ?_⟩
    dsimp only [V]
    rw [modByMonic_eq_sub_mul_div]
    linear_combination F * hab
  have hjet := (X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero (L * V - F) x 3).mp hdiv
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
    rw [h, ← taylor_coeff, show F = taylor (-x) (ofFn 3 v) from rfl, taylor_taylor,
      add_neg_cancel, taylor_zero, ofFn_coeff_eq_val_of_lt v i.isLt]

/-- Along a scalar line through the origin, the coefficient at degree j
is the degree-j homogeneous component evaluated at the direction. -/
private theorem coeff_line_through_zero (P : MvPolynomial (Fin 3) Geom) (v : Fin 3 → Geom) (j : ℕ) :
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

private theorem line_at_abscissa (P : Row 3) (S U : Geom[X]) (x : Geom) :
    (line P S U).map (evalRingHom x) =
      MvPolynomial.eval₂ Polynomial.C (fun i : Fin 3 => Polynomial.C ((jet U i).eval x) *
        Polynomial.X) (MvPolynomial.map (evalRingHom x) (shiftJet P S)) := by
  let f := evalRingHom x
  let g (i : Fin 3) : Geom[X] := Polynomial.C (f (jet U i)) * Polynomial.X
  change (mapRingHom f) (MvPolynomial.eval₂ Polynomial.C
    (fun i : Fin 3 => Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X) P) =
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

private theorem order_of_locator_lines (P : Row 3) (S L : Geom[X]) (hL : L ≠ 0) (d : ℕ)
    (h : ∀ (V : Geom[X]), V.natDegree ≤ 2 → ∀ j < d, (line P S (L * V)).coeff j = 0) :
    OrderAt P S d := by
  intro m hm
  change d ≤ m.degree
  by_contra! hlt
  have hz (x : Geom) (hx : L.eval x ≠ 0) : ((shiftJet P S).coeff m).eval x = 0 := by
    let A := MvPolynomial.map (evalRingHom x) (shiftJet P S)
    let Q := MvPolynomial.homogeneousComponent m.degree A
    have hQ : Q = 0 := by
      apply (MvPolynomial.homogeneousComponent_isHomogeneous _ _).eq_zero_of_forall_eval_eq_zero
      intro v
      obtain ⟨V, hV, hv⟩ := exists_direction L x hx v
      have heval := congrArg (evalRingHom x) (h V hV m.degree hlt)
      rw [map_zero, ← Polynomial.coeff_map, line_at_abscissa] at heval
      let along (u : Fin 3 → Geom) :=
        (MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (u i) * Polynomial.X) A).coeff
          m.degree
      have hdir := congrArg along (funext hv)
      have hvanish : along v = 0 := hdir.symm.trans heval
      simpa only [along, coeff_line_through_zero] using hvanish
    have hcoeff := congrArg (fun F : MvPolynomial (Fin 3) Geom => F.coeff m) hQ
    simpa [Q, MvPolynomial.coeff_homogeneousComponent, A, MvPolynomial.coeff_map]
      using hcoeff
  have hzero : (shiftJet P S).coeff m = 0 := by
    apply eq_zero_of_infinite_isRoot
    refine (finite_setOfPred_isRoot hL).infinite_compl.mono ?_
    intro x hx
    exact hz x hx
  exact MvPolynomial.mem_support_iff.mp hm hzero

private theorem translate_map (Q : Row 3) (T : Geom[X]) :
    K1_13_4.translate (trajectory T) (MvPolynomial.map inclX Q) =
      MvPolynomial.map inclX (shiftJet Q T) := by
  let left := (K1_13_4.translate (trajectory T)).comp (MvPolynomial.map inclX)
  let right := (MvPolynomial.map inclX).comp (MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin 3 => MvPolynomial.X i + MvPolynomial.C (jet T i)))
  have h : left = right := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [left, right, K1_13_4.translate]
    · intro i
      simp [left, right, K1_13_4.translate, trajectory]
  exact DFunLike.congr_fun h Q

private theorem raw_locator : RawLocator := by
  intro w H res T t k Q hT hhits hc hQ hcut
  obtain ⟨B, hB, hhits⟩ := hhits
  obtain ⟨A, hAB, hA⟩ := Finset.exists_subset_card_eq hB
  let x (i : I) := embed (node i)
  have ho : OrderAt Q T (k + 1) := by
    apply order_of_locator_lines Q T (locator x A) (locator_monic x A).ne_zero
    intro V hV j hj
    exact line_coeff_zero w H res T t 5000 Q hT hQ hc A hA
      (fun i hi => hhits i (hAB hi)) V hV j (by omega)
  intro a
  rw [translate_map]
  intro ha
  exact ho a (MvPolynomial.support_map_subset _ _ ha)

private theorem coeff_eq_zero_of_lowerOrder {F : Lower} {x : Fin 3 → GenericX}
    {d : ℕ} (h : LowerOrder F x d) (a : Fin 3 →₀ ℕ) (ha : a.degree < d) :
    (K1_13_4.translate x F).coeff a = 0 := by
  by_contra hz
  exact (not_le_of_gt ha) (h a (MvPolynomial.mem_support_iff.mpr hz))

private theorem mixedOrder_iff_coeff {F : GenericRow} {z : GenericX}
    {y : Fin 3 → GenericX} {d : ℕ} :
    MixedOrder F z y d ↔
      ∀ a, mixedWeight a < d → (K1_13_4.translate (atPoint z y) F).coeff a = 0 := by
  constructor
  · intro h a ha
    by_contra hz
    exact (not_le_of_gt ha) (h a (MvPolynomial.mem_support_iff.mpr hz))
  · intro h a ha
    by_contra! hlt
    exact (MvPolynomial.mem_support_iff.mp ha) (h a hlt)

private theorem weight_add (a b : SeedVar →₀ ℕ) :
    mixedWeight (a + b) = mixedWeight a + mixedWeight b := by
  change 7800 * (a + b) none + 49196 * (a + b).some.degree =
    (7800 * a none + 49196 * a.some.degree) + (7800 * b none + 49196 * b.some.degree)
  simp only [Finsupp.add_apply, Finsupp.some_add, map_add, Nat.mul_add]
  ac_rfl

private theorem fixed_seed_order (h2 : K1_13_4_3.c2) (h3 : RawLocator)
    {w Γ s} (hw : Messages w Γ s) (P : PoleData Γ s) (L : ResidueChart P)
    {box t F} (hF : Source w P L box t F) {γ} (hγ : γ ∈ Γ)
    (k : ℕ) (hk : t + 49196 * k < 5000 * 180169) :
    LowerOrder (atSeed (inclConst (P.z γ)) (toGeneric F))
      (trajectory (extend (s γ))) (k + 1) := by
  let res := residueAt L.numerator L.denominator (P.z γ)
  obtain ⟨Q, hQ, hrestore⟩ := h2 w Γ s P L box t F hF γ hγ
  obtain ⟨T, hT, hST⟩ := L.quotient γ hγ
  change extend (s γ) = P.H * T + res at hST
  obtain ⟨A, hA, hhits⟩ := hw.hits γ hγ
  have hhit : ∃ B : Finset I, 180169 ≤ B.card ∧
      ∀ i ∈ B, (P.H * T + res).eval (embed (node i)) = embed (w i) := by
    refine ⟨A, hA, fun i hi => ?_⟩
    rw [← hST, extend, Polynomial.eval_map, Polynomial.eval₂_at_apply, hhits i hi]
  have hcontact := rawContact_of_restore 5000 w P.H res (P.z γ) (box.b + box.j) F Q
    P.nodes hF.2.2.1 hrestore
  have ho := h3 w P.H res T t k Q hT hhit hcontact hQ hk
  rw [hST]
  exact trueOrder_of_raw P.H res T (P.z γ) (box.b + box.j) (k + 1) F Q
    P.monic.ne_zero hrestore ho

private theorem source_order (h1 : K1_13_4_3.c1) (h2 : K1_13_4_3.c2) (h3 : RawLocator)
    {w Γ s} (hw : Messages w Γ s) (P : PoleData Γ s) (L : ResidueChart P)
    {box t F} (hF : Source w P L box t F) {γ} (hγ : γ ∈ Γ)
    {d : ℕ} (hd : t + d ≤ 5000 * 180169) :
    MixedOrder (toGeneric F) (inclConst (P.z γ)) (trajectory (extend (s γ))) d := by
  set z := inclConst (P.z γ)
  set y := trajectory (extend (s γ))
  apply mixedOrder_iff_coeff.mpr
  intro m hm
  let a : SeedVar →₀ ℕ := Finsupp.single none (m none)
  let b : SeedVar →₀ ℕ := m.some.optionElim 0
  have hab : a + b = m := by
    ext i
    cases i <;> simp [a, b]
  have hdis : ∀ i, i ∉ a.support ∨ i ∉ b.support := by
    intro i
    cases i <;> simp [a, b, Finsupp.mem_support_iff]
  have hlt : t + 7800 * m none + 49196 * m.some.degree < 5000 * 180169 := by
    change 7800 * m none + 49196 * m.some.degree < d at hm
    omega
  have hD := h1 w Γ s P L box t F hF (m none)
  have ho := fixed_seed_order h2 h3 hw P L hD hγ m.some.degree hlt
  have hc := coeff_eq_zero_of_lowerOrder ho m.some (Nat.lt_succ_self _)
  change (K1_13_4.translate y (atSeed z (toGeneric (clearedSeed P.H (m none) F)))).coeff m.some = 0 at hc
  have hmap :
      K1_13_4.translate y (atSeed z (toGeneric (clearedSeed P.H (m none) F))) =
        MvPolynomial.C (inclX (P.H ^ (3 * m none))) *
          K1_13_4.translate y (atSeed z (toGeneric (mixedHasse a F))) := by
    simp [clearedSeed, toGeneric, a, atSeed, K1_13_4.translate]
  rw [hmap, MvPolynomial.coeff_C_mul] at hc
  have hn : inclX (P.H ^ (3 * m none)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Geom[X] GenericX)).mpr (pow_ne_zero _ P.monic.ne_zero)
  have hcoef := (mul_eq_zero.mp hc).resolve_left hn
  rw [translate_atSeed, coeff_atSeed_zero, ← partial_eq_mixedHasse, toGeneric, map_partial,
    translate_partial] at hcoef
  change (hasse a (K1_13_4.translate (atPoint z y) (toGeneric F))).coeff b = 0 at hcoef
  rw [coeff_partial_eq_of_disjoint _ _ _ hdis, hab] at hcoef
  exact hcoef

private theorem mixedHasse_order (F : PhysicalRow) (a : SeedVar →₀ ℕ)
    (z : GenericX) (y : Fin 3 → GenericX) (d : ℕ)
    (hF : MixedOrder (toGeneric F) z y (d + mixedWeight a)) :
    MixedOrder (toGeneric (mixedHasse a F)) z y d := by
  apply mixedOrder_iff_coeff.mpr
  intro b hb
  have hlt : mixedWeight (a + b) < d + mixedWeight a := by rw [weight_add]; omega
  have hz := mixedOrder_iff_coeff.mp hF _ hlt
  rw [← partial_eq_mixedHasse, toGeneric, map_partial, translate_partial]
  exact coeff_partial_eq_zero _ _ _ hz

theorem source_orders (w : I → K) {Γ s} (hw : Messages w Γ s)
    (P : PoleData Γ s) (L : ResidueChart P) :
    (∀ F, Source w P L firstBox newFirstCut F → ∀ γ ∈ Γ,
      MixedOrder (toGeneric F) (inclConst (P.z γ)) (trajectory (extend (s γ))) firstMixedOrder) ∧
    (∀ G ∈ Necessary w P L, ∀ γ ∈ Γ,
      MixedOrder (toGeneric G) (inclConst (P.z γ)) (trajectory (extend (s γ))) secondMixedOrder) := by
  have h1 := K1_13_4_3_1.proof
  have h2 := K1_13_4_3_2.proof
  have h3 := raw_locator
  constructor
  · intro F hF γ hγ
    exact source_order h1 h2 h3 hw P L hF hγ (by decide)
  · intro G hG γ hγ
    let z := inclConst (P.z γ)
    let y := trajectory (extend (s γ))
    change MixedOrder (toGeneric G) z y secondMixedOrder
    change G ∈ Submodule.span Geom _ at hG
    induction hG using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨t, F, a, hF, ht, rfl⟩ := hQ
      apply mixedHasse_order
      apply source_order h1 h2 h3 hw P L hF hγ
      rw [secondCut_eq] at ht
      change t + mixedWeight a ≤ 898555006 at ht
      change t + (2289994 + mixedWeight a) ≤ 5000 * 180169
      omega
    | zero =>
      exact mixedOrder_iff_coeff.mpr (fun _ _ => by simp [toGeneric])
    | add Q R _ _ hQ hR =>
      exact mixedOrder_iff_coeff.mpr (fun a ha => by
        simp only [toGeneric, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
        exact (congrArg₂ (· + ·)
          (mixedOrder_iff_coeff.mp hQ a ha) (mixedOrder_iff_coeff.mp hR a ha)).trans (add_zero 0))
    | smul c Q _ hQ =>
      apply mixedOrder_iff_coeff.mpr
      intro a ha
      have hsmul : c • Q = MvPolynomial.C (Polynomial.C c) * Q := by
        rw [Algebra.smul_def]
        rfl
      rw [hsmul]
      simp only [toGeneric, map_mul, MvPolynomial.map_C, K1_13_4.translate, MvPolynomial.eval₂Hom_C,
        MvPolynomial.coeff_C_mul]
      exact mul_eq_zero.mpr (Or.inr (mixedOrder_iff_coeff.mp hQ a ha))

private theorem moving_lower (h1 : K1_13_4_5.c1) (h2 : K1_13_4_5.c2) (f : GenericRow)
    (hf : Irreducible f) (hb : 0 < jetTotal f) (ht : jetTotal f ≤ 10)
    (hu : 0 < seedDegree f) (htop : f.degreeOf (some 2) = 0) :
    ∃ q : Lower, q ≠ 0 ∧ q.totalDegree ≤ 2 * seedDegree f * jetTotal f ∧
      lowerIndex q ≤ (2 * jetIndex f + 1) * seedDegree f ∧
      ∀ (z : Geom) (S : Geom[X]),
        MvPolynomial.eval (atPoint (inclConst z) (trajectory S)) f = 0 →
        MvPolynomial.eval (trajectory S) q = 0 := by
  obtain ⟨g, hrel, hgu, hgb, hgj, htraj⟩ := h1 f hf hb ht hu htop
  obtain ⟨htot, hind⟩ := h2 f g
  refine ⟨actualSeedResultant f g, actual_resultant_ne_zero hf hu hrel, ?_, ?_, fun z S hz =>
    actual_resultant_vanishes hu hz (htraj z S hz)⟩
  · calc
      _ ≤ seedDegree f * jetTotal f + seedDegree f * jetTotal f :=
        htot.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hgu) (Nat.mul_le_mul_left _ hgb))
      _ = _ := by ring
  · calc
      _ ≤ seedDegree f * jetIndex f + seedDegree f * (jetIndex f + 1) :=
        hind.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hgu) (Nat.mul_le_mul_left _ hgj))
      _ = _ := by ring

private theorem total_prod {ι : Type*} (s : Finset ι) (q : ι → Lower)
    (hn : ∀ i ∈ s, q i ≠ 0) :
    (∏ i ∈ s, q i).totalDegree = ∑ i ∈ s, (q i).totalDegree := by
  simp only [← MvPolynomial.weightedTotalDegree_one]
  exact MvPolynomial.weightedTotalDegree_prod _ s q hn

private theorem index_prod {ι : Type*} (s : Finset ι) (q : ι → Lower)
    (hn : ∀ i ∈ s, q i ≠ 0) :
    lowerIndex (∏ i ∈ s, q i) = ∑ i ∈ s, lowerIndex (q i) := by
  simp only [lowerIndex_eq_weighted]
  exact MvPolynomial.weightedTotalDegree_prod _ s q hn

private theorem eval_prod_factor_ne_zero {ι : Type*} {s : Finset ι} {q : ι → Lower}
    {y : Fin 3 → GenericX} (hq : MvPolynomial.eval y (∏ i ∈ s, q i) ≠ 0)
    {i : ι} (hi : i ∈ s) : MvPolynomial.eval y (q i) ≠ 0 :=
  (Finset.prod_ne_zero_iff.mp (by simpa only [map_prod] using hq)) i hi

private theorem remove_common_factors (Γ : Finset K) (z : K → Geom) (S : K → Geom[X])
    (hzinj : Function.Injective z) (F G : GenericRow) (D : CommonPair F G)
    (hOrders : ∀ γ ∈ Γ, NewPairOrders F G (inclConst (z γ)) (trajectory (S γ))) :
    ∃ (book : Finset K) (Q : Lower), book.card ≤ 140000 ∧ Q ≠ 0 ∧
      Q.totalDegree ≤ 6300 ∧ lowerIndex Q ≤ 2403 ∧
      ∀ γ ∈ Γ, γ ∉ book → MvPolynomial.eval (trajectory (S γ)) Q = 0 ∨
        NewPairOrders D.left D.right (inclConst (z γ)) (trajectory (S γ)) := by
  classical
  have h1 := K1_13_4_5_1.proof
  have h2 := K1_13_4_5_2.proof
  have fix_ne (f : GenericRow) (hf : f ∈ D.fixed) : f ≠ 0 :=
    (D.fixed_kind f hf).1.ne_zero
  have mov_ne (f : GenericRow) (hf : f ∈ D.moving) : f ≠ 0 :=
    (D.moving_kind f hf).1.ne_zero
  have mov_total : (∑ f ∈ D.moving, jetTotal f) ≤ 10 := by
    simpa only [jetTotal, MvPolynomial.weightedTotalDegree_prod _ _ _ mov_ne]
      using D.moving_total
  have mov_index : (∑ f ∈ D.moving, jetIndex f) ≤ 3 := by
    simpa only [jetIndex, MvPolynomial.weightedTotalDegree_prod _ _ _ mov_ne]
      using D.moving_index
  have mov_seed : (∑ f ∈ D.moving, seedDegree f) ≤ 112 := by
    simpa only [seedDegree, MvPolynomial.degreeOf_prod_eq _ _ mov_ne] using D.moving_seed
  have seed_le (f : GenericRow) (hf : f ∈ D.moving) : seedDegree f ≤ 112 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans mov_seed
  choose! q qn qt qi qe using
    (fun f hf => fixed_lower f (fix_ne f hf) (D.fixed_kind f hf).2.2)
  have exists_moving (f : GenericRow) (hf : f ∈ D.moving) :=
    moving_lower h1 h2 f (D.moving_kind f hf).1 (D.moving_kind f hf).2.1
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans mov_total)
      (D.moving_kind f hf).2.2.1 (D.moving_kind f hf).2.2.2
  choose! r rn rt ri re using exists_moving
  let P : Lower := ∏ f ∈ D.fixed, q f
  let R : Lower := ∏ f ∈ D.moving, r f
  have Pn : P ≠ 0 := Finset.prod_ne_zero_iff.mpr qn
  have Rn : R ≠ 0 := Finset.prod_ne_zero_iff.mpr rn
  have Pt : P.totalDegree ≤ 68 := by
    change (∏ f ∈ D.fixed, q f).totalDegree ≤ 68
    rw [total_prod _ _ qn]
    calc
      _ = ∑ f ∈ D.fixed, jetTotal f := Finset.sum_congr rfl qt
      _ ≤ _ := by
        simpa only [jetTotal, MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_total
  have Pi : lowerIndex P ≤ 23 := by
    change lowerIndex (∏ f ∈ D.fixed, q f) ≤ 23
    rw [index_prod _ _ qn]
    calc
      _ = ∑ f ∈ D.fixed, jetIndex f := Finset.sum_congr rfl qi
      _ ≤ _ := by
        simpa only [jetIndex, MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_index
  have Rt : R.totalDegree ≤ 2 * 112 * 10 := by
    change (∏ f ∈ D.moving, r f).totalDegree ≤ 2 * 112 * 10
    rw [total_prod _ _ rn]
    calc
      _ ≤ ∑ f ∈ D.moving, (2 * 112) * jetTotal f :=
        Finset.sum_le_sum fun f hf => (rt f hf).trans
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (seed_le f hf)))
      _ ≤ _ := by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ mov_total
  have Ri : lowerIndex R ≤ (2 * 3 + 1) * 112 := by
    change lowerIndex (∏ f ∈ D.moving, r f) ≤ (2 * 3 + 1) * 112
    rw [index_prod _ _ rn]
    calc
      _ ≤ ∑ f ∈ D.moving, ((2 * 112) * jetIndex f + seedDegree f) := by
        apply Finset.sum_le_sum
        intro f hf
        refine (ri f hf).trans ?_
        rw [Nat.add_mul, one_mul, Nat.mul_right_comm 2]
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (seed_le f hf))) _
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have hh := Nat.mul_le_mul_left (2 * 112) mov_index
        omega
  let book := seedBook Γ z D.pure
  have hbook : book.card ≤ 140000 :=
    (count_seed_roots Γ z hzinj D.pure D.pure_ne).trans D.pure_degree
  refine ⟨book, P * R, hbook, mul_ne_zero Pn Rn, ?_, ?_, ?_⟩
  · simp only [← MvPolynomial.weightedTotalDegree_one] at Pt Rt ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pt Rt).trans native_degree_arithmetic.2.2.1
  · simp only [lowerIndex_eq_weighted] at Pi Ri ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pi Ri).trans native_degree_arithmetic.2.2.2
  · intro γ hγ hnot
    let a := inclConst (z γ)
    let y := trajectory (S γ)
    change MvPolynomial.eval y (P * R) = 0 ∨ NewPairOrders D.left D.right a y
    by_cases hn : MvPolynomial.eval y (P * R) = 0
    · exact Or.inl hn
    rw [map_mul] at hn
    have hfixed (f : GenericRow) (hf : f ∈ D.fixed) :
        MvPolynomial.eval (atPoint a y) f ≠ 0 := by
      rw [qe f hf]
      exact eval_prod_factor_ne_zero (left_ne_zero_of_mul hn) hf
    have hmoving (f : GenericRow) (hf : f ∈ D.moving) :
        MvPolynomial.eval (atPoint a y) f ≠ 0 := by
      intro h0
      exact (eval_prod_factor_ne_zero (right_ne_zero_of_mul hn) hf) (re f hf _ _ h0)
    have hp : D.pure.eval a ≠ 0 := fun he => hnot (mem_seedBook.mpr ⟨hγ, he⟩)
    let A := pureSeed D.pure * (∏ f ∈ D.fixed, f ^ D.exponent f) *
      (∏ f ∈ D.moving, f ^ D.exponent f)
    have hA : MvPolynomial.eval (atPoint a y) A ≠ 0 := by
      simp only [A, map_mul, map_prod, map_pow, pure_eval]
      exact mul_ne_zero (mul_ne_zero hp (Finset.prod_ne_zero_iff.mpr
        fun f hf => pow_ne_zero _ (hfixed f hf))) (Finset.prod_ne_zero_iff.mpr
        fun f hf => pow_ne_zero _ (hmoving f hf))
    refine Or.inr ⟨mixedOrder_cancel A D.left a y _ hA ?_,
      mixedOrder_cancel A D.right a y _ hA ?_⟩
    · simpa only [A, ← D.left_eq] using (hOrders γ hγ).1
    · simpa only [A, ← D.right_eq] using (hOrders γ hγ).2

private theorem mixedWeight_add (a b : SeedVar →₀ ℕ) :
    mixedWeight (a + b) = mixedWeight a + mixedWeight b := by
  have hsum (m : Fin 3 →₀ ℕ) :
      m.sum (fun _ e => e) = Finsupp.weight (fun _ : Fin 3 => (1 : ℕ)) m := by
    simp [Finsupp.weight_apply]
  simp only [mixedWeight, hsum, Finsupp.add_apply, Finsupp.some_add, map_add, Nat.mul_add]
  ac_rfl

private theorem mixedOrder_pad {F : GenericRow} {z : GenericX} {y : Fin 3 → GenericX}
    {d : ℕ} (a : Geom[X]) (h : MixedOrder F z y d) :
    MixedOrder (pad F a) z y d := by
  classical
  intro m hm
  rw [pad, map_mul] at hm
  obtain ⟨u, hu, v, _, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  exact (h u hu).trans (by rw [mixedWeight_add]; exact Nat.le_add_right _ _)

private theorem resultant_taylor_formal {R : Type*} [CommRing R]
    (F G : R[X]) (z : R) {m n : ℕ} (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n) :
    resultant (F.taylor z) (G.taylor z) m n = resultant F G m n := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hF
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hG
  have expand (P Q : R[X]) :
      resultant P Q (P.natDegree + a) (Q.natDegree + b) =
        (-1) ^ ((Q.natDegree + b) * a) * Q.coeff (Q.natDegree + b) ^ a *
          (P.leadingCoeff ^ b * resultant P Q) := by
    rw [resultant_add_left_deg _ _ _ _ _ le_rfl,
      resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree]
  have coeff_preserved :
      (G.taylor z).coeff (G.natDegree + b) = G.coeff (G.natDegree + b) := by
    by_cases hb : b = 0
    · simp [hb]
    · have hlt : G.natDegree < G.natDegree + b := by omega
      rw [coeff_eq_zero_of_natDegree_lt hlt,
        coeff_eq_zero_of_natDegree_lt (by simpa only [natDegree_taylor] using hlt)]
  have h := expand (F.taylor z) (G.taylor z)
  rw [resultant_taylor] at h
  simp only [natDegree_taylor, leadingCoeff_taylor, coeff_preserved] at h
  exact h.trans (expand F G).symm

/-- The part of a mixed order still required after accounting for a seed exponent. -/
private def weight (d i : ℕ) : ℕ := d - 7800 * i

-- Put the variable in the recursive argument of Nat.add.
private def power (w : ℕ) : ℕ := (49195 + w) / 49196

private theorem coefficient_bound {k : Type*} [CommRing k]
    (P : k[X][X]) (d e i j : ℕ) (hij : j ≤ i)
    (hP : ∀ i l : ℕ, 7800 * i + 49196 * l < d → (P.coeff i).coeff l = 0) :
    (Polynomial.X : k[X]) ^ power (weight (d + e) i - weight e j) ∣ P.coeff (i - j) := by
  have hweight : weight (d + e) i ≤ weight e j + weight d (i - j) := by
    unfold weight
    omega
  apply X_pow_dvd_iff.mpr
  intro l hl
  apply hP
  unfold power at hl
  have hsmall : 49196 * l < weight (d + e) i - weight e j := by omega
  unfold weight at hweight hsmall
  omega

/-- The two sets of columns shift the coefficients of G and F, respectively.
Each column uses the weight for the opposite polynomial at its shift. -/
private def columnWeight {m n : ℕ} (j : Fin (m + n)) : ℕ :=
  j.addCases (fun j : Fin m => weight firstMixedOrder j) (fun j : Fin n => weight secondMixedOrder j)

private theorem sylvester_entry {k : Type*} [CommRing k]
    (F G : k[X][X]) (m n : ℕ)
    (hF : ∀ i l : ℕ, 7800 * i + 49196 * l < firstMixedOrder → (F.coeff i).coeff l = 0)
    (hG : ∀ i l : ℕ, 7800 * i + 49196 * l < secondMixedOrder → (G.coeff i).coeff l = 0)
    (i j : Fin (m + n)) :
    (Polynomial.X : k[X]) ^ power (weight (firstMixedOrder + secondMixedOrder) i - columnWeight j) ∣
      sylvester F G m n i j := by
  induction j using Fin.addCases with
  | left j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left, columnWeight, Set.mem_Icc]
    split_ifs with h
    · simpa only [add_comm secondMixedOrder firstMixedOrder] using
        coefficient_bound G secondMixedOrder firstMixedOrder i j h.1 hG
    · exact dvd_zero _
  | right j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_right, columnWeight, Set.mem_Icc]
    split_ifs with h
    · exact coefficient_bound F firstMixedOrder secondMixedOrder i j h.1 hF
    · exact dvd_zero _

/-- Every Leibniz term uses every row and every column once. Summing the
entry powers therefore bounds the divisibility of each whole term. -/
private theorem det_bound {k : Type*} [CommRing k] {N D : ℕ}
    (M : Matrix (Fin N) (Fin N) k[X]) (row col : Fin N → ℕ)
    (hM : ∀ i j, (Polynomial.X : k[X]) ^ power (row i - col j) ∣ M i j)
    (hbudget : (∑ j, col j) + 49196 * D ≤ (∑ i, row i) + 49195) :
    (Polynomial.X : k[X]) ^ D ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  let a : Fin N → ℕ := fun j => power (row (σ j) - col j)
  have hprod : (Polynomial.X : k[X]) ^ (∑ j, a j) ∣ ∏ j, M (σ j) j := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => hM (σ j) j)
  have hsum : (∑ i, row i) ≤ (∑ j, col j) + 49196 * (∑ j, a j) := by
    rw [← Equiv.sum_comp σ row, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    dsimp only [a, power]
    omega
  have hD : D ≤ ∑ j, a j := by omega
  exact dvd_mul_of_dvd_right ((pow_dvd_pow _ hD).trans hprod) _

private theorem sum_weight {d t N : ℕ} (ht : t ≤ N) (hend : d ≤ 7800 * t)
    (hbefore : ∀ i < t, 7800 * i ≤ d) :
    (∑ i : Fin N, weight d i) = t * d - 7800 * (t * (t - 1) / 2) := by
  rw [Fin.sum_univ_eq_sum_range]
  have htrim : (∑ i ∈ Finset.range t, weight d i) = ∑ i ∈ Finset.range N, weight d i := by
    apply Finset.sum_subset (Finset.range_mono ht)
    intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    unfold weight
    omega
  rw [← htrim]
  have hsum : (∑ i ∈ Finset.range t, weight d i) + 7800 * (∑ i ∈ Finset.range t, i) =
      t * d := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _i ∈ Finset.range t, d := by
        apply Finset.sum_congr rfl
        intro i hi
        have h := hbefore i (Finset.mem_range.mp hi)
        unfold weight
        omega
      _ = _ := by simp [Nat.mul_comm]
  rw [Finset.sum_range_id] at hsum
  omega

private theorem benchmark_budget :
    (∑ j : Fin (70000 + 70000), columnWeight (m := 70000) (n := 70000) j) + 49196 * 41482 ≤
      (∑ i : Fin (70000 + 70000), weight (firstMixedOrder + secondMixedOrder) i) + 49195 := by
  have hF : (∑ i : Fin 70000, weight firstMixedOrder i) = 3100681200 := by
    rw [sum_weight (t := 892) (by decide) (by decide)
      (by intro i hi; simp only [firstMixedOrder]; omega)]
    decide
  have hG : (∑ i : Fin 70000, weight secondMixedOrder i) = 337304436 := by
    rw [sum_weight (t := 294) (by decide) (by decide)
      (by intro i hi; simp only [secondMixedOrder]; omega)]
    decide
  have hFG : (∑ i : Fin (70000 + 70000), weight (firstMixedOrder + secondMixedOrder) i) =
      5478721890 := by
    rw [sum_weight (t := 1185) (by decide) (by decide)
      (by intro i hi; simp only [firstMixedOrder, secondMixedOrder]; omega)]
    decide
  rw [Fin.sum_univ_add, hFG]
  simp only [columnWeight, Fin.addCases_left, Fin.addCases_right, hF, hG]
  decide

private theorem resultant_bound
    (F G : GenericX[X][X]) (z : GenericX) {m n D : ℕ} (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n)
    (hFO : ∀ i l : ℕ, 7800 * i + 49196 * l < firstMixedOrder →
      ((F.taylor (C z)).coeff i).coeff l = 0)
    (hGO : ∀ i l : ℕ, 7800 * i + 49196 * l < secondMixedOrder →
      ((G.taylor (C z)).coeff i).coeff l = 0)
    (hbudget : (∑ j : Fin (m + n), columnWeight (m := m) (n := n) j) + 49196 * D ≤
      (∑ i : Fin (m + n), weight (firstMixedOrder + secondMixedOrder) i) + 49195) :
    (Polynomial.X : GenericX[X]) ^ D ∣ resultant F G m n := by
  rw [← resultant_taylor_formal F G (C z) hF hG]
  unfold resultant
  exact det_bound
    (sylvester (F.taylor (C z)) (G.taylor (C z)) m n)
    (fun i => weight (firstMixedOrder + secondMixedOrder) i)
    (columnWeight (m := m) (n := n))
    (sylvester_entry _ _ m n hFO hGO) hbudget

/-- R8's local bound, obtained by counting the powers in the fixed-size determinant. -/
private theorem local_sylvester_bound (F G : GenericX[X][X]) (z : GenericX)
    (hF : F.natDegree ≤ 70000) (hG : G.natDegree ≤ 70000)
    (hFO : LineOrder F z firstMixedOrder) (hGO : LineOrder G z secondMixedOrder) :
    Polynomial.X ^ 41482 ∣ Polynomial.resultant F G 70000 70000 := by
  exact resultant_bound F G z hF hG hFO hGO benchmark_budget

private def ray (v : Fin 3 → GenericX) : Lower →+* GenericX[X] :=
  MvPolynomial.eval₂Hom C (fun i => C (v i) * Polynomial.X)

private theorem ray_monomial (v : Fin 3 → GenericX) (a : Fin 3 →₀ ℕ) (c : GenericX) :
    ray v (MvPolynomial.monomial a c) =
      monomial a.degree (MvPolynomial.eval v (MvPolynomial.monomial a c)) := by
  rw [← C_mul_X_pow_eq_monomial]
  simp only [ray, MvPolynomial.eval₂Hom_monomial, MvPolynomial.eval_monomial, mul_pow,
    Finsupp.prod]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply, ← mul_assoc]
  simp only [map_mul, map_prod, map_pow]

private theorem ray_coeff (v : Fin 3 → GenericX) (Q : Lower) (j : ℕ) :
    (ray v Q).coeff j = MvPolynomial.eval v (MvPolynomial.homogeneousComponent j Q) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [ray_monomial, coeff_monomial,
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl)]
    by_cases h : a.degree = j
    · simp [h]
    · simp [h, Ne.symm h]
  | add Q R hQ hR =>
    rw [map_add, coeff_add, hQ, hR, map_add, map_add]

private theorem line_translation (F : GenericRow) (z : GenericX) (y v : Fin 3 → GenericX) :
    ((asSeedPoly F).map ((ray v).comp (translate y))).comp (Polynomial.X + C (C z)) =
      (asSeedPoly (translate (atPoint z y) F)).map (ray v) := by
  let e := (MvPolynomial.optionEquivLeft GenericX (Fin 3)).toRingHom
  let left := (compRingHom (Polynomial.X + C (C z))).comp ((mapRingHom ((ray v).comp (translate y))).comp e)
  let right := (mapRingHom (ray v)).comp (e.comp (translate (atPoint z y)))
  have he : left = right := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [left, right, e, translate, ray]
    · intro i
      cases i <;>
        simp [left, right, e, translate, ray, atPoint]
  exact DFunLike.congr_fun he F

private theorem line_order (F : GenericRow) (z : GenericX) (y v : Fin 3 → GenericX)
    (d : ℕ) (hF : MixedOrder F z y d) :
    LineOrder ((asSeedPoly F).map ((ray v).comp (translate y))) z d := by
  intro i j h
  rw [line_translation, coeff_map, ray_coeff]
  suffices hc : MvPolynomial.homogeneousComponent j
      ((asSeedPoly (translate (atPoint z y) F)).coeff i) = 0 by
    rw [hc, map_zero]
  apply MvPolynomial.homogeneousComponent_eq_zero'
  intro a ha hj
  have hmem : a.optionElim i ∈ (translate (atPoint z y) F).support := by
    rw [← MvPolynomial.mem_support_coeff_optionEquivLeft]
    exact ha
  have hb := hF _ hmem
  have hweight : mixedWeight (a.optionElim i) = 7800 * i + 49196 * j := by
    change 7800 * a.optionElim i none + 49196 * (a.optionElim i).some.degree = _
    rw [Finsupp.optionElim_apply_none, Finsupp.some_optionElim, hj]
  rw [hweight] at hb
  exact (Nat.not_lt_of_ge hb) h

private theorem order_of_rays (Q : Lower) (y : Fin 3 → GenericX) (d : ℕ)
    (h : ∀ v, Polynomial.X ^ d ∣ ray v (translate y Q)) :
    LowerOrder Q y d := by
  let _ : Infinite GenericX := Infinite.of_injective inclConst inclConst.injective
  intro a ha
  change d ≤ a.degree
  by_contra! ha'
  have hm : MvPolynomial.homogeneousComponent a.degree (translate y Q) = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_zero, ← ray_coeff]
    exact (X_pow_dvd_iff (n := d) (f := ray v (translate y Q))).mp (h v) a.degree ha'
  have hc := congrArg (fun P : Lower => P.coeff a) hm
  simp [MvPolynomial.coeff_homogeneousComponent] at hc
  exact (MvPolynomial.mem_support_iff.mp ha) hc

private theorem line_resultant (F G : GenericRow) (y v : Fin 3 → GenericX) :
    resultant ((asSeedPoly F).map ((ray v).comp (translate y)))
      ((asSeedPoly G).map ((ray v).comp (translate y))) 70000 70000 =
        ray v (translate y (seedResultant F G)) := by
  unfold seedResultant
  rw [resultant_map_map, RingHom.comp_apply]


theorem resultant_order (F G : GenericRow) (z : GenericX) (y : Fin 3 → GenericX)
    (hF : (asSeedPoly F).natDegree ≤ 70000) (hG : (asSeedPoly G).natDegree ≤ 70000)
    (h : NewPairOrders F G z y) :
    LowerOrder (seedResultant F G) y 41482 := by
  apply order_of_rays
  intro v
  rw [← line_resultant F G y v]
  exact local_sylvester_bound _ _ z (natDegree_map_le.trans hF) (natDegree_map_le.trans hG)
    (line_order F z y v _ h.1) (line_order G z y v _ h.2)

private theorem inclX_injective : Function.Injective inclX :=
  IsFractionRing.injective Geom[X] GenericX

private theorem clear_denominators (R : Lower) :
    ∃ (d : Geom[X]) (Q : Row 3), d ≠ 0 ∧ Q.support = R.support ∧
      MvPolynomial.map inclX Q = MvPolynomial.C (inclX d) * R := by
  classical
  let M := nonZeroDivisors (Geom[X])
  let d := IsLocalization.commonDenom M R.support R.coeff
  let num := IsLocalization.integerMultiple M R.support R.coeff
  let Q : Row 3 := ∑ a : ↥R.support, MvPolynomial.monomial a.val (num a)
  have hd : (d : Geom[X]) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hi : inclX (d : Geom[X]) ≠ 0 := (map_ne_zero_iff inclX inclX_injective).mpr hd
  have hQ : MvPolynomial.map inclX Q = MvPolynomial.C (inclX d) * R := by
    ext m
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, Q, MvPolynomial.coeff_sum]
    by_cases hm : m ∈ R.support
    · let a : ↥R.support := ⟨m, hm⟩
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
      · have hn := IsLocalization.map_integerMultiple M R.support R.coeff a
        change inclX (num a) = (d : Geom[X]) • R.coeff a.val at hn
        rw [Algebra.smul_def] at hn
        simpa [a] using hn
      · intro b _ hba
        have hb : b.val ≠ m := fun h => hba (Subtype.ext h)
        simp [MvPolynomial.coeff_monomial, hb]
    · have hz : R.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
      have hz' : (∑ a : ↥R.support,
          (MvPolynomial.monomial a.val (num a) : Row 3).coeff m) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        have ha : a.val ≠ m := fun h => hm (h ▸ a.property)
        simp [MvPolynomial.coeff_monomial, ha]
      rw [hz', hz, map_zero, mul_zero]
  refine ⟨d, Q, hd, ?_, hQ⟩
  rw [← MvPolynomial.support_map_of_injective Q inclX_injective, hQ]
  ext m
  simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, hi]

private theorem eval_cleared {Q : Row 3} {R : Lower} {d : Geom[X]}
    (hQ : MvPolynomial.map inclX Q = MvPolynomial.C (inclX d) * R) (S : Geom[X])
    (hR : MvPolynomial.eval (trajectory S) R = 0) : atJet Q S = 0 := by
  have hcomm : inclX (atJet Q S) =
      MvPolynomial.eval (trajectory S) (MvPolynomial.map inclX Q) := by
    rw [atJet, MvPolynomial.eval_map]
    exact MvPolynomial.eval₂_comp inclX (jet S) Q
  apply inclX_injective
  rw [map_zero, hcomm, hQ, map_mul, hR, mul_zero]

private theorem map_shift (Q : Row 3) (S : Geom[X]) :
    MvPolynomial.map inclX (shiftJet Q S) =
      translate (trajectory S) (MvPolynomial.map inclX Q) := by
  have hc : (MvPolynomial.map (σ := Fin 3) inclX).comp MvPolynomial.C =
      MvPolynomial.C.comp inclX := by
    apply RingHom.ext
    intro x
    simp
  unfold K1_13.shiftJet
  rw [MvPolynomial.eval₂_comp_left]
  change _ = MvPolynomial.eval₂ MvPolynomial.C
    (fun i => MvPolynomial.X i + MvPolynomial.C (trajectory S i)) (MvPolynomial.map inclX Q)
  rw [MvPolynomial.eval₂_map, hc]
  congr 1
  funext i
  simp [trajectory]

private theorem order_cleared {Q : Row 3} {R : Lower} {d : Geom[X]}
    (hQ : MvPolynomial.map inclX Q = MvPolynomial.C (inclX d) * R)
    (S : Geom[X]) {m : ℕ} (hR : LowerOrder R (trajectory S) m) : OrderAt Q S m := by
  have hs : MvPolynomial.map inclX (shiftJet Q S) =
      MvPolynomial.C (inclX d) * translate (trajectory S) R := by
    rw [map_shift, hQ, map_mul, translate, MvPolynomial.eval₂Hom_C]
  intro a ha
  apply hR
  have hcoeff := congrArg (fun P : Lower => P.coeff a) hs
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul] at hcoeff
  rw [MvPolynomial.mem_support_iff] at ha ⊢
  intro hz
  rw [hz, mul_zero] at hcoeff
  exact ha (inclX_injective (hcoeff.trans (map_zero _).symm))

private theorem lowerOrder_mono {R : Lower} {y : Fin 3 → GenericX} {d e : ℕ}
    (hde : d ≤ e) (h : LowerOrder R y e) : LowerOrder R y d :=
  fun m hm => hde.trans (h m hm)

/-- The retuned pole sources yield the published fat-equation conclusion at 180169 hits. -/
theorem fat_equations (w : I → K) {Γ s} (hw : Messages w Γ s) (P : PoleData Γ s)
    (hsmall : P.H.natDegree ≤ 2447) :
    ∃ (book : Finset K) (E : FatEquations), book.card ≤ 140000 ∧
      ∀ γ ∈ Γ, γ ∉ book → E.holds (extend (s γ)) := by
  obtain ⟨L⟩ := K1_13_4_1.proof Γ s P
  obtain ⟨⟨F, neF, hF⟩, rank2⟩ := source_pair_rank w P L hsmall
  obtain ⟨vanishes1, vanishes2⟩ := source_orders w hw P L
  have h4 := K1_13_4_4.of_children K1_13_4_4_1.proof K1_13_4_4_2.proof
  have h6 := K1_13_4_6.proof
  obtain ⟨G, hG, ⟨D⟩⟩ := h4 w Γ s P L F neF hF.1 rank2
  have hOrders : ∀ γ ∈ Γ, NewPairOrders (toGeneric F) (toGeneric G)
      (inclConst (P.z γ)) (trajectory (extend (s γ))) := fun γ hγ =>
    ⟨vanishes1 F hF γ hγ, vanishes2 G hG γ hγ⟩
  obtain ⟨book, Q, hcard, hQ, htQ, hiQ, hcover⟩ :=
    remove_common_factors Γ P.z (fun γ => extend (s γ)) P.injective _ _ D hOrders
  obtain ⟨J⟩ := h6 D.left D.right D.left_ne D.right_ne D.proper D.left_caps D.right_caps
  let R := seedResultant (pad D.left J.a) (pad D.right J.b)
  obtain ⟨dQ, Q', _, suppQ, mapQ⟩ := clear_denominators Q
  obtain ⟨dR, R', _, suppR, mapR⟩ := clear_denominators R
  have neQ : Q' ≠ 0 := by
    intro h
    rw [h, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at suppQ
    exact hQ suppQ
  have neR : R' ≠ 0 := by
    intro h
    rw [h, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at suppR
    exact J.nonzero suppR
  have totalQ : Q'.totalDegree ≤ 6300 := by
    simpa only [MvPolynomial.totalDegree, suppQ] using htQ
  have indexQ : indexDegree Q' ≤ 2403 := by
    simpa only [K1_13.indexDegree, lowerIndex, suppQ] using hiQ
  have totalR : R'.totalDegree ≤ 952630000 := by
    have htR : R.totalDegree ≤ 952630000 := J.total
    simpa only [MvPolynomial.totalDegree, suppR] using htR
  have indexR : indexDegree R' ≤ 322000000 := by
    have hiR : lowerIndex R ≤ 322000000 := J.index
    simpa only [K1_13.indexDegree, lowerIndex, suppR] using hiR
  refine ⟨book, ⟨Q', R', neQ, neR, totalQ, indexQ, totalR, indexR⟩, hcard, ?_⟩
  intro γ hγ hb
  rcases hcover γ hγ hb with he | ho
  · exact Or.inl (eval_cleared mapQ _ he)
  · refine Or.inr (order_cleared mapR _ ?_)
    have hr : LowerOrder R (trajectory (extend (s γ))) 41482 :=
      resultant_order (pad D.left J.a) (pad D.right J.b) (inclConst (P.z γ))
        (trajectory (extend (s γ))) J.degree_left.le J.degree_right.le
        ⟨mixedOrder_pad J.a ho.1, mixedOrder_pad J.b ho.2⟩
    exact lowerOrder_mono (R := R) (by decide : 41481 ≤ 41482) hr

end
end LowFat6921
