import ProximityPrize.SubmissionLower.Final50FatDefs

set_option Elab.async false
section Top_Final50FatContacts
namespace Final50FatContacts
noncomputable section
open Polynomial K1 K1_13 K1_13_4 K1_13_4_3 FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
open private line eval_line coeff_contact order_of_locator_lines translate_map from ProximityPrize.SubmissionLower.PortLow4
set_option maxRecDepth 12000
private def Bounded (F : Polynomial Geom[X]) (b : ℕ) : Prop :=
  ∀ j, (F.coeff j).natDegree ≤ b + 48817 * j
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
    (hQ : RawCut t Q) (hT : T.natDegree ≤ 131071) (hU : U.natDegree ≤ 179888)
    (j : ℕ) : ((line Q T U).coeff j).natDegree ≤ t + 48817 * j := by
  let b (i : Fin 3) : ℕ := 131071 - i.val
  let F (i : Fin 3) : Polynomial Geom[X] :=
    Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 3) : Bounded (F i) (b i) := by
    intro k
    have ht : (jet T i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le T i.val).trans (Nat.sub_le_sub_right hT _)
    have hu : (jet U i).natDegree ≤ b i + 48817 := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi := i.isLt
      change 179888 - i.val ≤ (131071 - i.val) + 48817
      omega
    change ((F i).coeff k).natDegree ≤ b i + 48817 * k
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
private theorem line_coeff_zero (w : I → K) (H res T : Geom[X]) (t r : ℕ) (Q : Row 3)
    (hT : T.natDegree ≤ 131071) (hQ : RawCut t Q) (hcontact : RawContact r w H res Q)
    (A : Finset I) (hA : A.card = 179886)
    (hhit : ∀ i ∈ A, (H * T + res).eval (embed (node i)) = embed (w i))
    (V : Geom[X]) (hV : V.natDegree ≤ 2) (j : ℕ) (hj : t + 48817 * j < r * 179886) :
    (line Q T (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ 179888 :=
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
theorem raw_locator_order (w : I → K) (H res T : Geom[X]) (t k : ℕ) (Q : Row 3)
    (hT : T.natDegree ≤ 131071)
    (hhits : ∃ A : Finset I, 179886 ≤ A.card ∧
      ∀ i ∈ A, (H * T + res).eval (embed (node i)) = embed (w i))
    (hc : RawContact 5000 w H res Q) (hQ : RawCut t Q)
    (hcut : t + 48817 * k < 5000 * 179886) :
    LowerOrder (MvPolynomial.map inclX Q) (trajectory T) (k + 1) := by
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
end
end Final50FatContacts
end Top_Final50FatContacts
section
namespace Final50FatContacts
noncomputable section
open K1 K1_13 K1_13_4_3 Final50Fat
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
open private coeff_scalar support_seed weight_shift from ProximityPrize.SubmissionLower.Fast050
open private coeff_eq_zero_of_lowerOrder from ProximityPrize.SubmissionLower.Fast050
private theorem trueCut_seed (H : Geom[X]) (i t : ℕ) (F : PhysicalRow)
    (hH : H.natDegree ≤ 2413) (hF : TrueCut H.natDegree t F) :
    TrueCut H.natDegree (t + 7239 * i) (clearedSeed H i F) := by
  intro b hb
  obtain ⟨u, hu⟩ := coeff_scalar F i b
  have hbefore := hF _ (support_seed hb)
  let w : SeedVar → ℕ := fun j => j.elim 0 (fun k => 131071 + H.natDegree - k.val)
  have hw (a : SeedVar →₀ ℕ) :
      a.sum (fun j e => j.elim 0 (fun k => (131071 + H.natDegree - k.val) * e)) =
        Finsupp.weight w a := by
    rw [Finsupp.weight_apply]
    congr 1
    funext j e
    cases j <;> simp [w, Nat.mul_comm]
  rw [hw, weight_shift w rfl] at hbefore
  rw [hw]
  have hcoeff : ((clearedSeed H i F).coeff b).natDegree ≤
      (H ^ (3 * i)).natDegree + (F.coeff (Finsupp.single none i + b)).natDegree := by
    simp only [clearedSeed, ← partial_eq_mixedHasse, MvPolynomial.coeff_C_mul, hu]
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add_left (Polynomial.natDegree_mul_C_le _ _) _)
  have hp' : (H ^ (3 * i)).natDegree ≤ 7239 * i := by
    calc
      _ ≤ (3 * i) * H.natDegree := Polynomial.natDegree_pow_le
      _ ≤ (3 * i) * 2413 := Nat.mul_le_mul_left _ hH
      _ = 7239 * i := by ring
  omega
private theorem seed_motion (w : I → K) {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (hh : P.H.natDegree ≤ 2413) (box : Shape) (t : ℕ) (F : PhysicalRow)
    (hF : Source w P L box t F) (i : ℕ) :
    Source w P L box (t + 7239 * i) (clearedSeed P.H i F) := by
  obtain ⟨hcap, hcut, hcontact, hpole⟩ := hF
  refine ⟨K1_13_4_3_1.caps_seed P.H i F box hcap, ?_, K1_13_4_3_1.contact_seed P.H i w F hcontact,
    K1_13_4_3_1.pole_seed P L _ i F hpole⟩
  simpa only [Nat.add_right_comm] using trueCut_seed P.H i _ F hh hcut
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
private theorem fixed_seed_order (h2 : K1_13_4_3.c2)
    {w Γ s} (hw : Final50Fat.Messages w Γ s) (P : PoleData Γ s) (L : ResidueChart P)
    {box t F} (hF : Source w P L box t F) {γ} (hγ : γ ∈ Γ)
    (k : ℕ) (hk : t + 48817 * k < 5000 * 179886) :
    LowerOrder (atSeed (inclConst (P.z γ)) (toGeneric F))
      (trajectory (extend (s γ))) (k + 1) := by
  let res := residueAt L.numerator L.denominator (P.z γ)
  obtain ⟨Q, hQ, hrestore⟩ := h2 w Γ s P L box t F hF γ hγ
  obtain ⟨T, hT, hST⟩ := L.quotient γ hγ
  change extend (s γ) = P.H * T + res at hST
  obtain ⟨A, hA, hhits⟩ := hw.hits γ hγ
  have hhit : ∃ B : Finset I, 179886 ≤ B.card ∧
      ∀ i ∈ B, (P.H * T + res).eval (embed (node i)) = embed (w i) := by
    refine ⟨A, hA, fun i hi => ?_⟩
    rw [← hST, extend, Polynomial.eval_map, Polynomial.eval₂_at_apply, hhits i hi]
  have hcontact := rawContact_of_restore 5000 w P.H res (P.z γ) (box.b + box.j) F Q
    P.nodes hF.2.2.1 hrestore
  have ho := raw_locator_order w P.H res T t k Q hT hhit hcontact hQ hk
  rw [hST]
  exact trueOrder_of_raw P.H res T (P.z γ) (box.b + box.j) (k + 1) F Q
    P.monic.ne_zero hrestore ho
private theorem source_order (h2 : K1_13_4_3.c2)
    {w Γ s} (hw : Final50Fat.Messages w Γ s) (P : PoleData Γ s) (L : ResidueChart P)
    {box t F} (hF : Source w P L box t F) {γ} (hγ : γ ∈ Γ)
    (hh : P.H.natDegree ≤ 2413) {d : ℕ} (hd : t + d ≤ 5000 * 179886) :
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
  have hlt : t + 7239 * m none + 48817 * m.some.degree < 5000 * 179886 := by
    change 7239 * m none + 48817 * m.some.degree < d at hm
    omega
  have hD := seed_motion w P L hh box t F hF (m none)
  have ho := fixed_seed_order h2 hw P L hD hγ m.some.degree hlt
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
  have hlt : mixedWeight (a + b) < d + mixedWeight a := by rw [mixedWeight_add]; omega
  have hz := mixedOrder_iff_coeff.mp hF _ hlt
  rw [← partial_eq_mixedHasse, toGeneric, map_partial, translate_partial]
  exact coeff_partial_eq_zero _ _ _ hz
theorem proof : Final50Fat.c3 := by
  intro w Γ s hw P L hh
  let h2 := K1_13_4_3_2.proof
  constructor
  · intro F hF γ hγ
    exact source_order h2 hw P L hF hγ hh (Nat.sub_add_cancel (show 5798170 ≤ 899430000 from by decide)).le
  · intro G hG γ hγ
    let z := inclConst (P.z γ)
    let y := trajectory (extend (s γ))
    change MixedOrder (toGeneric G) z y secondOrder
    change G ∈ Submodule.span Geom _ at hG
    induction hG using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨t, F, a, hF, ht, rfl⟩ := hQ
      apply mixedHasse_order
      apply source_order h2 hw P L hF hγ hh
      change t + mixedWeight a ≤ 5000 * 179886 - 2991921 at ht
      change t + (2991921 + mixedWeight a) ≤ 5000 * 179886
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
end
end Final50FatContacts
end

#print axioms Final50FatContacts.proof
