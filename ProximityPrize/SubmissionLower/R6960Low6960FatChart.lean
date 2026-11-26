import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdZCUPQZb
import ProximityPrize.SubmissionLower.R6960Anchor6966

section Merged6967_R6960Low6960FatChart
set_option Elab.async false



set_option Elab.async false
set_option maxHeartbeats 1000000
/-! Low-specific chart for the isolated-point bound: copy of `Fast056`/`Fast062` chart machinery
with the new resultant box (367,443,000, 124,200,000). -/
section
set_option autoImplicit false
namespace Low6960FatChart
noncomputable section
open K1_13 K1_13_7 MvPolynomial
open scoped Pointwise
open K1_13_7_6 (cap chartDegree zeroPrime chartDegree_eq_one cap_ncard)
open K1_13_7_6 (cap_add_subset nsmul_cap_subset indexWeight_eq zero_mem_cap)
abbrev totalCap : ℕ := 367443000
abbrev halfIndexCap : ℕ := 62100000
abbrev chartExponents := cap totalCap (2 * halfIndexCap)
abbrev chartMap := monomialMap GeometricX chartExponents
theorem chartMap_surjective : Function.Surjective chartMap := by
  apply monomialMap_surjective
  intro i
  change (Finsupp.single i 1).degree ≤ totalCap ∧
    Finsupp.single i 1 1 + 2 * Finsupp.single i 1 2 ≤ 2 * halfIndexCap
  fin_cases i <;> norm_num [Finsupp.degree_single, Finsupp.single_apply, totalCap, halfIndexCap]
private theorem genericRow_mem_chart (P : Row 3) (hP : LowerCaps P totalCap (2 * halfIndexCap)) :
    genericRow P ∈ restrictSupport GeometricX chartExponents := by
  intro e he
  have he' : e ∈ P.support := support_map_subset _ _ he
  refine ⟨(le_totalDegree he').trans hP.1, ?_⟩
  rw [← indexWeight_eq]
  exact (Finset.le_sup (f := fun m : Fin 3 →₀ ℕ => m.sum fun i a => i.val * a) he').trans hP.2
theorem chart_lift (P : Row 3) (hP : LowerCaps P totalCap (2 * halfIndexCap)) :
    ∃ L : MvPolynomial chartExponents GeometricX,
      chartMap L = genericRow P ∧ L.totalDegree ≤ 1 := by
  let h := genericRow_mem_chart P hP
  exact ⟨monomialLift (genericRow P) h, monomialMap_monomialLift (genericRow P) h,
    totalDegree_monomialLift_le_one (genericRow P) h⟩
private theorem chartHilbert_le (n : ℕ) :
    affineHilbertFunction (RingHom.ker chartMap) n ≤
      (cap (totalCap * n) ((2 * halfIndexCap) * n)).ncard := by
  let S := cap (totalCap * n) ((2 * halfIndexCap) * n)
  let M := restrictSupport GeometricX S
  let : Module.Finite GeometricX M := restrictSupport_finite (Set.toFinite S)
  have hmap (L : MvPolynomial chartExponents GeometricX) (hL : L.totalDegree ≤ n) :
      chartMap L ∈ M :=
    restrictSupport_mono GeometricX (nsmul_cap_subset _ _ n)
      (monomialMap_mem_restrictSupport_nsmul (zero_mem_cap _ _) hL)
  calc
    affineHilbertFunction (RingHom.ker chartMap) n ≤
        Module.finrank GeometricX (M.map (Ideal.Quotient.mkₐ GeometricX ⊥).toLinearMap) := by
      rw [RingHom.ker_eq_comap_bot]
      exact affineHilbertFunction_comap_le_finrank_map chartMap ⊥ M hmap
    _ ≤ Module.finrank GeometricX M := Submodule.finrank_map_le _ _
    _ = S.ncard := by
      rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport GeometricX S), Nat.card_coe_set_eq]
theorem chartDegree_bound :
    chartDegree chartMap zeroPrime ≤ 6 * (halfIndexCap : ℚ) ^ 2 * (totalCap - halfIndexCap : ℚ) := by
  let a : ℚ := halfIndexCap
  let b : ℚ := totalCap - halfIndexCap
  let H : Polynomial ℚ := Polynomial.C (a ^ 2 * b) * Polynomial.X ^ 3 +
    Polynomial.C (a ^ 2 + 2 * a * b) * Polynomial.X ^ 2 +
    Polynomial.C (2 * a + b) * Polynomial.X ^ 1 + Polynomial.C 1
  have hdim : (affineHilbertPolynomial (RingHom.ker chartMap)).natDegree = 3 := by
    rw [natDegree_affineHilbertPolynomial_ker_of_surjective chartMap chartMap_surjective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hH : H.natDegree ≤ 3 := by
    dsimp only [H]
    apply Polynomial.natDegree_add_le_of_degree_le _ (by simp)
    apply Polynomial.natDegree_add_le_of_degree_le _
      ((Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by decide))
    apply Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_C_mul_X_pow_le _ _)
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by decide)
  have hB : ∀ n : ℕ, 2 * (halfIndexCap * n) ≤ totalCap * n := fun n => by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right n (by decide)
  have hfit : ∀ n : ℕ, (affineHilbertFunction (RingHom.ker chartMap) n : ℚ) ≤ H.eval (n : ℚ) := by
    intro n
    have h := chartHilbert_le n
    rw [Nat.mul_assoc, cap_ncard _ _ (hB n)] at h
    refine (Nat.cast_le.mpr h).trans_eq ?_
    have hsub : halfIndexCap * n ≤ totalCap * n + 1 := by have := hB n; omega
    push_cast [Nat.cast_sub hsub]
    simp only [H, a, b, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  change affineDegree ((⊥ : Ideal Lower).comap chartMap) ≤ _
  rw [← RingHom.ker_eq_comap_bot]
  refine (affineDegree_le_of_eventually_affineHilbertFunction_le hdim hH
    (Filter.Eventually.of_forall hfit)).trans_eq ?_
  norm_num [H, a, b, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_one]
abbrev resultantBox : Shape := Low6960Fat.resultantBox
open K1_13_7_5 K1_13_7_6
theorem supported_resultant {P : Row 3} (hP : LowerCaps P resultantBox.b resultantBox.j) :
    Supported resultantBox (liftRow P) := by
  classical
  intro m hm
  change m ∈ (MvPolynomial.rename Fin.castSucc (genericRow P)).support at hm
  rw [MvPolynomial.support_rename_of_injective (Fin.castSucc_injective 3), Finset.mem_image] at hm
  obtain ⟨n, hn, rfl⟩ := hm
  have hn' : n ∈ P.support := MvPolynomial.support_map_subset genericCoeff P hn
  refine ⟨?_, ?_, ?_⟩
  · rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact (MvPolynomial.le_totalDegree hn').trans hP.1
  · rw [Finsupp.sum_mapDomain_index (fun _ => Nat.mul_zero _) (fun _ _ _ => Nat.mul_add ..)]
    exact (Finset.le_sup (f := fun m : Fin 3 →₀ ℕ => m.sum (fun i a => i.val * a)) hn').trans hP.2
  · have hlast : (3 : Fin 4) ∉ Set.range (@Fin.castSucc 3) := by
      rintro ⟨i, hi⟩
      exact Fin.castSucc_ne_last i hi
    exact (Finsupp.mapDomain_of_notMem_range n _ hlast).le
end
end Low6960FatChart
end

end Merged6967_R6960Low6960FatChart

section Merged6967_R6960Low6960FatContacts
set_option Elab.async false


set_option Elab.async false
section
namespace Low6960FatContacts
noncomputable section
open Polynomial K1 K1_13 K1_13_4 K1_13_4_3 FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
open P0_9_4 (line eval_line coeff_contact order_of_locator_lines translate_map)
set_option maxRecDepth 12000
private def Bounded (F : Polynomial (Polynomial Geom)) (b : ℕ) : Prop :=
  ∀ j, (F.coeff j).natDegree ≤ b + 48749 * j
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
private theorem line_degree (Q : Row 3) (T U : (Polynomial Geom)) (t : ℕ)
    (hQ : RawCut t Q) (hT : T.natDegree ≤ 131071) (hU : U.natDegree ≤ 179820)
    (j : ℕ) : ((line Q T U).coeff j).natDegree ≤ t + 48749 * j := by
  let b (i : Fin 3) : ℕ := 131071 - i.val
  let F (i : Fin 3) : Polynomial (Polynomial Geom) :=
    Polynomial.C (jet T i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 3) : Bounded (F i) (b i) := by
    intro k
    have ht : (jet T i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le T i.val).trans (Nat.sub_le_sub_right hT _)
    have hu : (jet U i).natDegree ≤ b i + 48749 := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi := i.isLt
      change 179820 - i.val ≤ (131071 - i.val) + 48749
      omega
    change ((F i).coeff k).natDegree ≤ b i + 48749 * k
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
private theorem line_coeff_zero (w : I → K) (H res T : (Polynomial Geom)) (t r : ℕ) (Q : Row 3)
    (hT : T.natDegree ≤ 131071) (hQ : RawCut t Q) (hcontact : RawContact r w H res Q)
    (A : Finset I) (hA : A.card = 179818)
    (hhit : ∀ i ∈ A, (H * T + res).eval (embed (node i)) = embed (w i))
    (V : (Polynomial Geom)) (hV : V.natDegree ≤ 2) (j : ℕ) (hj : t + 48749 * j < r * 179818) :
    (line Q T (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ 179820 :=
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
theorem raw_locator_order (w : I → K) (H res T : (Polynomial Geom)) (t k : ℕ) (Q : Row 3)
    (hT : T.natDegree ≤ 131071)
    (hhits : ∃ A : Finset I, 179818 ≤ A.card ∧
      ∀ i ∈ A, (H * T + res).eval (embed (node i)) = embed (w i))
    (hc : RawContact 5000 w H res Q) (hQ : RawCut t Q)
    (hcut : t + 48749 * k < 5000 * 179818) :
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
end Low6960FatContacts
end
section
namespace Low6960FatContacts
noncomputable section
open K1 K1_13 K1_13_4_3 Low6960Fat
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
open K1_13_4_3_1 (coeff_scalar support_seed weight_shift)
open K1_13_4_3 (coeff_eq_zero_of_lowerOrder)
private theorem trueCut_seed (H : (Polynomial Geom)) (i t : ℕ) (F : PhysicalRow)
    (hH : H.natDegree ≤ 2358) (hF : TrueCut H.natDegree t F) :
    TrueCut H.natDegree (t + 7074 * i) (clearedSeed H i F) := by
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
  have hp' : (H ^ (3 * i)).natDegree ≤ 7074 * i := by
    calc
      _ ≤ (3 * i) * H.natDegree := Polynomial.natDegree_pow_le
      _ ≤ (3 * i) * 2358 := Nat.mul_le_mul_left _ hH
      _ = 7074 * i := by ring
  omega
private theorem seed_motion (w : I → K) {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (hh : P.H.natDegree ≤ 2358) (box : Shape) (t : ℕ) (F : PhysicalRow)
    (hF : Source w P L box t F) (i : ℕ) :
    Source w P L box (t + 7074 * i) (clearedSeed P.H i F) := by
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
    {w Γ s} (hw : Low6960Fat.Messages w Γ s) (P : PoleData Γ s) (L : ResidueChart P)
    {box t F} (hF : Source w P L box t F) {γ} (hγ : γ ∈ Γ)
    (k : ℕ) (hk : t + 48749 * k < 5000 * 179818) :
    LowerOrder (atSeed (inclConst (P.z γ)) (toGeneric F))
      (trajectory (extend (s γ))) (k + 1) := by
  let res := residueAt L.numerator L.denominator (P.z γ)
  obtain ⟨Q, hQ, hrestore⟩ := h2 w Γ s P L box t F hF γ hγ
  obtain ⟨T, hT, hST⟩ := L.quotient γ hγ
  change extend (s γ) = P.H * T + res at hST
  obtain ⟨A, hA, hhits⟩ := hw.hits γ hγ
  have hhit : ∃ B : Finset I, 179818 ≤ B.card ∧
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
    {w Γ s} (hw : Low6960Fat.Messages w Γ s) (P : PoleData Γ s) (L : ResidueChart P)
    {box t F} (hF : Source w P L box t F) {γ} (hγ : γ ∈ Γ)
    (hh : P.H.natDegree ≤ 2358) {d : ℕ} (hd : t + d ≤ 5000 * 179818) :
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
  have hlt : t + 7074 * m none + 48749 * m.some.degree < 5000 * 179818 := by
    change 7074 * m none + 48749 * m.some.degree < d at hm
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
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericX)).mpr (pow_ne_zero _ P.monic.ne_zero)
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
theorem proof : Low6960Fat.c3 := by
  intro w Γ s hw P L hh
  let h2 := K1_13_4_3_2.proof
  constructor
  · intro F hF γ hγ
    exact source_order h2 hw P L hF.1 hγ hh (Nat.sub_add_cancel (show 4541009 ≤ 899090000 from by decide)).le
  · intro G hG γ hγ
    let z := inclConst (P.z γ)
    let y := trajectory (extend (s γ))
    change MixedOrder (toGeneric G) z y secondOrder
    change G ∈ Submodule.span Geom _ at hG
    induction hG using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨t, F, a, hF, ht, rfl⟩ := hQ
      apply mixedHasse_order
      apply source_order h2 hw P L hF.1 hγ hh
      change t + mixedWeight a ≤ 5000 * 179818 - 1814447 at ht
      change t + (1814447 + mixedWeight a) ≤ 5000 * 179818
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
end Low6960FatContacts
end

#print axioms Low6960FatContacts.proof

end Merged6967_R6960Low6960FatContacts

section Merged6967_R6960Low6960FatFactors
set_option Elab.async false


set_option Elab.async false

-- merged module R6960Low6960FatSlots
section Merged_R6960Low6960FatSlots

set_option Elab.async false
/-! Low-specific copies of the seed-cap dependent slot count of `Fast050` (K1_13_4_4),
at seed degree at most 27,000, i.e. 27,001 seed slots. -/
section
namespace Low6960FatSlots
noncomputable section
open K1 K1_13 K1_13_4
open K1_13_4_4 (capSpace mem_capSpace toGeneric_caps toGeneric_injective)
open Low6960Fat (Caps27 Source27)
open scoped Polynomial BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 1024
open K1_13_4_4 (Exponent slotExponent sum_value_choices sum_index_choices sum_odds rank_le_coeffs sum_squares)
def topSlots (a : ℕ) : ℕ := 27001 * 5671 * (1151 - a)^2
def capSpace27 (a : Shape) : Submodule GenericX GenericRow :=
  capSpace a ⊓
  MvPolynomial.restrictWeightedDegree (Pi.single (none : SeedVar) 1) 27000
theorem mem_capSpace27 {a : Shape} {F : GenericRow} : F ∈ capSpace27 a ↔ Caps27 a F := by
  classical
  simp only [capSpace27, Submodule.mem_inf, mem_capSpace,
    MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
    MvPolynomial.weightedTotalDegree_piSingle, Caps27, Low6960Fat.seedCap, seedDegree]
theorem seedDegree_toGeneric (F : PhysicalRow) : seedDegree (toGeneric F) = seedDegree F := by
  have hs : (toGeneric F).support = F.support :=
    MvPolynomial.support_map_of_injective F (IsFractionRing.injective (Polynomial Geom) GenericX)
  simp only [seedDegree, MvPolynomial.degreeOf_eq_sup, hs]
theorem toGeneric_caps27 {a : Shape} {F : PhysicalRow} (h : Caps27 a F) :
    Caps27 a (toGeneric F) :=
  ⟨toGeneric_caps h.1, by rw [seedDegree_toGeneric]; exact h.2⟩
def layerSpan {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P)
    (t : ℕ) : Submodule GenericX GenericRow :=
  Submodule.span GenericX {R | ∃ F, Source27 w P L secondBox t F ∧ toGeneric F = R}
theorem layerSpan_caps {Γ s} {w : I → K} {P : PoleData Γ s} {L : ResidueChart P}
    {t : ℕ} {F : GenericRow} (hF : F ∈ layerSpan w P L t) : Caps27 secondBox F := by
  apply mem_capSpace27.mp
  apply (Submodule.span_le.mpr ?_) hF
  rintro _ ⟨Q, hQ, rfl⟩
  exact mem_capSpace27.mpr (toGeneric_caps27 ⟨hQ.1.1, hQ.2⟩)
private def slotTuples (a : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.Ico a 1151).biUnion (fun k =>
    (Finset.range (2301 - 2*k)).biUnion (fun j =>
      (Finset.range (6821 - k - j)).biUnion (fun i =>
        (Finset.range 27001).image (fun z => (k, j, i, z)))))
private theorem tuples_card (a : ℕ) : (slotTuples a).card ≤ topSlots a := by
  unfold slotTuples
  calc
    _ ≤ ∑ k ∈ Finset.Ico a 1151, ∑ j ∈ Finset.range (2301 - 2*k),
        ∑ _ ∈ Finset.range (6821 - k - j), 27001 := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun k _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => ?_)
      exact Finset.card_image_le.trans_eq (Finset.card_range _)
    _ = topSlots a := by
      unfold topSlots
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      calc
        _ = ∑ k ∈ Finset.Ico a 1151, (27001 * 5671) * (2301 - 2*k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' : k ≤ 1150 := by have h := (Finset.mem_Ico.mp hk).2; omega
          rw [← Finset.sum_mul, sum_value_choices hk']
          ring
        _ = _ := by rw [← Finset.mul_sum, sum_index_choices]
private theorem exponent_mem {a : ℕ} {R : GenericRow} (hR : Caps27 secondBox R)
    {m : Exponent} (hm : m ∈ R.support) (ha : a ≤ m (some 2)) :
    m ∈ (slotTuples a).image slotExponent := by
  classical
  have ht := (MvPolynomial.le_weightedTotalDegree
    (fun i : SeedVar => i.elim 0 (fun _ => 1)) hm).trans hR.1.1
  have hj := (MvPolynomial.le_weightedTotalDegree
    (fun i : SeedVar => i.elim 0 Fin.val) hm).trans hR.1.2.1
  have hz := (MvPolynomial.le_degreeOf_of_mem_support (none : SeedVar) hm).trans hR.2
  have hk := (MvPolynomial.le_degreeOf_of_mem_support (some 2 : SeedVar) hm).trans hR.1.2.2.1
  have htotal : m (some 0) + m (some 1) + m (some 2) ≤ 6820 := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option,
      Fin.sum_univ_succ, secondBox, Nat.add_assoc] using ht
  have hindex : m (some 1) + 2 * m (some 2) ≤ 2300 := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option,
      Fin.sum_univ_succ, secondBox, Nat.mul_comm] using hj
  change m (some 2) ≤ 1150 at hk
  change m none ≤ 27000 at hz
  refine Finset.mem_image.mpr ⟨(m (some 2), m (some 1), m (some 0), m none), ?_, ?_⟩
  · simp only [slotTuples, Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_range,
      Finset.mem_image]
    exact ⟨m (some 2), ⟨ha, by omega⟩, m (some 1), by omega, m (some 0), by omega,
      m none, by omega, rfl⟩
  · ext i
    cases i with
    | none => simp [slotExponent]
    | some i => fin_cases i <;> simp [slotExponent]
theorem count_symbols (a r : ℕ) (e : Fin r → GenericRow) (he : LinearIndependent GenericX e)
    (h : ∀ R ∈ Submodule.span GenericX (Set.range e),
      Caps27 secondBox R ∧ (R ≠ 0 → a ≤ R.degreeOf (some 2))) :
    r ≤ topSlots a := by
  have hc := rank_le_coeffs ((slotTuples a).image slotExponent) e he (by
    intro R hR hn
    obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup R.support
      (MvPolynomial.support_nonempty.mpr hn) (fun u => u (some 2))
    have hdeg := (h R hR).2 hn
    rw [MvPolynomial.degreeOf_eq_sup, hmax] at hdeg
    exact ⟨m, exponent_mem (h R hR).1 hm hdeg, MvPolynomial.mem_support_iff.mp hm⟩)
  exact hc.trans (Finset.card_image_le.trans (tuples_card a))
theorem count_layer {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {a r t : ℕ}
    (hb : ∃ e : Fin r → GenericRow, LinearIndependent GenericX e ∧
      ∀ i, e i ∈ layerSpan w P L t)
    (hdeg : ∀ R ∈ layerSpan w P L t, R ≠ 0 → a ≤ R.degreeOf (some 2)) :
    r ≤ topSlots a := by
  obtain ⟨e, he, hs⟩ := hb
  have hspan : Submodule.span GenericX (Set.range e) ≤ layerSpan w P L t :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hs i)
  exact count_symbols a r e he (fun R hR => ⟨layerSpan_caps (hspan hR), hdeg R (hspan hR)⟩)
theorem slot_zero : topSlots 0 = 202857067663471 := by decide
theorem slot_sum : (∑ k ∈ Finset.range 1150, topSlots (1 + k)) = 77728095800419025 := by
  have hs : (∑ k ∈ Finset.range 1150, topSlots (1 + k)) =
      (27001 * 5671) * ∑ k ∈ Finset.range 1150, (1150 - k)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hk : 1151 - (1 + k) = 1150 - k := by omega
    rw [topSlots, hk]
  rw [hs]
  have hsquare : (∑ k ∈ Finset.range 1150, (1150 - k)^2) = 507619775 := by
    have h := sum_squares 1150
    omega
  rw [hsquare]
end
end Low6960FatSlots
end

end Merged_R6960Low6960FatSlots

-- merged module R6960Low6960FatFactors
section Merged_R6960Low6960FatFactors

set_option Elab.async false
section
namespace Low6960FatFactors
noncomputable section
open Polynomial K1 K1_13
open K1_13_4 (ResidueChart PhysicalRow GenericX GenericRow HasRank Source secondBox toGeneric)
open K1_13_4_4_1 (Exponent polePower weight)
open K1_13_4 (SeedVar seedDegree)
open Low6960Fat (secondCut bankRank)
open scoped BigOperators
open K1_13_4_4_1 (bank bankEval mem_bank kernel_le boundary below_boundary independent_generic)
open K1_13_4_4_1 (endpoint)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def seedSpace : Submodule Geom PhysicalRow :=
  (MvPolynomial.restrictWeightedDegree (Pi.single (none : SeedVar) 1) 27000).restrictScalars Geom
theorem mem_seedSpace {F : PhysicalRow} : F ∈ seedSpace ↔ seedDegree F ≤ 27000 := by
  simp only [seedSpace, Submodule.restrictScalars_mem,
    MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
    MvPolynomial.weightedTotalDegree_piSingle, seedDegree]
private def bank27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    Submodule Geom PhysicalRow := bank w P L t ⊓ seedSpace
private theorem mem_bank27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P)
    (t : ℕ) (F : PhysicalRow) : F ∈ bank27 w P L t ↔ Low6960Fat.Source27 w P L secondBox t F := by
  rw [bank27, Submodule.mem_inf, mem_bank, mem_seedSpace]
  rfl
private instance finite27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    Module.Finite Geom (bank27 w P L t) :=
  Submodule.finiteDimensional_of_le (inf_le_left : bank27 w P L t ≤ bank w P L t)
private def bankEval27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    bank27 w P L t →ₗ[Geom] (K1_13_4_4_1.Exponent → Geom) :=
  (boundary P.H.natDegree t).comp (bank27 w P L t).subtype
private theorem kernel_le27 {Γ s} (w : I → K) (P : PoleData Γ s) (L : ResidueChart P) (t : ℕ) :
    Module.finrank Geom (bankEval27 w P L (t + 1)).ker ≤
      Module.finrank Geom (bank27 w P L t) := by
  let f := (bank27 w P L (t + 1)).subtype.comp (bankEval27 w P L (t + 1)).ker.subtype
  have hm (F : (bankEval27 w P L (t + 1)).ker) : f F ∈ bank27 w P L t := by
    obtain ⟨⟨hc, hcut, hphys, hpole⟩, hseed⟩ := (mem_bank27 w P L _ _).mp F.val.property
    have hz : boundary P.H.natDegree (t + 1) F.val.val = 0 := LinearMap.mem_ker.mp F.property
    apply (mem_bank27 w P L _ _).mpr
    refine ⟨⟨hc, fun m hm => ?_, hphys, hpole⟩, hseed⟩
    have h := below_boundary hcut hz m hm
    change ((F.val.val).coeff m).natDegree + weight P.H.natDegree m ≤ t + polePower * P.H.natDegree
    omega
  apply LinearMap.finrank_le_finrank_of_injective (f := f.codRestrict _ hm)
  intro F G he
  have heq := congrArg (fun Q : bank27 w P L t => Q.val) he
  exact Subtype.ext (Subtype.ext heq)
theorem telescope (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) (P : PoleData Γ s)
    (L : ResidueChart P) (hr : Low6960Fat.HasRank27 w P L secondBox secondCut bankRank) :
    ∃ r : ℕ → ℕ, bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t ∧
      ∀ t ≤ secondCut, ∃ e : Fin (r t) → GenericRow,
        LinearIndependent GenericX e ∧ ∀ i, e i ∈ Low6960FatSlots.layerSpan w P L t := by
  classical
  let r (t : ℕ) := Module.finrank Geom (bankEval27 w P L t).range
  refine ⟨r, ?_, fun t _ => ?_⟩
  · have hzero : (bankEval27 w P L 0).ker = ⊥ := by
      apply LinearMap.ker_eq_bot'.mpr
      intro F hz
      have hsrc := ((mem_bank27 w P L _ _).mp F.property).1
      refine Subtype.ext (K1_13_4_4_1.endpoint Γ s P L F.val (fun m hm => ?_) hsrc.2.2.2)
      simpa only [Nat.zero_add] using below_boundary hsrc.2.1 hz m hm
    have hsum (t : ℕ) : Module.finrank Geom (bank27 w P L t) ≤
        ∑ v ∈ Finset.range (t + 1), r v := by
      induction t with
      | zero =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank27 w P L 0) (V₂ := Exponent → Geom) (bankEval27 w P L 0)
        rw [hzero, finrank_bot, Nat.add_zero] at h
        simpa only [Nat.zero_add, Finset.sum_range_one] using h.ge
      | succ t ih =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank27 w P L (t + 1)) (V₂ := Exponent → Geom) (bankEval27 w P L (t + 1))
        rw [Finset.sum_range_succ, ← h, add_comm]
        exact Nat.add_le_add (le_trans (kernel_le27 w P L t) ih) le_rfl
    obtain ⟨e, he, hmem⟩ := hr
    have hi : LinearIndependent Geom
        (fun i => (⟨e i, (mem_bank27 w P L _ _).mpr (hmem i)⟩ : bank27 w P L secondCut)) :=
      LinearIndependent.of_comp (bank27 w P L secondCut).subtype he
    exact (by simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank :
      bankRank ≤ Module.finrank Geom (bank27 w P L secondCut)).trans (hsum secondCut)
  · let b := Module.finBasis Geom (bankEval27 w P L t).range
    choose e he using fun i : Fin (r t) => LinearMap.mem_range.mp (b i).property
    have hsrc (i : Fin (r t)) : Low6960Fat.Source27 w P L secondBox t (e i).val :=
      (mem_bank27 w P L _ _).mp (e i).property
    refine ⟨fun i => toGeneric (e i).val,
      independent_generic (fun i => (e i).val) (fun i => (hsrc i).1.2.1) ?_,
      fun i => Submodule.subset_span ⟨(e i).val, hsrc i, rfl⟩⟩
    have h : LinearIndependent Geom (fun i => (b i).val) :=
      b.linearIndependent.map' (bankEval27 w P L t).range.subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have heq : (fun i => boundary P.H.natDegree t (e i).val) = fun i => (b i).val := funext he
    rwa [heq]
end
end Low6960FatFactors
end
section
namespace Low6960FatFactors
noncomputable section
open K1_13_4 hiding mixedWeight secondCut
open K1_13_4_4 (FactorsFor factorProduct mixedHasse_zero toGeneric_caps cutoff_sum_le)
open Low6960FatSlots (topSlots)
open Low6960Fat (mixedWeight secondCut bankRank)
open scoped Polynomial BigOperators
open K1_13_4_4_2 (line line_zero line_toGeneric transverse pow_dvd_of_coeff positive_jet_degree)
def reserveCost (moving : Bool) : ℕ := if moving then 7074 else 48749
def layerPower (e t : ℕ) : ℕ := 1 + (secondCut - t) / e
private theorem choose_coordinate {moving : Bool} {A : Finset GenericRow}
    (hA : FactorsFor moving A) {F f : GenericRow} (hF : F ≠ 0) (hcap : Caps secondBox F)
    (hf : f ∈ A) (hd : f ∣ F) :
    ∃ i : SeedVar, (∀ n, mixedWeight (Finsupp.single i n) = n * reserveCost moving) ∧
      ¬ f ∣ (line i f).coeff 1 := by
  classical
  cases moving with
  | false =>
    obtain ⟨j, hj⟩ := positive_jet_degree (hA.jets f hf)
    have hjet : jetTotal f ≤ 6820 :=
      (MvPolynomial.weightedTotalDegree_le_of_dvd _ hd hF).trans hcap.1
    have hdeg : f.degreeOf (some j) ≤ jetTotal f :=
      MvPolynomial.degreeOf_le_weightedTotalDegree
        (fun i : SeedVar => i.elim 0 (fun _ => 1)) (some j) Nat.one_pos f
    refine ⟨some j, ?_, transverse hj (hdeg.trans_lt (hjet.trans_lt (by decide)))⟩
    intro n
    simp [mixedWeight, reserveCost, mul_comm]
  | true =>
    have hs : 0 < seedDegree f := hA.seed f hf
    have hdeg : seedDegree f ≤ 70000 := by
      simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using
        (MvPolynomial.weightedTotalDegree_le_of_dvd (Pi.single (none : SeedVar) 1) hd hF).trans
          (by simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using hcap.2.2.2)
    refine ⟨none, ?_, transverse hs (hdeg.trans_lt (by decide))⟩
    intro n
    simp [mixedWeight, reserveCost, mul_comm]
theorem factor_power (moving : Bool) (A : Finset GenericRow) (F : PhysicalRow) (t : ℕ)
    (hA : FactorsFor moving A) (hcap : Caps secondBox F) (ht : t ≤ secondCut)
    (htest : ∀ f ∈ A, ∀ a, t + mixedWeight a ≤ secondCut → f ∣ toGeneric (mixedHasse a F)) :
    factorProduct A ^ layerPower (reserveCost moving) t ∣ toGeneric F := by
  classical
  by_cases hF : toGeneric F = 0
  · rw [hF]
    exact dvd_zero _
  unfold factorProduct
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_isRelPrime
  · intro f hf g hg hfg
    refine IsRelPrime.pow ((hA.irreducible f hf).isRelPrime_iff_not_dvd.mpr ?_)
    intro hd
    exact hA.different hf hg hfg ((hA.irreducible f hf).associated_of_dvd (hA.irreducible g hg) hd)
  · intro f hf
    have hdiv : f ∣ toGeneric F := by
      simpa [mixedWeight, mixedHasse_zero] using htest f hf 0 (by simpa [mixedWeight] using ht)
    obtain ⟨i, hi, hsep⟩ := choose_coordinate hA hF (toGeneric_caps hcap) hf hdiv
    apply pow_dvd_of_coeff (line i) (line_zero i)
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp (hA.irreducible f hf)) hsep
    intro a ha
    rw [line_toGeneric]
    apply htest f hf
    rw [hi]
    have ha' : a ≤ (secondCut - t) / reserveCost moving := by
      unfold layerPower at ha
      omega
    have hm := (Nat.mul_le_mul_right (reserveCost moving) ha').trans
      (Nat.div_mul_le_self (secondCut - t) (reserveCost moving))
    omega
set_option maxRecDepth 1024
theorem factor_arithmetic :
    let T := 202857067663471
    48749 * 6820 * T / bankRank = 122 ∧ 48749 * 2300 * T / bankRank = 41 ∧
      7074 * 6820 * T / bankRank = 17 ∧ 7074 * 2300 * T / bankRank = 5 ∧
      7074 * 27000 * T / bankRank = 70 := by decide
theorem resource_bound {e V d : ℕ} (he : 0 < e) (r : ℕ → ℕ)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (hcap : ∀ t ≤ secondCut, r t ≤ topSlots 0)
    (hspend : ∀ t ≤ secondCut, r t ≠ 0 → layerPower e t * d ≤ V) :
    d ≤ e * V * topSlots 0 / bankRank := by
  by_cases hd : d = 0
  · simp [hd]
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  let q (k : ℕ) := if k < V / d then topSlots 0 else 0
  have hb := cutoff_sum_le (W := secondCut) (n := V / d) he r q
    (fun t ht => by
      by_cases hn : r t = 0
      · simp [hn]
      have hle := (Nat.le_div_iff_mul_le hd').mpr (hspend t ht hn)
      have hlt : (secondCut - t) / e < V / d := by
        unfold layerPower at hle
        omega
      simpa [q, hlt] using hcap t ht)
    (fun k hk => ite_eq_right (Nat.not_lt.mpr hk))
  have hc : (∑ k ∈ Finset.range (V / d), q k) = (V / d) * topSlots 0 := by
    have hsum : (∑ k ∈ Finset.range (V / d), q k) =
        ∑ _ ∈ Finset.range (V / d), topSlots 0 :=
      Finset.sum_congr rfl fun k hk => ite_eq_left (Finset.mem_range.mp hk)
    rw [hsum]
    simp
  rw [hc] at hb
  apply (Nat.le_div_iff_mul_le (by decide : 0 < bankRank)).mpr
  calc
    d * bankRank ≤ d * (e * (V / d * topSlots 0)) :=
      Nat.mul_le_mul_left d (hr.trans hb)
    _ = (e * topSlots 0) * (V / d * d) := by ring
    _ ≤ (e * topSlots 0) * V := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
    _ = e * V * topSlots 0 := by ring
theorem top_exclusion (r : ℕ → ℕ)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (h : ∀ t ≤ secondCut, r t ≤ topSlots (layerPower 7074 t)) : False := by
  have hb := cutoff_sum_le (W := secondCut) (n := 1150) (by decide : 0 < 7074)
    r (fun k => topSlots (1 + k)) h (fun k hk => by
      have hk' : 1151 - (1 + k) = 0 := by omega
      simp [topSlots, hk'])
  rw [Low6960FatSlots.slot_sum] at hb
  exact (not_le_of_gt (by decide : 7074 * 77728095800419025 < bankRank)) (hr.trans hb)
end
end Low6960FatFactors
end
section
namespace Low6960FatFactors
noncomputable section
open K1 K1_13
open K1_13_4 hiding secondCut mixedWeight Necessary CommonPair
open K1_13_4_4 (FactorsFor factorProduct)
open Low6960Fat (CommonPair Caps27)
open scoped Polynomial BigOperators
open K1_13_4_4 (pureEval pureEval_section pure_degree_le caps_of_dvd)
private theorem seed_of_dvd {F Q : GenericRow} (hF : F ≠ 0) (hs : seedDegree F ≤ 27000)
    (hQ : Q ∣ F) : seedDegree Q ≤ 27000 := by
  simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using
    (MvPolynomial.weightedTotalDegree_le_of_dvd (Pi.single (none : SeedVar) 1) hQ hF).trans
      (by simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using hs)
theorem factor_pair27
    (F G : GenericRow) (hF : F ≠ 0) (hG : G ≠ 0)
    (hFCap : Caps27 firstBox F) (hGCap : Caps27 secondBox G)
    (hfixed : ∀ A, FactorsFor false A → (∀ f ∈ A, f ∣ F ∧ f ∣ G) →
      jetTotal (factorProduct A) ≤ 122 ∧ jetIndex (factorProduct A) ≤ 41)
    (hmoving : ∀ A, FactorsFor true A → (∀ f ∈ A, f ∣ F ∧ f ∣ G) →
      jetTotal (factorProduct A) ≤ 17 ∧ jetIndex (factorProduct A) ≤ 5 ∧
      seedDegree (factorProduct A) ≤ 70 ∧ ∀ f ∈ A, f.degreeOf (some 2) = 0) :
    Nonempty (CommonPair F G) := by
  classical
  let _ : StrongNormalizationMonoid GenericRow :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let _ : GCDMonoid GenericRow := UniqueFactorizationMonoid.toGCDMonoid GenericRow
  let g := gcd F G
  have hg : g ≠ 0 := gcd_ne_zero_of_left hF
  let N := UniqueFactorizationMonoid.normalizedFactors g
  let A := N.toFinset
  let pureFactors := A.filter (fun f => jetTotal f = 0)
  let jetFactors := A.filter (fun f => ¬ jetTotal f = 0)
  let fixed := jetFactors.filter (fun f => seedDegree f = 0)
  let moving := jetFactors.filter (fun f => ¬ seedDegree f = 0)
  let powCount : GenericRow → ℕ := N.count
  let pure : (Polynomial GenericX) := ∏ f ∈ pureFactors, (pureEval f) ^ powCount f
  have hpure : pureSeed pure = ∏ f ∈ pureFactors, f ^ powCount f := by
    let φ : (Polynomial GenericX) →+* GenericRow :=
      Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X none)
    change φ (∏ f ∈ pureFactors, (pureEval f) ^ powCount f) = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun f hf => ?_
    rw [map_pow]
    exact congrArg (fun R => R ^ powCount f)
      (pureEval_section (Finset.mem_filter.mp hf).2)
  let D := pureSeed pure * (∏ f ∈ fixed, f ^ powCount f) * (∏ f ∈ moving, f ^ powCount f)
  have hD : Associated D g := by
    suffices D = N.prod by
      rw [this]
      exact UniqueFactorizationMonoid.prod_normalizedFactors hg
    change pureSeed pure * (∏ f ∈ fixed, f ^ powCount f) *
      (∏ f ∈ moving, f ^ powCount f) = _
    rw [hpure, mul_assoc]
    unfold fixed moving
    rw [Finset.prod_filter_mul_prod_filter_not]
    unfold pureFactors jetFactors
    rw [Finset.prod_filter_mul_prod_filter_not]
    exact (Finset.prod_multiset_count N).symm
  have hDne : D ≠ 0 := ne_zero_of_dvd_ne_zero hg hD.dvd
  have hDF : D ∣ F := hD.dvd.trans (gcd_dvd_left F G)
  have hDG : D ∣ G := hD.dvd.trans (gcd_dvd_right F G)
  obtain ⟨F', hF'⟩ := hDF
  obtain ⟨G', hG'⟩ := hDG
  have hl : F' ≠ 0 := right_ne_zero_of_mul (hF' ▸ hF)
  have hr : G' ≠ 0 := right_ne_zero_of_mul (hG' ▸ hG)
  have hrel : IsRelPrime F' G' := by
    intro d hdF hdG
    have hdF' : D * d ∣ F := hF' ▸ mul_dvd_mul_left D hdF
    have hdG' : D * d ∣ G := hG' ▸ mul_dvd_mul_left D hdG
    have hd := (dvd_gcd hdF' hdG').trans hD.symm.dvd
    apply isUnit_of_dvd_one
    exact (mul_dvd_mul_iff_left hDne).mp (by simpa only [mul_one] using hd)
  have hcommon (f : GenericRow) (hf : f ∈ A) : f ∣ F ∧ f ∣ G := by
    have hfg : f ∣ g := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
      (Multiset.mem_toFinset.mp hf)
    exact ⟨hfg.trans (gcd_dvd_left F G), hfg.trans (gcd_dvd_right F G)⟩
  have hmake (b : Bool) (B : Finset GenericRow) (hBA : B ⊆ A)
      (hj : ∀ f ∈ B, 0 < jetTotal f)
      (hs : ∀ f ∈ B, if b then 0 < seedDegree f else seedDegree f = 0) :
      FactorsFor b B := by
    refine ⟨?_, ?_, hj, hs⟩
    · intro f hf q hq hne hassoc
      exact hne (UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
        (Multiset.mem_toFinset.mp (hBA hf)) (Multiset.mem_toFinset.mp (hBA hq)) hassoc)
    · intro f hf
      exact UniqueFactorizationMonoid.irreducible_of_normalized_factor _
        (Multiset.mem_toFinset.mp (hBA hf))
  have hfixedA : fixed ⊆ A := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hmovingA : moving ⊆ A := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hfix := hmake false fixed hfixedA
    (fun _ hf => Nat.pos_of_ne_zero (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2)
    (fun _ hf => (Finset.mem_filter.mp hf).2)
  have hmov := hmake true moving hmovingA
    (fun _ hf => Nat.pos_of_ne_zero (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2)
    (fun _ hf => Nat.pos_of_ne_zero (Finset.mem_filter.mp hf).2)
  obtain ⟨hft, hfi⟩ := hfixed fixed hfix (fun f hf => hcommon f (hfixedA hf))
  obtain ⟨hmt, hmi, hms, hlow⟩ := hmoving moving hmov (fun f hf => hcommon f (hmovingA hf))
  have hpureF : pureSeed pure ∣ F :=
    (show pureSeed pure ∣ D by
      exact ⟨_, mul_assoc _ _ _⟩).trans ⟨F', hF'⟩
  have hpure_ne : pure ≠ 0 := by
    intro hz
    apply hDne
    simp [D, hz, pureSeed]
  refine ⟨{
    fixed := fixed
    moving := moving
    pure := pure
    exponent := powCount
    left := F'
    right := G'
    pure_ne := hpure_ne
    pure_degree := (pure_degree_le hF hpureF).trans (hFCap.2.trans (by decide))
    fixed_kind := fun f hf => ⟨hfix.irreducible f hf, hfix.jets f hf, hfix.seed f hf⟩
    moving_kind := fun f hf => ⟨hmov.irreducible f hf, hmov.jets f hf, hmov.seed f hf, hlow f hf⟩
    fixed_total := hft
    fixed_index := hfi
    moving_total := hmt
    moving_index := hmi
    moving_seed := hms
    left_eq := hF'
    right_eq := hG'
    left_ne := hl
    right_ne := hr
    proper := hrel
    left_caps := ⟨caps_of_dvd hF hFCap.1 ⟨D, hF'.trans (mul_comm _ _)⟩, seed_of_dvd hF hFCap.2 ⟨D, hF'.trans (mul_comm _ _)⟩⟩
    right_caps := ⟨caps_of_dvd hG hGCap.1 ⟨D, hG'.trans (mul_comm _ _)⟩, seed_of_dvd hG hGCap.2 ⟨D, hG'.trans (mul_comm _ _)⟩⟩
  }⟩
end
end Low6960FatFactors
end
section
namespace Low6960FatFactors
noncomputable section
open K1 K1_13
open K1_13_4 hiding secondCut mixedWeight Necessary CommonPair
open K1_13_4_4 (FactorsFor factorProduct rowMap
  capSpace mem_capSpace mixedHasse_zero toGeneric_ne_zero toGeneric_caps mixedHasse_caps)
open Low6960FatSlots (topSlots layerSpan layerSpan_caps count_layer capSpace27 mem_capSpace27
  toGeneric_caps27)
open Low6960Fat (Caps27 HasRank27)
open Low6960Fat (Necessary mixedWeight secondCut bankRank)
open scoped BigOperators
open K1_13_4_4 (multiples mem_multiples weighted_pow)
set_option maxRecDepth 1024
private theorem mixedHasse_seed27 (a : SeedVar →₀ ℕ) (F : PhysicalRow)
    (hs : seedDegree F ≤ 27000) : seedDegree (mixedHasse a F) ≤ 27000 := by
  classical
  simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using
    (K1_13_4_4.mixedHasse_weightedDegree_le (Pi.single (none : SeedVar) 1) a F).trans
      (by simpa only [seedDegree, MvPolynomial.weightedTotalDegree_piSingle] using hs)
private theorem has_nonzero_necessary {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} (hr : HasRank27 w P L secondBox secondCut bankRank) :
    ∃ G : Necessary w P L, G ≠ 0 := by
  obtain ⟨e, he, hs⟩ := hr
  let i : Fin bankRank := ⟨0, by decide⟩
  have hmem : e i ∈ Necessary w P L := by
    apply Submodule.subset_span
    exact ⟨secondCut, e i, 0, hs i, by simp [mixedWeight], (mixedHasse_zero _).symm⟩
  refine ⟨⟨e i, hmem⟩, fun h => he.ne_zero i ?_⟩
  exact congrArg (fun Q : Necessary w P L => Q.val) h
private theorem necessary_caps {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {Q : PhysicalRow} (hQ : Q ∈ Necessary w P L) :
    Caps27 secondBox (toGeneric Q) := by
  have hle : Necessary w P L ≤ ((capSpace27 secondBox).restrictScalars Geom).comap rowMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, F, a, hF, _, rfl⟩
    exact mem_capSpace27.mpr (toGeneric_caps27 ⟨mixedHasse_caps a F hF.1.1, mixedHasse_seed27 a F hF.2⟩)
  exact mem_capSpace27.mp (hle hQ)
private theorem select_row {Γ s} {w : I → K} {P : PoleData Γ s} {L : ResidueChart P}
    {F : PhysicalRow} (hF : F ≠ 0) (hr : HasRank27 w P L secondBox secondCut bankRank) :
    ∃ G, G ∈ Necessary w P L ∧ G ≠ 0 ∧
      ∀ f : GenericRow, Irreducible f → f ∣ toGeneric F → f ∣ toGeneric G →
        ∀ Q ∈ Necessary w P L, f ∣ toGeneric Q := by
  classical
  let N := Necessary w P L
  let _ : StrongNormalizationMonoid GenericRow :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let bad := (UniqueFactorizationMonoid.normalizedFactors (toGeneric F)).toFinset.filter
    (fun f => ∃ Q ∈ N, ¬ f ∣ toGeneric Q)
  let sub : Option ↥bad → Submodule Geom N
    | none => ⊥
    | some f => ((multiples f.val).restrictScalars Geom).comap (rowMap.comp N.subtype)
  have hproper (i : Option ↥bad) : sub i ≠ ⊤ := by
    cases i with
    | none =>
      obtain ⟨Q, hQ⟩ := has_nonzero_necessary hr
      intro h
      have hm : Q ∈ sub none := h ▸ Submodule.mem_top
      exact hQ ((Submodule.mem_bot Geom).mp hm)
    | some f =>
      obtain ⟨Q, hQ, hnd⟩ := (Finset.mem_filter.mp f.property).2
      intro h
      have hm : (⟨Q, hQ⟩ : N) ∈ sub (some f) := h ▸ Submodule.mem_top
      exact hnd (mem_multiples.mp hm)
  obtain ⟨G, hG⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (ι := Option ↥bad) (K := Geom) (M := N) sub hproper
  refine ⟨G.val, G.property, ?_, fun f hf hdf hdg Q hQ => ?_⟩
  · intro h
    exact hG none ((Submodule.mem_bot Geom).mpr (Subtype.ext h))
  · by_contra hn
    obtain ⟨p, hp, hassoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd (toGeneric_ne_zero hF) hf hdf
    have hp' : p ∈ bad := Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr hp, Q, hQ, fun h => hn (hassoc.dvd_iff_dvd_left.mpr h)⟩
    exact hG (some ⟨p, hp'⟩) (mem_multiples.mpr (hassoc.dvd_iff_dvd_left.mp hdg))
private theorem layer_divides {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {moving : Bool} {A : Finset GenericRow} (hA : FactorsFor moving A)
    (hcommon : ∀ f ∈ A, ∀ Q ∈ Necessary w P L, f ∣ toGeneric Q)
    {t : ℕ} (ht : t ≤ secondCut) :
    layerSpan w P L t ≤ multiples (factorProduct A ^ layerPower (reserveCost moving) t) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨F, hF, rfl⟩
  apply mem_multiples.mpr (factor_power moving A F t hA hF.1.1 ht ?_)
  intro f hf a ha
  exact hcommon f hf _ (Submodule.subset_span ⟨t, F, a, hF, ha, rfl⟩)
private theorem product_ne_zero {moving : Bool} {A : Finset GenericRow} (hA : FactorsFor moving A) :
    factorProduct A ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun f hf => (hA.irreducible f hf).ne_zero
private theorem weighted_resource {Γ s} {w : I → K} {P : PoleData Γ s} {L : ResidueChart P}
    {e : ℕ} (he : 0 < e) {r : ℕ → ℕ} {D : GenericRow} (hD : D ≠ 0)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (hb : ∀ t ≤ secondCut, ∃ u : Fin (r t) → GenericRow, LinearIndependent GenericX u ∧
      ∀ i, u i ∈ layerSpan w P L t)
    (hcount : ∀ t ≤ secondCut, r t ≤ topSlots 0)
    (hdvd : ∀ t ≤ secondCut, layerSpan w P L t ≤ multiples (D ^ layerPower e t))
    (v : SeedVar → ℕ) (V : ℕ)
    (hcap : ∀ R : GenericRow, Caps27 secondBox R → R.weightedTotalDegree v ≤ V) :
    D.weightedTotalDegree v ≤ e * V * topSlots 0 / bankRank := by
  apply resource_bound he r hr hcount
  intro t ht hne
  obtain ⟨u, hu, hs⟩ := hb t ht
  let i : Fin (r t) := ⟨0, Nat.pos_of_ne_zero hne⟩
  have hm := MvPolynomial.weightedTotalDegree_le_of_dvd v
    (mem_multiples.mp (hdvd t ht (hs i))) (hu.ne_zero i)
  rw [weighted_pow _ _ hD] at hm
  exact hm.trans (hcap (u i) (layerSpan_caps (hs i)))
private theorem excludes_top {Γ s} {w : I → K} {P : PoleData Γ s}
    {L : ResidueChart P} {r : ℕ → ℕ} {A : Finset GenericRow} (hA : FactorsFor true A)
    (hr : bankRank ≤ ∑ t ∈ Finset.range (secondCut + 1), r t)
    (hb : ∀ t ≤ secondCut, ∃ u : Fin (r t) → GenericRow,
      LinearIndependent GenericX u ∧ ∀ i, u i ∈ layerSpan w P L t)
    (hdvd : ∀ t ≤ secondCut,
      layerSpan w P L t ≤ multiples (factorProduct A ^ layerPower 7074 t)) :
    ∀ f ∈ A, f.degreeOf (some 2) = 0 := by
  classical
  let v : SeedVar → ℕ := Pi.single (some 2) 1
  have hzero : (factorProduct A).weightedTotalDegree v = 0 := by
    by_contra hn
    apply top_exclusion r hr
    intro t ht
    apply count_layer (hb t ht)
    intro R hR hRne
    have h := MvPolynomial.weightedTotalDegree_le_of_dvd v
      (mem_multiples.mp (hdvd t ht hR)) hRne
    rw [weighted_pow _ _ (product_ne_zero hA)] at h
    have hle := Nat.mul_le_mul_left (layerPower 7074 t) (Nat.pos_of_ne_zero hn)
    rw [Nat.mul_one] at hle
    simpa only [v, MvPolynomial.weightedTotalDegree_piSingle] using hle.trans h
  intro f hf
  have hfd : f ∣ factorProduct A := Finset.dvd_prod_of_mem id hf
  have h := (MvPolynomial.weightedTotalDegree_le_of_dvd v hfd (product_ne_zero hA)).trans_eq hzero
  simpa only [v, MvPolynomial.weightedTotalDegree_piSingle, Nat.le_zero] using h
theorem proof : Low6960Fat.c2 := by
  classical
  intro w Γ s P L F hF hFCaps hRank
  obtain ⟨r, hr, hb⟩ := telescope w Γ s P L hRank
  have hcount : ∀ t ≤ secondCut, r t ≤ topSlots 0 := fun t ht =>
    count_layer (hb t ht) (fun _ _ _ => Nat.zero_le _)
  obtain ⟨G, hG, hGne, hchoose⟩ := select_row hF hRank
  have hdiv (moving : Bool) (A : Finset GenericRow) (hA : FactorsFor moving A)
      (hcomm : ∀ f ∈ A, f ∣ toGeneric F ∧ f ∣ toGeneric G) :
      ∀ t ≤ secondCut, layerSpan w P L t ≤
        multiples (factorProduct A ^ layerPower (reserveCost moving) t) :=
    fun _ ht => layer_divides hA
      (fun f hf => hchoose f (hA.irreducible f hf) (hcomm f hf).1 (hcomm f hf).2) ht
  have hbound (moving : Bool) (A : Finset GenericRow) (hA : FactorsFor moving A)
      (hcomm : ∀ f ∈ A, f ∣ toGeneric F ∧ f ∣ toGeneric G)
      (v : SeedVar → ℕ) (V : ℕ)
      (hc : ∀ R : GenericRow, Caps27 secondBox R → R.weightedTotalDegree v ≤ V) :
      (factorProduct A).weightedTotalDegree v ≤ reserveCost moving * V * topSlots 0 / bankRank :=
    weighted_resource (by cases moving <;> decide) (product_ne_zero hA) hr hb hcount
      (hdiv moving A hA hcomm) v V hc
  have hbcap (R : GenericRow) (h : Caps27 secondBox R) : jetTotal R ≤ 6820 := h.1.1
  have hjcap (R : GenericRow) (h : Caps27 secondBox R) : jetIndex R ≤ 2300 := h.1.2.1
  have hscap (R : GenericRow) (h : Caps27 secondBox R) :
      R.weightedTotalDegree (Pi.single (none : SeedVar) 1) ≤ 27000 := by
    rw [MvPolynomial.weightedTotalDegree_piSingle]
    exact h.2
  obtain ⟨bF, jF, bM, jM, sM⟩ := factor_arithmetic
  refine ⟨G, hG, factor_pair27 _ _ (toGeneric_ne_zero hF) (toGeneric_ne_zero hGne)
    (toGeneric_caps27 hFCaps) (necessary_caps hG) ?_ ?_⟩
  · intro A hA hcomm
    have hbt := hbound false A hA hcomm _ _ hbcap
    have hji := hbound false A hA hcomm _ _ hjcap
    change jetTotal _ ≤ _ at hbt
    change jetIndex _ ≤ _ at hji
    have hbt' : jetTotal (factorProduct A) ≤ 122 := by
      simp only [reserveCost, Bool.false_eq_true, ite_false, Low6960FatSlots.slot_zero, bF] at hbt
      exact hbt.trans (by decide)
    have hji' : jetIndex (factorProduct A) ≤ 41 := by
      simp only [reserveCost, Bool.false_eq_true, ite_false, Low6960FatSlots.slot_zero, jF] at hji
      exact hji.trans (by decide)
    exact ⟨hbt', hji'⟩
  · intro A hA hcomm
    have hbt := hbound true A hA hcomm _ _ hbcap
    have hji := hbound true A hA hcomm _ _ hjcap
    have hse := hbound true A hA hcomm _ _ hscap
    change jetTotal _ ≤ _ at hbt
    change jetIndex _ ≤ _ at hji
    rw [MvPolynomial.weightedTotalDegree_piSingle] at hse
    have hbt' : jetTotal (factorProduct A) ≤ 17 := by
      simpa only [reserveCost, ite_true, Low6960FatSlots.slot_zero, bM] using hbt
    have hji' : jetIndex (factorProduct A) ≤ 5 := by
      simpa only [reserveCost, ite_true, Low6960FatSlots.slot_zero, jM] using hji
    have hse' : seedDegree (factorProduct A) ≤ 70 := by
      simp only [reserveCost, ite_true, Low6960FatSlots.slot_zero, sM] at hse
      exact hse.trans (by decide)
    exact ⟨hbt', hji', hse', excludes_top hA hr hb (hdiv true A hA hcomm)⟩
end
end Low6960FatFactors
end

#print axioms Low6960FatFactors.proof

end Merged_R6960Low6960FatFactors

end Merged6967_R6960Low6960FatFactors

section Merged6967_R6960Low6960FatPadding
set_option Elab.async false


set_option Elab.async false

-- merged module R6960Low6960FatEliminate
section Merged_R6960Low6960FatEliminate

set_option Elab.async false
section
namespace Low6960Fat
noncomputable section
open K1 K1_13 K1_13_4_5
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
private theorem mixedWeight_pos {a : SeedVar →₀ ℕ} (ha : a ≠ 0) : 0 < mixedWeight a := by
  by_contra! h
  change 7074 * a none + 48749 * a.some.degree ≤ 0 at h
  have hn : a none = 0 := by omega
  have hd : a.some.degree = 0 := by omega
  have hs := (Finsupp.degree_eq_zero_iff _).mp hd
  apply ha
  ext i
  cases i with
  | none => simpa using hn
  | some i => simpa using DFunLike.congr_fun hs i
private theorem order_cancel_coeff (A B : GenericRow) (d : ℕ) (hA : A.coeff 0 ≠ 0)
    (hAB : ∀ a, mixedWeight a < d → (A * B).coeff a = 0) :
    ∀ a, mixedWeight a < d → B.coeff a = 0 := by
  classical
  suffices h : ∀ n a, mixedWeight a = n → n < d → B.coeff a = 0 by
    exact fun a ha => h _ a rfl ha
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro a ha hd
    have hab := hAB a (ha.symm ▸ hd)
    rw [MvPolynomial.coeff_mul, Finset.sum_eq_single_of_mem (0, a) (by simp)] at hab
    · exact (mul_eq_zero.mp hab).resolve_left hA
    · intro b hb hbne
      have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hb₁ : b.1 ≠ 0 := by
        intro hz
        apply hbne
        exact Prod.ext hz (by simpa [hz] using hs)
      have hw := mixedWeight_add b.1 b.2
      rw [hs, ha] at hw
      have hpos := mixedWeight_pos hb₁
      rw [ih (mixedWeight b.2) (by omega) b.2 rfl (by omega), mul_zero]
private theorem translated_const (F : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) :
    (translate (atPoint z y) F).coeff 0 = MvPolynomial.eval (atPoint z y) F := by
  let e : GenericRow →+* GenericX := MvPolynomial.eval (fun _ => 0)
  have he : e.comp (K1_13_4.translate (atPoint z y)) = MvPolynomial.eval (atPoint z y) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [e, K1_13_4.translate]
    · intro i
      simp [e, K1_13_4.translate]
  rw [← MvPolynomial.constantCoeff_eq, ← MvPolynomial.eval_zero']
  exact DFunLike.congr_fun he F
private theorem mixedOrder_cancel (A B : GenericRow) (z : GenericX) (y : Fin 3 → GenericX) (d : ℕ)
    (hA : MvPolynomial.eval (atPoint z y) A ≠ 0) (h : MixedOrder (A * B) z y d) :
    MixedOrder B z y d := by
  intro a ha
  by_contra! hlt
  refine (MvPolynomial.mem_support_iff.mp ha) (order_cancel_coeff
    (translate (atPoint z y) A) (translate (atPoint z y) B) d ?_ ?_ a hlt)
  · rwa [translated_const]
  · intro b hb
    rw [← map_mul]
    by_contra hne
    exact (Nat.not_lt_of_ge (h b (MvPolynomial.mem_support_iff.mpr hne))) hb
open P3_6_4 (moving_lower total_prod index_prod eval_prod_factor_ne_zero)
theorem eliminate_common (Γ : Finset K) (z : K → Geom) (S : K → (Polynomial Geom))
    (hzinj : Function.Injective z) {F G : GenericRow} (D : CommonPair F G)
    (hOrders : ∀ γ ∈ Γ, PairOrders F G (inclConst (z γ)) (trajectory (S γ))) :
      ∃ (book : Finset K) (Q : Lower), book.card ≤ 140000 ∧ Q ≠ 0 ∧
        Q.totalDegree ≤ 2502 ∧ lowerIndex Q ≤ 811 ∧
        ∀ γ ∈ Γ, γ ∉ book → MvPolynomial.eval (trajectory (S γ)) Q = 0 ∨
          PairOrders D.left D.right (inclConst (z γ)) (trajectory (S γ)) := by
  classical
  have fix_ne (f : GenericRow) (hf : f ∈ D.fixed) : f ≠ 0 :=
    (D.fixed_kind f hf).1.ne_zero
  have mov_ne (f : GenericRow) (hf : f ∈ D.moving) : f ≠ 0 :=
    (D.moving_kind f hf).1.ne_zero
  have mov_total : (∑ f ∈ D.moving, jetTotal f) ≤ 17 := by
    simpa only [jetTotal, MvPolynomial.weightedTotalDegree_prod _ _ _ mov_ne]
      using D.moving_total
  have mov_index : (∑ f ∈ D.moving, jetIndex f) ≤ 5 := by
    simpa only [jetIndex, MvPolynomial.weightedTotalDegree_prod _ _ _ mov_ne]
      using D.moving_index
  have mov_seed : (∑ f ∈ D.moving, seedDegree f) ≤ 70 := by
    simpa only [seedDegree, MvPolynomial.degreeOf_prod_eq _ _ mov_ne] using D.moving_seed
  have seed_le (f : GenericRow) (hf : f ∈ D.moving) : seedDegree f ≤ 70 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans mov_seed
  choose! q qn qt qi qe using
    (fun f hf => fixed_lower f (fix_ne f hf) (D.fixed_kind f hf).2.2)
  have exists_moving (f : GenericRow) (hf : f ∈ D.moving) :=
    moving_lower f (D.moving_kind f hf).1 (D.moving_kind f hf).2.1
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans mov_total)
      (D.moving_kind f hf).2.2.1 (D.moving_kind f hf).2.2.2
  choose! r rn rt ri re using exists_moving
  let P : Lower := ∏ f ∈ D.fixed, q f
  let R : Lower := ∏ f ∈ D.moving, r f
  have Pn : P ≠ 0 := Finset.prod_ne_zero_iff.mpr qn
  have Rn : R ≠ 0 := Finset.prod_ne_zero_iff.mpr rn
  have Pt : P.totalDegree ≤ 122 := by
    change (∏ f ∈ D.fixed, q f).totalDegree ≤ 122
    rw [total_prod _ _ qn]
    calc
      _ = ∑ f ∈ D.fixed, jetTotal f := Finset.sum_congr rfl qt
      _ ≤ _ := by
        simpa only [jetTotal, MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_total
  have Pi : lowerIndex P ≤ 41 := by
    change lowerIndex (∏ f ∈ D.fixed, q f) ≤ 41
    rw [index_prod _ _ qn]
    calc
      _ = ∑ f ∈ D.fixed, jetIndex f := Finset.sum_congr rfl qi
      _ ≤ _ := by
        simpa only [jetIndex, MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_index
  have Rt : R.totalDegree ≤ 2 * 70 * 17 := by
    change (∏ f ∈ D.moving, r f).totalDegree ≤ 2 * 70 * 17
    rw [total_prod _ _ rn]
    calc
      _ ≤ ∑ f ∈ D.moving, (2 * 70) * jetTotal f :=
        Finset.sum_le_sum fun f hf => (rt f hf).trans
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (seed_le f hf)))
      _ ≤ _ := by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ mov_total
  have Ri : lowerIndex R ≤ (2 * 5 + 1) * 70 := by
    change lowerIndex (∏ f ∈ D.moving, r f) ≤ (2 * 5 + 1) * 70
    rw [index_prod _ _ rn]
    calc
      _ ≤ ∑ f ∈ D.moving, ((2 * 70) * jetIndex f + seedDegree f) := by
        apply Finset.sum_le_sum
        intro f hf
        refine (ri f hf).trans ?_
        rw [Nat.add_mul, one_mul, Nat.mul_right_comm 2]
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (seed_le f hf))) _
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have hh := Nat.mul_le_mul_left (2 * 70) mov_index
        omega
  let book := seedBook Γ z D.pure
  have hbook : book.card ≤ 140000 :=
    (count_seed_roots Γ z hzinj D.pure D.pure_ne).trans D.pure_degree
  refine ⟨book, P * R, hbook, mul_ne_zero Pn Rn, ?_, ?_, ?_⟩
  · simp only [← MvPolynomial.weightedTotalDegree_one] at Pt Rt ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pt Rt).trans (show 122 + 2 * 70 * 17 ≤ 2502 by decide)
  · simp only [lowerIndex_eq_weighted] at Pi Ri ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pi Ri).trans (show 41 + (2 * 5 + 1) * 70 ≤ 811 by decide)
  · intro γ hγ hnot
    let a := inclConst (z γ)
    let y := trajectory (S γ)
    change MvPolynomial.eval y (P * R) = 0 ∨ PairOrders D.left D.right a y
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
end
end Low6960Fat
end
section
namespace Low6960Fat
open Polynomial
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped Polynomial BigOperators
open P3_6_4 (resultant_taylor_formal)
private def weight (d i : ℕ) : ℕ := d - 7074 * i
private def power (w : ℕ) : ℕ := (48748 + w) / 48749
private theorem coefficient_bound {k : Type*} [CommRing k]
    (P : (Polynomial (Polynomial k))) (d e i j : ℕ) (hij : j ≤ i)
    (hP : ∀ i l : ℕ, 7074 * i + 48749 * l < d → (P.coeff i).coeff l = 0) :
    (Polynomial.X : (Polynomial k)) ^ power (weight (d + e) i - weight e j) ∣ P.coeff (i - j) := by
  have hweight : weight (d + e) i ≤ weight e j + weight d (i - j) := by
    unfold weight
    omega
  apply X_pow_dvd_iff.mpr
  intro l hl
  apply hP
  unfold power at hl
  have hsmall : 48749 * l < weight (d + e) i - weight e j := by omega
  unfold weight at hweight hsmall
  omega
private def columnWeight {m n : ℕ} (j : Fin (m + n)) : ℕ :=
  j.addCases (fun j : Fin m => weight firstOrder j) (fun j : Fin n => weight secondOrder j)
private theorem sylvester_entry {k : Type*} [CommRing k]
    (F G : (Polynomial (Polynomial k))) (m n : ℕ)
    (hF : ∀ i l : ℕ, 7074 * i + 48749 * l < firstOrder → (F.coeff i).coeff l = 0)
    (hG : ∀ i l : ℕ, 7074 * i + 48749 * l < secondOrder → (G.coeff i).coeff l = 0)
    (i j : Fin (m + n)) :
    (Polynomial.X : (Polynomial k)) ^ power (weight (firstOrder + secondOrder) i - columnWeight j) ∣
      sylvester F G m n i j := by
  induction j using Fin.addCases with
  | left j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left, columnWeight, Set.mem_Icc]
    split_ifs with h
    · simpa only [add_comm secondOrder firstOrder] using
        coefficient_bound G secondOrder firstOrder i j h.1 hG
    · exact dvd_zero _
  | right j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_right, columnWeight, Set.mem_Icc]
    split_ifs with h
    · exact coefficient_bound F firstOrder secondOrder i j h.1 hF
    · exact dvd_zero _
private theorem det_bound {k : Type*} [CommRing k] {N D : ℕ}
    (M : Matrix (Fin N) (Fin N) (Polynomial k)) (row col : Fin N → ℕ)
    (hM : ∀ i j, (Polynomial.X : (Polynomial k)) ^ power (row i - col j) ∣ M i j)
    (hbudget : (∑ j, col j) + 48749 * D ≤ (∑ i, row i) + 48748) :
    (Polynomial.X : (Polynomial k)) ^ D ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  let a : Fin N → ℕ := fun j => power (row (σ j) - col j)
  have hprod : (Polynomial.X : (Polynomial k)) ^ (∑ j, a j) ∣ ∏ j, M (σ j) j := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => hM (σ j) j)
  have hsum : (∑ i, row i) ≤ (∑ j, col j) + 48749 * (∑ j, a j) := by
    rw [← Equiv.sum_comp σ row, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    dsimp only [a, power]
    omega
  have hD : D ≤ ∑ j, a j := by omega
  exact dvd_mul_of_dvd_right ((pow_dvd_pow _ hD).trans hprod) _
private theorem sum_weight {d t N : ℕ} (ht : t ≤ N) (hend : d ≤ 7074 * t)
    (hbefore : ∀ i < t, 7074 * i ≤ d) :
    (∑ i : Fin N, weight d i) = t * d - 7074 * (t * (t - 1) / 2) := by
  rw [Fin.sum_univ_eq_sum_range]
  have htrim : (∑ i ∈ Finset.range t, weight d i) = ∑ i ∈ Finset.range N, weight d i := by
    apply Finset.sum_subset (Finset.range_mono ht)
    intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    unfold weight
    omega
  rw [← htrim]
  have hsum : (∑ i ∈ Finset.range t, weight d i) + 7074 * (∑ i ∈ Finset.range t, i) =
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
    (∑ j : Fin (27000 + 27000), columnWeight (m := 27000) (n := 27000) j) + 48749 * 23893 ≤
      (∑ i : Fin (27000 + 27000), weight (firstOrder + secondOrder) i) + 48748 := by
  have hF : (∑ i : Fin 27000, weight firstOrder i) = 1459774464 := by
    rw [sum_weight (t := 642) (by decide) (by decide)
      (by intro i hi; simp only [firstOrder]; omega)]
    decide
  have hG : (∑ i : Fin 27000, weight secondOrder i) = 233606575 := by
    rw [sum_weight (t := 257) (by decide) (by decide)
      (by intro i hi; simp only [secondOrder]; omega)]
    decide
  have hFG : (∑ i : Fin (27000 + 27000), weight (firstOrder + secondOrder) i) =
      2858127770 := by
    rw [sum_weight (t := 899) (by decide) (by decide)
      (by intro i hi; simp only [firstOrder, secondOrder]; omega)]
    decide
  rw [Fin.sum_univ_add, hFG]
  simp only [columnWeight, Fin.addCases_left, Fin.addCases_right, hF, hG]
  decide
private theorem resultant_bound
    (F G : (Polynomial (Polynomial GenericX))) (z : GenericX) {m n D : ℕ} (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n)
    (hFO : ∀ i l : ℕ, 7074 * i + 48749 * l < firstOrder →
      ((F.taylor (C z)).coeff i).coeff l = 0)
    (hGO : ∀ i l : ℕ, 7074 * i + 48749 * l < secondOrder →
      ((G.taylor (C z)).coeff i).coeff l = 0)
    (hbudget : (∑ j : Fin (m + n), columnWeight (m := m) (n := n) j) + 48749 * D ≤
      (∑ i : Fin (m + n), weight (firstOrder + secondOrder) i) + 48748) :
    (Polynomial.X : (Polynomial GenericX)) ^ D ∣ resultant F G m n := by
  rw [← resultant_taylor_formal F G (C z) hF hG]
  unfold resultant
  exact det_bound
    (sylvester (F.taylor (C z)) (G.taylor (C z)) m n)
    (fun i => weight (firstOrder + secondOrder) i)
    (columnWeight (m := m) (n := n))
    (sylvester_entry _ _ m n hFO hGO) hbudget
theorem line_resultant_order (F G : (Polynomial (Polynomial GenericX))) (z : GenericX)
    (hF : F.natDegree ≤ 27000) (hG : G.natDegree ≤ 27000)
    (hFO : ∀ i j, 7074 * i + 48749 * j < firstOrder →
      ((F.taylor (Polynomial.C z)).coeff i).coeff j = 0)
    (hGO : ∀ i j, 7074 * i + 48749 * j < secondOrder →
      ((G.taylor (Polynomial.C z)).coeff i).coeff j = 0) :
    (Polynomial.X : (Polynomial GenericX)) ^ 23893 ∣ Polynomial.resultant F G 27000 27000 := by
  exact resultant_bound F G z (m := 27000) (n := 27000) (D := 23893)
    hF hG hFO hGO benchmark_budget
end Low6960Fat
end
section
namespace Low6960Fat
noncomputable section
open K1_13 Polynomial
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open scoped BigOperators
set_option maxRecDepth 4000
private def ray (v : Fin 3 → GenericX) : Lower →+* (Polynomial GenericX) :=
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
    ((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y))).comp (Polynomial.X + C (C z)) =
      (asSeedPoly (K1_13_4.translate (atPoint z y) F)).map (ray v) := by
  let e := (MvPolynomial.optionEquivLeft GenericX (Fin 3)).toRingHom
  let left := (compRingHom (Polynomial.X + C (C z))).comp ((mapRingHom ((ray v).comp (K1_13_4.translate y))).comp e)
  let right := (mapRingHom (ray v)).comp (e.comp (K1_13_4.translate (atPoint z y)))
  have he : left = right := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [left, right, e, K1_13_4.translate, ray]
    · intro i
      cases i <;>
        simp [left, right, e, K1_13_4.translate, ray, atPoint]
  exact DFunLike.congr_fun he F
private theorem line_order (F : GenericRow) (z : GenericX) (y v : Fin 3 → GenericX)
    (d : ℕ) (hF : MixedOrder F z y d) :
    ∀ i j, 7074 * i + 48749 * j < d →
      ((((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y))).taylor (C z)).coeff i).coeff j = 0 := by
  intro i j h
  change ((((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y))).comp
    (Polynomial.X + C (C z))).coeff i).coeff j = 0
  rw [line_translation, coeff_map, ray_coeff]
  suffices hc : MvPolynomial.homogeneousComponent j
      ((asSeedPoly (K1_13_4.translate (atPoint z y) F)).coeff i) = 0 by
    rw [hc, map_zero]
  apply MvPolynomial.homogeneousComponent_eq_zero'
  intro a ha hj
  have hmem : a.optionElim i ∈ (K1_13_4.translate (atPoint z y) F).support := by
    rw [← MvPolynomial.mem_support_coeff_optionEquivLeft]
    exact ha
  have hb := hF _ hmem
  have hweight : mixedWeight (a.optionElim i) = 7074 * i + 48749 * j := by
    change 7074 * a.optionElim i none + 48749 * (a.optionElim i).some.degree = _
    rw [Finsupp.optionElim_apply_none, Finsupp.some_optionElim, hj]
  rw [hweight] at hb
  exact (Nat.not_lt_of_ge hb) h
private theorem order_of_rays (Q : Lower) (y : Fin 3 → GenericX) (d : ℕ)
    (h : ∀ v, Polynomial.X ^ d ∣ ray v (K1_13_4.translate y Q)) :
    LowerOrder Q y d := by
  let _ : Infinite GenericX := Infinite.of_injective inclConst inclConst.injective
  intro a ha
  change d ≤ a.degree
  by_contra! ha'
  have hm : MvPolynomial.homogeneousComponent a.degree (K1_13_4.translate y Q) = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_zero, ← ray_coeff]
    exact (X_pow_dvd_iff (n := d) (f := ray v (K1_13_4.translate y Q))).mp (h v) a.degree ha'
  have hc := congrArg (fun P : Lower => P.coeff a) hm
  simp [MvPolynomial.coeff_homogeneousComponent] at hc
  exact (MvPolynomial.mem_support_iff.mp ha) hc
def seedResultant27 (F G : GenericRow) : Lower :=
  Polynomial.resultant (asSeedPoly F) (asSeedPoly G) 27000 27000
private theorem line_resultant (F G : GenericRow) (y v : Fin 3 → GenericX) :
    resultant ((asSeedPoly F).map ((ray v).comp (K1_13_4.translate y)))
      ((asSeedPoly G).map ((ray v).comp (K1_13_4.translate y))) 27000 27000 =
        ray v (K1_13_4.translate y (seedResultant27 F G)) := by
  unfold seedResultant27
  rw [resultant_map_map, RingHom.comp_apply]
theorem mixedOrder_pad {F : GenericRow} {z : GenericX} {y : Fin 3 → GenericX}
    {d : ℕ} (a : (Polynomial Geom)) (h : MixedOrder F z y d) :
    MixedOrder (pad F a) z y d := by
  classical
  intro m hm
  rw [pad, map_mul] at hm
  obtain ⟨u, hu, v, _, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  exact (h u hu).trans (by rw [mixedWeight_add]; exact Nat.le_add_right _ _)
theorem resultant_order (F G : GenericRow) (z : GenericX)
    (y : Fin 3 → GenericX) (hF : (asSeedPoly F).natDegree ≤ 27000)
    (hG : (asSeedPoly G).natDegree ≤ 27000) (h : PairOrders F G z y) :
    LowerOrder (seedResultant27 F G) y 23893 := by
  apply order_of_rays
  intro v
  rw [← line_resultant F G y v]
  exact line_resultant_order _ _ z (natDegree_map_le.trans hF) (natDegree_map_le.trans hG)
    (line_order F z y v _ h.1) (line_order G z y v _ h.2)
end
end Low6960Fat
end

#print axioms Low6960Fat.resultant_order

end Merged_R6960Low6960FatEliminate

-- merged module R6960Low6960FatPadding
section Merged_R6960Low6960FatPadding

set_option Elab.async false
/-! Low-specific padding of a coprime pair to seed degree exactly 27,000 and the resulting
resultant box (367,443,000, 124,200,000); a copy of the padding part of `Fast074`. -/
section
namespace Low6960Fat
noncomputable section
open K1_13 K1_13_4 Polynomial
open scoped Polynomial BigOperators Pointwise
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
open K1_13_4_6 (Fiber toFiber embedConstant toFiber_injective coprime_in_fiber exists_constant_nonroot coprime_linear asSeedPoly_ne_zero deg deg_pad_coeff deg_resultant)
structure PaddedPair27 (F G : GenericRow) where
  a : (Polynomial Geom)
  b : (Polynomial Geom)
  degree_left : (asSeedPoly (pad F a)).natDegree = 27000
  degree_right : (asSeedPoly (pad G b)).natDegree = 27000
  nonzero : seedResultant27 (pad F a) (pad G b) ≠ 0
  total : (seedResultant27 (pad F a) (pad G b)).totalDegree ≤ 367443000
  index : lowerIndex (seedResultant27 (pad F a) (pad G b)) ≤ 124200000
  keeps_order : ∀ z y, PairOrders F G z y → PairOrders (pad F a) (pad G b) z y
private theorem pad_degree27 (F : GenericRow) (hF : F ≠ 0)
    (hcap : seedDegree F ≤ 27000) (a : Geom) :
    (asSeedPoly (pad F (((Polynomial.X : (Polynomial Geom)) - C a) ^
      (27000 - (asSeedPoly F).natDegree)))).natDegree = 27000 := by
  have hcap' : (asSeedPoly F).natDegree ≤ 27000 := by
    simpa only [asSeedPoly, MvPolynomial.natDegree_optionEquivLeft, seedDegree] using hcap
  rw [K1_13_4_6.asSeedPoly_pad, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    natDegree_mul (asSeedPoly_ne_zero hF) (pow_ne_zero _ (X_sub_C_ne_zero _)),
    natDegree_pow, natDegree_X_sub_C, mul_one, Nat.add_sub_of_le hcap']
theorem padding_exists27 {F G : GenericRow} (hF : F ≠ 0) (hG : G ≠ 0)
    (hfg : IsRelPrime F G) (hf : seedDegree F ≤ 27000) (hg : seedDegree G ≤ 27000) :
    ∃ a b : (Polynomial Geom), (asSeedPoly (pad F a)).natDegree = 27000 ∧
      (asSeedPoly (pad G b)).natDegree = 27000 ∧ seedResultant27 (pad F a) (pad G b) ≠ 0 := by
  classical
  let f := (asSeedPoly F).map toFiber
  let g := (asSeedPoly G).map toFiber
  have hf0 : f ≠ 0 := (Polynomial.map_ne_zero_iff toFiber_injective).mpr (asSeedPoly_ne_zero hF)
  have hg0 : g ≠ 0 := (Polynomial.map_ne_zero_iff toFiber_injective).mpr (asSeedPoly_ne_zero hG)
  have hcop : IsCoprime f g := by
    apply coprime_in_fiber (asSeedPoly_ne_zero hF)
    intro d hdf hdg
    let e := MvPolynomial.optionEquivLeft GenericX (Fin 3)
    have hu : IsUnit (e.symm d) :=
      hfg (by simpa [e, asSeedPoly] using map_dvd e.symm.toRingHom hdf)
        (by simpa [e, asSeedPoly] using map_dvd e.symm.toRingHom hdg)
    have he := hu.map e.toRingHom
    change IsUnit (e (e.symm d)) at he
    rwa [e.apply_symm_apply] at he
  obtain ⟨a, ha, _⟩ := exists_constant_nonroot g hg0 ∅
  obtain ⟨b, hb, hba⟩ := exists_constant_nonroot f hf0 {toFiber (embedConstant a)}
  let p := ((Polynomial.X : (Polynomial Geom)) - C a) ^ (27000 - (asSeedPoly F).natDegree)
  let q := ((Polynomial.X : (Polynomial Geom)) - C b) ^ (27000 - (asSeedPoly G).natDegree)
  have hp : (asSeedPoly (pad F p)).natDegree = 27000 := pad_degree27 F hF hf a
  have hq : (asSeedPoly (pad G q)).natDegree = 27000 := pad_degree27 G hG hg b
  refine ⟨p, q, hp, hq, ?_⟩
  have hab : toFiber (embedConstant a) ≠ toFiber (embedConstant b) := by
    simpa using (Finset.notMem_singleton.mp hba).symm
  have hpad : IsCoprime ((asSeedPoly (pad F p)).map toFiber)
      ((asSeedPoly (pad G q)).map toFiber) := by
    simp only [K1_13_4_6.asSeedPoly_pad, Polynomial.map_mul, p, q, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
    exact (hcop.mul_right (coprime_linear f hb).symm.pow_right).mul_left
      ((coprime_linear g ha).pow_left.mul_right
        (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit).pow)
  have hn := resultant_ne_zero _ _ hpad
  rw [natDegree_map_eq_of_injective toFiber_injective,
    natDegree_map_eq_of_injective toFiber_injective, hp, hq, resultant_map_map] at hn
  intro hz
  exact hn ((congrArg toFiber hz).trans (map_zero _))

theorem padded27 {F G : GenericRow} (hF : F ≠ 0) (hG : G ≠ 0) (hp : IsRelPrime F G)
    (hf : Low6960Fat.Caps27 firstBox F) (hg : Low6960Fat.Caps27 secondBox G) :
    Nonempty (PaddedPair27 F G) := by
  obtain ⟨a, b, ha, hb, hn⟩ := padding_exists27 hF hG hp (hf.2.trans (by decide)) (hg.2.trans (by decide))
  refine ⟨⟨a, b, ha, hb, hn, ?_, ?_, ?_⟩⟩
  · have h := deg_resultant (1 : Fin 3 → ℕ) (asSeedPoly (pad F a)) (asSeedPoly (pad G b))
      27000 27000 6789 6820 (fun i => (deg_pad_coeff _ F a i).trans hf.1.1)
      (fun i => (deg_pad_coeff _ G b i).trans hg.1.1)
    simpa only [MvPolynomial.weightedTotalDegree_one, seedResultant27,
      ← Nat.mul_add, Nat.add_comm 6820 6789] using h.trans_eq (by norm_num)
  · have h := deg_resultant Fin.val (asSeedPoly (pad F a)) (asSeedPoly (pad G b))
      27000 27000 2300 2300 (fun i => (deg_pad_coeff _ F a i).trans hf.1.2.1)
      (fun i => (deg_pad_coeff _ G b i).trans hg.1.2.1)
    simpa only [MvPolynomial.weightedTotalDegree, Finsupp.weight_apply, Nat.nsmul_eq_mul,
      Nat.mul_comm, lowerIndex, seedResultant27, ← Nat.mul_add] using h.trans_eq (by norm_num)
  · intro z y h
    exact ⟨mixedOrder_pad a h.1, mixedOrder_pad b h.2⟩
end
end Low6960Fat
end

end Merged_R6960Low6960FatPadding

end Merged6967_R6960Low6960FatPadding
