import ProximityPrize.SubmissionLower.Low48Price
import ProximityPrize.SubmissionLower.Low48FatPad
import ProximityPrize.SubmissionLower.PortLow5

set_option Elab.async false
set_option autoImplicit true
section
namespace Low48FatCount
noncomputable section
open K1_13 (Shape chart ceilDiv mixed32 Row)
open K1_13_7 (LowerPoint pointIdeal pairIdeal tripleIdeal localColength)
open Low48Price (commonBox resultantBox fatOrder divisorOrder isolatedOrder taylorLength
  linearChart incidenceGap physicalDegree)
abbrev residualOrder : ℕ := fatOrder - divisorOrder + 1
abbrev curveLength : ℕ := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
abbrev pointLength : ℕ := fatOrder * residualOrder * isolatedOrder
def HighCurve (P Q : Row 3) (y : LowerPoint) : Prop :=
  ∃ q : PrimeSpectrum K1_13_7.Lower,
    q.asIdeal ∈ (pairIdeal P Q).minimalPrimes ∧ q.asIdeal.height = 2 ∧
      q.asIdeal ≤ pointIdeal y ∧
      (curveLength : ℕ∞) ≤ localColength q (pairIdeal P Q) ∧
      localColength q (pairIdeal P Q) < ⊤
def IsolatedFat (P Q R : Row 3) (y : LowerPoint) : Prop :=
  ∃ q : PrimeSpectrum K1_13_7.Lower,
    q.asIdeal = pointIdeal y ∧ q.asIdeal ∈ (tripleIdeal P Q R).minimalPrimes ∧
      (pointLength : ℕ∞) ≤ localColength q (tripleIdeal P Q R) ∧
      localColength q (tripleIdeal P Q R) < ⊤
def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
def divisorBox : Shape :=
  ⟨commonBox.b + resultantBox.b / divisorOrder, commonBox.j + resultantBox.j / divisorOrder, 0⟩
theorem divisorBox_eq : divisorBox = ⟨24978, 8353, 0⟩ := by
  have hb : commonBox.b + resultantBox.b / divisorOrder = 24978 := by decide
  have hj : commonBox.j + resultantBox.j / divisorOrder = 8353 := by decide
  unfold divisorBox
  rw [hb, hj]
def hypersurfacePrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := fatChart x
  let big := divisorBox
  let cut : Shape :=
    ⟨max (max h.b big.b) (max h.j (big.j + 1)), max h.j (big.j + 1), max 1 h.t⟩
  ceilDiv (Low48Price.errors * mixed32 p big cut h) (32 * incidenceGap) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b ^ 2 + 5 * physicalDegree * p.b * h.b + 1
def singularPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := fatChart x
  if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b ^ 2 + 1 else 0
def highCurvePrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := fatChart x
  let q := resultantBox
  ceilDiv (Low48Price.errors * mixed32 p q q h + incidenceGap * mixed32 p q q p)
    (32 * incidenceGap * curveLength)
def isolatedPrice : ℕ :=
  let q := resultantBox
  ceilDiv (3 * q.j ^ 2 * (2 * q.b - q.j)) (4 * fatOrder * residualOrder * isolatedOrder)
theorem fat_price_sum (x : Shape) : Low48Price.fatPrice x =
    hypersurfacePrice x + singularPrice x + highCurvePrice x + isolatedPrice := rfl
end
end Low48FatCount
end
section
namespace Low48FatCount
noncomputable section
open Polynomial K1_13 MvPolynomial UniqueFactorizationMonoid
open K1_13_4 (Lower inclX inclConst GenericX lowerIndex LowerOrder trajectory translate)
open K1_13_7 (LowerCaps ProperLowerPair)
open K1_13_7_3 (inclX_injective support_toGeneric clear_denominators eval_toGeneric order_toGeneric
  order_cancel order_clear)
open Low48Price (commonBox resultantBox fatOrder divisorOrder)
open private K1_13_7_3_2.Exponent iterPartial source_support translate_iter exact_iter_not_dvd
  exists_separant from ProximityPrize.SubmissionLower.Fast073
open private caps_of_support ne_of_support caps_mul proper_clear from ProximityPrize.SubmissionLower.Fast073
private theorem exact_exponent {P f : Lower} (hf : Prime f)
    (hlow : K1_13_7_3.LowPowers P divisorOrder) :
    ∃ a < divisorOrder, f ^ a ∣ P ∧ ¬ f ^ (a + 1) ∣ P := by
  classical
  have hex : ∃ n : ℕ, ¬ f ^ n ∣ P := ⟨divisorOrder, hlow f hf⟩
  have hpos : 0 < Nat.find hex := by
    by_contra! h
    have hz : Nat.find hex = 0 := by omega
    exact Nat.find_spec hex (by simp [hz])
  have hle := Nat.find_min' hex (hlow f hf)
  let a := Nat.find hex - 1
  have ha : a + 1 = Nat.find hex := Nat.sub_add_cancel hpos
  refine ⟨a, by omega, not_not.mp (Nat.find_min hex (by omega : a < Nat.find hex)), ?_⟩
  rw [ha]
  exact Nat.find_spec hex
private theorem index_weight (m : K1_13_7_3_2.Exponent) :
    Finsupp.weight (R := ℕ) (Fin.val : Fin 3 → ℕ) m = m.sum (fun i e => i.val * e) := by
  simp only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm]
private def admissible (P : Lower) : Submodule GenericX Lower where
  carrier := {Q |
    (∀ m ∈ Q.support, m.degree ≤ resultantBox.b ∧
      Finsupp.weight (R := ℕ) (Fin.val : Fin 3 → ℕ) m ≤ resultantBox.j) ∧
    ∀ y, LowerOrder P y fatOrder → LowerOrder Q y residualOrder}
  zero_mem' := by
    simp [LowerOrder]
  add_mem' := by
    intro Q R hQ hR
    change (_ ∧ _) at hQ hR ⊢
    refine ⟨fun m hm => ?_, fun y hy m hm => ?_⟩
    · exact (Finset.mem_union.mp (support_add hm)).elim (hQ.1 m) (hR.1 m)
    · rw [map_add] at hm
      exact (Finset.mem_union.mp (support_add hm)).elim (hQ.2 y hy m) (hR.2 y hy m)
  smul_mem' := by
    intro c Q hQ
    change (_ ∧ _) at hQ ⊢
    rw [Algebra.smul_def]
    change (_ ∧ ∀ y, LowerOrder P y fatOrder → LowerOrder (MvPolynomial.C c * Q) y residualOrder)
    refine ⟨fun m hm => hQ.1 m (support_C_mul_le Q c hm), fun y hy m hm => ?_⟩
    rw [map_mul, show translate y (MvPolynomial.C c) = MvPolynomial.C c by simp [K1_13_4.translate]] at hm
    exact hQ.2 y hy m (support_C_mul_le (translate y Q) c hm)
private theorem iter_mem_admissible {P : Lower} (hb : P.totalDegree ≤ resultantBox.b)
    (hj : lowerIndex P ≤ resultantBox.j) (i : Fin 3) {a : ℕ} (ha : a < divisorOrder) :
    iterPartial i a P ∈ admissible P := by
  refine ⟨fun m hm => ?_, fun y hy m hm => ?_⟩
  · have hs := source_support i a P hm
    have htotal := (le_totalDegree hs).trans hb
    change (m + Finsupp.single i a).degree ≤ _ at htotal
    rw [map_add, Finsupp.degree_single] at htotal
    have hindex := (Finset.le_sup (f := fun x : K1_13_7_3_2.Exponent => x.sum (fun j e => j.val * e)) hs).trans hj
    rw [← index_weight, map_add] at hindex
    exact ⟨(Nat.le_add_right _ _).trans htotal, (Nat.le_add_right _ _).trans hindex⟩
  · rw [translate_iter] at hm
    have hord := hy _ (source_support i a (translate y P) hm)
    change fatOrder ≤ (m + Finsupp.single i a).degree at hord
    change residualOrder ≤ m.degree
    rw [map_add, Finsupp.degree_single] at hord
    change a < 50853 at ha
    change 55566 ≤ m.degree + a at hord
    change 4714 ≤ m.degree
    omega
private theorem proper_partial (P : Lower) (hP : P ≠ 0)
    (hb : P.totalDegree ≤ resultantBox.b) (hj : lowerIndex P ≤ resultantBox.j)
    (hlow : K1_13_7_3.LowPowers P divisorOrder) :
    ∃ Q : Lower, Q ≠ 0 ∧ Q.totalDegree ≤ resultantBox.b ∧
      lowerIndex Q ≤ resultantBox.j ∧ IsRelPrime P Q ∧
      ∀ y, LowerOrder P y fatOrder → LowerOrder Q y residualOrder := by
  classical
  let partials : Set Lower := {Q | ∃ (i : Fin 3) (a : ℕ), a < divisorOrder ∧ Q = iterPartial i a P}
  let N := Submodule.span GenericX partials
  have hN : N ≤ admissible P := Submodule.span_le.mpr (by
    rintro _ ⟨i, a, ha, rfl⟩
    exact iter_mem_admissible hb hj i ha)
  have hPN : P ∈ N := Submodule.subset_span ⟨0, 0, by decide, rfl⟩
  let _ : StrongNormalizationMonoid Lower := UniqueFactorizationMonoid.strongNormalizationMonoid
  let _ : Infinite GenericX := Infinite.of_injective inclConst inclConst.injective
  let factors := (normalizedFactors P).toFinset
  let forbidden : Option ↥factors → Submodule GenericX N
    | none => ⊥
    | some f => ((Ideal.span {f.val}).restrictScalars GenericX).comap N.subtype
  have hproper (k : Option ↥factors) : forbidden k ≠ ⊤ := by
    cases k with
    | none =>
      intro he
      have hm : (⟨P, hPN⟩ : N) ∈ forbidden none := he ▸ Submodule.mem_top
      exact hP (congrArg Subtype.val ((Submodule.mem_bot GenericX).mp hm))
    | some f =>
      have hm : f.val ∈ normalizedFactors P := Multiset.mem_toFinset.mp f.property
      have hf := prime_of_normalized_factor f.val hm
      have hfp := dvd_of_mem_normalizedFactors hm
      obtain ⟨i, hi⟩ := exists_separant hf
        (((totalDegree_le_of_dvd_of_isDomain hfp hP).trans hb).trans_lt (by decide))
      obtain ⟨a, ha, hdiv, hnext⟩ := exact_exponent hf hlow
      obtain ⟨U, hU⟩ := hdiv
      have hnd : ¬ f.val ∣ U := by
        rintro ⟨V, hv⟩
        exact hnext ⟨V, by rw [hU, hv, pow_succ, mul_assoc]⟩
      have hc : ¬ f.val ∣ iterPartial i a P := by
        rw [hU]
        exact exact_iter_not_dvd i hf hi a (ha.trans (by decide)) hnd
      let G : N := ⟨iterPartial i a P, Submodule.subset_span ⟨i, a, ha, rfl⟩⟩
      intro he
      have hg : G ∈ forbidden (some f) := he ▸ Submodule.mem_top
      exact hc (Ideal.mem_span_singleton.mp hg)
  obtain ⟨Q, hQ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (ι := Option ↥factors) (K := GenericX) (M := N) forbidden hproper
  have hgood := hN Q.property
  refine ⟨Q.val, ?_, ?_, ?_, ?_, hgood.2⟩
  · exact fun hz => hQ none ((Submodule.mem_bot GenericX).mpr (Subtype.ext hz))
  · exact Finset.sup_le (fun m hm => (hgood.1 m hm).1)
  · exact Finset.sup_le (fun m hm => (index_weight m) ▸ (hgood.1 m hm).2)
  · apply (isRelPrime_iff_no_prime_factors hP).mpr
    intro d hdP hdQ hd
    obtain ⟨f, hf, hassoc⟩ := exists_mem_normalizedFactors_of_dvd hP hd.irreducible hdP
    exact hQ (some ⟨f, Multiset.mem_toFinset.mpr hf⟩)
      (Ideal.mem_span_singleton.mpr (hassoc.dvd_iff_dvd_left.mp hdQ))
theorem buy_divisors (E : Low48Price.FatEquations) : ∃ D P Q : Row 3,
    D ≠ 0 ∧ LowerCaps D divisorBox.b divisorBox.j ∧
    LowerCaps P resultantBox.b resultantBox.j ∧ LowerCaps Q resultantBox.b resultantBox.j ∧
    ProperLowerPair P Q ∧ ∀ S : Geom[X], Low48Price.Holds E S →
      atJet D S = 0 ∨ (OrderAt P S fatOrder ∧ OrderAt Q S residualOrder) := by
  let R := MvPolynomial.map inclX E.residual
  have hsR : E.residual.support = R.support := (support_toGeneric _).symm
  have hnR : R ≠ 0 := (map_ne_zero_iff _ (MvPolynomial.map_injective _ inclX_injective)).mpr E.residual_ne
  have hbR : R.totalDegree ≤ resultantBox.b := by
    simpa only [MvPolynomial.totalDegree, hsR] using E.residual_total
  have hjR : lowerIndex R ≤ resultantBox.j := by
    simpa only [lowerIndex, indexDegree, hsR] using E.residual_index
  obtain ⟨H, A, P, hnH, hnP, heq, hdiv, hbH, hjH, hbP, hjP, hlow⟩ :=
    K1_13_7_3_1.proof R hnR resultantBox.b resultantBox.j divisorOrder (by decide) hbR hjR
  obtain ⟨Q, hnQ, hbQ, hjQ, hrel, horderQ⟩ := proper_partial P hnP hbP hjP hlow
  obtain ⟨dH, H', _, hsH, hmH⟩ := clear_denominators H
  obtain ⟨dP, P', hdP, hsP, hmP⟩ := clear_denominators P
  obtain ⟨dQ, Q', hdQ, hsQ, hmQ⟩ := clear_denominators Q
  have hnH' := ne_of_support hsH hnH
  have hcH : LowerCaps H' (resultantBox.b / divisorOrder) (resultantBox.j / divisorOrder) :=
    caps_of_support hsH hbH hjH
  have hcap : LowerCaps (E.common * H') divisorBox.b divisorBox.j :=
    caps_mul E.common_ne hnH' ⟨E.common_total, E.common_index⟩ hcH
  refine ⟨E.common * H', P', Q', mul_ne_zero E.common_ne hnH', hcap,
    caps_of_support hsP hbP hjP, caps_of_support hsQ hbQ hjQ,
    ⟨ne_of_support hsP hnP, ne_of_support hsQ hnQ, proper_clear hnP hnQ hrel hdP hdQ hmP hmQ⟩, ?_⟩
  intro S hS
  by_cases hd : atJet (E.common * H') S = 0
  · exact Or.inl hd
  right
  have hc : atJet E.common S ≠ 0 := fun h => hd (by
    simp [atJet, show MvPolynomial.eval (jet S) E.common = 0 from h])
  have hHval : MvPolynomial.eval (trajectory S) H ≠ 0 := by
    intro hz
    have hh := eval_toGeneric H' S
    rw [hmH, map_mul, hz, mul_zero] at hh
    have hz' : atJet H' S = 0 := inclX_injective (hh.symm.trans (map_zero _).symm)
    exact hd (by simp [atJet, show MvPolynomial.eval (jet S) H' = 0 from hz'])
  have hAval : MvPolynomial.eval (trajectory S) A ≠ 0 := by
    have hh := map_dvd (MvPolynomial.eval (trajectory S)) hdiv
    rw [map_pow] at hh
    intro hz
    exact pow_ne_zero _ hHval (zero_dvd_iff.mp (hz ▸ hh))
  have hRord : LowerOrder R (trajectory S) fatOrder :=
    (order_toGeneric E.residual S _).mpr (hS.resolve_left hc)
  rw [heq] at hRord
  have hPord := order_cancel hAval hRord
  exact ⟨order_clear hdP hmP S hPord, order_clear hdQ hmQ S (horderQ _ hPord)⟩
end
end Low48FatCount
end
section
namespace Low48FatCount
noncomputable section
open Polynomial K1_13 K1_13_7_4
open K1_13_7 (Lower LowerCaps ProperLowerPair genericRow lowerPoint pairIdeal tripleIdeal
  localColength)
open Low48Price (resultantBox fatOrder)
open scoped BigOperators
open private hasse_caps from ProximityPrize.SubmissionLower.Fast068
open private support_mul_C_subset from ProximityPrize.SubmissionLower.Fast068
private def thirdCuts (P Q : Row 3) : Submodule Geom (Row 3) where
  carrier := {R | LowerCaps R resultantBox.b resultantBox.j ∧
    ∀ S : Geom[X], OrderAt P S 55566 → OrderAt Q S 4714 → OrderAt R S 645}
  zero_mem' := by
    constructor
    · simp [LowerCaps, indexDegree]
    · intro S _ _
      change ∀ m ∈ (shiftHom S 0).support, _
      simp
  add_mem' := by
    intro R T hR hT
    change LowerCaps R _ _ ∧ _ at hR
    change LowerCaps T _ _ ∧ _ at hT
    obtain ⟨⟨hRb, hRj⟩, hr⟩ := hR
    obtain ⟨⟨hTb, hTj⟩, ht⟩ := hT
    change LowerCaps (R + T) _ _ ∧ _
    refine ⟨⟨(MvPolynomial.totalDegree_add R T).trans (max_le hRb hTb), ?_⟩, ?_⟩
    · apply Finset.sup_le
      intro m hm
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with hm | hm
      · exact (Finset.le_sup hm).trans hRj
      · exact (Finset.le_sup hm).trans hTj
    · intro S hp hq m hm
      change m ∈ (shiftHom S (R + T)).support at hm
      rw [map_add] at hm
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with hm | hm
      · exact hr S hp hq m hm
      · exact ht S hp hq m hm
  smul_mem' := by
    intro a R hR
    change LowerCaps R _ _ ∧ _ at hR
    obtain ⟨⟨hRb, hRj⟩, hr⟩ := hR
    change LowerCaps (a • R) _ _ ∧ _
    have hs : a • R = MvPolynomial.C (Polynomial.C a) * R := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_eq Geom Geom[X] (Row 3)]
      rfl
    rw [hs]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (Finset.sup_mono (support_mul_C_subset R (Polynomial.C a))).trans hRb
    · exact (Finset.sup_mono (support_mul_C_subset R (Polynomial.C a))).trans hRj
    · intro S hp hq m hm
      change m ∈ (shiftHom S (MvPolynomial.C (Polynomial.C a) * R)).support at hm
      rw [map_mul, shiftHom, MvPolynomial.eval₂Hom_C] at hm
      exact hr S hp hq m (support_mul_C_subset _ _ hm)
private theorem local_length : K1_13_7_4.c2 :=
  K1_13_7_4_2.of_children K1_13_7_4_2_1.proof K1_13_7_4_2_2.proof
private theorem avoid_low {P Q : Row 3}
    (hpq : ProperLowerPair P Q) (hp : LowerCaps P resultantBox.b resultantBox.j)
    (hq : LowerCaps Q resultantBox.b resultantBox.j) :
    ∃ R ∈ thirdCuts P Q, ∀ (q : PrimeSpectrum Lower),
      q.asIdeal ∈ (pairIdeal P Q).minimalPrimes →
      localColength q (pairIdeal P Q) < (curveLength : ℕ∞) → genericRow R ∉ q.asIdeal := by
  classical
  let partials (F : Row 3) (d : ℕ) : Set (Row 3) :=
    {D | ∃ a, multiOrder a < d ∧ D = hassePartial a F}
  let V := Submodule.span Geom (partials P 54922 ∪ partials Q 4070)
  have hadm : V ≤ thirdCuts P Q := by
    apply Submodule.span_le.mpr
    rintro D (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · refine ⟨hasse_caps a hp, ?_⟩
      intro S hPS _ m hm
      exact (by omega : 645 ≤ 55566 - multiOrder a).trans (hasse_order P S a _ hPS m hm)
    · refine ⟨hasse_caps a hq, ?_⟩
      intro S _ hQS m hm
      exact (by omega : 645 ≤ 4714 - multiOrder a).trans (hasse_order Q S a _ hQS m hm)
  let bad := {p : Ideal Lower | p ∈ (pairIdeal P Q).minimalPrimes ∧
    ∃ q : PrimeSpectrum Lower, q.asIdeal = p ∧ localColength q (pairIdeal P Q) < (curveLength : ℕ∞)}
  have hf : bad.Finite :=
    (pairIdeal P Q).finite_minimalPrimes_of_isNoetherianRing.subset fun _ h => h.1
  have hw : ∀ p ∈ bad, ∃ R ∈ V, genericRow R ∉ p := by
    intro p hp'
    obtain ⟨hmin, q, rfl, hsmall⟩ := hp'
    have hheight : q.asIdeal.height = 2 := pair_height hpq hmin
    by_contra! h
    have hP : VanishesTo q (genericRow P) 54922 := by
      exact K1_13_7_4_1.proof q P 54922 hheight fun a ha => h _ (Submodule.subset_span (Or.inl ⟨a, ha, rfl⟩))
    have hQ : VanishesTo q (genericRow Q) 4070 := by
      exact K1_13_7_4_1.proof q Q 4070 hheight fun a ha => h _ (Submodule.subset_span (Or.inr ⟨a, ha, rfl⟩))
    have hrange : Ideal.span (Set.range ![genericRow P, genericRow Q]) = pairIdeal P Q := by
      simp only [pairIdeal, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]
    have hlarge := local_length 2 (Or.inl rfl) q ![genericRow P, genericRow Q] ![54922, 4070]
      hheight (hrange ▸ hmin)
      (by simp [Fin.forall_fin_two]) (by simpa [Fin.forall_fin_two] using And.intro hP hQ)
    have hnum : (∏ i : Fin 2, (![54922, 4070] : Fin 2 → ℕ) i) = curveLength := by
      rw [Fin.prod_univ_two]
      decide
    rw [hnum, hrange] at hlarge
    exact (not_le_of_gt hsmall) hlarge
  obtain ⟨R, hR, havoid⟩ := exists_avoiding V bad hf hw
  exact ⟨R, hadm hR, fun q hmin hlow => havoid q.asIdeal ⟨hmin, q, rfl, hlow⟩⟩
theorem residual_strata (P Q : Row 3) (hpq : ProperLowerPair P Q)
    (hP : LowerCaps P resultantBox.b resultantBox.j)
    (hQ : LowerCaps Q resultantBox.b resultantBox.j) :
    ∃ R : Row 3, LowerCaps R resultantBox.b resultantBox.j ∧
      ∀ S : Geom[X], OrderAt P S fatOrder → OrderAt Q S residualOrder →
        HighCurve P Q (lowerPoint S) ∨ IsolatedFat P Q R (lowerPoint S) := by
  obtain ⟨R, hR, havoid⟩ := avoid_low hpq hP hQ
  refine ⟨R, hR.1, ?_⟩
  intro S hPS hQS
  by_cases hhigh : HighCurve P Q (lowerPoint S)
  · exact Or.inl hhigh
  right
  let q := pointPrime (lowerPoint S)
  have hRub := hR.2 S hPS hQS
  change OrderAt P S 55566 at hPS
  change OrderAt Q S 4714 at hQS
  have hp : VanishesTo q (genericRow P) 55566 := point_order hPS
  have hq : VanishesTo q (genericRow Q) 4714 := point_order hQS
  have hr : VanishesTo q (genericRow R) 645 := point_order hRub
  have hle : tripleIdeal P Q R ≤ q.asIdeal := triple_le_iff.mpr
    ⟨vanishes_at_prime (by decide) hp, vanishes_at_prime (by decide) hq,
      vanishes_at_prime (by decide) hr⟩
  have height_three_of_le (p : PrimeSpectrum Lower)
      (hpI : tripleIdeal P Q R ≤ p.asIdeal) (hpq' : p.asIdeal ≤ q.asIdeal) :
      p.asIdeal.height = 3 := by
    obtain ⟨I, hI, hIp⟩ := Ideal.exists_minimalPrimes_le
      (pair_le_iff.mpr ⟨(triple_le_iff.mp hpI).1, (triple_le_iff.mp hpI).2.1⟩)
    let t : PrimeSpectrum Lower := ⟨I, hI.isPrime⟩
    have : I.IsPrime := hI.isPrime
    have ht : t.asIdeal.height = 2 := pair_height hpq hI
    have hlow : localColength t (pairIdeal P Q) < (curveLength : ℕ∞) := by
      apply lt_of_not_ge
      intro h
      exact hhigh ⟨t, hI, ht, hIp.trans hpq', h, localColength_lt_top hI⟩
    have hlt : t.asIdeal < p.asIdeal := by
      apply lt_of_le_of_ne hIp
      intro heq
      apply havoid t hI hlow
      change genericRow R ∈ I
      rw [heq]
      exact (triple_le_iff.mp hpI).2.2
    have hh := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [ht] at hh
    exact le_antisymm (height_le_three p) hh
  have hheight := height_three_of_le q hle le_rfl
  have hmin : q.asIdeal ∈ (tripleIdeal P Q R).minimalPrimes := by
    refine ⟨⟨q.isPrime, hle⟩, ?_⟩
    intro I hI hIq
    let p : PrimeSpectrum Lower := ⟨I, hI.1⟩
    have : I.IsPrime := hI.1
    have hph := height_three_of_le p hI.2 hIq
    have heq : I = q.asIdeal := Ideal.eq_of_le_of_height_le I hIq (by
      change q.asIdeal.height ≤ p.asIdeal.height
      rw [hheight, hph])
    exact heq.ge
  refine ⟨q, rfl, hmin, ?_, localColength_lt_top hmin⟩
  have hrange : Ideal.span (Set.range ![genericRow P, genericRow Q, genericRow R]) =
      tripleIdeal P Q R := by
    simp only [tripleIdeal, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  have hlen := local_length 3 (Or.inr rfl) q ![genericRow P, genericRow Q, genericRow R]
    ![55566, 4714, 645] hheight (hrange ▸ hmin) (by simp [Fin.forall_fin_succ])
    (by simpa [Fin.forall_fin_succ] using And.intro hp (And.intro hq hr))
  rw [hrange] at hlen
  have hnum : (∏ i : Fin 3, (![55566, 4714, 645] : Fin 3 → ℕ) i) = pointLength := by
    rw [Fin.prod_univ_three]
    decide
  rwa [hnum] at hlen
end
end Low48FatCount
end
section
namespace Low48FatCount
noncomputable section
open K1_13 (Row ceilDiv)
open K1_13_7 (Lower LowerCaps LowerPoint GeometricX genericRow localColength pointIdeal)
open K1_13_7_6
open MvPolynomial (affineDegree_nonneg)
open Low48Price (resultantBox fatOrder isolatedOrder)
private theorem isolated_fee {n w a b : ℕ} (hw : 0 < w) (hab : a ≤ b)
    (h : (n : ℚ) * w ≤ 6 * (a : ℚ) ^ 2 * ((b : ℚ) - a)) :
    n ≤ ceilDiv (3 * (2 * a) ^ 2 * (2 * b - 2 * a)) (4 * w) := by
  have hcost : n * w ≤ 6 * a ^ 2 * (b - a) := by
    apply (Nat.cast_le (α := ℚ)).mp
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sub hab] using h
  have hvol : 4 * (6 * a ^ 2 * (b - a)) = 3 * (2 * a) ^ 2 * (2 * b - 2 * a) := by
    rw [← Nat.mul_sub_left_distrib]
    ring
  have hm := Nat.mul_le_mul_left 4 hcost
  rw [hvol] at hm
  unfold ceilDiv
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos (by decide) hw)).mpr
  rw [show n * (4 * w) = 4 * (n * w) from by ac_rfl]
  exact hm.trans (by omega)
theorem isolated_bound (P Q R : Row 3)
    (hP : LowerCaps P resultantBox.b resultantBox.j)
    (hQ : LowerCaps Q resultantBox.b resultantBox.j)
    (hR : LowerCaps R resultantBox.b resultantBox.j)
    (points : Finset LowerPoint) (hpoints : ∀ y ∈ points, IsolatedFat P Q R y) :
    points.card ≤ isolatedPrice := by
  classical
  unfold isolatedPrice
  change points.card ≤ ceilDiv _ (4 * fatOrder * residualOrder * isolatedOrder)
  rw [Nat.mul_assoc 4 fatOrder residualOrder, Nat.mul_assoc 4 _ isolatedOrder]
  change points.card ≤ ceilDiv (3 * (2 * halfIndexCap) ^ 2 *
    (2 * totalCap - 2 * halfIndexCap)) (4 * pointLength)
  let f := genericRow P
  let g := genericRow Q
  let h := genericRow R
  let D := chartDegree chartMap
  have hcuts : ∀ t : Lower, t ∈ ({f, g, h} : Set Lower) →
      ∃ L : MvPolynomial chartExponents GeometricX, chartMap L = t ∧ L.totalDegree ≤ 1 := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact chart_lift P hP
    · exact chart_lift Q hQ
    · exact chart_lift R hR
  have hpay : ∀ t : Lower, t ∈ ({f, g, h} : Set Lower) →
      ∀ p : PrimeSpectrum Lower, t ∉ p.asIdeal →
        ∀ qs : Finset (PrimeSpectrum Lower),
          (∀ q ∈ qs, q.asIdeal ∈ (cutIdeal p t).minimalPrimes) →
          (∀ q ∈ qs, localColength q (cutIdeal p t) < ⊤) →
          cutCost D p t qs ≤ D p := by
    intro t ht p hp qs hmin hfin
    obtain ⟨L, rfl, hL⟩ := hcuts t ht
    exact K1_13_7_6_1.proof chartMap chartMap_surjective p L hL hp qs hmin hfin
  have hpoints_cost := (K1_13_7_6_2.of_children K1_13_7_6_2_1.proof
    K1_13_7_6_2_2.proof) f g h D
    (fun q => affineDegree_nonneg (q.asIdeal.comap chartMap))
    (fun y q hy => (chartDegree_eq_one chartMap chartMap_surjective y q hy).ge)
    hpay points pointLength hpoints
  exact isolated_fee (by decide : 0 < pointLength) (by decide : halfIndexCap ≤ totalCap)
    (hpoints_cost.trans chartDegree_bound)
end
end Low48FatCount
end
section
namespace Low48FatCount
noncomputable section
open Polynomial
open P3 (K)
open Low48Price (Messages SmallFactor resultantBox)
open K1_13 (FatEligible Row atJet embed extend OnFactor shape)
open K1_13_7 (RegularAt LowerCaps ProperLowerPair lowerPoint
  lowerPoint_injective)
def c1 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → FatEligible (shape f) →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ)) ∧ ¬ RegularAt f (extend (s γ))) →
    Γ.card ≤ singularPrice (shape f)
def c2 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → FatEligible (shape f) →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ)) ∧ RegularAt f (extend (s γ))) →
    ∀ D : Row 3, D ≠ 0 → LowerCaps D divisorBox.b divisorBox.j →
      (∀ γ ∈ Γ, atJet D (extend (s γ)) = 0) → Γ.card ≤ hypersurfacePrice (shape f)
def c3 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → FatEligible (shape f) →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ)) ∧ RegularAt f (extend (s γ))) →
    ∀ P Q : Row 3, ProperLowerPair P Q →
      LowerCaps P resultantBox.b resultantBox.j → LowerCaps Q resultantBox.b resultantBox.j →
      (∀ γ ∈ Γ, HighCurve P Q (lowerPoint (extend (s γ)))) →
      Γ.card ≤ highCurvePrice (shape f)
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : Low48Price.c7 := by
  classical
  intro w Γ s hmsg f hf hon helig E hE
  obtain ⟨D, P, Q, hD, hDb, hPb, hQb, hpq, hres⟩ := buy_divisors E
  obtain ⟨R, hRb, hstrata⟩ := residual_strata P Q hpq hPb hQb
  let S : K → K1_13.Geom[X] := fun γ => extend (s γ)
  let singular := Γ.filter (fun γ => ¬ RegularAt f (S γ))
  let divisors := Γ.filter (fun γ => RegularAt f (S γ) ∧ atJet D (S γ) = 0)
  let curves := Γ.filter (fun γ => RegularAt f (S γ) ∧ HighCurve P Q (lowerPoint (S γ)))
  let isolated := Γ.filter (fun γ => IsolatedFat P Q R (lowerPoint (S γ)))
  have hsingular : singular.card ≤ singularPrice (shape f) :=
    h1 w singular s (Low48Price.Messages.mono hmsg (Finset.filter_subset _ _)) f hf helig
      (fun γ hγ => ⟨hon γ (Finset.mem_filter.mp hγ).1, (Finset.mem_filter.mp hγ).2⟩)
  have hdivisors : divisors.card ≤ hypersurfacePrice (shape f) :=
    h2 w divisors s (Low48Price.Messages.mono hmsg (Finset.filter_subset _ _)) f hf helig
      (fun γ hγ => ⟨hon γ (Finset.mem_filter.mp hγ).1, (Finset.mem_filter.mp hγ).2.1⟩)
      D hD hDb (fun _ hγ => (Finset.mem_filter.mp hγ).2.2)
  have hcurves : curves.card ≤ highCurvePrice (shape f) :=
    h3 w curves s (Low48Price.Messages.mono hmsg (Finset.filter_subset _ _)) f hf helig
      (fun γ hγ => ⟨hon γ (Finset.mem_filter.mp hγ).1, (Finset.mem_filter.mp hγ).2.1⟩)
      P Q hpq hPb hQb (fun _ hγ => (Finset.mem_filter.mp hγ).2.2)
  have hisolated : isolated.card ≤ isolatedPrice := by
    let points := isolated.image (fun γ => lowerPoint (S γ))
    have hinj : Set.InjOn (fun γ => lowerPoint (S γ)) (isolated : Set K) := by
      intro a ha b hb hab
      exact hmsg.distinct (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective (lowerPoint_injective hab))
    have hcard : points.card = isolated.card := Finset.card_image_of_injOn hinj
    rw [← hcard]
    apply isolated_bound P Q R hPb hQb hRb points
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hγ).2
  have hcover : Γ ⊆ divisors ∪ singular ∪ curves ∪ isolated := by
    intro γ hγ
    by_cases hr : RegularAt f (S γ)
    · rcases hres (S γ) (hE γ hγ) with hd | ⟨hp, hq⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hr, hd⟩)))
      · rcases hstrata (S γ) hp hq with hc | hi
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hγ, hr, hc⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hi⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hr⟩)))
  rw [fat_price_sum]
  calc
    Γ.card ≤ (divisors ∪ singular ∪ curves ∪ isolated).card := Finset.card_le_card hcover
    _ ≤ (divisors ∪ singular ∪ curves).card + isolated.card := Finset.card_union_le _ _
    _ ≤ (divisors ∪ singular).card + curves.card + isolated.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ divisors.card + singular.card + curves.card + isolated.card :=
      Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hdivisors hsingular) hcurves) hisolated
end
end Low48FatCount
end
section
namespace Low48FatCount_1
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_7_1
open P3 (K)
open K1_13_1 (topView topView_degree)
open K1_13_7 (RegularAt)
open P0_9_7_1 (sparse_bound surface_sections)
open private topAt eval_topAt topAt_coeff topView_separant from ProximityPrize.SubmissionLower.Fast056
open private derivativeBox derivative_box from ProximityPrize.SubmissionLower.PortLow7
private theorem regular_derivative (f : Row 4) (S : Geom[X])
    (htop : (shape f).t ≤ 13) (hon : OnFactor f S) (hs : atJet (separant f) S = 0) :
    ∃ j, 0 < j ∧ j < (shape f).t ∧
      atJet ((separant^[j]) f) S = 0 ∧ atJet (separant ((separant^[j]) f)) S ≠ 0 := by
  classical
  let t := (shape f).t
  let P := topAt S f
  have hdeg : P.natDegree ≤ t := Polynomial.natDegree_map_le.trans_eq (topView_degree f)
  have hnz : (derivative^[t] P).coeff 0 ≠ 0 := by
    rw [coeff_iterate_derivative, Nat.zero_add, Nat.descFactorial_self, nsmul_eq_mul]
    change (t.factorial : Geom[X]) * P.coeff t ≠ 0
    rw [← map_natCast (Polynomial.C : Geom →+* Geom[X])]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      (factorial_cast_ne_zero (htop.trans_lt (by decide : 13 < K1.p))))
      (by simpa only [P, t, topAt_coeff] using hon.2)
  have hc : derivative^[t] P = Polynomial.C ((derivative^[t] P).coeff 0) :=
    eq_C_of_natDegree_le_zero ((natDegree_iterate_derivative _ _).trans
      (by omega : P.natDegree - t ≤ 0))
  have he (k : ℕ) : atJet ((separant^[k]) f) S =
      (derivative^[k] P).eval (jet S (3 : Fin 4)) := by
    rw [← eval_topAt]
    congr 1
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [Function.iterate_succ_apply']
      change (topView (separant ((separant^[k]) f))).map (MvPolynomial.eval (jet S)) = _
      rw [topView_separant, ← derivative_map]
      exact congrArg derivative ih
  have ht_nonzero : atJet ((separant^[t]) f) S ≠ 0 := by
    rw [he, hc, Polynomial.eval_C]
    exact hnz
  have hex : ∃ k, atJet ((separant^[k]) f) S ≠ 0 := ⟨t, ht_nonzero⟩
  let k := Nat.find hex
  have hk : atJet ((separant^[k]) f) S ≠ 0 := Nat.find_spec hex
  have hkt : k ≤ t := Nat.find_min' hex ht_nonzero
  have hk0 : k ≠ 0 := by
    intro h
    apply hk
    simpa only [h, Function.iterate_zero_apply] using hon.1
  have hk1 : k ≠ 1 := by
    intro h
    apply hk
    simpa only [h, Function.iterate_one] using hs
  have hprev : k - 1 + 1 = k := by omega
  refine ⟨k - 1, by omega, by omega, ?_, ?_⟩
  · exact not_ne_iff.mp (Nat.find_min hex (by omega : k - 1 < k))
  · have he' : (separant^[k]) f = separant ((separant^[k - 1]) f) := by
      conv_lhs => rw [← hprev]
      rw [Function.iterate_succ_apply']
    simpa only [he'] using hk
private theorem chart_le (p : Shape) (hp : Chamber p) (ht : 1 < p.t) (hb : p.b ≤ 60) :
    InBox (chart (K1_13.taylorLength + 4) (derivativeBox p))
      (chart (Low48Price.taylorLength + 4) p) := by
  obtain ⟨hjb, htj⟩ := hp
  have hB : 1 + 267352 * (p.b - 1 - 1) ≤ 1 + 266862 * (p.b - 1) := by omega
  have hJ : 267352 * (p.j - 3 - 3) + 133676 + 3 ≤
      266862 * (p.j - 3) + 133431 + 3 := by omega
  have hT : 267352 * (p.t - 1 - 1) + 133676 + 1 ≤
      266862 * (p.t - 1) + 133431 + 1 := by omega
  exact ⟨max_le_max hB hJ, hJ, min_le_min hT (Nat.div_le_div_right hJ)⟩
private theorem exists_derivative_chart (f : Row 4) (he : FatEligible (shape f))
    (ht : 1 < (shape f).t) {j : ℕ} (hj : 0 < j) :
    let g := (separant^[j]) f
    ∃ C : TaylorChart, C.Fits (chart (Low48Price.taylorLength + 4) (shape f).chamber) ∧
      ∀ S : Geom[X], atJet g S = 0 → RegularAt g S → C.Recovers S := by
  dsimp only
  let p := (shape f).chamber
  let q := derivativeBox p
  have hp : Chamber p := shape_chamber f
  have htp : 1 < p.t := ht
  have hpb : p.b ≤ 60 := max_le he.1 (he.2.trans (by decide))
  have hq : Chamber q := by
    obtain ⟨hjb, htj⟩ := hp
    change p.j - 3 ≤ p.b - 1 ∧ 3 * (p.t - 1) ≤ p.j - 3
    omega
  have htq : 0 < q.t := by
    change 0 < p.t - 1
    omega
  obtain ⟨C, hC, hrecover⟩ := exists_chart ((separant^[j]) f) q (derivative_box f hj) hq htq
  have hbox := chart_le p hp htp hpb
  have widen {P : GeoJets} (hP : GeoFits P (chart (K1_13.taylorLength + 4) q)) :
      GeoFits P (chart (Low48Price.taylorLength + 4) p) :=
    ⟨hP.1.trans hbox.1, hP.2.1.trans hbox.2.1, hP.2.2.trans hbox.2.2⟩
  exact ⟨C, ⟨widen hC.1, fun i => widen (hC.2 i)⟩, hrecover⟩
private theorem box_chamber (f : Row 4) : InBox (shape f) (shape f).chamber :=
  ⟨le_max_left _ _, le_rfl, le_rfl⟩
private theorem derivative_proper {f : Row 4} (hf : Low48Price.SmallFactor f) (j : ℕ)
    (hj : 0 < j) (hg : (separant^[j]) f ≠ 0) : ¬ f ∣ (separant^[j]) f := by
  rintro ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    intro hz
    exact hg (by rw [hq, hz, mul_zero])
  have hd := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.1.ne_zero hq0
  have h := derivative_degree f j
  have ht : 0 < f.degreeOf 3 := hf.2.1
  change ((separant^[j]) f).degreeOf 3 ≤ f.degreeOf 3 - j at h
  rw [hq, hd] at h
  omega
private theorem one_piece {w Γ s} (hm : Low48Price.Messages w Γ s) (f : Row 4) (hf : Low48Price.SmallFactor f) (j : ℕ)
    (hj : 0 < j) (helig : FatEligible (shape f)) (ht : 1 < (shape f).t)
    (hmarks : ∀ γ ∈ Γ, atJet f (extend (s γ)) = 0 ∧
      atJet ((separant^[j]) f) (extend (s γ)) = 0 ∧
      RegularAt ((separant^[j]) f) (extend (s γ))) :
    let p := (shape f).chamber
    let h := chart (Low48Price.taylorLength + 4) p
    Γ.card ≤ 4 * (mixed32 p p h h / 32) := by
  classical
  dsimp only
  by_cases hΓ : Γ.Nonempty
  · obtain ⟨γ, hγ⟩ := hΓ
    let g := (separant^[j]) f
    let p := (shape f).chamber
    let h := chart (Low48Price.taylorLength + 4) p
    let d := mixed32 p p h h / 32
    have hg0 : g ≠ 0 := by
      intro hz
      exact (hmarks γ hγ).2.2 (by simp [show (separant^[j]) f = 0 from hz, atJet])
    have hpf := box_chamber f
    have hpg : InBox (shape g) p := by
      have hb := derivative_in_box f j
      exact ⟨hb.1.trans hpf.1, hb.2.1.trans hpf.2.1, hb.2.2.trans hpf.2.2⟩
    have hp := shape_chamber f
    obtain ⟨C, hC, hrecover⟩ := exists_derivative_chart f helig ht hj
    have hdegree : Low48Price.physicalDegree ≤ 133671 := by decide
    have hbound : SliceBound (toGeneric f) (toGeneric g) C d := by
      intro a b points hpts
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 32)).mpr (by
        rw [Nat.mul_comm]
        exact sparse_bound p h hp (chart_chamber _ _) _ _ _ _
          (toGeneric_fits hpf) (toGeneric_fits hpg) (C.pullback_fits hC a)
          (C.pullback_fits hC b) points (fun y hy => (hpts y hy).1))
    obtain ⟨B, hcover, hsurfaces, hpos, hsum⟩ :=
      surface_sections (toGeneric f) (toGeneric g)
        (fun hz => hf.1.ne_zero (toGeneric_injective (hz.trans (map_zero _).symm)))
        (fun hz => hg0 (toGeneric_injective (hz.trans (map_zero _).symm)))
        (proper_generic f g hf.1 (derivative_proper hf j hj hg0))
        C d hbound Γ s hm.distinct (fun a ha => by
          obtain ⟨hf', hg', hr⟩ := hmarks a ha
          refine ⟨(hm.degree a ha).trans hdegree, ?_, ?_, hrecover _ hg' hr⟩
          · rw [evalGeneric_toGeneric, hf', map_zero]
          · rw [evalGeneric_toGeneric, hg', map_zero])
    exact (Finset.card_le_card hcover).trans
      ((Low48FatPad.pieces_surface_capacity B hm hsurfaces hpos).trans (Nat.mul_le_mul_left 4 hsum))
  · simp [Finset.not_nonempty_iff_eq_empty.mp hΓ]
theorem proof : Low48FatCount.c1 := by
  classical
  intro w Γ s hm f hf helig hmarks
  let t := (shape f).t
  have hcover (γ : K) (hγ : γ ∈ Γ) :
      ∃ j, 0 < j ∧ j < t ∧
        atJet ((separant^[j]) f) (extend (s γ)) = 0 ∧
        RegularAt ((separant^[j]) f) (extend (s γ)) :=
    regular_derivative f _ hf.2.2.1.2.2 (hmarks γ hγ).1 (Classical.not_not.mp (hmarks γ hγ).2)
  by_cases ht : 1 < t
  · let p := (shape f).chamber
    let h := chart (Low48Price.taylorLength + 4) p
    let m := mixed32 p p h h
    let part (j : Fin t) := Γ.filter fun γ =>
      0 < j.val ∧ atJet ((separant^[j.val]) f) (extend (s γ)) = 0 ∧
        RegularAt ((separant^[j.val]) f) (extend (s γ))
    have hall : Γ ⊆ Finset.univ.biUnion part := by
      intro γ hγ
      obtain ⟨j, hj, hjt, hz, hr⟩ := hcover γ hγ
      exact Finset.mem_biUnion.mpr ⟨⟨j, hjt⟩, Finset.mem_univ _, Finset.mem_filter.mpr
        ⟨hγ, hj, hz, hr⟩⟩
    have hpart (j : Fin t) : (part j).card ≤ 4 * (m / 32) := by
      by_cases hj : 0 < j.val
      · have hsub : part j ⊆ Γ := Finset.filter_subset _ _
        apply one_piece (Low48Price.Messages.mono hm hsub) f hf j.val hj helig ht
        intro γ hγ
        have hp := Finset.mem_filter.mp hγ
        exact ⟨(hmarks γ hp.1).1.1, hp.2.2⟩
      · simp [part, hj]
    have hprice : 4 * t * (m / 32) ≤ ceilDiv (4 * t * m) 32 := by
      unfold ceilDiv
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 32)).mpr
      rw [Nat.mul_assoc]
      exact (Nat.mul_le_mul_left (4 * t) (Nat.div_mul_le_self m 32)).trans (by omega)
    have hchart : Low48FatCount.fatChart (shape f) = h := by
      unfold Low48FatCount.fatChart
      exact ite_eq_right (by omega : t ≠ 1)
    unfold Low48FatCount.singularPrice
    rw [ite_eq_left ht, hchart]
    change Γ.card ≤ ceilDiv (4 * t * m) 32 + t * (shape f).b ^ 2 + 1
    calc
      Γ.card ≤ (Finset.univ.biUnion part).card := Finset.card_le_card hall
      _ ≤ ∑ j : Fin t, (part j).card := Finset.card_biUnion_le
      _ ≤ ∑ _ : Fin t, 4 * (m / 32) := Finset.sum_le_sum fun j _ => hpart j
      _ = 4 * t * (m / 32) := by simp [Nat.mul_comm, Nat.mul_assoc]
      _ ≤ ceilDiv (4 * t * m) 32 := hprice
      _ ≤ _ := by omega
  · have hempty : Γ = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨γ, hγ⟩
      obtain ⟨j, hj, hjt, _, _⟩ := hcover γ hγ
      omega
    simp [hempty]
end
end Low48FatCount_1
end
section
namespace Low48FatCount_2
noncomputable section
open Polynomial
open K1_13 (Geom Row Shape InBox shape mixed32 atJet)
open K1_13_6 (GeoJets toGeneric separant cycleLength intersectionIdeal Invariant)
open K1_13_7 (LowerCaps genericRow)
open K1_13_7_2 (evalTrajectory LiftedSurface lowerFlow liftLower)
open Low48Price (taylorLength physicalDegree)
open Low48FatCount (fatChart divisorBox)
structure ReducedCut (f : Row 4) (D q : Row 3) : Prop where
  ne_zero : q ≠ 0
  divides : q ∣ D
  caps : LowerCaps q divisorBox.b divisorBox.j
  reduced : Squarefree (genericRow q)
  proper : IsRelPrime (toGeneric f) (toGeneric (liftLower q))
  roots : ∀ S : Geom[X], atJet D S = 0 → atJet q S = 0
  flow_box : InBox (shape (lowerFlow q)) ⟨divisorBox.b, divisorBox.j + 1, 1⟩
  simple : ∀ surface, (h : LiftedSurface f q surface) → surface.height = 2 ∧
    cycleLength (intersectionIdeal f (liftLower q)) surface h.minimal.isPrime = 1
  invariant : ∀ surface, LiftedSurface f q surface → toGeneric (lowerFlow q) ∈ surface → Invariant f surface
def cutBox (x : Shape) : Shape :=
  let h := fatChart x
  ⟨max (max h.b divisorBox.b) (max h.j (divisorBox.j + 1)),
    max h.j (divisorBox.j + 1), max 1 h.t⟩
def curveMass32 (x : Shape) : ℕ :=
  mixed32 x.chamber divisorBox (cutBox x) (fatChart x)
def componentMass32 (x : Shape) : ℕ :=
  mixed32 x.chamber divisorBox (cutBox x) x.chamber
structure FatTaylor (f : Row 4) where
  denom : Row 4
  numer : Fin taylorLength → Row 4
  test : Row 4
  denom_box : InBox (shape denom) (fatChart (shape f))
  numer_box : ∀ i, InBox (shape (numer i)) (fatChart (shape f))
  test_box : InBox (shape test) (fatChart (shape f))
  test_iff : ∀ (surface : Ideal GeoJets), surface.IsPrime → toGeneric f ∈ surface →
    toGeneric (separant f) ∉ surface →
    (toGeneric test ∈ surface ↔ toGeneric (Low48FatPad.membershipTest f) ∈ surface)
  recovers : ∀ (L : Type) [Field L] [Algebra Geom L] (S : L[X]),
    S.natDegree ≤ physicalDegree → evalTrajectory f S = 0 →
    evalTrajectory (separant f) S ≠ 0 →
    evalTrajectory denom S ≠ 0 ∧ evalTrajectory test S = 0 ∧
      ∀ i, evalTrajectory (numer i) S = evalTrajectory denom S * C (S.coeff i.val)
abbrev CoeffRing := MvPolynomial (Fin taylorLength) Geom
def universalPolynomial : CoeffRing[X] :=
  ∑ i : Fin taylorLength, C (MvPolynomial.X i) * Polynomial.X ^ i.val
def universalEval (f : Row 4) : CoeffRing[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom (MvPolynomial.C : Geom →+* CoeffRing))
    (fun i => hasseDeriv i.val universalPolynomial) f
def coefficientPointIdeal (S : Geom[X]) : Ideal CoeffRing :=
  RingHom.ker (MvPolynomial.eval (fun i : Fin taylorLength => S.coeff i.val))
structure ActualFamily (f : Row 4) (P : Ideal CoeffRing) : Prop where
  prime : P.IsPrime
  dimension : 2 ≤ (MvPolynomial.affineHilbertPolynomial P).natDegree
  solves : ∀ i, (universalEval f).coeff i ∈ P
  regular : ∃ i, (universalEval (separant f)).coeff i ∉ P
def IntegratedMark (f : Row 4) (S : Geom[X]) : Prop :=
  ∃ P, ActualFamily f P ∧ P ≤ coefficientPointIdeal S
end
end Low48FatCount_2
end
section
namespace Low48FatCount_2_1
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_6
open K1 (K)
open K1_13_7 (LowerCaps RegularAt)
open K1_13_7_1 (Chamber GeoFits chart_chamber toGeneric_fits weight_const_mul_le
  evalGeneric_toGeneric)
open K1_13_7_2 (liftLower lowerFlow evalTrajectory_geom)
open Low48FatCount (fatChart divisorBox divisorBox_eq)
open Low48FatCount_2 (ReducedCut FatTaylor cutBox)
theorem lower_fits {q : Row 3} (hq : LowerCaps q divisorBox.b divisorBox.j) :
    GeoFits (toGeneric (liftLower q)) divisorBox := by
  apply toGeneric_fits
  refine ⟨(totalDegree_rename_le _ _).trans hq.1, ?_, ?_⟩
  · change indexDegree (MvPolynomial.rename Fin.castSucc q) ≤ divisorBox.j
    rw [K1_13_1.indexDegree_eq, weightedTotalDegree_rename_of_injective (Fin.castSucc_injective 3)]
    change q.weightedTotalDegree Fin.val ≤ divisorBox.j
    rw [← K1_13_1.indexDegree_eq]
    exact hq.2
  · change (liftLower q).degreeOf 3 ≤ 0
    rw [K1_13_7_2_1.degreeOf_liftLower]
theorem chart_chamber_pos (f : Row 4) :
    Chamber (fatChart (shape f)) ∧ 0 < (fatChart (shape f)).t := by
  let p := (shape f).chamber
  unfold fatChart
  split
  · let i := 3 + Low48Price.taylorLength * (p.j - 2)
    have hi : 3 ≤ i := Nat.le_add_right _ _
    change Chamber ⟨max (1 + Low48Price.taylorLength * (p.b - 1)) i, i,
      min (Low48Price.taylorLength + 1) (i / 3)⟩ ∧ 0 < min (Low48Price.taylorLength + 1) (i / 3)
    refine ⟨⟨le_max_right _ _, ?_⟩, ?_⟩
    · exact (Nat.mul_le_mul_left 3 (min_le_right _ _)).trans (Nat.mul_div_le _ _)
    · exact lt_min (by omega) (by omega)
  · let L := Low48Price.taylorLength + 4
    let i := 2 * L * (p.j - 3) + L + 3
    have hi : 3 ≤ i := Nat.le_add_left _ _
    refine ⟨chart_chamber _ _, ?_⟩
    change 0 < min (2 * L * (p.t - 1) + L + 1) (i / 3)
    exact lt_min (by omega) (by omega)
theorem cut_chamber {x : Shape} (hh : Chamber (fatChart x)) : Chamber (cutBox x) := by
  refine ⟨le_max_right _ _, ?_⟩
  change 3 * max 1 (fatChart x).t ≤ max (fatChart x).j (divisorBox.j + 1)
  rw [mul_max]
  have hflow : 3 ≤ divisorBox.j + 1 := by
    rw [divisorBox_eq]
    decide
  exact max_le (le_max_of_le_right hflow) (hh.2.trans (le_max_left _ _))
theorem test_fits_cut {f : Row 4} (T : FatTaylor f) :
    GeoFits (toGeneric T.test) (cutBox (shape f)) :=
  toGeneric_fits ⟨T.test_box.1.trans ((le_max_left _ _).trans (le_max_left _ _)),
    T.test_box.2.1.trans (le_max_left _ _), T.test_box.2.2.trans (le_max_right _ _)⟩
theorem flow_fits_cut {f : Row 4} {D q : Row 3} (hq : ReducedCut f D q) :
    GeoFits (toGeneric (lowerFlow q)) (cutBox (shape f)) :=
  toGeneric_fits ⟨hq.flow_box.1.trans ((le_max_right _ _).trans (le_max_left _ _)),
    hq.flow_box.2.1.trans (le_max_right _ _), hq.flow_box.2.2.trans (le_max_left _ _)⟩
private abbrev constant : K →+* GeoField :=
  genericCoeffs.comp ((Polynomial.C : Geom →+* Geom[X]).comp embed)
def valueSection {f : Row 4} (T : FatTaylor f) (x a : K) : GeoJets :=
  (∑ i : Fin Low48Price.taylorLength, MvPolynomial.C (constant (x ^ i.val)) * toGeneric (T.numer i)) -
    MvPolynomial.C (constant a) * toGeneric T.denom
theorem value_fits {f : Row 4} (T : FatTaylor f) (x a : K) :
    GeoFits (valueSection T x a) (fatChart (shape f)) := by
  classical
  let h := fatChart (shape f)
  have hw (w : Fin 4 → ℕ) (d : ℕ)
      (hD : (toGeneric T.denom).weightedTotalDegree w ≤ d)
      (hN : ∀ i, (toGeneric (T.numer i)).weightedTotalDegree w ≤ d) :
      (valueSection T x a).weightedTotalDegree w ≤ d := by
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    unfold valueSection
    apply Submodule.sub_mem
    · apply Submodule.sum_mem
      intro i _
      exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((weight_const_mul_le _ _ _).trans (hN i))
    · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((weight_const_mul_le _ _ _).trans hD)
  have hD : GeoFits (toGeneric T.denom) h := toGeneric_fits T.denom_box
  have hN (i : Fin Low48Price.taylorLength) : GeoFits (toGeneric (T.numer i)) h :=
    toGeneric_fits (T.numer_box i)
  refine ⟨?_, hw Fin.val h.j hD.2.1 (fun i => (hN i).2.1), ?_⟩
  · simpa only [weightedTotalDegree_one] using hw 1 h.b
      (by simpa only [weightedTotalDegree_one] using hD.1)
      (fun i => by simpa only [weightedTotalDegree_one] using (hN i).1)
  · simpa only [weightedTotalDegree_piSingle] using hw (Pi.single (3 : Fin 4) 1) h.t
      (by simpa only [weightedTotalDegree_piSingle] using hD.2.2)
      (fun i => by simpa only [weightedTotalDegree_piSingle] using (hN i).2.2)
private theorem genericCoeffs_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective Geom[X] GenericField)
theorem chart_on_mark {S : Geom[X]} {f : Row 4} (T : FatTaylor f)
    (hd : S.natDegree ≤ Low48Price.physicalDegree) (hf : atJet f S = 0) (hr : RegularAt f S) :
    atJet T.denom S ≠ 0 ∧ atJet T.test S = 0 ∧
      ∀ i, atJet (T.numer i) S = atJet T.denom S * Polynomial.C (S.coeff i.val) := by
  have h := T.recovers Geom S hd ((evalTrajectory_geom _ _).trans hf)
    (fun hz => hr ((evalTrajectory_geom _ _).symm.trans hz))
  simpa only [evalTrajectory_geom] using h
theorem value_at_mark {f : Row 4} (T : FatTaylor f) {S : K[X]}
    (hd : S.natDegree ≤ Low48Price.physicalDegree) (hf : atJet f (extend S) = 0)
    (hr : RegularAt f (extend S)) (x a : K) :
    evalGeneric (extend S) (valueSection T x a) = 0 ↔ S.eval x = a := by
  have h := chart_on_mark T (Polynomial.natDegree_map_le.trans hd) hf hr
  let d := evalGeneric (extend S) (toGeneric T.denom)
  have hd0 : d ≠ 0 := by
    change evalGeneric (extend S) (toGeneric T.denom) ≠ 0
    rw [evalGeneric_toGeneric]
    exact (map_ne_zero_iff _ genericCoeffs_injective).mpr h.1
  have hn (i : Fin Low48Price.taylorLength) :
      evalGeneric (extend S) (toGeneric (T.numer i)) = d * constant (S.coeff i.val) := by
    rw [evalGeneric_toGeneric, h.2.2 i, map_mul]
    simp only [d, evalGeneric_toGeneric, constant, RingHom.comp_apply, Polynomial.coeff_map]
  have hsum : (∑ i : Fin Low48Price.taylorLength, constant (S.coeff i.val * x ^ i.val)) =
      constant (S.eval x) := by
    rw [Polynomial.eval_eq_sum_range' (n := Low48Price.taylorLength)
      (Nat.lt_succ_of_le hd), ← Fin.sum_univ_eq_sum_range]
    exact (map_sum _ _ _).symm
  have he : evalGeneric (extend S) (valueSection T x a) =
      d * constant (S.eval x - a) := by
    have hconst (c : K) : evalGeneric (extend S) (MvPolynomial.C (constant c)) = constant c :=
      MvPolynomial.eval_C _
    unfold valueSection
    simp only [map_sub, map_sum, map_mul, hconst, hn]
    change (∑ i : Fin Low48Price.taylorLength, constant (x ^ i.val) * (d * constant (S.coeff i.val))) -
      constant a * d = _
    rw [mul_sub, ← hsum, Finset.mul_sum, mul_comm (constant a) d]
    apply congrArg (fun v : GeoField => v - d * constant a)
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul]
    ac_rfl
  rw [he, mul_eq_zero, or_iff_right hd0, map_eq_zero_iff _ (by
    exact genericCoeffs_injective.comp (Polynomial.C_injective.comp embed.injective)), sub_eq_zero]
end
end Low48FatCount_2_1
end
section
namespace Low48FatCount_2
noncomputable section
open K1_13 K1_13_6 K1_13_7 K1_13_7_2 K1_13_7_2_1
open K1_13_1 (indexDegree_eq)
open Low48FatCount (divisorBox divisorBox_eq)
open MvPolynomial UniqueFactorizationMonoid
open scoped Polynomial
open private geometric_injective liftLower_ne_zero from ProximityPrize.SubmissionLower.Fast070
open private local_length_one tangent_invariant from ProximityPrize.SubmissionLower.Fast070
open private partialFlow_weight from ProximityPrize.SubmissionLower.Fast066
open private local_generators from ProximityPrize.SubmissionLower.PortLow7
private theorem proper_lift {f : Row 4} (hf : Low48Price.SmallFactor f) {q : Row 3} (hq : q ≠ 0) :
    IsRelPrime (toGeneric f) (toGeneric (liftLower q)) := by
  apply (isRelPrime_iff_no_prime_factors (fun hz => hf.1.ne_zero
    (geometric_injective 4 (by simpa [toGeneric] using hz)))).mpr
  intro r hrf hrq hr
  obtain ⟨a, ha, he⟩ := comap_span_prime hr hf.1.ne_zero hrf
  have had {x : Row 4} (h : r ∣ toGeneric x) : a ∣ x := by
    apply Ideal.mem_span_singleton.mp
    rw [← he]
    exact Ideal.mem_span_singleton.mpr h
  have haf : a ∣ f := had hrf
  have hfa : f ∣ a := (ha.irreducible.associated_of_dvd hf.1 haf).dvd'
  obtain ⟨R, hR⟩ := hfa.trans (had hrq)
  have hRn : R ≠ 0 := fun hz => liftLower_ne_zero hq (by simp [hR, hz])
  have hdeg := degreeOf_liftLower q
  rw [hR, ← weightedTotalDegree_piSingle, weightedTotalDegree_mul _ _ _ hf.1.ne_zero hRn,
    weightedTotalDegree_piSingle, weightedTotalDegree_piSingle] at hdeg
  have := hf.2.1
  change 0 < f.degreeOf 3 at this
  omega
private theorem reduced_divisor {b j : ℕ} (D : Row 3) (hD : D ≠ 0) (hcap : LowerCaps D b j) :
    ∃ q : Row 3, q ≠ 0 ∧ q ∣ D ∧ LowerCaps q b j ∧ Squarefree q ∧
      (∀ S : Polynomial Geom, atJet D S = 0 → atJet q S = 0) := by
  let : StrongNormalizationMonoid (Row 3) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let q := radical D
  have hd : q ∣ D := radical_dvd_self (a := D)
  have hq : q ≠ 0 := fun hz => hD (zero_dvd_iff.mp (hz ▸ hd))
  refine ⟨q, hq, hd, ?_, squarefree_radical, ?_⟩
  · obtain ⟨R, hR⟩ := hd
    have hRn : R ≠ 0 := fun hz => hD (by simp [hR, hz])
    refine ⟨?_, ?_⟩
    · have h := hcap.1
      rw [hR, totalDegree_mul_of_isDomain hq hRn] at h
      omega
    · have h := hcap.2
      rw [hR, indexDegree_eq, weightedTotalDegree_mul _ _ _ hq hRn, ← indexDegree_eq,
        ← indexDegree_eq] at h
      omega
  · obtain ⟨m, hm⟩ := exists_dvd_radical_self_pow hD
    intro S hS
    let ev := MvPolynomial.eval (jet S : Fin 3 → Polynomial Geom)
    have hh := map_dvd ev hm
    rw [map_pow, show ev D = 0 from hS] at hh
    exact eq_zero_of_pow_eq_zero (zero_dvd_iff.mp hh)
private theorem flow_box {q : Row 3} {b j : ℕ} (hb : 1 ≤ b) (hj : 2 ≤ j)
    (hq : LowerCaps q b j) :
    InBox (shape (lowerFlow q)) ⟨b, j + 1, 1⟩ := by
  have lift_weight (w : Fin 4 → ℕ) :
      (liftLower q).weightedTotalDegree w = q.weightedTotalDegree (w ∘ Fin.castSucc) :=
    weightedTotalDegree_rename_of_injective (Fin.castSucc_injective 3)
  refine ⟨?_, ?_, ?_⟩
  · have h := partialFlow_weight 1 b 0 (by simp) (fun _ => hb) (liftLower q) (by
      simpa only [lift_weight, show (1 : Fin 4 → ℕ) ∘ Fin.castSucc = 1 from rfl,
        weightedTotalDegree_one] using hq.1)
    simpa only [shape, lowerFlow, weightedTotalDegree_one, Nat.add_zero] using h
  · have h := partialFlow_weight Fin.val j 1 (fun i => by simp [Fin.val_succ])
      (fun i => (Nat.le_of_lt_succ i.isLt).trans hj) (liftLower q) (by
        simpa only [lift_weight, show (Fin.val : Fin 4 → ℕ) ∘ Fin.castSucc = Fin.val from rfl,
          ← indexDegree_eq] using hq.2)
    simpa only [shape, lowerFlow, ← indexDegree_eq] using h
  · let w : Fin 4 → ℕ := Pi.single 3 1
    have h := partialFlow_weight w 0 1 (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide) (liftLower q) (by
        simp [w, weightedTotalDegree_piSingle, degreeOf_liftLower])
    simpa [shape, lowerFlow, w, weightedTotalDegree_piSingle] using h
theorem reduce (f : Row 4) (hf : Low48Price.SmallFactor f)
    (D : Row 3) (hD : D ≠ 0) (hcap : LowerCaps D divisorBox.b divisorBox.j) :
    ∃ q : Row 3, ReducedCut f D q := by
  obtain ⟨q, hq, hdvd, hqcap, hsq, hroots⟩ := reduced_divisor D hD hcap
  have hgeom := K1_13_7_2_1_1.proof q hsq (hqcap.1.trans_lt (by rw [divisorBox_eq]; decide))
  have hproper := proper_lift hf hq
  have hlocal (surface : Ideal GeoJets) (h : LiftedSurface f q surface) :
      LocalGenerators f q surface h.minimal.isPrime := local_generators f q hgeom surface h
  have hflow := flow_box (by rw [divisorBox_eq]; decide) (by rw [divisorBox_eq]; decide) hqcap
  exact ⟨q, hq, hdvd, hqcap, hgeom, hproper, hroots, hflow,
    fun surface h => ⟨lifted_height hf.1.ne_zero hproper h,
      local_length_one h.minimal.isPrime (hlocal surface h)⟩,
    fun surface h => tangent_invariant h (hlocal surface h)⟩
end
end Low48FatCount_2
end
section
namespace Low48FatCount_2
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_6
open K1_13_7_2_2 (stride raw topLinear denominator numerator hasseNumerator)
open K1_13_7_1 (weight_const_mul_le top_le_index shape_chamber Chamber)
open K1_13_1 (indexDegree_eq)
open private raw_false raw_true_compare from ProximityPrize.SubmissionLower.Fast070
open private raw_bound sep_pow_bound from ProximityPrize.SubmissionLower.Fast070
open private specializes topLinear_regular from ProximityPrize.SubmissionLower.Fast070
local notation "W" => MvPolynomial.weightedTotalDegree
private theorem numerator_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g : Row 4} {B : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (i : Fin Low48Price.taylorLength) :
    W w (numerator g i) ≤ w 0 + Low48Price.taylorLength * (stride (topLinear g) * (B - w 3) + Δ) := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sum_mem
  intro j _
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
  apply (weight_const_mul_le _ _ _).trans
  unfold hasseNumerator
  apply (weight_const_mul_le _ _ _).trans
  apply (weightedTotalDegree_mul_le _ _ _).trans
  let k := stride (topLinear g)
  calc
    _ ≤ k * (Low48Price.taylorLength - j.val) * (B - w 3) +
        (w 0 + j.val * (k * (B - w 3) + Δ)) :=
      Nat.add_le_add (sep_pow_bound g w _ hg) (raw_bound _ w Δ hshift hB hg _)
    _ = w 0 + (Low48Price.taylorLength - j.val + j.val) * (k * (B - w 3)) + j.val * Δ := by ring
    _ ≤ _ := by
      rw [Nat.sub_add_cancel j.isLt.le, Nat.mul_add, ← Nat.add_assoc]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right Δ j.isLt.le) _
private theorem fatChart_support {g Q : Row 4} (hg : 0 < (shape g).t)
    (h : ∀ (w : Fin 4 → ℕ) (Δ B : ℕ), (∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) →
      w 3 ≤ B → W w g ≤ B →
      W w Q ≤ w 0 + Low48Price.taylorLength * (stride (topLinear g) * (B - w 3) + Δ)) :
    InBox (shape Q) (Low48FatCount.fatChart (shape g)) := by
  let p := (shape g).chamber
  let k := stride (topLinear g)
  have hch : Chamber p := shape_chamber g
  have hj : 3 ≤ p.j := by
    have htop : 3 * p.t ≤ p.j := hch.2
    have hpos : 0 < p.t := hg
    omega
  have hb : 1 ≤ p.b := by have hb : p.j ≤ p.b := hch.1; omega
  let w : Fin 4 → ℕ := Pi.single 3 1
  have hbQ : Q.totalDegree ≤ 1 + Low48Price.taylorLength * (k * (p.b - 1)) := by
    have hbg : W (1 : Fin 4 → ℕ) g ≤ p.b := by
      rw [weightedTotalDegree_one]
      change g.totalDegree ≤ max g.totalDegree (indexDegree g)
      exact le_max_left _ _
    have h' := h 1 0 p.b (fun _ => by simp) hb hbg
    simpa only [weightedTotalDegree_one, Pi.one_apply, add_zero] using h'
  have hjQ : W Fin.val Q ≤ Low48Price.taylorLength * (k * (p.j - 3) + 1) := by
    have h' := h Fin.val 1 p.j (fun _ => by rfl) hj (by rw [← indexDegree_eq]; rfl)
    change W Fin.val Q ≤ 0 + Low48Price.taylorLength * (k * (p.j - 3) + 1) at h'
    rwa [zero_add] at h'
  have htQ : Q.degreeOf 3 ≤ Low48Price.taylorLength * (k * (p.t - 1) + 1) := by
    have h' := h w 1 p.t (fun i => by fin_cases i <;> decide)
      (by change 1 ≤ p.t; exact hg)
      (by simp only [w, weightedTotalDegree_piSingle]; exact le_rfl)
    simpa only [w, weightedTotalDegree_piSingle, show w 0 = 0 by decide,
      show w 3 = 1 by decide, zero_add] using h'
  unfold Low48FatCount.fatChart
  change InBox (shape Q) (if (shape g).t = 1 then Low48Price.linearChart p else chart (Low48Price.taylorLength + 4) p)
  have hbox (b j t : ℕ) (hB : Q.totalDegree ≤ b) (hJ : W Fin.val Q ≤ j)
      (hT : Q.degreeOf 3 ≤ t) : InBox (shape Q) ⟨max b j, j, min t (j / 3)⟩ := by
    refine ⟨hB.trans (le_max_left _ _), ?_, le_min hT ?_⟩
    · change indexDegree Q ≤ j
      rwa [indexDegree_eq]
    · change Q.degreeOf 3 ≤ j / 3
      have htj := (top_le_index Q).trans hJ
      omega
  split_ifs with hlin
  · have hk : k = 1 := by simp [k, topLinear, hlin, stride]
    have ht : p.t = 1 := hlin
    apply hbox
    · simpa only [hk, one_mul] using hbQ
    · rw [hk, one_mul, show p.j - 3 + 1 = p.j - 2 by omega] at hjQ
      exact hjQ.trans (Nat.le_add_left _ _)
    · simp only [hk, ht, Nat.sub_self, mul_zero, zero_add, mul_one] at htQ
      exact htQ.trans (Nat.le_succ _)
  · have hk : k = 2 := by simp [k, topLinear, hlin, stride]
    have hw : Low48Price.taylorLength ≤ Low48Price.taylorLength + 4 := Nat.le_add_right _ _
    have hscale (n : ℕ) : Low48Price.taylorLength * (2 * n) ≤ 2 * (Low48Price.taylorLength + 4) * n := by
      rw [← Nat.mul_assoc, Nat.mul_comm Low48Price.taylorLength 2]
      exact Nat.mul_le_mul_right n (Nat.mul_le_mul_left 2 hw)
    apply hbox
    · rw [hk] at hbQ
      exact hbQ.trans (Nat.add_le_add_left (hscale _) 1)
    · simp only [hk, Nat.mul_add, mul_one] at hjQ
      exact hjQ.trans ((Nat.add_le_add (hscale _) hw).trans (Nat.le_add_right _ _))
    · simp only [hk, Nat.mul_add, mul_one] at htQ
      exact htQ.trans ((Nat.add_le_add (hscale _) hw).trans (Nat.le_add_right _ _))
theorem denominator_box {g : Row 4} (hg : 0 < (shape g).t) :
    InBox (shape (denominator g Low48Price.taylorLength)) (Low48FatCount.fatChart (shape g)) := by
  apply fatChart_support hg
  intro w Δ B _ _ hB
  have hp := sep_pow_bound g w (stride (topLinear g) * Low48Price.taylorLength) hB
  refine hp.trans ?_
  calc
    _ = Low48Price.taylorLength * (stride (topLinear g) * (B - w 3)) := by ring
    _ ≤ _ := Nat.le_add_left_of_le (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
theorem numerator_box {g : Row 4} (hg : 0 < (shape g).t) (i : Fin Low48Price.taylorLength) :
    InBox (shape (numerator g i)) (Low48FatCount.fatChart (shape g)) :=
  fatChart_support hg (fun w Δ _ hs h3 hB => numerator_bound w Δ hs h3 hB i)
theorem test_box {g : Row 4} (hg : 0 < (shape g).t) :
    InBox (shape (raw (topLinear g) g Low48Price.taylorLength)) (Low48FatCount.fatChart (shape g)) :=
  fatChart_support hg (fun w Δ _ hs h3 hB => raw_bound _ w Δ hs h3 hB _)
private theorem test_mem_iff (linear : Bool) (g : Row 4)
    (hl : linear = true → separant (separant g) = 0)
    (surface : Ideal GeoJets) (hp : surface.IsPrime) (hr : toGeneric (separant g) ∉ surface) :
    toGeneric (raw linear g Low48Price.taylorLength) ∈ surface ↔ toGeneric (Low48FatPad.membershipTest g) ∈ surface := by
  cases linear with
  | false => rw [raw_false, Low48FatPad.membershipTest]
  | true =>
    have hn : toGeneric (separant g) ^ Low48Price.taylorLength ∉ surface :=
      fun h => hr (hp.mem_of_pow_mem _ h)
    unfold Low48FatPad.membershipTest
    rw [raw_true_compare g (hl rfl)]
    simp only [toGeneric, map_mul, map_pow] at hn ⊢
    exact ⟨fun h => surface.mul_mem_left _ h, fun h => (hp.mem_or_mem h).resolve_left hn⟩
theorem fat_taylor (g : Row 4) (hg : 0 < (shape g).t) : Nonempty (FatTaylor g) := by
  have hp : Low48Price.taylorLength < K1.p := by decide
  refine ⟨{
    denom := denominator g Low48Price.taylorLength
    numer := numerator g
    test := raw (topLinear g) g Low48Price.taylorLength
    denom_box := denominator_box hg
    numer_box := numerator_box hg
    test_box := test_box hg
    test_iff := fun surface hprime _ hr => test_mem_iff _ _ (topLinear_regular g) surface hprime hr
    recovers := ?_ }⟩
  intro L _ _ S hd hs hr
  exact specializes g S (n := Low48Price.taylorLength) (Nat.lt_succ_of_le hd) hp.le hs hr
end
end Low48FatCount_2
end
section
namespace Low48FatCount_2
noncomputable section
open Polynomial
open P3 (K I node)
open Low48Price (Messages SmallFactor physicalDegree)
open Low48FatCount (fatChart divisorBox)
open K1_13 (Geom Row Shape extend shape OnFactor FatEligible ceilDiv)
open K1_13_6 (GeoJets toGeneric separant Invariant markIdeal Pieces)
open K1_13_7 (LowerCaps RegularAt)
open K1_13_7_2 (ProperMark ThreefoldSections ThreefoldPieces lowerFlow)
open private lifted_at_mark from ProximityPrize.SubmissionLower.Fast066
def c1 : Prop :=
  ∀ (Γ : Finset K) (s : K → K[X]) (f : Row 4) (D q : Row 3),
    0 < (shape f).t → ReducedCut f D q → ∀ T : FatTaylor f,
    Set.InjOn s (Γ : Set K) → (∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree) →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ)) ∧ RegularAt f (extend (s γ))) →
    ∃ C : Pieces Γ, C.curves s ∧
      (∀ γ ∈ Γ, ProperMark f q T.test (extend (s γ)) → γ ∈ C.union) ∧
      32 * C.total ≤ curveMass32 (shape f) ∧
      32 * C.n ≤ componentMass32 (shape f)
def c2 : Prop :=
  ∀ f : Row 4, SmallFactor f → ∀ surface : Ideal GeoJets, surface.IsPrime → surface.height = 2 →
    toGeneric f ∈ surface → toGeneric (separant f) ∉ surface →
    Invariant f surface → toGeneric (Low48FatPad.membershipTest f) ∈ surface →
    ∀ S : Geom[X], surface ≤ markIdeal S → RegularAt f S → S.natDegree ≤ physicalDegree →
      IntegratedMark f S
def c3 : Prop :=
  ∀ (Γ : Finset K) (s : K → K[X]) (f : Row 4),
    SmallFactor f → FatEligible (shape f) → FatTaylor f →
    Set.InjOn s (Γ : Set K) → (∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree) →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ)) ∧ RegularAt f (extend (s γ))) →
    ∃ C F : Pieces Γ, C.surfaces s ∧ ThreefoldPieces F s ∧
      (∀ i, 0 < C.degree i) ∧ (∀ i, 0 < F.degree i) ∧
      (∀ γ ∈ Γ, IntegratedMark f (extend (s γ)) → γ ∈ C.union ∪ F.union) ∧
      2 * C.total ≤ physicalDegree * (shape f).chamber.b * (fatChart (shape f)).b ∧
      F.total ≤ (shape f).chamber.b * (fatChart (shape f)).b ^ 2
theorem threefold_capacity {w Γ s d} (h : Messages w Γ s)
    (hs : ThreefoldSections Γ s d) (hd : 0 < d) : Γ.card ≤ 8 * d := by
  classical
  have hsection (i : I) (hi : ∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i) :
      (Γ.filter (fun γ => (s γ).eval (node i) = w i)).card ≤ 4 * d := by
    obtain ⟨C, hC, hc, hpos, hdeg⟩ := hs (node i) (w i) hi
    have hH := Low48Price.Messages.mono h (Finset.filter_subset (fun γ => (s γ).eval (node i) = w i) Γ)
    exact (Finset.card_le_card hC).trans ((Low48FatPad.pieces_surface_capacity C hH hc hpos).trans
      (Nat.mul_le_mul_left 4 hdeg))
  have := Low48FatPad.section_capacity h (4 * d) hsection
  omega
theorem threefold_pieces_capacity {w Γ s} (C : Pieces Γ) (h : Messages w Γ s)
    (hc : ThreefoldPieces C s) (hd : ∀ i, 0 < C.degree i) : C.union.card ≤ 8 * C.total := by
  classical
  calc
    _ ≤ ∑ i, (C.piece i).card := Finset.card_biUnion_le
    _ ≤ ∑ i, 8 * C.degree i := Finset.sum_le_sum fun i _ =>
      threefold_capacity (Low48Price.Messages.mono h (C.subset i)) (hc i) (hd i)
    _ = _ := by simp [Pieces.total, Finset.mul_sum]
private theorem proper_capacity {w Γ s} {x : Shape} (C : Pieces Γ) (h : Messages w Γ s)
    (hc : C.curves s) (hb : 32 * C.total ≤ curveMass32 x)
    (hn : 32 * C.n ≤ componentMass32 x) :
    C.union.card ≤ ceilDiv (82229 * curveMass32 x) (32 * 46489) +
      ceilDiv (componentMass32 x) 32 := by
  have hcap := Low48FatPad.pieces_curve_capacity C h hc
  unfold ceilDiv
  omega
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : Low48FatCount.c2 := by
  classical
  intro w Γ s hm f hf helig hon D hD hbox hDmark
  obtain ⟨q, hq⟩ := reduce f hf D hD hbox
  obtain ⟨T⟩ := fat_taylor f hf.2.1
  obtain ⟨A, hA, hcoverA, hcurve, hcomp⟩ :=
    h1 Γ s f D q hf.2.1 hq T hm.distinct hm.degree hon
  obtain ⟨C, F, hC, hF, hposC, hposF, hcoverI, hdegC, hdegF⟩ :=
    h3 Γ s f hf helig T hm.distinct hm.degree hon
  have hcover : Γ ⊆ A.union ∪ (C.union ∪ F.union) := by
    intro γ hγ
    let S := extend (s γ)
    have hfS := (hon γ hγ).1
    have hrS := (hon γ hγ).2
    have hdS : S.natDegree ≤ physicalDegree := Polynomial.natDegree_map_le.trans (hm.degree γ hγ)
    obtain ⟨surface, hZ, hle⟩ := lifted_at_mark hfS hrS (hq.roots S (hDmark γ hγ))
    by_cases hE : toGeneric T.test ∈ surface
    · by_cases hflow : toGeneric (lowerFlow q) ∈ surface
      · have hfZ : toGeneric f ∈ surface := hZ.minimal.le (Ideal.subset_span (by simp))
        have hmem : toGeneric (Low48FatPad.membershipTest f) ∈ surface :=
          (T.test_iff surface hZ.minimal.isPrime hfZ hZ.regular).mp hE
        have hI : IntegratedMark f S := h2 f hf surface hZ.minimal.isPrime (hq.simple surface hZ).1
          hfZ hZ.regular (hq.invariant surface hZ hflow) hmem S hle hrS hdS
        exact Finset.mem_union_right _ (hcoverI γ hγ hI)
      · exact Finset.mem_union_left _ (hcoverA γ hγ ⟨surface, hZ, hle, Or.inr hflow⟩)
    · exact Finset.mem_union_left _ (hcoverA γ hγ ⟨surface, hZ, hle, Or.inl hE⟩)
  have hAcard := proper_capacity A hm hA hcurve hcomp
  have hCcard := Low48FatPad.pieces_surface_capacity C hm hC hposC
  have hFcard := threefold_pieces_capacity F hm hF hposF
  have hsum := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hsumI := Finset.card_union_le C.union F.union
  let p := (shape f).chamber
  let h := fatChart (shape f)
  change Γ.card ≤ ceilDiv (82229 * curveMass32 (shape f)) (32 * 46489) +
    ceilDiv (componentMass32 (shape f)) 32 + 20 * p.b * h.b ^ 2 +
    5 * physicalDegree * p.b * h.b + 1
  have hreserveC : C.union.card ≤ 5 * physicalDegree * p.b * h.b := by
    have ht := Nat.mul_le_mul_left 2 hdegC
    simp only [← Nat.mul_assoc] at ht
    change 4 * C.total ≤ 2 * physicalDegree * p.b * h.b at ht
    refine hCcard.trans (ht.trans ?_)
    gcongr
    decide
  have hreserveF : F.union.card ≤ 20 * p.b * h.b ^ 2 := by
    have ht := Nat.mul_le_mul_left 8 hdegF
    simp only [← Nat.mul_assoc] at ht
    refine hFcard.trans (ht.trans ?_)
    gcongr
    decide
  omega
end
end Low48FatCount_2
end
section
namespace Low48FatCount_2_1
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
open K1 (K)
open K1_13_7 (RegularAt)
open K1_13_7_2 (ProperMark LiftedSurface lowerFlow liftLower eval_liftLower eval_lowerFlow)
open K1_13_7_2_3 (ProperComponent)
open Low48FatCount (fatChart divisorBox divisorBox_eq)
open Low48FatCount_2 (ReducedCut FatTaylor cutBox)
open scoped BigOperators
private theorem sparse_curve_bound : K1_13_7_2_3.c1 :=
  K1_13_7_2_3_1.of_children K1_13_7_2_3_1_1.proof
    (K1_13_7_2_3_1_2.of_children K1_13_7_2_3_1_2_1.proof K1_13_7_2_3_1_2_2.proof)
    K1_13_7_2_3_1_3.proof
private theorem sparse_section_bound : K1_13_7_2_3.c2 :=
  K1_13_7_2_3_2.of_children K1_13_6_1_5_2_1.proof K1_13_6_1_5_2_2.proof
private def cutter {f : Row 4} (q : Row 3) (T : FatTaylor f) (surface : Ideal GeoJets) : Row 4 := by
  classical
  exact if toGeneric T.test ∈ surface then lowerFlow q else T.test
private theorem cutter_fits {f : Row 4} {D q : Row 3} (hq : ReducedCut f D q)
    (T : FatTaylor f) (surface : Ideal GeoJets) :
    GeoFits (toGeneric (cutter q T surface)) (cutBox (shape f)) := by
  classical
  by_cases h : toGeneric T.test ∈ surface
  · simpa [cutter, h] using flow_fits_cut hq
  · simpa [cutter, h] using test_fits_cut T
private theorem exists_marked_curve {f : Row 4} {D q : Row 3} {S : Geom[X]}
    (hq : ReducedCut f D q) (T : FatTaylor f) (hd : S.natDegree ≤ Low48Price.physicalDegree)
    (hf : OnFactor f S) (hr : RegularAt f S) (hm : ProperMark f q T.test S) :
    ∃ C surface : Ideal GeoJets, LiftedSurface f q surface ∧
      ProperComponent surface (toGeneric (cutter q T surface)) C ∧ C ≤ markIdeal S := by
  classical
  obtain ⟨surface, hZ, hZS, hmark⟩ := hm
  have hP : toGeneric (cutter q T surface) ∉ surface := by
    by_cases h : toGeneric T.test ∈ surface
    · simpa [cutter, h] using hmark.resolve_left (not_not_intro h)
    · simp [cutter, h]
  have hvan : atJet (cutter q T surface) S = 0 := by
    by_cases h : toGeneric T.test ∈ surface
    · have hqZ : toGeneric (liftLower q) ∈ surface := hZ.minimal.le (Ideal.subset_span (by simp))
      have hqS : atJet q S = 0 := by
        simpa only [eval_liftLower] using K1_13_7_2.mem_markIdeal.mp (hZS hqZ)
      simpa [cutter, h] using eval_lowerFlow hf.1 hr hqS
    · simpa [cutter, h] using (chart_on_mark T hd hf.1 hr).2.1
  obtain ⟨C, hC, hCS⟩ := mark_curve hZS hvan
  exact ⟨C, surface, hZ, ⟨hZ.minimal.isPrime, (hq.simple surface hZ).1, hP, hC⟩, hCS⟩
private theorem curveSections_of_component (h2 : K1_13_7_2_3.c2)
    {Γ : Finset K} {s : K → K[X]} {f : Row 4} (T : FatTaylor f)
    (hh : Chamber (fatChart (shape f))) (ht : 0 < (fatChart (shape f)).t)
    {surface C : Ideal GeoJets} {P : GeoJets} (hC : ProperComponent surface P C)
    (huniq : Set.InjOn s (Γ : Set K)) (hd : ∀ γ ∈ Γ, (s γ).natDegree ≤ Low48Price.physicalDegree)
    (hreg : ∀ γ ∈ Γ, OnFactor f (extend (s γ)) ∧ RegularAt f (extend (s γ)))
    (hle : ∀ γ ∈ Γ, C ≤ markIdeal (extend (s γ))) :
    CurveSections Γ s (sectionDegree C ((fatChart (shape f)).scale 6) / 6) := by
  classical
  intro x a hmiss
  let g (γ : K) := K1_13_6_2.actualPoint (extend (s γ))
  let A := Γ.filter fun γ => (s γ).eval x = a
  let U := valueSection T x a
  have hval (γ : K) (hγ : γ ∈ Γ) :
      evalGeneric (extend (s γ)) U = 0 ↔ (s γ).eval x = a :=
    value_at_mark T (hd γ hγ) (hreg γ hγ).1.1 (hreg γ hγ).2 x a
  have hU : U ∉ C := by
    obtain ⟨γ, hγ, hne⟩ := hmiss
    intro hmem
    exact hne ((hval γ hγ).mp (hle γ hγ hmem))
  have hpoints : ∀ y ∈ A.image g, C ≤ RingHom.ker (MvPolynomial.eval y) ∧
      MvPolynomial.eval y U = 0 := by
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hΓ, hvalue⟩ := Finset.mem_filter.mp hγ
    exact ⟨hle γ hΓ, (hval γ hΓ).mpr hvalue⟩
  have hcard : (A.image g).card = A.card := by
    apply Finset.card_image_of_injOn
    intro γ hγ δ hδ he
    exact huniq (Finset.mem_filter.mp hγ).1 (Finset.mem_filter.mp hδ).1
      (Polynomial.map_injective embed embed.injective (K1_13_6_2.actualPoint_injective he))
  have hb := (h2 _ hh ht surface P C hC).2 U (A.image g) (value_fits T x a) hU hpoints
  rw [hcard] at hb
  change A.card ≤ _
  omega
theorem proof : Low48FatCount_2.c1 := by
  have h1 := sparse_curve_bound
  have h2 := sparse_section_bound
  classical
  intro Γ s f D q hft hq T huniq hd hreg
  let p := (shape f).chamber
  let h := fatChart (shape f)
  have hp : Chamber p := shape_chamber f
  have hpt : 0 < p.t := hft
  have hqbox : Chamber divisorBox := by
    rw [divisorBox_eq]
    exact ⟨by decide, by decide⟩
  have hqfits := lower_fits hq.caps
  obtain ⟨hh, hht⟩ := chart_chamber_pos f
  let marked := Γ.filter fun γ => ProperMark f q T.test (extend (s γ))
  have hfind (γ : marked) : ∃ C surface : Ideal GeoJets, LiftedSurface f q surface ∧
      ProperComponent surface (toGeneric (cutter q T surface)) C ∧ C ≤ markIdeal (extend (s γ)) := by
    obtain ⟨hγ, hm⟩ := Finset.mem_filter.mp γ.property
    exact exists_marked_curve hq T (Polynomial.natDegree_map_le.trans (hd γ hγ))
      (hreg γ hγ).1 (hreg γ hγ).2 hm
  choose chooseCurve chooseSurface hsurface hproper hon using hfind
  let curves := marked.attach.image chooseCurve
  have hcurves (C : Ideal GeoJets) (hC : C ∈ curves) :
      ∃ surface, (Ideal.span {toGeneric f, toGeneric (liftLower q)}).IsMinimalPrime surface ∧
        ProperComponent surface (toGeneric (cutter q T surface)) C ∧
        GeoFits (toGeneric (cutter q T surface)) (cutBox (shape f)) := by
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨chooseSurface γ, (hsurface γ).minimal, hproper γ, cutter_fits hq T _⟩
  have hbound (a : Shape) (ha : Chamber a) (hat : 0 < a.t) :
      32 * (∑ C ∈ curves, sectionDegree C (a.scale 6)) ≤
        6 * mixed32 p divisorBox (cutBox (shape f)) a :=
    h1 p divisorBox (cutBox (shape f)) a hp hqbox (cut_chamber hh) ha hat
      _ _ hq.proper (toGeneric_fits ⟨le_max_left _ _, le_rfl, le_rfl⟩)
      hqfits (fun surface => toGeneric (cutter q T surface)) curves hcurves
  let part (C : Ideal GeoJets) := Γ.filter fun γ => C ≤ markIdeal (extend (s γ))
  let d (C : Ideal GeoJets) := sectionDegree C (h.scale 6) / 6
  let e := curves.equivFin.symm
  let B : Pieces Γ := ⟨curves.card, fun i => part (e i), fun _ => Finset.filter_subset _ _, fun i => d (e i)⟩
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨surface, _, hC, _⟩ := hcurves (e i) (e i).property
    exact curveSections_of_component h2 T hh hht hC
      (huniq.mono (Finset.filter_subset _ _))
      (fun γ hγ => hd γ (Finset.mem_filter.mp hγ).1)
      (fun γ hγ => hreg γ (Finset.mem_filter.mp hγ).1)
      (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  · intro γ hγ hm
    let α : marked := ⟨γ, Finset.mem_filter.mpr ⟨hγ, hm⟩⟩
    have hc : chooseCurve α ∈ curves := Finset.mem_image.mpr ⟨α, Finset.mem_attach _ _, rfl⟩
    let i := curves.equivFin ⟨chooseCurve α, hc⟩
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
    change γ ∈ part (e i)
    rw [show e i = ⟨chooseCurve α, hc⟩ from e.apply_symm_apply _]
    exact Finset.mem_filter.mpr ⟨hγ, hon α⟩
  · have hs : 6 * B.total ≤ ∑ C ∈ curves, sectionDegree C (h.scale 6) := by
      change 6 * (∑ i, d (e i)) ≤ _
      rw [Finset.mul_sum]
      calc
        _ ≤ ∑ i, sectionDegree (e i).val (h.scale 6) :=
          Finset.sum_le_sum fun i _ => Nat.mul_div_le _ _
        _ = _ := by
          rw [← Finset.sum_attach curves (fun C => sectionDegree C (h.scale 6))]
          exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    have hb := hbound h hh hht
    change 32 * B.total ≤ mixed32 p divisorBox (cutBox (shape f)) h
    omega
  · have hs : 6 * B.n ≤ ∑ C ∈ curves, sectionDegree C (p.scale 6) := by
      calc
        _ = ∑ _ ∈ curves, 6 := by simp [B, Nat.mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun C hc => by
          obtain ⟨surface, _, hC, _⟩ := hcurves C hc
          exact (h2 p hp hpt surface _ C hC).1
    have hb := hbound p hp hpt
    change 32 * B.n ≤ mixed32 p divisorBox (cutBox (shape f)) p
    omega
end
end Low48FatCount_2_1
end
section
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
namespace Low48FatCount_2_2
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_6_3 K1_13_7
open K1_13_7_2_4 K1_13_7_2_4_2
open Low48Price (physicalDegree anchorCutoff)
open private intDerivation coeffDeriv coeffDeriv_zero_of_shift zero_of_stationary_eval
  rowTrajectory rowTrajectory_stationary eval_chartTrajectory from ProximityPrize.SubmissionLower.Fast066
open private sum_monomial_eq_of_coeffs from ProximityPrize.SubmissionLower.Fast066
open private trajectory_at_component component_ne_zero from ProximityPrize.SubmissionLower.Fast066
private theorem length_le : Low48Price.taylorLength ≤ K1_13.taylorLength := by decide
private theorem numerator_mem_from {f : Row 4} {P : Ideal GeoJets}
    (hinv : Invariant f P) (hmem : toGeneric (Low48FatPad.membershipTest f) ∈ P)
    {n : ℕ} (hn : Low48Price.taylorLength ≤ n) : toGeneric (jetNumerator f n) ∈ P := by
  induction n, hn using Nat.le_induction with
  | base => exact hmem
  | succ n _ ih =>
    rw [jetNumerator, clearedStep]
    simp only [toGeneric, map_sub, map_mul]
    exact P.sub_mem (P.mul_mem_left _ (hinv _ ih)) (P.mul_mem_left _ ih)
private theorem chart_degree {f : Row 4} {P : Ideal GeoJets}
    (hinv : Invariant f P) (hmem : toGeneric (Low48FatPad.membershipTest f) ∈ P) :
    (chartPolynomial f P).natDegree ≤ physicalDegree := by
  rw [chartPolynomial, natDegree_taylor]
  apply natDegree_sum_le_of_forall_le
  intro i _
  by_cases hi : i.val < Low48Price.taylorLength
  · exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ hi)
  · have htail := numerator_mem_from hinv hmem (Nat.le_of_not_gt hi)
    have hi4 : ¬i.val < 4 := fun h => hi (h.trans (by decide : 4 < Low48Price.taylorLength))
    rw [chartJet, dite_eq_right hi4, onChart_zero (f := f) htail, mul_zero, monomial_zero_right,
      natDegree_zero]
    exact Nat.zero_le _
private theorem row_degree {R : Type*} [CommRing R]
    (k : Geom →+* R) (Q : Row 4) (U : R[X]) {B : ℕ}
    (hQ : Low48Price.TrueWeightLE Q B) (hU : U.natDegree ≤ physicalDegree) :
    (rowTrajectory k Q U).natDegree ≤ B := by
  classical
  unfold rowTrajectory
  rw [MvPolynomial.eval₂_eq]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  refine (natDegree_mul_le_of_le Polynomial.natDegree_map_le ?_).trans (hQ m hm)
  refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  change _ ≤ (physicalDegree - i.val) * m i
  rw [Nat.mul_comm]
  exact natDegree_pow_le_of_le _ ((natDegree_hasseDeriv_le _ _).trans (Nat.sub_le_sub_right hU _))
private theorem solves_fresh {f : Row 4} {P : Ideal GeoJets} [P.IsPrime]
    (hs : toGeneric (separant f) ∉ P) (hw : Low48Price.TrueWeightLE f anchorCutoff)
    (hf : toGeneric f ∈ P) (hinv : Invariant f P)
    (hmem : toGeneric (Low48FatPad.membershipTest f) ∈ P)
    (δ : Derivation Geom (ChartRing f P) (ChartRing f P)) (hδ : FollowsFlow f P δ) :
    trajectory (componentConstants P) f ((chartPolynomial f P).map (genericLift f P hs)) = 0 := by
  let U := chartPolynomial f P
  let x := chartCenter f P
  let k := chartConstants f P
  let V := rowTrajectory k f U
  let d := intDerivation (R := ChartRing f P) δ.toLinearMap.toAddMonoidHom δ.map_one_eq_zero
    (fun a b => by
      change δ (a * b) = a * δ b + b * δ a
      simpa only [smul_eq_mul] using δ.leibniz a b)
  have hx : d x = 1 := chartCenter_deriv hδ
  have hc (a : Geom) : d (k a) = 0 := chartConstants_deriv hδ a
  have hU : coeffDeriv d U = 0 :=
    coeffDeriv_zero_of_shift d x hx U
      (chartTaylor_shift hδ (numerator_mem_from hinv hmem length_le))
  have he : V.eval x = 0 := (eval_chartTrajectory f P f).trans (onChart_zero hf)
  have hd : V.natDegree ≤ anchorCutoff := row_degree k f U hw (chart_degree hinv hmem)
  have hz : V = 0 := zero_of_stationary_eval d x hx V
    (rowTrajectory_stationary d k hc f U hU) he (fun n hn => chart_factorial_unit f P
      (hn.trans_lt (hd.trans_lt (by decide : anchorCutoff < K1.p))))
  let φ := genericLift f P hs
  have hk : φ.comp (chartConstants f P) = componentConstants P := by
    apply RingHom.ext
    intro a
    simpa only [RingHom.comp_apply, chartConstants, componentConstants, geomConstants,
      toGeneric, MvPolynomial.map_C] using
      genericLift_onChart f P hs (MvPolynomial.C (C a))
  have hm : V.map φ = trajectory (componentConstants P) f (U.map φ) := by
    change (mapRingHom φ) (MvPolynomial.eval₂ (mapRingHom (chartConstants f P))
      (fun i : Fin 4 => hasseDeriv i.val U) f) = _
    rw [MvPolynomial.hom_eval₂ f (mapRingHom (chartConstants f P)) (mapRingHom φ)
      (fun i : Fin 4 => hasseDeriv i.val U), mapRingHom_comp, hk, trajectory]
    simp only [coe_mapRingHom, hasseDeriv_map]
  rw [← hm, hz, Polynomial.map_zero]
private def retunedEval {L : Type} [Field L] (k : Geom →+* L) (U : L[X]) :
    Low48FatCount_2.CoeffRing →+* L :=
  MvPolynomial.eval₂Hom k (fun i : Fin Low48Price.taylorLength => U.coeff i.val)
private def forgetTail : K1_13_6_3.CoeffRing →ₐ[Geom] Low48FatCount_2.CoeffRing :=
  MvPolynomial.aeval (fun i : Fin K1_13.taylorLength =>
    if hi : i.val < Low48Price.taylorLength then MvPolynomial.X ⟨i.val, hi⟩ else 0)
private theorem retuned_dimension {L : Type} [Field L] (k : Geom →+* L) (U : L[X])
    (hd : U.natDegree < Low48Price.taylorLength) :
    (MvPolynomial.affineHilbertPolynomial (coefficientKernel k U)).natDegree ≤
    (MvPolynomial.affineHilbertPolynomial (RingHom.ker (retunedEval k U))).natDegree := by
  let e := retunedEval k U
  let A := RingHom.ker e
  have he : e.comp forgetTail.toRingHom =
      MvPolynomial.eval₂Hom k (fun i : Fin K1_13.taylorLength => U.coeff i.val) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [e, forgetTail, retunedEval]
    · intro i
      rw [MvPolynomial.eval₂Hom_X']
      change e (forgetTail (MvPolynomial.X i)) = U.coeff i.val
      simp only [forgetTail, MvPolynomial.aeval_X]
      split_ifs with hi
      · exact MvPolynomial.eval₂Hom_X' _ _ _
      · rw [map_zero, coeff_eq_zero_of_natDegree_lt (hd.trans_le (Nat.le_of_not_gt hi))]
  have hker : coefficientKernel k U = A.comap forgetTail.toRingHom := by
    ext Q
    change _ ↔ (e.comp forgetTail.toRingHom) Q = 0
    rw [he]
    rfl
  rw [hker]
  exact MvPolynomial.natDegree_affineHilbertPolynomial_le_of_injective
    (Ideal.quotientMapₐ A forgetTail le_rfl)
    (Ideal.quotientMap_injective (I := A) (f := forgetTail.toRingHom))
private theorem specializes_retuned {f : Row 4} {P : Ideal GeoJets} [P.IsPrime]
    (hs : toGeneric (separant f) ∉ P) {S : Geom[X]}
    (hP : P ≤ markIdeal S) (hr : RegularAt f S) (hf : atJet f S = 0)
    (hd : S.natDegree ≤ physicalDegree) :
    RingHom.ker (retunedEval (componentConstants P)
      ((chartPolynomial f P).map (genericLift f P hs))) ≤ Low48FatCount_2.coefficientPointIdeal S := by
  let U := (chartPolynomial f P).map (genericLift f P hs)
  let j : Fin Low48Price.taylorLength → Fin K1_13.taylorLength := Fin.castLE length_le
  have hold : coefficientKernel (componentConstants P) U ≤ K1_13_7_2.coefficientPointIdeal S :=
    specializes hs hP hr hf (hd.trans (by decide : physicalDegree ≤ 133671))
  intro Q hQ
  have hentry : MvPolynomial.rename j Q ∈ coefficientKernel (componentConstants P) U := by
    change MvPolynomial.eval₂Hom (componentConstants P)
      (fun i : Fin K1_13.taylorLength => U.coeff i.val) (MvPolynomial.rename j Q) = 0
    rw [MvPolynomial.eval₂Hom_rename]
    exact hQ
  have hm := hold hentry
  change MvPolynomial.eval (fun i : Fin K1_13.taylorLength => S.coeff i.val)
    (MvPolynomial.rename j Q) = 0 at hm
  rw [MvPolynomial.eval_rename] at hm
  exact hm
private theorem map_universal {L : Type} [Field L] (k : Geom →+* L) (U : L[X])
    (hd : U.natDegree < Low48Price.taylorLength) (Q : Row 4) :
    (Low48FatCount_2.universalEval Q).map (retunedEval k U) = trajectory k Q U := by
  let e := retunedEval k U
  have hU : Low48FatCount_2.universalPolynomial.map e = U := by
    rw [Low48FatCount_2.universalPolynomial, Polynomial.map_sum]
    simp only [C_mul_X_pow_eq_monomial, map_monomial, e, retunedEval, MvPolynomial.eval₂Hom_X']
    exact sum_monomial_eq_of_coeffs _ U hd (fun _ => rfl)
  have hk : e.comp MvPolynomial.C = k := RingHom.ext fun a => MvPolynomial.eval₂Hom_C _ _ a
  change (mapRingHom e) (MvPolynomial.eval₂ (mapRingHom MvPolynomial.C)
    (fun i : Fin 4 => hasseDeriv i.val Low48FatCount_2.universalPolynomial) Q) = trajectory k Q U
  rw [MvPolynomial.hom_eval₂, Polynomial.mapRingHom_comp, hk]
  simp only [Polynomial.coe_mapRingHom, ← hasseDeriv_map, hU, trajectory]
theorem proof : Low48FatCount_2.c2 := by
  intro f hf P hp hheight hfP hs hinv hmem S hle hreg hd
  let := hp
  obtain ⟨δ, hδ⟩ := K1_13_7_2_4_1.proof f P hp hs hinv
  let U := (chartPolynomial f P).map (genericLift f P hs)
  have hdegree : U.natDegree < Low48Price.taylorLength :=
    Nat.lt_succ_of_le (Polynomial.natDegree_map_le.trans (chart_degree hinv hmem))
  have hjet : ∀ i : Fin 4,
      (hasseDeriv i.val U).eval (onComponent P (MvPolynomial.C genericArgument)) =
        onComponent P (MvPolynomial.X i) := by
    intro i
    simpa only [U, chartCenter, genericLift_onChart, genericArgument,
      toGeneric, MvPolynomial.map_C, MvPolynomial.map_X] using
      eval_hasse_chartPolynomial (genericLift f P hs) i
  have hsolve : trajectory (componentConstants P) f U = 0 :=
    solves_fresh hs hf.2.2.2 hfP hinv hmem δ hδ
  have hregular : trajectory (componentConstants P) (separant f) U ≠ 0 := by
    intro hzero
    apply component_ne_zero hs
    rw [← trajectory_at_component P U (separant f) hjet, hzero, eval_zero]
  have hdim := (K1_13_7_2_4_3.proof P hp U hheight (hdegree.trans_le length_le) hjet).trans
    (retuned_dimension (componentConstants P) U hdegree)
  let e := retunedEval (componentConstants P) U
  refine ⟨RingHom.ker e, ⟨RingHom.ker_isPrime _, hdim, ?_, ?_⟩, ?_⟩
  · intro i
    change e ((Low48FatCount_2.universalEval f).coeff i) = 0
    rw [← Polynomial.coeff_map, map_universal _ _ hdegree, hsolve, coeff_zero]
  · obtain ⟨i, hi⟩ := not_forall.mp (mt Polynomial.ext_iff.mpr hregular)
    refine ⟨i, ?_⟩
    change e ((Low48FatCount_2.universalEval (separant f)).coeff i) ≠ 0
    rw [← Polynomial.coeff_map, map_universal _ _ hdegree]
    simpa only [coeff_zero] using hi
  · exact specializes_retuned hs hle hreg (K1_13_7_2.mem_markIdeal.mp (hle hfP)) hd
end
end Low48FatCount_2_2
end
section
set_option autoImplicit false
namespace Low48FatCount_2_3
noncomputable section
open Polynomial MvPolynomial
open K1_13 (Geom Row)
open K1_13_6 (GeoField GeoJets toGeneric separant)
open K1_13_6_3 (JetIdeal dimension geomConstants genericArgument)
open Low48Price (taylorLength)
open Low48FatCount_2 (CoeffRing FatTaylor)
abbrev CoeffIdeal := Ideal CoeffRing
abbrev FreshCoeffRing := MvPolynomial (Fin taylorLength) GeoField
def jetLinear {k : Type*} [Field k] (a : k) (i : ℕ) :
    MvPolynomial (Fin taylorLength) k :=
  ∑ j : Fin taylorLength,
    MvPolynomial.C ((j.val.choose i : k) * a ^ (j.val - i)) * MvPolynomial.X j
def extendIdeal (A : CoeffIdeal) : Ideal FreshCoeffRing :=
  A.map (MvPolynomial.map geomConstants)
def freshJetMap : GeoJets →+* FreshCoeffRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => jetLinear genericArgument i.val)
def freshImage (A : CoeffIdeal) : JetIdeal :=
  (extendIdeal A).comap freshJetMap
def FreshBirational (A : CoeffIdeal) : Prop :=
  ∀ h : FreshCoeffRing, ∃ u v : GeoJets,
    freshJetMap v ∉ extendIdeal A ∧ h * freshJetMap v - freshJetMap u ∈ extendIdeal A
structure FreshChart (f : Row 4) (T : FatTaylor f) (A : CoeffIdeal) : Prop where
  extended_prime : (extendIdeal A).IsPrime
  dimension_eq : dimension (freshImage A) = dimension A
  factor : toGeneric f ∈ freshImage A
  regular : toGeneric (separant f) ∉ freshImage A
  test : toGeneric T.test ∈ freshImage A
  denom : toGeneric T.denom ∉ freshImage A
  recovers : ∀ i, MvPolynomial.X i * freshJetMap (toGeneric T.denom) -
    freshJetMap (toGeneric (T.numer i)) ∈ extendIdeal A
end
end Low48FatCount_2_3
end
section
namespace Low48FatCount_2_3
noncomputable section
open Polynomial MvPolynomial
open K1_13 (Geom Row shape)
open K1_13_6 (GeoJets toGeneric divisorIdeal)
open K1_13_6_3 (geomConstants)
open K1_13_7_2_5 (wholeComponents properComponents)
open P0_9_7_2_3 (whole_sum)
open Low48FatCount (fatChart)
open Low48FatCount_2 (CoeffRing FatTaylor)
open scoped BigOperators
private theorem common_clearing {f : Row 4} (T : FatTaylor f) (g : FreshCoeffRing) :
    ∃ (u : GeoJets) (n : ℕ), ∀ A : CoeffIdeal, FreshChart f T A →
      g * freshJetMap (toGeneric T.denom) ^ n - freshJetMap u ∈ extendIdeal A := by
  let D := toGeneric T.denom
  let d := freshJetMap D
  induction g using MvPolynomial.induction_on with
  | C c =>
    refine ⟨MvPolynomial.C c, 0, ?_⟩
    intro A _
    simp only [pow_zero, mul_one, freshJetMap, MvPolynomial.eval₂Hom_C, sub_self, Ideal.zero_mem]
  | add p q hp hq =>
    obtain ⟨u, n, hu⟩ := hp
    obtain ⟨v, m, hv⟩ := hq
    refine ⟨u * D ^ m + v * D ^ n, n + m, ?_⟩
    intro A hA
    let J := extendIdeal A
    have hpu := J.mul_mem_right (d ^ m) (hu A hA)
    have hqv := J.mul_mem_right (d ^ n) (hv A hA)
    have he : (p + q) * d ^ (n + m) - freshJetMap (u * D ^ m + v * D ^ n) =
        (p * d ^ n - freshJetMap u) * d ^ m + (q * d ^ m - freshJetMap v) * d ^ n := by
      have hd : freshJetMap D = d := rfl
      simp only [map_add, map_mul, map_pow, hd, pow_add]
      ring
    change (p + q) * d ^ (n + m) - freshJetMap (u * D ^ m + v * D ^ n) ∈ J
    rw [he]
    exact J.add_mem hpu hqv
  | mul_X p i hp =>
    obtain ⟨u, n, hu⟩ := hp
    let v := toGeneric (T.numer i)
    refine ⟨u * v, n + 1, ?_⟩
    intro A hA
    let J := extendIdeal A
    have hpu := J.mul_mem_right (MvPolynomial.X i * d) (hu A hA)
    have hiv := J.mul_mem_left (freshJetMap u) (hA.recovers i)
    have he : p * MvPolynomial.X i * d ^ (n + 1) - freshJetMap (u * v) =
        (p * d ^ n - freshJetMap u) * (MvPolynomial.X i * d) +
          freshJetMap u * (MvPolynomial.X i * d - freshJetMap v) := by
      rw [map_mul, pow_succ]
      ring
    change p * MvPolynomial.X i * d ^ (n + 1) - freshJetMap (u * v) ∈ J
    rw [he]
    exact J.add_mem hpu hiv
theorem fresh_birational {f : Row 4} {T : FatTaylor f} {A : CoeffIdeal}
    (h : FreshChart f T A) : FreshBirational A := by
  intro g
  obtain ⟨u, n, hu⟩ := common_clearing T g
  refine ⟨u, toGeneric T.denom ^ n, ?_, ?_⟩
  · rw [map_pow]
    exact fun hz => h.denom (h.extended_prime.mem_of_pow_mem _ hz)
  · rw [map_pow]
    exact hu A h
private theorem original_mem {B : CoeffIdeal} (hB : B.IsPrime) {g : CoeffRing}
    (hg : MvPolynomial.map geomConstants g ∈ extendIdeal B) : g ∈ B := by
  rw [← hB.radical, ← vanishingIdeal_zeroLocus_eq_radical (K := Geom)]
  intro x hx
  let ψ := MvPolynomial.eval (geomConstants ∘ x)
  have hψ : ψ.comp (MvPolynomial.map geomConstants) = geomConstants.comp (MvPolynomial.eval x) := by
    apply RingHom.ext
    intro q
    exact (eval_map _ _ _).trans (eval₂_comp _ _ _).symm
  have hker : extendIdeal B ≤ RingHom.ker ψ := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro q hq
    change ψ (MvPolynomial.map geomConstants q) = 0
    rw [← RingHom.comp_apply, hψ, RingHom.comp_apply]
    have hq0 : MvPolynomial.eval x q = 0 := hx q hq
    rw [hq0, map_zero]
  have hv := RingHom.mem_ker.mp (hker hg)
  change (ψ.comp (MvPolynomial.map geomConstants)) g = 0 at hv
  rw [hψ, RingHom.comp_apply, ← map_zero geomConstants] at hv
  exact geomConstants.injective hv
theorem le_of_freshImage_le {f : Row 4} {T : FatTaylor f} {A B : CoeffIdeal}
    (hA : FreshChart f T A) (hB : FreshChart f T B) (hp : B.IsPrime)
    (hle : freshImage A ≤ freshImage B) : A ≤ B := by
  intro g hg
  apply original_mem hp
  let q := MvPolynomial.map geomConstants g
  have hq : q ∈ extendIdeal A := Ideal.mem_map_of_mem _ hg
  obtain ⟨u, n, hu⟩ := common_clearing T q
  let d := freshJetMap (toGeneric T.denom)
  have huA : u ∈ freshImage A := by
    change freshJetMap u ∈ extendIdeal A
    have hm := (extendIdeal A).mul_mem_right (d ^ n) hq
    simpa only [d, sub_sub_cancel] using (extendIdeal A).sub_mem hm (hu A hA)
  have hm : q * d ^ n ∈ extendIdeal B := by
    have huB : freshJetMap u ∈ extendIdeal B := hle huA
    simpa only [sub_add_cancel] using (extendIdeal B).add_mem (hu B hB) huB
  exact (hB.extended_prime.mem_or_mem hm).resolve_right
    (fun hz => hB.denom (hB.extended_prime.mem_of_pow_mem _ hz))
private theorem generic_degree_le (g : Row 4) : (toGeneric g).totalDegree ≤ g.totalDegree := by
  rw [toGeneric, MvPolynomial.totalDegree_eq, MvPolynomial.totalDegree_eq]
  exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
private theorem sum_biUnion_le {α β : Type} [DecidableEq β] (A : Finset α) (B : α → Finset β)
    (w : β → ℚ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x ∈ A.biUnion B, w x) ≤ ∑ i ∈ A, ∑ x ∈ B i, w x := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have hu := Finset.sum_union_inter (f := w) (s₁ := B i) (s₂ := A.biUnion B)
    have hn : 0 ≤ ∑ x ∈ B i ∩ A.biUnion B, w x := Finset.sum_nonneg fun x _ => hw x
    linarith
theorem proper_sum {f : Row 4} (hf : Irreducible f) (T : FatTaylor f) :
    ∑ P ∈ properComponents f T.test, affineDegree P ≤
      ((shape f).chamber.b : ℚ) * (fatChart (shape f)).b := by
  classical
  let V := (wholeComponents f).filter (fun component => toGeneric T.test ∉ component)
  let b := (fatChart (shape f)).b
  have hdeg : (toGeneric T.test).totalDegree ≤ b := (generic_degree_le _).trans T.test_box.1
  calc
    _ ≤ ∑ component ∈ V, ∑ P ∈ (divisorIdeal component T.test).minimalPrimesFinset, affineDegree P :=
      sum_biUnion_le V _ affineDegree affineDegree_nonneg
    _ ≤ ∑ component ∈ V, (b : ℚ) * affineDegree component := by
      refine Finset.sum_le_sum fun component hZ => ?_
      obtain ⟨hZ, ht⟩ := Finset.mem_filter.mp hZ
      let _ := (Ideal.mem_minimalPrimesFinset.mp hZ).isPrime
      exact principalCut_sum_affineDegree_minimalPrimes_le ht hdeg
    _ = (b : ℚ) * ∑ component ∈ V, affineDegree component := (Finset.mul_sum ..).symm
    _ ≤ (b : ℚ) * (shape f).chamber.b :=
      mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun component _ _ => affineDegree_nonneg component)).trans (whole_sum hf))
        (by positivity)
    _ = _ := mul_comm _ _
end
end Low48FatCount_2_3
end
section
set_option autoImplicit false
set_option maxRecDepth 1500
namespace Low48FatCount_2_3
noncomputable section
open Polynomial
open K1_13 (Geom Row)
open K1_13_6 (GeoField GeoJets GenericField genericCoeffs toGeneric separant)
open K1_13_6_3 (geomConstants genericArgument)
open K1_13_7_2 (evalTrajectory)
open Low48Price (physicalDegree taylorLength)
open Low48FatCount_2 (CoeffRing FatTaylor ActualFamily universalPolynomial universalEval)
open scoped BigOperators
private def evaluateFresh : CoeffRing[X] →+* FreshCoeffRing :=
  Polynomial.eval₂RingHom (MvPolynomial.map geomConstants) (MvPolynomial.C genericArgument)
private theorem evaluateFresh_hasse (i : ℕ) :
    evaluateFresh (hasseDeriv i universalPolynomial) = jetLinear genericArgument i := by
  classical
  simp only [universalPolynomial, C_mul_X_pow_eq_monomial, map_sum, jetLinear]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hasseDeriv_monomial]
  simp only [evaluateFresh, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
    map_mul, map_natCast, MvPolynomial.map_X, map_pow]
  ac_rfl
private theorem generic_eval :
    Polynomial.eval₂RingHom geomConstants genericArgument = genericCoeffs := by
  apply Polynomial.ringHom_ext
  · intro b
    exact Polynomial.eval₂_C _ _
  · exact Polynomial.eval₂_X _ _
private theorem evaluateFresh_row (R : Row 4) :
    evaluateFresh (universalEval R) = freshJetMap (toGeneric R) := by
  change (evaluateFresh.comp
      (MvPolynomial.eval₂Hom (Polynomial.mapRingHom MvPolynomial.C)
        (fun i : Fin 4 => hasseDeriv i.val universalPolynomial))) R =
    (freshJetMap.comp (MvPolynomial.map genericCoeffs)) R
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C, freshJetMap]
    change Polynomial.eval₂ (MvPolynomial.map geomConstants) (MvPolynomial.C genericArgument)
        (a.map MvPolynomial.C) = MvPolynomial.C (genericCoeffs a)
    have hm : (MvPolynomial.map geomConstants).comp (MvPolynomial.C : Geom →+* CoeffRing) =
        (MvPolynomial.C : GeoField →+* FreshCoeffRing).comp geomConstants := by
      apply RingHom.ext
      simp
    rw [Polynomial.eval₂_map, hm, ← Polynomial.hom_eval₂]
    change MvPolynomial.C ((Polynomial.eval₂RingHom geomConstants genericArgument) a) = _
    rw [generic_eval]
  · intro i
    simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X,
      freshJetMap] using evaluateFresh_hasse i.val
private theorem evaluateFresh_mem {A : CoeffIdeal} (hA : A.IsPrime)
    (p : CoeffRing[X]) :
    evaluateFresh p ∈ extendIdeal A ↔ ∀ n, p.coeff n ∈ A := by
  constructor
  · intro hp n
    rw [← hA.radical, ← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Geom)]
    intro x hx
    let ev := MvPolynomial.eval (geomConstants ∘ x)
    have hev : ev.comp (MvPolynomial.map geomConstants) =
        geomConstants.comp (MvPolynomial.eval x) := by
      apply RingHom.ext
      intro q
      exact (MvPolynomial.eval_map _ _ _).trans (MvPolynomial.eval₂_comp _ _ _).symm
    have hker : extendIdeal A ≤ RingHom.ker ev := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro q hq
      change (ev.comp (MvPolynomial.map geomConstants)) q = 0
      rw [hev, RingHom.comp_apply, (show MvPolynomial.eval x q = 0 from hx q hq), map_zero]
    have he : ev (evaluateFresh p) = genericCoeffs (p.map (MvPolynomial.eval x)) := by
      change ev (p.eval₂ (MvPolynomial.map geomConstants) (MvPolynomial.C genericArgument)) = _
      rw [Polynomial.hom_eval₂, hev]
      have hC : ev (MvPolynomial.C genericArgument) = genericArgument := MvPolynomial.eval_C _
      rw [hC, ← Polynomial.eval₂_map]
      exact RingHom.congr_fun generic_eval _
    have hzero : genericCoeffs (p.map (MvPolynomial.eval x)) = 0 :=
      he.symm.trans (RingHom.mem_ker.mp (hker hp))
    have hinj : Function.Injective genericCoeffs :=
      (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective Geom[X] GenericField)
    have hz : p.map (MvPolynomial.eval x) = 0 := hinj (hzero.trans (map_zero _).symm)
    simpa only [MvPolynomial.aeval_eq_eval, Polynomial.coeff_map, Polynomial.coeff_zero] using
      congrArg (fun g : Geom[X] => g.coeff n) hz
  · intro hp
    rw [congrArg evaluateFresh p.as_sum_range, map_sum]
    apply Ideal.sum_mem
    intro n _
    rw [evaluateFresh, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hp n))
private abbrev CoeffField (A : CoeffIdeal) := FractionRing (CoeffRing ⧸ A)
private def coefficientMap (A : CoeffIdeal) :
    CoeffRing →+* CoeffField A :=
  (algebraMap (CoeffRing ⧸ A) (CoeffField A)).comp (Ideal.Quotient.mk A)
private theorem coefficientMap_zero_iff (A : CoeffIdeal) [A.IsPrime]
    (a : CoeffRing) :
    coefficientMap A a = 0 ↔ a ∈ A := by
  change algebraMap (CoeffRing ⧸ A) (CoeffField A) (Ideal.Quotient.mk A a) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective (CoeffRing ⧸ A) (CoeffField A)),
    Ideal.Quotient.eq_zero_iff_mem]
private def powerSum {m : ℕ} (a : Fin m → CoeffRing) :
    CoeffRing[X] :=
  ∑ j : Fin m, C (a j) * Polynomial.X ^ j.val
private theorem coeff_sum {m : ℕ} (a : Fin m → CoeffRing) (n : ℕ) :
    (powerSum a).coeff n = if hn : n < m then a ⟨n, hn⟩ else 0 := by
  classical
  simp only [powerSum, C_mul_X_pow_eq_monomial, Polynomial.finsetSum_coeff]
  split_ifs with hn
  · rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin m)]
    · exact coeff_monomial_same _ _
    · intro j _ hj
      exact coeff_monomial_of_ne _ (fun he => hj (Fin.ext he.symm))
    · simp
  · exact Finset.sum_eq_zero fun j _ => coeff_monomial_of_ne _ (fun he => hn (he.symm ▸ j.isLt))
private theorem coeff_sum_at {m : ℕ} (a : Fin m → CoeffRing) (i : Fin m) :
    (powerSum a).coeff i.val = a i := by
  rw [coeff_sum, dite_eq_left i.isLt]
private theorem coeff_sum_above {m : ℕ} (a : Fin m → CoeffRing) (n : ℕ)
    (hn : ¬ n < m) : (powerSum a).coeff n = 0 := by
  rw [coeff_sum, dite_eq_right hn]
private theorem universal_eq :
    universalPolynomial = powerSum (m := taylorLength) MvPolynomial.X :=
  rfl
private theorem universal_coeff (i : Fin taylorLength) :
    universalPolynomial.coeff i.val = MvPolynomial.X i := by
  rw [universal_eq]
  exact coeff_sum_at (m := taylorLength) MvPolynomial.X i
private theorem universal_degree :
    universalPolynomial.natDegree ≤ physicalDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [universal_eq]
  have hlen : ¬ n < taylorLength := not_lt_of_ge (Nat.succ_le_of_lt hn)
  exact coeff_sum_above (m := taylorLength) MvPolynomial.X n hlen
private theorem map_universal (A : CoeffIdeal) [A.IsPrime]
    [Algebra Geom (CoeffField A)]
    (hk : algebraMap Geom (CoeffField A) = (coefficientMap A).comp MvPolynomial.C)
    (R : Row 4) :
    (universalEval R).map (coefficientMap A) =
      evalTrajectory R (universalPolynomial.map (coefficientMap A)) := by
  change (mapRingHom (coefficientMap A)) (MvPolynomial.eval₂ (mapRingHom MvPolynomial.C)
    (fun i : Fin 4 => hasseDeriv i.val universalPolynomial) R) = _
  rw [MvPolynomial.hom_eval₂, Polynomial.mapRingHom_comp, ← hk]
  simp only [Polynomial.coe_mapRingHom, ← hasseDeriv_map, evalTrajectory]
theorem fresh_identities {f : Row 4} (T : FatTaylor f) {A : CoeffIdeal}
    (h : ActualFamily f A) :
    toGeneric f ∈ freshImage A ∧
      toGeneric (separant f) ∉ freshImage A ∧
      toGeneric T.test ∈ freshImage A ∧
      toGeneric T.denom ∉ freshImage A ∧
      ∀ i, MvPolynomial.X i * freshJetMap (toGeneric T.denom) -
        freshJetMap (toGeneric (T.numer i)) ∈ extendIdeal A := by
  let : A.IsPrime := h.prime
  let k : Geom →+* CoeffField A := (coefficientMap A).comp MvPolynomial.C
  let : Algebra Geom (CoeffField A) := k.toAlgebra
  let U := universalPolynomial.map (coefficientMap A)
  have hmap (R : Row 4) : (universalEval R).map (coefficientMap A) = evalTrajectory R U :=
    map_universal A rfl R
  have heval (p : CoeffRing[X]) :
      p.map (coefficientMap A) = 0 ↔ evaluateFresh p ∈ extendIdeal A := by
    rw [evaluateFresh_mem h.prime]
    exact ⟨fun hz n => (coefficientMap_zero_iff A _).mp (by
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using
        congrArg (fun g : (CoeffField A)[X] => g.coeff n) hz),
      fun hn => Polynomial.ext fun n => by
        rw [Polynomial.coeff_map, Polynomial.coeff_zero, coefficientMap_zero_iff]
        exact hn n⟩
  have hfresh (R : Row 4) : evalTrajectory R U = 0 ↔ toGeneric R ∈ freshImage A := by
    change evalTrajectory R U = 0 ↔ freshJetMap (toGeneric R) ∈ extendIdeal A
    rw [← hmap, ← evaluateFresh_row, heval]
  have hf : toGeneric f ∈ freshImage A := by
    change freshJetMap (toGeneric f) ∈ extendIdeal A
    rw [← evaluateFresh_row, evaluateFresh_mem h.prime]
    exact h.solves
  have hs : toGeneric (separant f) ∉ freshImage A := by
    change freshJetMap (toGeneric (separant f)) ∉ extendIdeal A
    rw [← evaluateFresh_row, evaluateFresh_mem h.prime]
    obtain ⟨n, hn⟩ := h.regular
    exact fun hall => hn (hall n)
  have hd : U.natDegree ≤ physicalDegree := natDegree_map_le.trans universal_degree
  obtain ⟨hden, ht, hr⟩ := T.recovers (CoeffField A) U hd ((hfresh f).mpr hf)
    (fun hz => hs ((hfresh (separant f)).mp hz))
  refine ⟨hf, hs, (hfresh T.test).mp ht, fun hm => hden ((hfresh T.denom).mpr hm), ?_⟩
  intro i
  let p := C (MvPolynomial.X i : CoeffRing) * universalEval T.denom -
    universalEval (T.numer i)
  have hp : p.map (coefficientMap A) = 0 := by
    change mapRingHom (coefficientMap A) p = 0
    simp only [p, map_sub, map_mul, Polynomial.coe_mapRingHom, Polynomial.map_C, hmap]
    rw [hr i, show U.coeff i.val = coefficientMap A (MvPolynomial.X i) by
      rw [Polynomial.coeff_map, universal_coeff], mul_comm, sub_self]
  have hm := (heval p).mp hp
  simpa only [p, map_sub, map_mul, evaluateFresh_row,
    show ∀ a : CoeffRing, evaluateFresh (C a) = MvPolynomial.map geomConstants a
      from fun _ => eval₂_C _ _, MvPolynomial.map_X] using hm
end
end Low48FatCount_2_3
end
section
set_option autoImplicit false
namespace Low48FatCount_2_3
noncomputable section
open MvPolynomial
open K1_13 (Geom Row)
open K1_13_6 (GeoField GeoJets)
open K1_13_6_3 (dimension geomConstants genericArgument)
open Low48Price (taylorLength)
open Low48FatCount_2 (FatTaylor ActualFamily)
private def jetAlg : GeoJets →ₐ[GeoField] FreshCoeffRing :=
  aeval (fun i : Fin 4 => jetLinear genericArgument i.val)
private theorem dimension_of_recovery {A : CoeffIdeal} (hA : (extendIdeal A).IsPrime)
    (D : GeoJets) (N : Fin taylorLength → GeoJets)
    (hD : D ∉ freshImage A)
    (hN : ∀ i, MvPolynomial.X i * freshJetMap D - freshJetMap (N i) ∈ extendIdeal A) :
    dimension (freshImage A) = dimension (extendIdeal A) := by
  let I := extendIdeal A
  let J := freshImage A
  let q := Ideal.Quotient.mk I
  let F := Ideal.quotientMapₐ I jetAlg (show J ≤ I.comap jetAlg.toRingHom from le_rfl)
  have hF (p : GeoJets) : F (Ideal.Quotient.mk J p) = q (freshJetMap p) := rfl
  have hinj : Function.Injective F :=
    Ideal.quotientMap_injective' (H := show J ≤ I.comap jetAlg.toRingHom from le_rfl) le_rfl
  apply le_antisymm (natDegree_affineHilbertPolynomial_le_of_injective F hinj)
  let d := q (freshJetMap D)
  have hX (i : Fin taylorLength) : q (freshJetMap (N i)) = d * q (MvPolynomial.X i) := by
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr (hN i)
    change q (MvPolynomial.X i * freshJetMap D - freshJetMap (N i)) = 0 at hz
    rw [map_sub, sub_eq_zero, map_mul, mul_comm] at hz
    exact hz.symm
  have hclear (p : FreshCoeffRing) : ∃ (u : GeoJets) (n : ℕ),
      q (freshJetMap u) = d ^ n * q p := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine ⟨MvPolynomial.C a, 0, ?_⟩
      simp only [pow_zero, one_mul, freshJetMap, MvPolynomial.eval₂Hom_C]
    | add p r hp hr =>
      obtain ⟨u, n, hu⟩ := hp
      obtain ⟨v, m, hv⟩ := hr
      refine ⟨u * D ^ m + v * D ^ n, n + m, ?_⟩
      simp only [map_add, map_mul, map_pow, hu, hv, pow_add]
      change d ^ n * q p * d ^ m + d ^ m * q r * d ^ n =
        d ^ n * d ^ m * (q p + q r)
      ring
    | mul_X p i hp =>
      obtain ⟨u, n, hu⟩ := hp
      refine ⟨u * N i, n + 1, ?_⟩
      simp only [map_mul, hu, hX, pow_succ]
      ring
  let t := Ideal.Quotient.mk J D
  let L := Localization.Away d
  let : IsLocalization.Away (F t) L := by
    change IsLocalization.Away d L
    infer_instance
  let G := IsLocalization.Away.mapₐ (R := GeoField) (Localization.Away t) L F t
  have hsurj : Function.Surjective G := by
    apply (IsLocalization.Away.map_surjective_iff _ _ F.toRingHom t).mpr
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨u, n, hu⟩ := hclear p
    refine ⟨Ideal.Quotient.mk J u, n, ?_⟩
    change F (Ideal.Quotient.mk J u) = F (Ideal.Quotient.mk J D) ^ n * q p
    rw [hF, hF]
    exact hu
  let : I.IsPrime := hA
  have hreg : IsLeftRegular d := IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    (mt Ideal.Quotient.eq_zero_iff_mem.mp hD)
  exact natDegree_affineHilbertPolynomial_le_of_surjective_away_away hreg G hsurj
theorem fresh_chart {f : Row 4} (T : FatTaylor f) {A : CoeffIdeal}
    (hA : ActualFamily f A) : FreshChart f T A := by
  let : Algebra Geom GeoField := geomConstants.toAlgebra
  have hp : (extendIdeal A).IsPrime := K1_13_6_3_5_2.isPrime_map A hA.prime
  have hd := congrArg Polynomial.natDegree (K1_13_5_5_2.hilbertPolynomial_map (E := GeoField) A)
  obtain ⟨hf, hs, ht, hD, hN⟩ := fresh_identities T hA
  exact ⟨hp, (dimension_of_recovery hp _ _ hD hN).trans hd, hf, hs, ht, hD, hN⟩
end
end Low48FatCount_2_3
end
section
set_option autoImplicit false
namespace Low48FatCount_2_3
noncomputable section
open P3 (K)
open Low48Price (physicalDegree taylorLength)
open Low48FatCount_2 (CoeffRing)
open K1_13 (Geom embed extend)
open K1_13_6 (Pieces CurveSections SurfaceSections)
open K1_13_6_3 (dimension)
open K1_13_7_2 (ThreefoldSections)
open Polynomial MvPolynomial
open scoped BigOperators
def markPoint (s : K → K[X]) (γ : K) : Fin taylorLength → Geom :=
  fun i => (extend (s γ)).coeff i.val
theorem markPoint_inj {Γ : Finset K} {s : K → K[X]}
    (hs : Set.InjOn s (Γ : Set K)) (hd : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree) :
    Set.InjOn (markPoint s) (Γ : Set K) := by
  intro α hα β hβ he
  apply hs hα hβ
  apply Polynomial.ext
  intro n
  by_cases hn : n < taylorLength
  · have hc := congrFun he ⟨n, hn⟩
    exact embed.injective (by simpa only [markPoint, Polynomial.coeff_map] using hc)
  · have hlt : physicalDegree < n := by
      exact Nat.lt_of_succ_le (Nat.le_of_not_gt hn)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hd α hα).trans_lt hlt),
      Polynomial.coeff_eq_zero_of_natDegree_lt ((hd β hβ).trans_lt hlt)]
def valueCut (x a : K) : CoeffRing := jetLinear (embed x) 0 - MvPolynomial.C (embed a)
theorem valueCut_degree (x a : K) : (valueCut x a).totalDegree ≤ 1 := by
  unfold valueCut jetLinear
  apply (totalDegree_sub _ _).trans
  simp only [totalDegree_C, Nat.max_zero]
  exact totalDegree_finsetSum_le (fun j _ =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X, zero_add]))
private theorem valueJet_eval {m : ℕ} {S : K[X]} {x : K} (h : S.natDegree < m) :
    aeval (fun j : Fin m => (extend S).coeff j.val)
      (∑ j : Fin m, MvPolynomial.C ((j.val.choose 0 : Geom) * (embed x) ^ (j.val - 0)) *
        MvPolynomial.X j) = embed (S.eval x) := by
  rw [Polynomial.eval_eq_sum_range' h, ← Fin.sum_univ_eq_sum_range, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Algebra.algebraMap_self_apply, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul,
    Polynomial.coeff_map]
  exact mul_comm _ _
theorem valueCut_eval {s : K → K[X]} {γ x a : K} (h : (s γ).natDegree < taylorLength) :
    aeval (markPoint s γ) (valueCut x a) = 0 ↔ (s γ).eval x = a := by
  have heval : aeval (markPoint s γ) (jetLinear (embed x) 0) = embed ((s γ).eval x) :=
    valueJet_eval h
  rw [valueCut, map_sub, heval, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, sub_eq_zero, embed.injective.eq_iff]
def degreeAllowance (A : CoeffIdeal) : ℕ := ⌊affineDegree A⌋₊
theorem degreeAllowance_le (A : CoeffIdeal) : (degreeAllowance A : ℚ) ≤ affineDegree A :=
  Nat.floor_le (affineDegree_nonneg A)
private theorem degree_at_point {A : CoeffIdeal} (hp : A.IsPrime)
    {x : Fin taylorLength → Geom} (hx : x ∈ zeroLocus Geom A) : 1 ≤ affineDegree A := by
  classical
  generalize hd : dimension A = d
  induction d using Nat.strong_induction_on generalizing A with
  | h d ih =>
    by_cases hd0 : d = 0
    · obtain ⟨hf, hdeg⟩ := finite_zeroLocus_and_ncard_le_affineDegree
        (K := Geom) A (hd.trans hd0)
      have hcard : 1 ≤ (zeroLocus Geom A).ncard := by
        simpa using Set.ncard_le_ncard (Set.singleton_subset_iff.mpr hx) hf
      exact (by exact_mod_cast hcard : (1 : ℚ) ≤ _).trans hdeg
    have hcut : ∃ i, MvPolynomial.X i - MvPolynomial.C (x i) ∉ A := by
      by_contra! hall
      let φ := Ideal.Quotient.mk A
      have hmaps : φ = φ.comp (MvPolynomial.C.comp (MvPolynomial.eval x)) := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [φ]
        · intro i
          simp only [RingHom.comp_apply, MvPolynomial.eval_X]
          exact sub_eq_zero.mp (by
            rw [← map_sub]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (hall i))
      have hsurj : Function.Surjective (algebraMap Geom (CoeffRing ⧸ A)) := by
        intro q
        obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
        refine ⟨MvPolynomial.eval x g, ?_⟩
        exact (RingHom.congr_fun hmaps g).symm
      let _ : Module.Finite Geom (CoeffRing ⧸ A) :=
        Module.Finite.of_surjective (Algebra.linearMap Geom (CoeffRing ⧸ A)) hsurj
      exact hd0 (hd.symm.trans (by simp [dimension, affineHilbertPolynomial_eq_C_finrank]))
    obtain ⟨i, hi⟩ := hcut
    let cut : CoeffRing := MvPolynomial.X i - MvPolynomial.C (x i)
    have hdeg : cut.totalDegree ≤ 1 := (totalDegree_sub _ _).trans (by simp)
    have hzero : x ∈ zeroLocus Geom (A ⊔ Ideal.span {cut}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hx, by simp [cut]⟩
    obtain ⟨B, hB, hxB⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus
      _ (1 : CoeffRing) _ hzero (by simp)
    have hm := (Ideal.mem_retainedMinimalPrimes.mp hB).1
    let _ := hp
    have hdim := principalCut_natDegree_affineHilbertPolynomial_add_one hi hm
    change dimension B + 1 = dimension A at hdim
    have hBdeg := ih (dimension B) (by omega) hm.isPrime hxB rfl
    have hsum := principalCut_sum_affineDegree_retainedMinimalPrimes_le
      (1 : CoeffRing) hi hdeg
    have hle := Finset.single_le_sum (f := affineDegree) (fun B _ => affineDegree_nonneg B) hB
    simpa only [Nat.cast_one, one_mul] using hBdeg.trans (hle.trans hsum)
def marksOn (Γ : Finset K) (s : K → K[X]) (A : CoeffIdeal) : Finset K := by
  classical
  exact Γ.filter fun γ => markPoint s γ ∈ zeroLocus Geom A
theorem mem_marksOn {Γ : Finset K} {s : K → K[X]} {A : CoeffIdeal} {γ : K} :
    γ ∈ marksOn Γ s A ↔ γ ∈ Γ ∧ markPoint s γ ∈ zeroLocus Geom A := by
  classical
  simp [marksOn]
theorem degreeAllowance_pos {Γ : Finset K} {s : K → K[X]} {A : CoeffIdeal}
    (hp : A.IsPrime) (h : (marksOn Γ s A).Nonempty) : 0 < degreeAllowance A := by
  obtain ⟨γ, hγ⟩ := h
  exact Nat.floor_pos.mpr (degree_at_point hp (mem_marksOn.mp hγ).2)
def piecesOf {Γ : Finset K} (T : Finset CoeffIdeal) (part : CoeffIdeal → Finset K)
    (hpart : ∀ A ∈ T, part A ⊆ Γ) : Pieces Γ :=
  ⟨T.card, fun i => part (T.equivFin.symm i),
    fun i => hpart _ (T.equivFin.symm i).property, fun i => degreeAllowance (T.equivFin.symm i)⟩
theorem mem_piecesOf {Γ : Finset K} {T : Finset CoeffIdeal} {part : CoeffIdeal → Finset K}
    {hpart : ∀ A ∈ T, part A ⊆ Γ} {γ : K} :
    γ ∈ (piecesOf T part hpart).union ↔ ∃ A ∈ T, γ ∈ part A := by
  classical
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
    exact ⟨T.equivFin.symm i, (T.equivFin.symm i).property, hi⟩
  · rintro ⟨A, hA, hγ⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨T.equivFin ⟨A, hA⟩, Finset.mem_univ _, ?_⟩
    simpa [piecesOf] using hγ
theorem piecesOf_total {Γ : Finset K} {T : Finset CoeffIdeal} {part : CoeffIdeal → Finset K}
    {hpart : ∀ A ∈ T, part A ⊆ Γ} :
    (piecesOf T part hpart).total = ∑ A ∈ T, degreeAllowance A := by
  change ∑ i : Fin T.card, degreeAllowance (T.equivFin.symm i) = _
  calc
    _ = ∑ A : T, degreeAllowance A := Fintype.sum_equiv T.equivFin.symm _ _ (fun _ => rfl)
    _ = _ := Finset.sum_attach T degreeAllowance
theorem piecesOf_le_degree {Γ : Finset K} {T : Finset CoeffIdeal} {part : CoeffIdeal → Finset K}
    {hpart : ∀ A ∈ T, part A ⊆ Γ} :
    ((piecesOf T part hpart).total : ℚ) ≤ ∑ A ∈ T, affineDegree A := by
  rw [piecesOf_total, Nat.cast_sum]
  exact Finset.sum_le_sum fun A _ => degreeAllowance_le A
private theorem proper_cut {Γ : Finset K} {s : K → K[X]} {A : CoeffIdeal} {x a : K}
    (hdegree : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength)
    (hpoints : ∀ γ ∈ Γ, markPoint s γ ∈ zeroLocus Geom A)
    (hmiss : ∃ γ ∈ Γ, (s γ).eval x ≠ a) : valueCut x a ∉ A := by
  obtain ⟨γ, hγ, hmiss⟩ := hmiss
  exact fun hmem => hmiss (valueCut_eval (hdegree γ hγ) |>.mp (hpoints γ hγ _ hmem))
private theorem mark_on_cut {s : K → K[X]} {A : CoeffIdeal} {x a γ : K}
    (hdegree : (s γ).natDegree < taylorLength) (hpoint : markPoint s γ ∈ zeroLocus Geom A)
    (hvalue : (s γ).eval x = a) :
    markPoint s γ ∈ zeroLocus Geom (A ⊔ Ideal.span {valueCut x a}) :=
  mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hpoint, (valueCut_eval hdegree).mpr hvalue⟩
theorem curveSections_of_prime {Γ : Finset K} {s : K → K[X]} {A : CoeffIdeal}
    (hp : A.IsPrime) (hdim : dimension A = 1)
    (hdegree : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength)
    (hdistinct : Set.InjOn (markPoint s) (Γ : Set K))
    (hpoints : ∀ γ ∈ Γ, markPoint s γ ∈ zeroLocus Geom A) :
    CurveSections Γ s (degreeAllowance A) := by
  classical
  let _ := hp
  intro x a hmiss
  let cut := valueCut x a
  let J := A ⊔ Ideal.span {cut}
  let H := Γ.filter fun γ => (s γ).eval x = a
  have hproper := proper_cut hdegree hpoints hmiss
  have hJdim : dimension J = 0 := by
    have hd := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hp hproper (valueCut_degree x a)).1
    change dimension J ≤ dimension A - 1 at hd
    omega
  have hJdeg : affineDegree J ≤ affineDegree A := by
    have h := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hp hproper (valueCut_degree x a)).2
    have ha : (affineHilbertPolynomial A).natDegree = 1 := hdim
    have hj : (affineHilbertPolynomial J).natDegree = 0 := hJdim
    simpa [affineDegree, ha, hj, J, cut, Polynomial.leadingCoeff] using h
  obtain ⟨hfinite, hcard⟩ := finite_zeroLocus_and_ncard_le_affineDegree (K := Geom) J hJdim
  have hsub : (H.image (markPoint s) : Set _) ⊆ zeroLocus Geom J := by
    intro p hp
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hΓ, hv⟩ := Finset.mem_filter.mp hγ
    exact mark_on_cut (hdegree γ hΓ) (hpoints γ hΓ) hv
  have hcount := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, Finset.card_image_of_injOn
    (hdistinct.mono (Finset.filter_subset _ _))] at hcount
  exact Nat.le_floor ((Nat.cast_le.mpr hcount).trans (hcard.trans hJdeg))
theorem surfaceSections_of_prime {Γ : Finset K} {s : K → K[X]} {A : CoeffIdeal}
    (hp : A.IsPrime) (hdim : dimension A = 2)
    (hdegree : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength)
    (hdistinct : Set.InjOn (markPoint s) (Γ : Set K))
    (hpoints : ∀ γ ∈ Γ, markPoint s γ ∈ zeroLocus Geom A) :
    SurfaceSections Γ s (degreeAllowance A) := by
  classical
  let _ := hp
  intro x a hmiss H
  let J := A ⊔ Ideal.span {valueCut x a}
  let T := J.minimalPrimesFinset.filter (fun B => (marksOn H s B).Nonempty)
  have hproper := proper_cut hdegree hpoints hmiss
  have hsubset (B : CoeffIdeal) (_ : B ∈ T) : marksOn H s B ⊆ H :=
    fun _ h => (mem_marksOn.mp h).1
  have hprime (B : CoeffIdeal) (hB : B ∈ T) : J.IsMinimalPrime B :=
    Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp hB).1
  refine ⟨piecesOf T (marksOn H s) hsubset, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨hΓ, hvalue⟩ := Finset.mem_filter.mp hγ
    have hzero : markPoint s γ ∈ zeroLocus Geom J :=
      mark_on_cut (hdegree γ hΓ) (hpoints γ hΓ) hvalue
    obtain ⟨B, hB, hxB⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus
      J (1 : CoeffRing) _ hzero (by simp)
    have hmarks : γ ∈ marksOn H s B := mem_marksOn.mpr ⟨hγ, hxB⟩
    exact mem_piecesOf.mpr ⟨B, Finset.mem_filter.mpr ⟨Ideal.mem_minimalPrimesFinset.mpr
      (Ideal.mem_retainedMinimalPrimes.mp hB).1, ⟨γ, hmarks⟩⟩, hmarks⟩
  · intro i
    let B := T.equivFin.symm i
    have hm := hprime B B.property
    have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hproper hm
    change dimension (B : CoeffIdeal) + 1 = dimension A at hd
    have hdimB : dimension (B : CoeffIdeal) = 1 := by omega
    apply curveSections_of_prime hm.isPrime hdimB
    · exact fun γ hγ => hdegree γ (Finset.mem_filter.mp (mem_marksOn.mp hγ).1).1
    · exact hdistinct.mono (fun γ hγ => (Finset.mem_filter.mp (mem_marksOn.mp hγ).1).1)
    · exact fun _ hγ => (mem_marksOn.mp hγ).2
  · intro i
    let B := T.equivFin.symm i
    exact degreeAllowance_pos (hprime B B.property).isPrime
      (Finset.mem_filter.mp B.property).2
  · apply Nat.le_floor
    have hsum := principalCut_sum_affineDegree_minimalPrimes_le hproper (valueCut_degree x a)
    exact piecesOf_le_degree.trans ((Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun B _ _ => affineDegree_nonneg B)).trans
      (by simpa only [Nat.cast_one, one_mul] using hsum))
theorem threefoldSections_of_prime {Γ : Finset K} {s : K → K[X]} {A : CoeffIdeal}
    (hp : A.IsPrime) (hdim : dimension A = 3)
    (hd : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength)
    (hinj : Set.InjOn (markPoint s) (Γ : Set K))
    (hpoint : ∀ γ ∈ Γ, markPoint s γ ∈ zeroLocus Geom A) :
    ThreefoldSections Γ s (degreeAllowance A) := by
  classical
  let _ := hp
  intro x a hmiss H
  let J := A ⊔ Ideal.span {valueCut x a}
  let S := J.minimalPrimesFinset.filter (fun B => (marksOn H s B).Nonempty)
  have hproper : valueCut x a ∉ A := by
    obtain ⟨γ, hγ, h⟩ := hmiss
    exact fun hm => h ((valueCut_eval (hd γ hγ)).mp (hpoint γ hγ _ hm))
  have hsub (B : CoeffIdeal) (_ : B ∈ S) : marksOn H s B ⊆ H := fun _ h => (mem_marksOn.mp h).1
  have hprime (B : CoeffIdeal) (hB : B ∈ S) : J.IsMinimalPrime B :=
    Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp hB).1
  refine ⟨piecesOf S (marksOn H s) hsub, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨hΓ, hvalue⟩ := Finset.mem_filter.mp hγ
    have hz : markPoint s γ ∈ zeroLocus Geom J :=
      mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hpoint γ hΓ, (valueCut_eval (hd γ hΓ)).mpr hvalue⟩
    obtain ⟨B, hB, hxB⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus J
      (1 : CoeffRing) _ hz (by simp)
    have hmarks := mem_marksOn.mpr ⟨hγ, hxB⟩
    exact mem_piecesOf.mpr ⟨B, Finset.mem_filter.mpr ⟨Ideal.mem_minimalPrimesFinset.mpr
      (Ideal.mem_retainedMinimalPrimes.mp hB).1, ⟨γ, hmarks⟩⟩, hmarks⟩
  · intro i
    let B := S.equivFin.symm i
    have hm := hprime B B.property
    have hdimB := principalCut_natDegree_affineHilbertPolynomial_add_one hproper hm
    change dimension (B : CoeffIdeal) + 1 = dimension A at hdimB
    have hdimB' : dimension (B : CoeffIdeal) = 2 := by omega
    apply surfaceSections_of_prime hm.isPrime hdimB'
    · exact fun γ hγ => hd γ (Finset.mem_filter.mp (mem_marksOn.mp hγ).1).1
    · exact hinj.mono (fun γ hγ => (Finset.mem_filter.mp (mem_marksOn.mp hγ).1).1)
    · exact fun _ hγ => (mem_marksOn.mp hγ).2
  · intro i
    let B := S.equivFin.symm i
    exact degreeAllowance_pos (hprime B B.property).isPrime (Finset.mem_filter.mp B.property).2
  · apply Nat.le_floor
    have hsum := principalCut_sum_affineDegree_minimalPrimes_le hproper (valueCut_degree x a)
    exact piecesOf_le_degree.trans ((Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun B _ _ => affineDegree_nonneg B)).trans
      (by simpa only [Nat.cast_one, one_mul] using hsum))
end
end Low48FatCount_2_3
end
section
set_option autoImplicit false
namespace Low48FatCount_2_3
noncomputable section
open Polynomial
open P3 (K)
open Low48Price (physicalDegree taylorLength SmallFactor)
open Low48FatPad (membershipTest)
open Low48FatCount (fatChart)
open Low48FatCount_2 (CoeffRing FatTaylor ActualFamily IntegratedMark coefficientPointIdeal)
open K1_13 (Row Geom extend shape)
open K1_13_6 (Pieces toGeneric separant divisorIdeal)
open K1_13_6_3 (JetIdeal dimension)
open K1_13_7_2_5 (wholeComponents properComponents)
open P0_9_7_2_3 (whole_dimension whole_sum)
open scoped BigOperators
def c1 : Prop :=
  ∀ (f : Row 4), SmallFactor f → ∀ (component : JetIdeal),
    (Ideal.span {toGeneric f}).IsMinimalPrime component → toGeneric (separant f) ∉ component →
    toGeneric (membershipTest f) ∈ component →
    ∃ A : CoeffIdeal, ActualFamily f A ∧ freshImage A ≤ component
def c2 : Prop :=
  ∀ A : CoeffIdeal, A.IsPrime → (extendIdeal A).IsPrime →
    dimension A = 2 → FreshBirational A →
    2 * MvPolynomial.affineDegree A ≤
      (physicalDegree : ℚ) * MvPolynomial.affineDegree (freshImage A)
def c3 : Prop :=
  ∀ (f : Row 4) (T : FatTaylor f) (A : CoeffIdeal), ActualFamily f A → FreshChart f T A →
    dimension A = 3 →
    MvPolynomial.affineDegree A ≤ MvPolynomial.affineDegree (freshImage A) *
      ((fatChart (shape f)).b : ℚ) ^ 2
open MvPolynomial
private theorem eq_of_le_of_dimension_two {P Q : JetIdeal} (hp : P.IsPrime) (hle : P ≤ Q)
    (hdP : dimension P = 2) (hdQ : 2 ≤ dimension Q) : P = Q := by
  by_contra hne
  have hn : ∃ x, x ∈ Q ∧ x ∉ P := by
    by_contra! hall
    exact hne (le_antisymm hle hall)
  obtain ⟨x, hxQ, hxP⟩ := hn
  have hJ : P ⊔ Ideal.span {x} ≤ Q := sup_le hle (Ideal.span_le.mpr (by simpa using hxQ))
  have hcut := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hp hxP (le_refl x.totalDegree)).1
  have hmon := natDegree_affineHilbertPolynomial_le_of_le hJ
  change dimension (P ⊔ Ideal.span {x}) ≤ dimension P - 1 at hcut
  change dimension Q ≤ dimension (P ⊔ Ideal.span {x}) at hmon
  omega
private def FamilyCase (f : Row 4) (T : FatTaylor f) (A : CoeffIdeal) : Prop :=
  (dimension A = 2 ∧ freshImage A ∈ properComponents f T.test) ∨
    (dimension A = 3 ∧ freshImage A ∈ wholeComponents f)
private theorem family_of_mark (h1 : c1) {f : Row 4} (hf : SmallFactor f)
    (T : FatTaylor f) {S : Geom[X]} (hm : IntegratedMark f S) :
    ∃ A : CoeffIdeal, ActualFamily f A ∧ FamilyCase f T A ∧ A ≤ coefficientPointIdeal S := by
  classical
  obtain ⟨A, ha, hApoint⟩ := hm
  have hA := fresh_chart T ha
  let Q := freshImage A
  let _ : Q.IsPrime := hA.extended_prime.comap freshJetMap
  have hspan : Ideal.span {toGeneric f} ≤ Q := Ideal.span_le.mpr (by simpa using hA.factor)
  obtain ⟨component, hZ, hZle⟩ := Ideal.exists_minimalPrimes_le hspan
  let _ := hZ.isPrime
  have hfZ : toGeneric f ∈ component := hZ.le (Ideal.subset_span (by simp))
  have hreg : toGeneric (separant f) ∉ component := fun h => hA.regular (hZle h)
  have hdimZ := whole_dimension hf.1 hZ
  by_cases ht : toGeneric T.test ∈ component
  · have htest := (T.test_iff component hZ.isPrime hfZ hreg).mp ht
    obtain ⟨B, hb, hBle⟩ := h1 f hf component hZ hreg htest
    have hB := fresh_chart T hb
    have hmin : Minimal (fun P : JetIdeal => P.IsPrime ∧ Ideal.span {toGeneric f} ≤ P)
        component := hZ
    have heq : freshImage B = component := Minimal.eq_of_le hmin
      ⟨hB.extended_prime.comap freshJetMap, Ideal.span_le.mpr (by simpa using hB.factor)⟩ hBle
    have hBA : B ≤ A := le_of_freshImage_le hB hA ha.prime (hBle.trans hZle)
    have hdimB : dimension B = 3 := by rw [← hB.dimension_eq, heq, hdimZ]
    have hmem : freshImage B ∈ wholeComponents f := by
      rw [heq]
      exact Ideal.mem_minimalPrimesFinset.mpr hZ
    exact ⟨B, hb, Or.inr ⟨hdimB, hmem⟩, hBA.trans hApoint⟩
  · have hcut : divisorIdeal component T.test ≤ Q :=
      sup_le hZle (Ideal.span_le.mpr (by simpa using hA.test))
    obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hcut
    have hdimP := principalCut_natDegree_affineHilbertPolynomial_add_one ht hP
    change dimension P + 1 = dimension component at hdimP
    have hp : dimension P = 2 := by omega
    have hdimQ : 2 ≤ dimension Q := by
      change 2 ≤ dimension (freshImage A)
      rw [hA.dimension_eq]
      exact ha.dimension
    have heq : P = Q := eq_of_le_of_dimension_two hP.isPrime hPle hp hdimQ
    have hdimA : dimension A = 2 := by
      rw [← hA.dimension_eq]
      change dimension Q = 2
      rwa [← heq]
    refine ⟨A, ha, Or.inl ⟨hdimA, ?_⟩, hApoint⟩
    change Q ∈ properComponents f T.test
    rw [← heq]
    exact Finset.mem_biUnion.mpr ⟨component,
      Finset.mem_filter.mpr ⟨Ideal.mem_minimalPrimesFinset.mpr hZ, ht⟩,
      Ideal.mem_minimalPrimesFinset.mpr hP⟩
private theorem sum_fresh_le (S : Finset CoeffIdeal) (V : Finset JetIdeal)
    (hinj : Set.InjOn freshImage (S : Set CoeffIdeal))
    (hV : ∀ A ∈ S, freshImage A ∈ V) :
    ∑ A ∈ S, affineDegree (freshImage A) ≤ ∑ P ∈ V, affineDegree P := by
  classical
  have hsub : S.image freshImage ⊆ V := by
    intro P hp
    obtain ⟨A, ha, rfl⟩ := Finset.mem_image.mp hp
    exact hV A ha
  calc
    _ = ∑ P ∈ S.image freshImage, affineDegree P := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun P _ _ => affineDegree_nonneg P)
private theorem mem_marks_of_le {Γ : Finset K} {s : K → K[X]} {A : CoeffIdeal} {γ : K}
    (hγ : γ ∈ Γ) (hle : A ≤ coefficientPointIdeal (extend (s γ))) : γ ∈ marksOn Γ s A := by
  refine mem_marksOn.mpr ⟨hγ, ?_⟩
  intro g hg
  exact RingHom.mem_ker.mp (hle hg)
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : Low48FatCount_2.c3 := by
  classical
  intro Γ s f hf _helig T hdistinct hdegree _hon
  let M := Γ.filter (fun γ => IntegratedMark f (extend (s γ)))
  have hw (γ : M) : ∃ A : CoeffIdeal, ActualFamily f A ∧ FamilyCase f T A ∧
      γ.val ∈ marksOn Γ s A := by
    obtain ⟨hγ, hmark⟩ := Finset.mem_filter.mp γ.property
    obtain ⟨A, ha, hc, hp⟩ := family_of_mark h1 hf T hmark
    exact ⟨A, ha, hc, mem_marks_of_le hγ hp⟩
  let A : M → CoeffIdeal := fun γ => Classical.choose (hw γ)
  have hA (γ : M) : ActualFamily f (A γ) ∧ FamilyCase f T (A γ) ∧ γ.val ∈ marksOn Γ s (A γ) :=
    Classical.choose_spec (hw γ)
  let U := M.attach.image A
  let U₂ := U.filter (fun B => dimension B = 2)
  let U₃ := U.filter (fun B => dimension B = 3)
  have hU (B : CoeffIdeal) (hB : B ∈ U) :
      ActualFamily f B ∧ FamilyCase f T B ∧ (marksOn Γ s B).Nonempty := by
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hB
    exact ⟨(hA γ).1, (hA γ).2.1, ⟨γ.val, (hA γ).2.2⟩⟩
  have hV₂ (B : CoeffIdeal) (hB : B ∈ U₂) : freshImage B ∈ properComponents f T.test := by
    obtain ⟨hBU, hd⟩ := Finset.mem_filter.mp hB
    rcases (hU B hBU).2.1 with h | h
    · exact h.2
    · have := h.1
      omega
  have hV₃ (B : CoeffIdeal) (hB : B ∈ U₃) : freshImage B ∈ wholeComponents f := by
    obtain ⟨hBU, hd⟩ := Finset.mem_filter.mp hB
    rcases (hU B hBU).2.1 with h | h
    · have := h.1
      omega
    · exact h.2
  have hinj : Set.InjOn freshImage (U : Set CoeffIdeal) := by
    intro B hB D hD he
    have hBp := (hU B hB).1
    have hDp := (hU D hD).1
    have hBm := fresh_chart T hBp
    have hDm := fresh_chart T hDp
    exact le_antisymm (le_of_freshImage_le hBm hDm hDp.prime he.le)
      (le_of_freshImage_le hDm hBm hBp.prime he.ge)
  have hpart (B : CoeffIdeal) : marksOn Γ s B ⊆ Γ := fun _ hγ => (mem_marksOn.mp hγ).1
  let C := piecesOf U₂ (marksOn Γ s) (fun B _ => hpart B)
  let F := piecesOf U₃ (marksOn Γ s) (fun B _ => hpart B)
  have hd (γ : K) (hγ : γ ∈ Γ) : (s γ).natDegree < taylorLength := Nat.lt_succ_of_le (hdegree γ hγ)
  have hpoints (B : CoeffIdeal) : ∀ γ ∈ marksOn Γ s B, markPoint s γ ∈ zeroLocus Geom B :=
    fun _ hγ => (mem_marksOn.mp hγ).2
  have hpointInj := markPoint_inj hdistinct hdegree
  refine ⟨C, F, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    let B := U₂.equivFin.symm i
    obtain ⟨hBU, hdim⟩ := Finset.mem_filter.mp B.property
    exact surfaceSections_of_prime (hU B hBU).1.prime hdim
      (fun γ hγ => hd γ (hpart B hγ)) (hpointInj.mono (hpart B)) (hpoints B)
  · intro i
    let B := U₃.equivFin.symm i
    obtain ⟨hBU, hdim⟩ := Finset.mem_filter.mp B.property
    exact threefoldSections_of_prime (hU B hBU).1.prime hdim
      (fun γ hγ => hd γ (hpart B hγ)) (hpointInj.mono (hpart B)) (hpoints B)
  · intro i
    let B := U₂.equivFin.symm i
    have h := hU B (Finset.mem_filter.mp B.property).1
    exact degreeAllowance_pos h.1.prime h.2.2
  · intro i
    let B := U₃.equivFin.symm i
    have h := hU B (Finset.mem_filter.mp B.property).1
    exact degreeAllowance_pos h.1.prime h.2.2
  · intro γ hγ hm
    let γ' : M := ⟨γ, Finset.mem_filter.mpr ⟨hγ, hm⟩⟩
    have hmem : A γ' ∈ U := Finset.mem_image_of_mem A (Finset.mem_attach _ _)
    rcases (hA γ').2.1 with h | h
    · exact Finset.mem_union_left _ (mem_piecesOf.mpr
        ⟨_, Finset.mem_filter.mpr ⟨hmem, h.1⟩, (hA γ').2.2⟩)
    · exact Finset.mem_union_right _ (mem_piecesOf.mpr
        ⟨_, Finset.mem_filter.mpr ⟨hmem, h.1⟩, (hA γ').2.2⟩)
  · have hsum := sum_fresh_le U₂ (properComponents f T.test)
      (hinj.mono (Finset.filter_subset _ _)) hV₂
    have hb : 2 * (C.total : ℚ) ≤
        (physicalDegree : ℚ) * (shape f).chamber.b * (fatChart (shape f)).b := calc
      _ ≤ 2 * ∑ B ∈ U₂, affineDegree B :=
        mul_le_mul_of_nonneg_left (piecesOf_le_degree (T := U₂) (part := marksOn Γ s)) (by positivity)
      _ ≤ ∑ B ∈ U₂, (physicalDegree : ℚ) * affineDegree (freshImage B) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun B hB => ?_
        obtain ⟨hBU, hdim⟩ := Finset.mem_filter.mp hB
        have h := (hU B hBU).1
        have hb := fresh_chart T h
        exact h2 B h.prime hb.extended_prime hdim (fresh_birational hb)
      _ = (physicalDegree : ℚ) * ∑ B ∈ U₂, affineDegree (freshImage B) := (Finset.mul_sum ..).symm
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hsum.trans (proper_sum hf.1 T)) (by positivity)
    exact_mod_cast hb
  · let b := ((fatChart (shape f)).b : ℚ)
    have hsum := sum_fresh_le U₃ (wholeComponents f)
      (hinj.mono (Finset.filter_subset _ _)) hV₃
    have hb : (F.total : ℚ) ≤ ((shape f).chamber.b : ℚ) * b ^ 2 := calc
      _ ≤ ∑ B ∈ U₃, affineDegree B := piecesOf_le_degree
      _ ≤ ∑ B ∈ U₃, affineDegree (freshImage B) * b ^ 2 := by
        refine Finset.sum_le_sum fun B hB => ?_
        obtain ⟨hBU, hdim⟩ := Finset.mem_filter.mp hB
        have h := (hU B hBU).1
        exact h3 f T B h (fresh_chart T h) hdim
      _ = (∑ B ∈ U₃, affineDegree (freshImage B)) * b ^ 2 := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hsum.trans (whole_sum hf.1)) (by positivity)
    dsimp only [b] at hb
    exact_mod_cast hb
end
end Low48FatCount_2_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Low48FatCount_2_3_1
noncomputable section
open Polynomial
open K1_13 (Row)
open K1_13_6 (GeoField GeoJets toGeneric separant Invariant flowNumerator)
open K1_13_6_3 (JetIdeal JetField dimension geomConstants genericArgument
  onComponent componentConstants trajectory)
open K1_13_7_2_4 (contraction chartPolynomial genericLift genericLift_onChart chartCenter
  eval_hasse_chartPolynomial)
open Low48Price (taylorLength)
open Low48FatCount_2 (universalEval)
open Low48FatCount_2_3 (CoeffIdeal FreshCoeffRing jetLinear extendIdeal freshJetMap freshImage)
open P0_9_7_2_3 (generic_ne_zero whole_dimension)
open Low48FatCount_2_2 (chart_degree solves_fresh retunedEval map_universal)
open private trajectory_at_component component_ne_zero from ProximityPrize.SubmissionLower.Fast066
private theorem whole_contraction {f : Row 4} (hf : Irreducible f) {P : JetIdeal}
    (hP : (Ideal.span {toGeneric f}).IsMinimalPrime P) :
    contraction P = Ideal.span {f} := by
  let : P.IsPrime := hP.isPrime
  have hmem : toGeneric f ∈ P := hP.le (Ideal.subset_span (Set.mem_singleton _))
  have hne : P ≠ ⊥ := fun h => generic_ne_zero hf (Ideal.mem_bot.mp (h ▸ hmem))
  have hheight : P.height = 1 := by
    apply le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)
    exact Order.one_le_iff_ne_zero.mpr (fun h => hne (Ideal.height_eq_zero_iff_eq_bot.mp h))
  obtain ⟨r, hrP, hr⟩ := hP.isPrime.exists_mem_prime_of_ne_bot hne
  have he := P.eq_span_singleton_of_height_eq_one hheight hrP hr
  have hrf : r ∣ toGeneric f := Ideal.mem_span_singleton.mp (he ▸ hmem)
  obtain ⟨a, ha, haeq⟩ := K1_13_7_2_1.comap_span_prime hr hf.ne_zero hrf
  have hc : contraction P = Ideal.span {a} := by
    rw [contraction, he, haeq]
  have had : a ∣ f := Ideal.mem_span_singleton.mp (hc ▸ (show f ∈ contraction P from hmem))
  have hassoc := ha.irreducible.associated_of_dvd hf had
  exact hc.trans (le_antisymm
    (Ideal.span_singleton_le_span_singleton.mpr hassoc.dvd')
    (Ideal.span_singleton_le_span_singleton.mpr hassoc.dvd))
private theorem whole_invariant {f : Row 4} (hf : Irreducible f) {P : JetIdeal}
    (hP : (Ideal.span {toGeneric f}).IsMinimalPrime P) : Invariant f P := by
  have hc := whole_contraction hf hP
  intro Q hQ
  have hmem : Q ∈ contraction P := hQ
  rw [hc, Ideal.mem_span_singleton] at hmem
  obtain ⟨R, rfl⟩ := hmem
  change flowNumerator f (f * R) ∈ contraction P
  rw [hc, K1_13_7_2_1.flow_mul, K1_13_7_2_1.flow_self, mul_zero, add_zero,
    Ideal.mem_span_singleton]
  exact dvd_mul_right _ _
private def componentScalars (P : JetIdeal) : GeoField →+* JetField P :=
  (onComponent P).comp MvPolynomial.C
private def sourceEval (P : JetIdeal) [P.IsPrime] (U : (JetField P)[X]) :
    FreshCoeffRing →+* JetField P :=
  MvPolynomial.eval₂Hom (componentScalars P) (fun j => U.coeff j.val)
private theorem eval_jet_sum {F L : Type*} [Field F] [Field L]
    (M : ℕ) (k : F →+* L) (x : F) {U : L[X]} (hd : U.natDegree < M) (i : ℕ) :
    (MvPolynomial.eval₂Hom k (fun j : Fin M => U.coeff j.val))
      (∑ j : Fin M, MvPolynomial.C ((j.val.choose i : F) * x ^ (j.val - i)) *
        MvPolynomial.X j) =
      (hasseDeriv i U).eval (k x) := by
  have hsum : U = ∑ j : Fin M, monomial j.val (U.coeff j.val) := by
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => monomial n (U.coeff n))]
    exact U.as_sum_range' _ hd
  rw [congrArg (fun V => (hasseDeriv i V).eval (k x)) hsum]
  simp only [map_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hasseDeriv_monomial, eval_monomial, map_mul,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', map_natCast, map_pow]
  ring
private theorem sourceEval_jetLinear (P : JetIdeal) [P.IsPrime] {U : (JetField P)[X]}
    (hd : U.natDegree < taylorLength) (i : ℕ) :
    sourceEval P U (jetLinear genericArgument i) =
      (hasseDeriv i U).eval (componentScalars P genericArgument) :=
  eval_jet_sum _ (componentScalars P) genericArgument hd i
private theorem fresh_le_source (P : JetIdeal) [P.IsPrime] {U : (JetField P)[X]}
    (hd : U.natDegree < taylorLength)
    (hjet : ∀ i : Fin 4, (hasseDeriv i.val U).eval
      (onComponent P (MvPolynomial.C genericArgument)) = onComponent P (MvPolynomial.X i)) :
    freshImage (RingHom.ker (retunedEval (componentConstants P) U)) ≤ P := by
  have hmap : (sourceEval P U).comp (MvPolynomial.map geomConstants) =
      retunedEval (componentConstants P) U := by
    ext a <;> simp [sourceEval, componentScalars, retunedEval, componentConstants]
  have hkill : extendIdeal (RingHom.ker (retunedEval (componentConstants P) U)) ≤
      RingHom.ker (sourceEval P U) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    exact (DFunLike.congr_fun hmap a).trans ha
  have hcomp : (sourceEval P U).comp freshJetMap = onComponent P := by
    ext a
    · simp [sourceEval, freshJetMap, componentScalars]
    · rw [RingHom.comp_apply, freshJetMap, MvPolynomial.eval₂Hom_X', sourceEval_jetLinear P hd]
      exact hjet a
  intro a ha
  have hz : onComponent P a = 0 :=
    (DFunLike.congr_fun hcomp a).symm.trans (hkill ha)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply IsFractionRing.injective (GeoJets ⧸ P) (JetField P)
  exact hz.trans (map_zero _).symm
private theorem fresh_dimension_le (A : CoeffIdeal) : dimension (freshImage A) ≤ dimension A := by
  let φ : GeoJets →ₐ[GeoField] FreshCoeffRing :=
    MvPolynomial.aeval (fun i : Fin 4 => jetLinear genericArgument i.val)
  let ψ := Ideal.quotientMapₐ (extendIdeal A) φ
    (show freshImage A ≤ (extendIdeal A).comap φ.toRingHom from le_rfl)
  have hinj : Function.Injective ψ := Ideal.quotientMap_injective
  let : Algebra K1_13.Geom GeoField := geomConstants.toAlgebra
  have hbase : MvPolynomial.affineHilbertPolynomial (extendIdeal A) =
      MvPolynomial.affineHilbertPolynomial A :=
    K1_13_5_5_2.hilbertPolynomial_map (E := GeoField) A
  exact (MvPolynomial.natDegree_affineHilbertPolynomial_le_of_injective ψ hinj).trans_eq
    (congrArg Polynomial.natDegree hbase)
theorem proof : Low48FatCount_2_3.c1 := by
  intro f hf P hP hs htest
  let : P.IsPrime := hP.isPrime
  have hfP : toGeneric f ∈ P := hP.le (Ideal.subset_span (Set.mem_singleton _))
  have hinv := whole_invariant hf.1 hP
  obtain ⟨δ, hδ⟩ := K1_13_7_2_4_1.proof f P hP.isPrime hs hinv
  let U := (chartPolynomial f P).map (genericLift f P hs)
  have hd : U.natDegree < taylorLength :=
    Nat.lt_succ_of_le (Polynomial.natDegree_map_le.trans (chart_degree hinv htest))
  have hjet (i : Fin 4) :
      (hasseDeriv i.val U).eval (onComponent P (MvPolynomial.C genericArgument)) =
        onComponent P (MvPolynomial.X i) := by
    simpa only [U, chartCenter, genericLift_onChart, genericArgument,
      toGeneric, MvPolynomial.map_C, MvPolynomial.map_X] using
      eval_hasse_chartPolynomial (genericLift f P hs) i
  have hsolve : trajectory (componentConstants P) f U = 0 :=
    solves_fresh hs hf.2.2.2 hfP hinv htest δ hδ
  have hregular : trajectory (componentConstants P) (separant f) U ≠ 0 := by
    intro hzero
    apply component_ne_zero hs
    rw [← trajectory_at_component P U (separant f) hjet, hzero, eval_zero]
  let e := retunedEval (componentConstants P) U
  let A := RingHom.ker e
  have hAP : freshImage A ≤ P := fresh_le_source P hd hjet
  have hdim : dimension P ≤ dimension A :=
    (MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le hAP).trans (fresh_dimension_le A)
  rw [whole_dimension hf.1 hP] at hdim
  refine ⟨A, ⟨RingHom.ker_isPrime _, (by decide : 2 ≤ 3).trans hdim, ?_, ?_⟩, hAP⟩
  · intro j
    change e ((universalEval f).coeff j) = 0
    rw [← coeff_map, Low48FatCount_2_2.map_universal _ _ hd, hsolve, coeff_zero]
  · obtain ⟨j, hj⟩ := not_forall.mp (mt Polynomial.ext_iff.mpr hregular)
    refine ⟨j, ?_⟩
    change e ((universalEval (separant f)).coeff j) ≠ 0
    rw [← coeff_map, Low48FatCount_2_2.map_universal _ _ hd]
    simpa only [coeff_zero] using hj
end
end Low48FatCount_2_3_1
end
section
set_option autoImplicit false
set_option maxRecDepth 1800
namespace Low48FatCount_2_3_2
noncomputable section
open MvPolynomial
open K1_13 (Geom)
open K1_13_6 (GeoField)
open K1_13_6_3 (dimension geomConstants genericArgument)
open Low48Price (taylorLength)
open Low48FatCount_2_3 (CoeffIdeal extendIdeal freshImage freshJetMap)
open scoped BigOperators
open private restrictVariables restrict_rename padded_hilbert from ProximityPrize.SubmissionLower.PortLow5
private theorem length_le : taylorLength ≤ K1_13.taylorLength := by decide
private theorem drop_map {k E : Type*} [Field k] [Field E] (f : k →+* E)
    {m n : ℕ} :
    (MvPolynomial.aeval (restrictVariables (k := E) (m := m) (n := n))).toRingHom.comp
        (MvPolynomial.map f) =
      (MvPolynomial.map f).comp (MvPolynomial.aeval
        (restrictVariables (k := k) (m := m) (n := n))).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [RingHom.comp_apply]
  · intro i
    by_cases hi : i.val < m <;> simp [RingHom.comp_apply, restrictVariables, hi]
private theorem drop_sum {k : Type*} [Field k] {m n : ℕ} (h : m ≤ n) (c : ℕ → k) :
    MvPolynomial.aeval (restrictVariables (m := m))
        (∑ i : Fin n, C (c i.val) * MvPolynomial.X i) =
      ∑ i : Fin m, C (c i.val) * MvPolynomial.X i := by
  let e : Fin m ↪ Fin n := ⟨Fin.castLE h, Fin.castLE_injective h⟩
  rw [map_sum]
  calc
    _ = ∑ j ∈ Finset.univ.map e, aeval restrictVariables (C (c j.val) * MvPolynomial.X j) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have htail : ¬ j.val < m := fun hl =>
        hj (Finset.mem_map.mpr ⟨⟨j.val, hl⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      simp only [map_mul, aeval_X, restrictVariables, dite_eq_right htail, mul_zero]
    _ = _ := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i _
      simp only [map_mul, aeval_C, algebraMap_eq, aeval_X, restrictVariables,
        e, Function.Embedding.coeFn_mk, Fin.val_castLE, dite_eq_left i.isLt]
private def drop (k : Type) [Field k] :
    MvPolynomial (Fin K1_13.taylorLength) k →ₐ[k] MvPolynomial (Fin taylorLength) k :=
  aeval restrictVariables
private def pad (A : CoeffIdeal) : K1_13_6_3.CoeffIdeal :=
  A.comap (drop Geom)
private theorem pad_support (A : CoeffIdeal) : Low48FatPad.ShortSupport (pad A) := by
  intro i hi
  change drop Geom (MvPolynomial.X i) ∈ A
  rw [drop, aeval_X, restrictVariables, dite_eq_right (not_lt.mpr hi)]
  exact A.zero_mem
private theorem pad_extend (A : CoeffIdeal) :
    K1_13_6_3.extendIdeal (pad A) = (extendIdeal A).comap (drop GeoField) := by
  let B := K1_13_6_3.extendIdeal (pad A)
  let e := Fin.castLE length_le
  have hrename : (extendIdeal A).map (rename (R := GeoField) e) ≤ B := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change rename e (MvPolynomial.map geomConstants p) ∈ B
    rw [← map_rename]
    apply Ideal.mem_map_of_mem
    change aeval restrictVariables (rename (Fin.castLE length_le) p) ∈ A
    rwa [restrict_rename length_le]
  have hq : (Ideal.Quotient.mk B).comp
      ((rename (R := GeoField) e).toRingHom.comp (drop GeoField).toRingHom) =
        Ideal.Quotient.mk B := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [RingHom.comp_apply, drop]
    · intro i
      by_cases hi : i.val < taylorLength
      · have hei : e ⟨i.val, hi⟩ = i := Fin.ext rfl
        simp [RingHom.comp_apply, drop, restrictVariables, hi, hei]
      · have hz : (Ideal.Quotient.mk B) (MvPolynomial.X i) = 0 := by
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          rw [← MvPolynomial.map_X geomConstants]
          exact Ideal.mem_map_of_mem _ (pad_support A i (le_of_not_gt hi))
        simp [RingHom.comp_apply, drop, restrictVariables, hi, hz]
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change drop GeoField (MvPolynomial.map geomConstants p) ∈ extendIdeal A
    rw [show drop GeoField (MvPolynomial.map geomConstants p) =
      MvPolynomial.map geomConstants (drop Geom p) from
      DFunLike.congr_fun (drop_map geomConstants) p]
    exact Ideal.mem_map_of_mem _ hp
  · intro p hp
    have hz : rename e (drop GeoField p) ∈ B :=
      hrename (Ideal.mem_map_of_mem _ hp)
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((DFunLike.congr_fun hq p).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hz))
private theorem drop_jet :
    (drop GeoField).toRingHom.comp K1_13_6_3.freshJetMap = freshJetMap := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [RingHom.comp_apply, drop, K1_13_6_3.freshJetMap, freshJetMap]
  · intro i
    change drop GeoField (K1_13_6_3.freshJetMap (MvPolynomial.X i)) =
      freshJetMap (MvPolynomial.X i)
    rw [K1_13_6_3.freshJetMap, freshJetMap, eval₂Hom_X', eval₂Hom_X']
    unfold drop K1_13_6_3.jetLinear Low48FatCount_2_3.jetLinear
    exact drop_sum (m := taylorLength) (n := K1_13.taylorLength) length_le
      (fun j => (j.choose i.val : GeoField) * genericArgument ^ (j - i.val))
private theorem drop_jet_apply (g : K1_13_6.GeoJets) :
    drop GeoField (K1_13_6_3.freshJetMap g) = freshJetMap g :=
  DFunLike.congr_fun drop_jet g
theorem proof : Low48FatCount_2_3.c2 := by
  intro A hA hAe hdim hbir
  have hh : affineHilbertPolynomial (pad A) = affineHilbertPolynomial A :=
    padded_hilbert length_le A
  have hd : dimension (pad A) = 2 :=
    (congrArg Polynomial.natDegree hh).trans hdim
  have he : (K1_13_6_3.extendIdeal (pad A)).IsPrime := by
    rw [pad_extend]
    exact hAe.comap (drop GeoField)
  have hb : K1_13_6_3.FreshBirational (pad A) := by
    intro p
    obtain ⟨u, v, hv, huv⟩ := hbir (drop GeoField p)
    refine ⟨u, v, ?_, ?_⟩
    · rw [pad_extend, Ideal.mem_comap, drop_jet_apply]
      exact hv
    · rw [pad_extend, Ideal.mem_comap, map_sub, map_mul, drop_jet_apply, drop_jet_apply]
      exact huv
  have him : K1_13_6_3.freshImage (pad A) = freshImage A := by
    rw [K1_13_6_3.freshImage, pad_extend]
    change ((extendIdeal A).comap (drop GeoField).toRingHom).comap
      K1_13_6_3.freshJetMap = freshImage A
    rw [Ideal.comap_comap, drop_jet]
    rfl
  have hdeg : affineDegree (pad A) = affineDegree A := by
    simp only [affineDegree, hh]
  have h := Low48FatPad.padding (pad A) (hA.comap (drop Geom)) he hd hb (pad_support A)
  rw [hdeg, him] at h
  exact h
end
end Low48FatCount_2_3_2
end
section
set_option autoImplicit false
namespace Low48FatCount_2_3_3
noncomputable section
open MvPolynomial
open K1_13 (Geom)
open K1_13_6_3 (dimension geomConstants)
open K1_13_6_3_4 (boundaryChart)
open K1_13_7_2_5_4 (cut saturate)
open Low48Price (taylorLength)
open Low48FatCount_2 (CoeffRing)
open Low48FatCount_2_3 (CoeffIdeal FreshCoeffRing extendIdeal)
structure CoeffHyperplane where
  offset : Geom
  slope : Fin taylorLength → Geom
def CoeffHyperplane.form (H : CoeffHyperplane) : CoeffRing :=
  MvPolynomial.C H.offset + ∑ i, MvPolynomial.C (H.slope i) * MvPolynomial.X i
def CoeffHyperplane.freshForm (H : CoeffHyperplane) : FreshCoeffRing :=
  MvPolynomial.map geomConstants H.form
def coefficientSurface (A : CoeffIdeal) (H : CoeffHyperplane) : CoeffIdeal :=
  cut A H.form
def coefficientCurve (A : CoeffIdeal) (H G : CoeffHyperplane) : CoeffIdeal :=
  cut (coefficientSurface A H) G.form
def retainedSurface (A : CoeffIdeal) (d : FreshCoeffRing) (H : CoeffHyperplane) :
    Ideal FreshCoeffRing :=
  saturate (extendIdeal (coefficientSurface A H)) d
def retainedCurve (A : CoeffIdeal) (d : FreshCoeffRing) (H G : CoeffHyperplane) :
    Ideal FreshCoeffRing :=
  saturate (extendIdeal (coefficientCurve A H G)) d
structure TwoSlices (A : CoeffIdeal) (d : FreshCoeffRing) where
  first : CoeffHyperplane
  second : CoeffHyperplane
  first_proper : first.freshForm ∉ extendIdeal A
  second_regular : IsLeftRegular (Ideal.Quotient.mk (retainedSurface A d first) second.freshForm)
  curve_dimension : dimension (retainedCurve A d first second) = 1
  curve_degree : affineDegree (retainedCurve A d first second) = affineDegree A
  boundary_finite : ∀ i, dimension (boundaryChart (coefficientCurve A first second) i) = 0
end
end Low48FatCount_2_3_3
end
section
set_option autoImplicit false
set_option maxRecDepth 2000
namespace Low48FatCount_2_3_3
noncomputable section
open MvPolynomial
open K1_13 (Geom)
open K1_13_6 (GeoField)
open K1_13_6_3 (dimension geomConstants)
open K1_13_6_3_4 (boundaryIdeal)
open K1_13_7_2_5_4 (cut)
open K1_13_7_2_5_4_1 (regular_of_avoids_associated denominator_regular_after_cut
  saturate_eq_of_regular boundary_homogeneous boundary_charts_of_curve)
open Low48Price (taylorLength)
open Low48FatCount_2_3 (CoeffIdeal FreshCoeffRing extendIdeal)
open private slopeMap formMap slopeMap_apply formMap_apply exists_parameters linearForm_homogeneous
  from ProximityPrize.SubmissionLower.Fast066
open private backwardDifference_degree from ProximityPrize.SubmissionLower.Fast073
private def freshSlope (H : CoeffHyperplane) : FreshCoeffRing :=
  ∑ i : Fin taylorLength, MvPolynomial.C (geomConstants (H.slope i)) * MvPolynomial.X i
private theorem freshSlope_homogeneous (H : CoeffHyperplane) : (freshSlope H).IsHomogeneous 1 :=
  linearForm_homogeneous (fun i : Fin taylorLength ↦ geomConstants (H.slope i))
private theorem freshForm_eq (H : CoeffHyperplane) :
    H.freshForm = MvPolynomial.C (geomConstants H.offset) + freshSlope H := by
  simp only [freshSlope, CoeffHyperplane.freshForm, CoeffHyperplane.form,
    map_add, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
private theorem exists_slice (I J B : Ideal FreshCoeffRing) :
    ∃ H : CoeffHyperplane,
      (∀ P ∈ associatedPrimes FreshCoeffRing (FreshCoeffRing ⧸ I), H.freshForm ∉ P) ∧
      (∀ P ∈ associatedPrimes FreshCoeffRing (FreshCoeffRing ⧸ J), H.freshForm ∉ P) ∧
      (∀ P ∈ associatedPrimes FreshCoeffRing (FreshCoeffRing ⧸ B),
        (∃ i : Fin taylorLength, MvPolynomial.X i ∉ P) → freshSlope H ∉ P) := by
  let : Algebra Geom GeoField := geomConstants.toAlgebra
  obtain ⟨v, hp, hq, hb⟩ := exists_parameters (k := Geom) I J B
  let H : CoeffHyperplane := ⟨v.1, v.2⟩
  have hSlope : slopeMap v = freshSlope H := slopeMap_apply v
  have hForm : formMap v = H.freshForm := by
    rw [formMap_apply, hSlope, freshForm_eq]
    rfl
  exact ⟨H, fun P hP ↦ hForm ▸ hp P hP, fun P hP ↦ hForm ▸ hq P hP,
    fun P hP hi ↦ hSlope ▸ hb P hP hi⟩
private theorem extend_cut (A : CoeffIdeal) (H : CoeffHyperplane) :
    extendIdeal (cut A H.form) = cut (extendIdeal A) H.freshForm := by
  simp only [extendIdeal, cut, CoeffHyperplane.freshForm, Ideal.map_sup, Ideal.map_span,
    Set.image_singleton]
theorem hilbert_extend (A : CoeffIdeal) :
    affineHilbertPolynomial (extendIdeal A) = affineHilbertPolynomial A :=
  let : Algebra Geom GeoField := geomConstants.toAlgebra
  K1_13_5_5_2.hilbertPolynomial_map (E := GeoField) A
theorem regular_of_prime {B : Ideal FreshCoeffRing} (hB : B.IsPrime)
    {p : FreshCoeffRing} (hp : p ∉ B) : IsLeftRegular (Ideal.Quotient.mk B p) := by
  let : B.IsPrime := hB
  exact IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    (mt Ideal.Quotient.eq_zero_iff_mem.mp hp)
private theorem next_slice (A : CoeffIdeal)
    (d : FreshCoeffRing) (hd : IsLeftRegular (Ideal.Quotient.mk (extendIdeal A) d))
    (hA : 0 < dimension A) :
    ∃ H : CoeffHyperplane,
      IsLeftRegular (Ideal.Quotient.mk (extendIdeal A) H.freshForm) ∧
      IsLeftRegular (Ideal.Quotient.mk (extendIdeal (coefficientSurface A H)) d) ∧
      dimension (coefficientSurface A H) = dimension A - 1 ∧
      affineDegree (extendIdeal (coefficientSurface A H)) = affineDegree (extendIdeal A) := by
  let I := extendIdeal A
  obtain ⟨H, hp, hq, hb⟩ := exists_slice I (cut I d) (boundaryIdeal I)
  have hf := regular_of_avoids_associated I H.freshForm hp
  have hfd := regular_of_avoids_associated (cut I d) H.freshForm hq
  have he : extendIdeal (coefficientSurface A H) = cut I H.freshForm := extend_cut A H
  have hm := K1_13_7_2_5_4_1_1.proof (boundaryIdeal I) (freshSlope H) (boundary_homogeneous I)
    (freshSlope_homogeneous H) hb
  have hform : IsLeftRegular (Ideal.Quotient.mk I (MvPolynomial.C (geomConstants H.offset) + freshSlope H)) := by
    rwa [← freshForm_eq H]
  have hpoly := K1_13_7_2_5_4_1_2.proof I _ _ (freshSlope_homogeneous H) hform hm
  rw [← freshForm_eq H, ← he] at hpoly
  have hAext : 0 < dimension I := by
    change 0 < (affineHilbertPolynomial (extendIdeal A)).natDegree
    rwa [hilbert_extend]
  obtain ⟨hdim, hdeg⟩ := backwardDifference_degree I _ hAext hpoly
  refine ⟨H, hf, he.symm ▸ denominator_regular_after_cut I d H.freshForm hd hfd, ?_, hdeg⟩
  change (affineHilbertPolynomial (extendIdeal (coefficientSurface A H))).natDegree =
    (affineHilbertPolynomial (extendIdeal A)).natDegree - 1 at hdim
  rwa [hilbert_extend, hilbert_extend] at hdim
theorem two_slices (A : CoeffIdeal) (hprime : (extendIdeal A).IsPrime)
    (hdim : dimension A = 3) (d : FreshCoeffRing) (hd : d ∉ extendIdeal A) :
    Nonempty (TwoSlices A d) := by
  obtain ⟨H, hH, hdH, hdimH, hdegH⟩ := next_slice A d (regular_of_prime hprime hd) (by omega)
  let U := coefficientSurface A H
  have hU : dimension U = 2 := by dsimp [U]; omega
  obtain ⟨G, hG, hdG, hdimG, hdegG⟩ := next_slice U d hdH (by omega)
  let V := coefficientCurve A H G
  have hV : dimension V = 1 := by
    change dimension (coefficientSurface U G) = 1
    omega
  have hs : retainedSurface A d H = extendIdeal U := saturate_eq_of_regular _ _ hdH
  have ht : retainedCurve A d H G = extendIdeal V := saturate_eq_of_regular _ _ hdG
  refine ⟨⟨H, G, ?_, hs.symm ▸ hG, ?_, ?_, boundary_charts_of_curve V hV⟩⟩
  · let : (extendIdeal A).IsPrime := hprime
    intro hh
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hh] at hH
    have heq : (0 : FreshCoeffRing ⧸ extendIdeal A) * 0 = 0 * 1 := by simp
    exact zero_ne_one (hH heq)
  · rw [ht]
    change (affineHilbertPolynomial (extendIdeal V)).natDegree = 1
    rwa [hilbert_extend]
  · rw [ht]
    calc
      affineDegree (extendIdeal V) = affineDegree (extendIdeal U) := hdegG
      _ = affineDegree (extendIdeal A) := hdegH
      _ = affineDegree A := by rw [affineDegree, affineDegree, hilbert_extend]
end
end Low48FatCount_2_3_3
end
section
set_option autoImplicit false
set_option maxRecDepth 2000
namespace Low48FatCount_2_3_3
noncomputable section
open MvPolynomial
open K1_13 (Geom)
open K1_13_6 (GeoField GeoJets GenericField genericCoeffs)
open K1_13_6_3 (dimension geomConstants genericArgument)
open K1_13_6_3_4 (boundaryIdeal boundaryChart NoBoundaryZero ValueReduction)
open K1_13_7_2_5_4 (le_saturate)
open Low48Price (taylorLength)
open Low48FatCount_2_3 (CoeffIdeal FreshCoeffRing extendIdeal jetLinear freshJetMap)
open private eval₂_scale eval_scale_zero map_boundary_generator linear_sum_homogeneous
  finite_chart_coordinates polynomial_value_ne_zero from ProximityPrize.SubmissionLower.Fast053
open private value_reduction from ProximityPrize.SubmissionLower.Fast053
open private hilbert_le_shift degree_le_of_shift from ProximityPrize.SubmissionLower.Fast066
private theorem jetLinear_homogeneous (a : GeoField) (r : ℕ) :
    (jetLinear a r).IsHomogeneous 1 :=
  linear_sum_homogeneous fun j : Fin taylorLength ↦ (j.val.choose r : GeoField) * a ^ (j.val - r)
private theorem normalize_boundary (A : CoeffIdeal) {x : Fin taylorLength → GeoField}
    (hx : x ∈ zeroLocus GeoField (boundaryIdeal (extendIdeal A)))
    {i : Fin taylorLength} (hi : x i ≠ 0) :
    letI : Algebra Geom GeoField := geomConstants.toAlgebra
    (fun j ↦ (x i)⁻¹ * x j) ∈ zeroLocus GeoField (boundaryChart A i) := by
  let : Algebra Geom GeoField := geomConstants.toAlgebra
  let b : Fin taylorLength → GeoField := fun j ↦ (x i)⁻¹ * x j
  change boundaryChart A i ≤ RingHom.ker (eval₂Hom geomConstants b)
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro _ ⟨p, n, hp, hn, rfl⟩
    have he := hx (MvPolynomial.map geomConstants (homogeneousComponent n p))
      (map_boundary_generator geomConstants A hp hn)
    change (MvPolynomial.map geomConstants (homogeneousComponent n p)).eval x = 0 at he
    rw [eval_map] at he
    change eval₂ geomConstants b (homogeneousComponent n p) = 0
    rw [eval₂_scale geomConstants x ((x i)⁻¹) (homogeneousComponent_isHomogeneous ..), he,
      mul_zero]
  · apply Ideal.span_le.mpr
    rintro _ (rfl : _ = MvPolynomial.X i - 1)
    change eval₂ geomConstants b (MvPolynomial.X i - 1) = 0
    rw [eval₂_sub, eval₂_X, eval₂_one]
    exact sub_eq_zero.mpr (inv_mul_cancel₀ hi)
private theorem fresh_value_ne_zero {a : Fin taylorLength → Geom} {i : Fin taylorLength}
    (hi : a i ≠ 0) : eval (geomConstants ∘ a) (jetLinear genericArgument 0) ≠ 0 := by
  have hinj : Function.Injective genericCoeffs :=
    (algebraMap GenericField GeoField).injective.comp
      (IsFractionRing.injective (Polynomial Geom) GenericField)
  have hne := polynomial_value_ne_zero genericCoeffs hinj Fin.val Fin.val_injective a hi
  intro h
  apply hne
  rw [← h]
  unfold jetLinear
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [map_mul, eval_C, eval_X, Nat.choose_zero_right, Nat.cast_one, one_mul,
    Nat.sub_zero, Function.comp_apply, genericArgument, geomConstants, RingHom.comp_apply]
private theorem noBoundaryZero_of_charts (A : CoeffIdeal)
    (hA : ∀ i, dimension (boundaryChart A i) = 0) :
    NoBoundaryZero (extendIdeal A) (jetLinear genericArgument 0) := by
  classical
  let : Algebra Geom GeoField := geomConstants.toAlgebra
  intro x hx hval
  funext i
  change x i = 0
  by_contra hi
  let b : Fin taylorLength → GeoField := fun j ↦ (x i)⁻¹ * x j
  have hb : b ∈ zeroLocus GeoField (boundaryChart A i) := normalize_boundary A hx hi
  choose a ha using fun j ↦ finite_chart_coordinates (boundaryChart A i) (hA i) hb j
  have he : geomConstants ∘ a = b := funext ha
  have hai : a i ≠ 0 := by
    intro ha₀
    have hz := ha i
    change geomConstants (a i) = (x i)⁻¹ * x i at hz
    rw [ha₀, map_zero, inv_mul_cancel₀ hi] at hz
    exact zero_ne_one hz
  apply fresh_value_ne_zero hai
  rw [he]
  exact eval_scale_zero x ((x i)⁻¹) (jetLinear_homogeneous genericArgument 0) hval
private theorem boundary_mono {I J : Ideal FreshCoeffRing} (h : I ≤ J) :
    boundaryIdeal I ≤ boundaryIdeal J := by
  apply Ideal.span_mono
  rintro _ ⟨p, n, hp, hdeg, rfl⟩
  exact ⟨p, n, h hp, hdeg, rfl⟩
theorem retained_value_reduction {A : CoeffIdeal} {d : FreshCoeffRing}
    (S : TwoSlices A d) :
    ValueReduction (retainedCurve A d S.first S.second) (jetLinear genericArgument 0) := by
  apply value_reduction (jetLinear_homogeneous genericArgument 0)
  intro x hx hvalue
  apply noBoundaryZero_of_charts _ S.boundary_finite x _ hvalue
  exact zeroLocus_anti_mono
    (boundary_mono (le_saturate (extendIdeal (coefficientCurve A S.first S.second)) d)) hx
private def jetAlg : GeoJets →ₐ[GeoField] FreshCoeffRing :=
  aeval (fun i : Fin 4 ↦ jetLinear genericArgument i.val)
private def jetQuot (I : Ideal FreshCoeffRing) :
    (GeoJets ⧸ I.comap freshJetMap) →ₐ[GeoField] (FreshCoeffRing ⧸ I) :=
  Ideal.quotientMapₐ I jetAlg (fun _ hp ↦ hp)
private theorem jetQuot_mk (I : Ideal FreshCoeffRing) (p : GeoJets) :
    jetQuot I (Ideal.Quotient.mk (I.comap freshJetMap) p) =
      Ideal.Quotient.mk I (freshJetMap p) := rfl
theorem degree_le_fresh_curve (I : Ideal FreshCoeffRing) (D : GeoJets)
    (hreg : IsLeftRegular (Ideal.Quotient.mk I (freshJetMap D)))
    (hrec : ∀ i : Fin taylorLength, ∃ n : GeoJets, MvPolynomial.X i * freshJetMap D - freshJetMap n ∈ I)
    (hred : ValueReduction I (jetLinear genericArgument 0)) :
    dimension (I.comap freshJetMap) = dimension I ∧ affineDegree I ≤ affineDegree (I.comap freshJetMap) := by
  let J := I.comap freshJetMap
  let d : GeoJets ⧸ J := Ideal.Quotient.mk J D
  have hd : IsLeftRegular (jetQuot I d) := hreg
  have hgen (i : Fin taylorLength) :
      ∃ a, jetQuot I d * Ideal.Quotient.mk I (MvPolynomial.X i) = jetQuot I a := by
    obtain ⟨p, hp⟩ := hrec i
    refine ⟨Ideal.Quotient.mk J p, ?_⟩
    rw [show jetQuot I d = Ideal.Quotient.mk I (freshJetMap D) from jetQuot_mk I D,
      jetQuot_mk, mul_comm, ← map_mul]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hp
  have hv : jetQuot I (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin 4))) =
      Ideal.Quotient.mk I (jetLinear genericArgument 0) := by
    rw [jetQuot_mk]
    exact congrArg (Ideal.Quotient.mk I) (eval₂Hom_X' _ _ _)
  have hinj : Function.Injective (jetQuot I) :=
    Ideal.quotientMap_injective' (H := show J ≤ I.comap jetAlg.toRingHom from le_rfl) le_rfl
  obtain ⟨C, hC⟩ := hilbert_le_shift (jetQuot I) d hd hgen 0 hv hred
  exact degree_le_of_shift (jetQuot I) hinj hC
end
end Low48FatCount_2_3_3
end
section
set_option autoImplicit false
namespace Low48FatCount_2_3_3
noncomputable section
open MvPolynomial
open K1_13 (Row shape)
open K1_13_6 (GeoField GeoJets toGeneric genericCoeffs)
open K1_13_6_3 (dimension geomConstants)
open K1_13_7_2_5_4 (cut le_cut mem_cut le_saturate saturate_mono regular_saturate regular_cut_bound)
open Low48Price (taylorLength)
open Low48FatCount (fatChart)
open Low48FatCount_2 (FatTaylor)
open Low48FatCount_2_3 (CoeffIdeal FreshCoeffRing FreshChart extendIdeal freshJetMap freshImage)
def jetCut {f : Row 4} (T : FatTaylor f) (H : CoeffHyperplane) : GeoJets :=
  MvPolynomial.C (geomConstants H.offset) * toGeneric T.denom +
    ∑ i, MvPolynomial.C (geomConstants (H.slope i)) * toGeneric (T.numer i)
theorem jetCut_degree {f : Row 4} (T : FatTaylor f) (H : CoeffHyperplane) :
    (jetCut T H).totalDegree ≤ (fatChart (shape f)).b := by
  let b := (fatChart (shape f)).b
  have hmap (p : Row 4) (hp : p.totalDegree ≤ b) :
      toGeneric p ∈ restrictTotalDegree (Fin 4) GeoField b := by
    rw [mem_restrictTotalDegree]
    exact (Finset.sup_mono (support_map_subset genericCoeffs p)).trans hp
  rw [← mem_restrictTotalDegree]
  apply Submodule.add_mem
  · rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (hmap T.denom T.denom_box.1)
  · apply Submodule.sum_mem
    intro i _
    rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (hmap (T.numer i) (T.numer_box i).1)
theorem jetCut_mk {f : Row 4} {T : FatTaylor f} {A : CoeffIdeal} (hA : FreshChart f T A)
    {B : Ideal FreshCoeffRing} (hAB : extendIdeal A ≤ B) (H : CoeffHyperplane) :
    Ideal.Quotient.mk B (freshJetMap (jetCut T H)) =
      Ideal.Quotient.mk B (freshJetMap (toGeneric T.denom)) *
        Ideal.Quotient.mk B H.freshForm := by
  let e := Ideal.Quotient.mk B
  let d := freshJetMap (toGeneric T.denom)
  have hC (a : GeoField) : freshJetMap (MvPolynomial.C a) = MvPolynomial.C a :=
    eval₂Hom_C _ _ a
  have hre (i : Fin taylorLength) :
      e (freshJetMap (toGeneric (T.numer i))) = e d * e (MvPolynomial.X i) := by
    rw [← map_mul, mul_comm, eq_comm]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hAB (hA.recovers i))
  change e (freshJetMap (jetCut T H)) = e d * e H.freshForm
  simp only [jetCut, CoeffHyperplane.freshForm, CoeffHyperplane.form, map_add, map_mul,
    map_sum, MvPolynomial.map_C, MvPolynomial.map_X, hC, hre, d]
  rw [mul_add, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro i _
    ac_rfl
theorem jetCut_mem {f : Row 4} {T : FatTaylor f} {A : CoeffIdeal} (hA : FreshChart f T A)
    {B : Ideal FreshCoeffRing} (hAB : extendIdeal A ≤ B) {H : CoeffHyperplane}
    (hH : H.freshForm ∈ B) : jetCut T H ∈ B.comap freshJetMap := by
  change freshJetMap (jetCut T H) ∈ B
  rw [← Ideal.Quotient.eq_zero_iff_mem, jetCut_mk hA hAB,
    Ideal.Quotient.eq_zero_iff_mem.mpr hH, mul_zero]
theorem jetCut_regular {f : Row 4} {T : FatTaylor f} {A : CoeffIdeal} (hA : FreshChart f T A)
    {B : Ideal FreshCoeffRing} (hAB : extendIdeal A ≤ B) {H : CoeffHyperplane}
    (hD : IsLeftRegular (Ideal.Quotient.mk B (freshJetMap (toGeneric T.denom))))
    (hH : IsLeftRegular (Ideal.Quotient.mk B H.freshForm)) :
    IsLeftRegular (Ideal.Quotient.mk (B.comap freshJetMap) (jetCut T H)) := by
  let φ : (GeoJets ⧸ B.comap freshJetMap) →+* (FreshCoeffRing ⧸ B) :=
    Ideal.quotientMap B freshJetMap le_rfl
  have hφ : Function.Injective φ := Ideal.quotientMap_injective
  have hmap : φ (Ideal.Quotient.mk _ (jetCut T H)) =
      Ideal.Quotient.mk B (freshJetMap (toGeneric T.denom)) * Ideal.Quotient.mk B H.freshForm :=
    jetCut_mk hA hAB H
  intro x y hxy
  apply hφ
  apply hD.mul hH
  simpa only [map_mul, hmap] using congrArg φ hxy
set_option maxHeartbeats 800000 in
theorem proof : Low48FatCount_2_3.c3 := by
  intro f T A _ hChart hdim
  let D := toGeneric T.denom
  let d := freshJetMap D
  have hd : d ∉ extendIdeal A := hChart.denom
  obtain ⟨S⟩ := two_slices A hChart.extended_prime hdim d hd
  let B := retainedSurface A d S.first
  let C := retainedCurve A d S.first S.second
  let Q := B.comap freshJetMap
  let R := C.comap freshJetMap
  let b := (fatChart (shape f)).b
  have hAB : extendIdeal A ≤ B :=
    (Ideal.map_mono (le_cut A S.first.form)).trans (le_saturate _ d)
  have hBC : B ≤ C := saturate_mono (Ideal.map_mono (le_cut _ S.second.form)) d
  have hfirst : S.first.freshForm ∈ B :=
    le_saturate _ d (Ideal.mem_map_of_mem _ (mem_cut A S.first.form))
  have hsecond : S.second.freshForm ∈ C :=
    le_saturate _ d (Ideal.mem_map_of_mem _ (mem_cut _ S.second.form))
  have hJQ : cut (freshImage A) (jetCut T S.first) ≤ Q :=
    sup_le (Ideal.comap_mono hAB) ((Ideal.span_singleton_le_iff_mem _).mpr
      (jetCut_mem hChart hAB hfirst))
  have hQR : cut Q (jetCut T S.second) ≤ R :=
    sup_le (Ideal.comap_mono hBC) ((Ideal.span_singleton_le_iff_mem _).mpr
      (jetCut_mem hChart (hAB.trans hBC) hsecond))
  have hU := regular_cut_bound hJQ
    (jetCut_regular hChart le_rfl (regular_of_prime hChart.extended_prime hd)
      (regular_of_prime hChart.extended_prime S.first_proper))
    (jetCut_degree T S.first)
  have hV := regular_cut_bound hQR
    (jetCut_regular hChart hAB (regular_saturate _ d) S.second_regular)
    (jetCut_degree T S.second)
  obtain ⟨hRdim, hRdegree⟩ := degree_le_fresh_curve C D (regular_saturate _ d)
    (fun i ↦ ⟨toGeneric (T.numer i), (hAB.trans hBC) (hChart.recovers i)⟩)
    (retained_value_reduction S)
  have hR : dimension R = 1 := hRdim.trans S.curve_dimension
  have hthree : dimension (freshImage A) = 3 := hChart.dimension_eq.trans hdim
  have htwo : dimension Q = 2 := by
    have hu := hU.1
    have hv := hV.1
    omega
  have hfirstDegree := hU.2 (by omega)
  have hsecondDegree := hV.2 (by omega)
  calc
    affineDegree A = affineDegree C := S.curve_degree.symm
    _ ≤ affineDegree R := hRdegree
    _ ≤ (b : ℚ) * affineDegree Q := hsecondDegree
    _ ≤ (b : ℚ) * ((b : ℚ) * affineDegree (freshImage A)) :=
      mul_le_mul_of_nonneg_left hfirstDegree (by positivity)
    _ = affineDegree (freshImage A) * (b : ℚ) ^ 2 := by ring
end
end Low48FatCount_2_3_3
end
section
namespace Low48FatCount_3
noncomputable section
open Polynomial K1_13 K1_13_7 K1_13_7_1 K1_13_7_5 K1_13_7_5_1 K1_13_7_5_3
open Low48Price (resultantBox)
open Low48FatCount (curveLength)
open scoped BigOperators
open private lift_length_ge lift_length_finite from ProximityPrize.SubmissionLower.Fast066
open private supported_anchor supported_lower supported_coordinate mixed_matches from ProximityPrize.SubmissionLower.Fast066
open private common_section sparse_length from ProximityPrize.SubmissionLower.PortLow7
structure LiftedCurve (f : Row 4) (P Q : Row 3) (r : PrimeSpectrum Jets) : Prop where
  component : r.asIdeal ∈ (liftIdeal f P Q).minimalPrimes
  height : r.asIdeal.height = 3
  heavy : (curveLength : ℕ∞) ≤ liftLength r (liftIdeal f P Q)
  finite : liftLength r (liftIdeal f P Q) < ⊤
theorem lift_curve (f : Row 4) (P Q : Row 3) (S : Geom[X])
    (hf : OnFactor f S) (hcurve : Low48FatCount.HighCurve P Q (lowerPoint S)) :
    ∃ r : PrimeSpectrum Jets, LiftedCurve f P Q r ∧
      r.asIdeal < jetPointIdeal (jetPoint S) := by
  obtain ⟨q, hmin, hht, hy, hweight, _⟩ := hcurve
  obtain ⟨p, hover, hr, hry⟩ := exists_ambient_component hf hmin hy
  let r := PrimeSpectrum.comap (chartMap f) p
  have hc : r.asIdeal.comap lowerInclusion = q.asIdeal := by
    change (p.asIdeal.comap (chartMap f)).comap lowerInclusion = _
    rw [Ideal.comap_comap, chartMap_comp_lower]
    exact hover.over.symm
  obtain ⟨ht, hproper⟩ := ambient_component_height_and_strict hf hht hy hr hry hc
  have ha : (upperPolynomial f).leadingCoeff ≠ 0 :=
    fun h => upperPolynomial_lead_nonzero hf (by rw [h, map_zero])
  exact ⟨r, ⟨hr, ht, hweight.trans (lift_length_ge p rfl ha), lift_length_finite hr⟩, hproper⟩
theorem sparse_sections (f : Row 4) (P Q : Row 3)
    (hP : LowerCaps P resultantBox.b resultantBox.j) (hQ : LowerCaps Q resultantBox.b resultantBox.j)
    (R : Finset (PrimeSpectrum Jets)) (hR : ∀ r ∈ R, LiftedCurve f P Q r)
    (H : Shape) (hch : Chamber H ∧ 1 ≤ H.t)
    (cut : PrimeSpectrum Jets → Jets) (points : PrimeSpectrum Jets → Finset JetPoint)
    (hpoints : ∀ r ∈ R, Supported H (cut r) ∧ cut r ∉ r.asIdeal ∧
      ∀ y ∈ points r, r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y (cut r) = 0) :
    32 * curveLength * (∑ r ∈ R, (points r).card) ≤
      mixed32 (shape f).chamber resultantBox resultantBox H := by
  classical
  let p := (shape f).chamber
  let J := liftIdeal f P Q
  have hp : Chamber p := shape_chamber f
  have hq : Chamber resultantBox := by
    constructor <;> decide
  have hopen (r : PrimeSpectrum Jets) (hr : r ∈ R) : ∃ a, CurveOpen J r a :=
    K1_13_7_5_3_2.proof J r (hR r hr).component (hR r hr).height (hR r hr).finite
  let guard (r : PrimeSpectrum Jets) : Jets :=
    if hr : r ∈ R then Classical.choose (hopen r hr) else 0
  have hguard (r : PrimeSpectrum Jets) (hr : r ∈ R) : CurveOpen J r (guard r) := by
    simpa only [guard, dite_eq_left hr] using Classical.choose_spec (hopen r hr)
  obtain ⟨D, selected, hD, hselected⟩ :=
    common_section H (supported_coordinate hch.1 hch.2) R (fun r hr => (hR r hr).height)
      guard (fun r hr => (hguard r hr).1) cut points (fun r hr => hpoints r hr)
  have hdisjoint : (R : Set (PrimeSpectrum Jets)).PairwiseDisjoint selected := by
    intro r hr s hs hrs
    apply Finset.disjoint_left.mpr
    intro y hyr hys
    have hmem : guard r ∈ s.asIdeal :=
      (hguard r hr).2.1 s.asIdeal (hR s hs).component (fun heq => hrs (PrimeSpectrum.ext heq.symm))
    have hcontains := ((hselected s hs).2.1.2 y hys).1
    have heval : MvPolynomial.eval y (guard r) = 0 := RingHom.mem_ker.mp (hcontains hmem)
    exact (hselected r hr).2.2 y hyr heval
  let all := R.biUnion selected
  have hisolated (y : JetPoint) (hy : y ∈ all) : IsolatedLengthGE (cutIdeal J D) curveLength y := by
    obtain ⟨r, hr, hyr⟩ := Finset.mem_biUnion.mp hy
    have h := hselected r hr
    obtain ⟨hcontains, hzero⟩ := h.2.1.2 y hyr
    obtain ⟨hmin, hlen⟩ := (hguard r hr).2.2 D h.2.1.1 y hcontains (h.2.2 y hyr) hzero
    exact ⟨hmin, (hR r hr).heavy.trans hlen⟩
  have hbound :=
    sparse_length p resultantBox H hp hq hch.1 (geometricFactor f) (liftRow P) (liftRow Q) D
      (supported_anchor f) (supported_lower hP) (supported_lower hQ) hD curveLength all hisolated
  rw [mixed_matches K1_13_7_5_3_4.proof hp hq hq hch.1] at hbound
  have hbound_int :
      ((32 * curveLength * all.card : ℕ) : ℤ) ≤
        difference (difference (difference (difference volume32 p) resultantBox) resultantBox) H
          ⟨0, 0, 0⟩ := by
    apply (Int.cast_le (R := ℝ)).mp
    simpa only [Int.cast_natCast] using hbound
  have hbound_nat : 32 * curveLength * all.card ≤ mixed32 p resultantBox resultantBox H := by
    simpa only [mixed32, Int.toNat_natCast] using Int.toNat_le_toNat hbound_int
  apply le_trans _ hbound_nat
  apply Nat.mul_le_mul_left
  rw [show all.card = ∑ r ∈ R, (selected r).card from Finset.card_biUnion hdisjoint]
  exact Finset.sum_le_sum fun r hr => (hselected r hr).1
end
end Low48FatCount_3
end
section
namespace Low48FatCount_3
noncomputable section
open Polynomial MvPolynomial K1 K1_13 K1_13_6 K1_13_7 K1_13_7_1 K1_13_7_5
open K1_13_1 (indexDegree_eq)
open Low48Price (physicalDegree)
section
open private K1_13_7_5_2.denominator from ProximityPrize.SubmissionLower.Fast072
open private numerator P0_9_7_3_1.numerator_bound denominator_bound P0_9_7_3_1.coefficients_recover from ProximityPrize.SubmissionLower.PortLow7
local notation "W" => MvPolynomial.weightedTotalDegree
private theorem coefficient_fits (f : Row 4) (ht : (shape f).t = 1) :
    let L := Low48Price.taylorLength
    let H := Low48Price.linearChart (shape f).chamber
    GeoFits (toGeneric (K1_13_7_5_2.denominator L f)) H ∧
      ∀ i : Fin L, GeoFits (toGeneric (numerator L f i.val)) H := by
  let L := Low48Price.taylorLength
  let p := (shape f).chamber
  have hpt : p.t = 1 := ht
  have hj : 3 ≤ p.j := by
    have h := (shape_chamber f).2
    change 3 * p.t ≤ p.j at h
    omega
  have hb : 1 ≤ p.b := (by omega : 1 ≤ p.j).trans (shape_chamber f).1
  have hbF : W 1 f ≤ p.b := by
    rw [weightedTotalDegree_one]
    exact le_max_left _ _
  have hjF : W Fin.val f ≤ p.j := by
    rw [← indexDegree_eq]
    exact le_rfl
  let w : Fin 4 → ℕ := Pi.single 3 1
  have hwF : W w f ≤ 1 := by simpa only [w, weightedTotalDegree_piSingle, shape] using ht.le
  have hw3 : w 3 = 1 := by decide
  have hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + 1 := by
    intro i
    fin_cases i <;> decide
  have hw : ∀ i, w i ≤ 1 := by
    intro i
    fin_cases i <;> decide
  have pack (P : Row 4) (hb' : W 1 P ≤ 1 + L * (p.b - 1))
      (hj' : W Fin.val P ≤ 3 + L * (p.j - 2))
      (ht' : W w P ≤ L + 1) : GeoFits (toGeneric P) (Low48Price.linearChart p) := by
    apply toGeneric_fits
    refine ⟨?_, ?_, ?_⟩
    · change P.totalDegree ≤ max _ _
      exact (by simpa only [weightedTotalDegree_one] using hb' :
        P.totalDegree ≤ 1 + L * (p.b - 1)).trans (le_max_left _ _)
    · change indexDegree P ≤ _
      rwa [indexDegree_eq]
    · change P.degreeOf 3 ≤ min _ ((3 + L * (p.j - 2)) / 3)
      apply le_min
      · simpa only [w, weightedTotalDegree_piSingle] using ht'
      · have h := (top_le_index P).trans hj'
        omega
  change GeoFits (toGeneric (K1_13_7_5_2.denominator L f)) (Low48Price.linearChart p) ∧
    ∀ i : Fin L, GeoFits (toGeneric (numerator L f i.val)) (Low48Price.linearChart p)
  constructor
  · apply pack
    · exact (denominator_bound L 1 hbF).trans (Nat.le_add_left _ _)
    · have h := denominator_bound L Fin.val hjF
      change W Fin.val (K1_13_7_5_2.denominator L f) ≤ L * (p.j - 3) at h
      exact h.trans ((Nat.mul_le_mul_left _ (by omega : p.j - 3 ≤ p.j - 2)).trans
        (Nat.le_add_left _ _))
    · have h := denominator_bound L w hwF
      rw [hw3, Nat.sub_self, Nat.mul_zero] at h
      exact h.trans (Nat.zero_le _)
  · intro i
    apply pack
    · simpa only [Pi.one_apply, add_zero] using
        P0_9_7_3_1.numerator_bound i.isLt.le 1 0 1 (fun _ => by simp) (fun _ => le_rfl) hb hbF
    · have h := P0_9_7_3_1.numerator_bound i.isLt.le Fin.val 1 3 (fun _ => by rfl)
        (fun j : Fin 4 => Nat.le_of_lt_succ j.isLt) hj hjF
      change W Fin.val (numerator L f i.val) ≤ 3 + L * (p.j - 3 + 1) at h
      rwa [show p.j - 3 + 1 = p.j - 2 by omega] at h
    · have h := P0_9_7_3_1.numerator_bound i.isLt.le w 1 1 hshift hw (show w 3 ≤ 1 from hw3.le) hwF
      simpa only [hw3, Nat.sub_self, zero_add, Nat.mul_one, Nat.add_comm] using h
private theorem linear_values (f : Row 4) (ht : (shape f).t = 1) :
    ∃ C : ValueChart (Low48FatCount.fatChart (shape f)),
      ∀ S : K[X], S.natDegree ≤ physicalDegree → OnFactor f (extend S) →
        RegularAt f (extend S) → C.recovers S := by
  rw [Low48FatCount.fatChart, ite_eq_left ht]
  obtain ⟨hD, hN⟩ := coefficient_fits f ht
  obtain ⟨C, hC⟩ := P0_9_7_3_1.values_of_coefficients _ _ hD hN
  have hchar : Low48Price.taylorLength < K1.p := by decide
  exact ⟨C, fun S hS hon hr =>
    hC S (Nat.lt_succ_of_le hS) (P0_9_7_3_1.coefficients_recover hchar ht (extend S) hon.1 hr)⟩
end
section
open private K1_13_7_1.denominator from ProximityPrize.SubmissionLower.Fast059
open private coefficientNumerator coefficients_fit P0_9_7_3_2.coefficients_recover from ProximityPrize.SubmissionLower.PortLow7
theorem regular_chart (f : Row 4) (hf : Low48Price.SmallFactor f) :
    ∃ C : ValueChart (Low48FatCount.fatChart (shape f)),
      ∀ S : K[X], S.natDegree ≤ physicalDegree → OnFactor f (extend S) →
        RegularAt f (extend S) → C.recovers S := by
  by_cases ht : (shape f).t = 1
  · exact linear_values f ht
  rw [Low48FatCount.fatChart, ite_eq_right ht]
  let M := Low48Price.taylorLength
  let L := M + 4
  have hchar : M < K1.p := by decide
  have horder (j : Fin M) : j.val ≤ L := j.isLt.le.trans (Nat.le_add_right _ _)
  obtain ⟨hD, hN⟩ := coefficients_fit L f (shape f).chamber
    ⟨le_max_left _ _, le_rfl, le_rfl⟩ (shape_chamber f) hf.2.1
  obtain ⟨C, hC⟩ := P0_9_7_3_1.values_of_coefficients (toGeneric (K1_13_7_1.denominator L f))
    (fun j : Fin M => toGeneric (coefficientNumerator L f j.val))
    hD (fun j => hN j.val (horder j))
  refine ⟨C, fun S hS hon hr => ?_⟩
  obtain ⟨hne, hcoeff⟩ := P0_9_7_3_2.coefficients_recover L f (extend S) hon.1 hr
  exact hC S (Nat.lt_succ_of_le hS) ⟨hne, fun j => hcoeff j.val (horder j) (j.isLt.trans hchar)⟩
end
end
end Low48FatCount_3
end
section
namespace Low48FatCount_3
noncomputable section
open Polynomial Finset K1 K1_13 K1_13_7 K1_13_7_5 K1_13_7_1
open Low48Price (resultantBox)
open Low48FatCount (curveLength)
open scoped BigOperators
open private supported_C jetPoint_injective chart_section eval_chart_section weighted_ceil
  from ProximityPrize.SubmissionLower.Fast066
open private choose_linear_cut from ProximityPrize.SubmissionLower.PortLow7
private theorem fat_chamber (p : Shape) : Chamber (Low48FatCount.fatChart p) := by
  unfold Low48FatCount.fatChart
  split
  · let j := 3 + Low48Price.taylorLength * (p.chamber.j - 2)
    refine ⟨le_max_right _ _, ?_⟩
    change 3 * min (Low48Price.taylorLength + 1) (j / 3) ≤ j
    have hj := min_le_right (Low48Price.taylorLength + 1) (j / 3)
    omega
  · exact chart_chamber _ _
private theorem fat_top (p : Shape) : 1 ≤ (Low48FatCount.fatChart p).t := by
  unfold Low48FatCount.fatChart
  split
  · change 1 ≤ min (Low48Price.taylorLength + 1) ((3 + Low48Price.taylorLength * (p.chamber.j - 2)) / 3)
    exact le_min (by omega) (by omega)
  · let L := Low48Price.taylorLength + 4
    change 1 ≤ min (2 * L * (p.chamber.t - 1) + L + 1)
      ((2 * L * (p.chamber.j - 3) + L + 3) / 3)
    exact le_min (by omega) (by omega)
private theorem choose_section {w Γ s} (hm : Low48Price.Messages w Γ s) {H : Shape} (C : ValueChart H)
    (hC : ∀ γ ∈ Γ, C.recovers (s γ)) {r : PrimeSpectrum Jets}
    (hr : ∀ γ ∈ Γ, r.asIdeal ≤ jetPointIdeal (jetPoint (extend (s γ)))) :
    ∃ (F : Jets) (selected : Finset JetPoint), Supported H F ∧ F ∉ r.asIdeal ∧
      (∀ y ∈ selected, r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y F = 0) ∧
      Low48Price.incidenceGap * Γ.card ≤ Low48Price.errors * selected.card + Low48Price.incidenceGap := by
  classical
  let proper := (univ : Finset I).filter (fun i => ∃ γ ∈ Γ, (s γ).eval (node i) ≠ w i)
  let hits (i : I) := Γ.filter (fun γ => (s γ).eval (node i) = w i)
  by_cases h : proper.Nonempty
  · obtain ⟨i, hi, hmax⟩ := proper.exists_max_image (fun i => (hits i).card) h
    let F : Jets := C.numerator i - MvPolynomial.C (constantCoeff (w i)) * C.denominator
    let toPoint (γ : K) := jetPoint (extend (s γ))
    let selected := (hits i).image toPoint
    have hcard : selected.card = (hits i).card := Finset.card_image_of_injOn (by
      intro a ha b hb hab
      exact hm.distinct (filter_subset _ _ ha) (filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective (jetPoint_injective hab)))
    refine ⟨F, selected, chart_section C i (w i), ?_, ?_, ?_⟩
    · intro hF
      obtain ⟨γ, hγ, hne⟩ := (mem_filter.mp hi).2
      exact hne ((eval_chart_section (hC γ hγ) i (w i)).mp (RingHom.mem_ker.mp (hr γ hγ hF)))
    · intro y hy
      obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hy
      exact ⟨hr γ (mem_filter.mp hγ).1,
        (eval_chart_section (hC γ (mem_filter.mp hγ).1) i (w i)).mpr (mem_filter.mp hγ).2⟩
    · rw [hcard]
      exact Low48FatPad.section_capacity hm _ (fun j hj => hmax j (mem_filter.mpr ⟨mem_univ _, hj⟩))
  · refine ⟨1, ∅, ?_, r.isPrime.one_notMem, by simp, ?_⟩
    · simpa only [map_one] using supported_C H (1 : GeometricX)
    · apply Low48FatPad.section_capacity hm 0
      intro i hi
      exact (h ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩).elim
theorem proof : Low48FatCount.c3 := by
  classical
  intro w Γ s hm f hf _hEligible hOn P Q _hpq hbP hbQ hHigh
  have hlift (γ : K) (hγ : γ ∈ Γ) :=
    lift_curve f P Q (extend (s γ)) (hOn γ hγ).1 (hHigh γ hγ)
  choose lift hLift hPoint using hlift
  let R := Γ.attach.image (fun γ : {a // a ∈ Γ} => lift γ.val γ.property)
  let piece (r : PrimeSpectrum Jets) := Γ.filter (fun γ =>
    r.asIdeal ≤ jetPointIdeal (jetPoint (extend (s γ))))
  have hR (r : PrimeSpectrum Jets) (hr : r ∈ R) :
      LiftedCurve f P Q r ∧ ∃ γ ∈ Γ, r.asIdeal < jetPointIdeal (jetPoint (extend (s γ))) := by
    obtain ⟨γ, _, rfl⟩ := mem_image.mp hr
    exact ⟨hLift γ.val γ.property, γ.val, γ.property, hPoint γ.val γ.property⟩
  have hcover : Γ.card ≤ ∑ r ∈ R, (piece r).card := by
    refine (card_le_card (t := R.biUnion piece) ?_).trans card_biUnion_le
    intro γ hγ
    exact mem_biUnion.mpr ⟨lift γ hγ, mem_image.mpr ⟨Subtype.mk γ hγ, mem_attach _ _, rfl⟩,
      mem_filter.mpr ⟨hγ, (hPoint γ hγ).le⟩⟩
  obtain ⟨C, hC⟩ := regular_chart f hf
  have hsections (r : PrimeSpectrum Jets) :
      ∃ (F : Jets) (selected : Finset JetPoint), Supported (Low48FatCount.fatChart (shape f)) F ∧ F ∉ r.asIdeal ∧
        (∀ y ∈ selected, r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y F = 0) ∧
        Low48Price.incidenceGap * (piece r).card ≤ Low48Price.errors * selected.card + Low48Price.incidenceGap :=
    choose_section (hm.mono (filter_subset _ _)) C
      (fun γ hγ => hC (s γ) (hm.degree γ (mem_filter.mp hγ).1)
        (hOn γ (mem_filter.mp hγ).1).1 (hOn γ (mem_filter.mp hγ).1).2)
      (fun _ hγ => (mem_filter.mp hγ).2)
  choose cut selected hCut hProper hY hFee using hsections
  have hDegree := sparse_sections f P Q hbP hbQ R (fun r hr => (hR r hr).1)
    (Low48FatCount.fatChart (shape f))
      ⟨fat_chamber (shape f), fat_top (shape f)⟩ cut selected (fun r _ => ⟨hCut r, hProper r, hY r⟩)
  have hlinear (r : PrimeSpectrum Jets) : ∃ (F : Jets) (singlePoint : Finset JetPoint),
      (r ∈ R → Supported (shape f).chamber F ∧ F ∉ r.asIdeal ∧
        ∀ y ∈ singlePoint, r.asIdeal ≤ jetPointIdeal y ∧ MvPolynomial.eval y F = 0) ∧
      (r ∈ R → singlePoint.card = 1) := by
    by_cases hr : r ∈ R
    · obtain ⟨γ, _, hpoint⟩ := (hR r hr).2
      obtain ⟨F, hF, hproper, hmem, hzero⟩ := choose_linear_cut hf.2.1 hpoint
      exact ⟨F, {jetPoint (extend (s γ))}, fun _ => ⟨hF, hproper, by simpa using And.intro hmem hzero⟩, fun _ => by simp⟩
    · exact ⟨0, ∅, fun h => (hr h).elim, fun h => (hr h).elim⟩
  choose linear singlePoint hLinear hOne using hlinear
  have hCount := sparse_sections f P Q hbP hbQ R (fun r hr => (hR r hr).1)
    (shape f).chamber ⟨shape_chamber f, hf.2.1⟩ linear singlePoint hLinear
  rw [sum_congr rfl hOne, sum_const, smul_eq_mul, Nat.mul_one] at hCount
  have hsum : Low48Price.incidenceGap * Γ.card ≤ Low48Price.errors * (∑ r ∈ R, (selected r).card) + Low48Price.incidenceGap * R.card := calc
    _ ≤ Low48Price.incidenceGap * (∑ r ∈ R, (piece r).card) := Nat.mul_le_mul_left _ hcover
    _ = ∑ r ∈ R, Low48Price.incidenceGap * (piece r).card := mul_sum ..
    _ ≤ ∑ r ∈ R, (Low48Price.errors * (selected r).card + Low48Price.incidenceGap) := sum_le_sum fun r _ => hFee r
    _ = _ := by rw [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul, Nat.mul_comm R.card]
  change Γ.card ≤ ceilDiv
    (Low48Price.errors * mixed32 (shape f).chamber resultantBox resultantBox (Low48FatCount.fatChart (shape f)) +
      Low48Price.incidenceGap * mixed32 (shape f).chamber resultantBox resultantBox (shape f).chamber)
    (32 * Low48Price.incidenceGap * curveLength)
  rw [Nat.mul_right_comm 32 Low48Price.incidenceGap curveLength]
  exact weighted_ceil (32 * curveLength) Low48Price.errors Low48Price.incidenceGap (Nat.mul_pos (Nat.mul_pos (by decide) (by decide)) (by decide))
    hsum hDegree hCount
end
end Low48FatCount_3
end

namespace Low48FatCount

theorem proof : Low48Price.c7 :=
  of_children Low48FatCount_1.proof
    (Low48FatCount_2.of_children Low48FatCount_2_1.proof Low48FatCount_2_2.proof
      (Low48FatCount_2_3.of_children Low48FatCount_2_3_1.proof Low48FatCount_2_3_2.proof
        Low48FatCount_2_3_3.proof))
    Low48FatCount_3.proof

end Low48FatCount

#print axioms Low48FatCount.proof
