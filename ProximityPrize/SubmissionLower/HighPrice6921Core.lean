import ProximityPrize.SubmissionLower.Fast055
import ProximityPrize.SubmissionLower.Fast074

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

namespace HighPrice6921

noncomputable section

open K1 K1_14 Polynomial Finset ProximityPrize.Benchmark
open K1_14_6 (LinearCover LinearRing ClosedField mixedDegree)
open scoped BigOperators

structure FixedWord (w : I → K) (T : Finset K) (s : K → K[X]) (d : ℕ) : Prop where
  distinct : Set.InjOn s (T : Set K)
  degree : ∀ γ ∈ T, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ T, ∃ B : Finset I, 180120 ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i

theorem FixedWord.mono {w T s d} (h : FixedWord w T s d) {U : Finset K} (hU : U ⊆ T) :
    FixedWord w U s d :=
  ⟨h.distinct.mono hU, fun γ hγ => h.degree γ (hU hγ), fun γ hγ => h.hits γ (hU hγ)⟩

/-- First and second moments of the node occupancies of equally sized supports. -/
private theorem occupancy {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (marks : Finset α) (nodes : Finset ι) (B : α → Finset ι) (x t cap : ℕ)
    (hB : ∀ a ∈ marks, B a ⊆ nodes ∧ (B a).card = x)
    (hpair : ∀ a ∈ marks, ∀ b ∈ marks, a ≠ b → (B a ∩ B b).card ≤ t)
    (hocc : ∀ i ∈ nodes, (marks.filter fun a => i ∈ B a).card ≤ cap) :
    (marks.card * x)^2 ≤ nodes.card * (marks.card * (x + (marks.card - 1)*t)) ∧
      marks.card * x ≤ nodes.card * cap := by
  classical
  let occ (i : ι) := (marks.filter fun a => i ∈ B a).card
  have section_eq (V : Finset ι) (hV : V ⊆ nodes) :
      (nodes.filter fun i => i ∈ V) = V := by
    ext i
    exact mem_filter.trans ⟨And.right, fun hi => ⟨hV hi, hi⟩⟩
  have first : ∑ i ∈ nodes, occ i = marks.card * x := by
    calc
      _ = ∑ a ∈ marks, (B a).card := by
        simp only [occ, card_filter]
        rw [sum_comm]
        refine sum_congr rfl fun a ha => ?_
        rw [sum_boole, Nat.cast_id, section_eq _ (hB a ha).1]
      _ = _ := by rw [sum_congr rfl (fun a ha => (hB a ha).2), sum_const, smul_eq_mul]
  have second : ∑ i ∈ nodes, occ i ^ 2 =
      ∑ a ∈ marks, ∑ b ∈ marks, (B a ∩ B b).card := by
    simp only [occ, sq, card_filter]
    simp_rw [sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun a ha => ?_
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    have identity (i : ι) :
        (if i ∈ B a then 1 else 0 : ℕ) * (if i ∈ B b then 1 else 0) =
          if i ∈ B a ∩ B b then 1 else 0 := by
      by_cases h₁ : i ∈ B a <;> by_cases h₂ : i ∈ B b <;> simp [h₁, h₂]
    simp_rw [identity]
    rw [sum_boole, Nat.cast_id, section_eq _ (inter_subset_left.trans (hB a ha).1)]
  have row (a : α) (ha : a ∈ marks) :
      ∑ b ∈ marks, (B a ∩ B b).card ≤ x + (marks.card - 1) * t := by
    rw [← add_sum_erase marks _ ha, inter_self, (hB a ha).2]
    refine Nat.add_le_add_left ?_ _
    calc
      _ ≤ ∑ b ∈ marks.erase a, t := sum_le_sum fun b hb =>
        hpair a ha b (mem_of_mem_erase hb) (ne_of_mem_erase hb).symm
      _ = _ := by rw [sum_const, card_erase_of_mem ha, smul_eq_mul]
  have second_le : ∑ i ∈ nodes, occ i ^ 2 ≤ marks.card * (x + (marks.card - 1) * t) := by
    rw [second]
    exact (sum_le_sum row).trans_eq (by rw [sum_const, smul_eq_mul])
  have cs := sq_sum_le_card_mul_sum_sq (s := nodes) (f := occ)
  rw [first] at cs
  refine ⟨cs.trans (Nat.mul_le_mul_left _ second_le), ?_⟩
  rw [← first, ← smul_eq_mul, ← sum_const]
  exact sum_le_sum hocc

private theorem incidence_arithmetic (m x gap cap : ℕ)
    (hm : 0 < m) (hg : 0 < gap) (hx : gap ≤ x)
    (hsecond : (m*x)^2 ≤ (x+82024) * (m * (x + (m-1)*(x-gap))))
    (hfirst : m*x ≤ (x+82024)*cap) :
    gap*m ≤ 82024*cap + gap := by
  have hcancel : m*x^2 ≤ (x+82024) * (x + (m-1)*(x-gap)) := by
    apply Nat.le_of_mul_le_mul_left _ hm
    calc
      _ = (m*x)^2 := by ring
      _ ≤ _ := hsecond
      _ = _ := by ring
  have hM : ((m - 1 : ℕ) : ℤ) = (m : ℤ)-1 := Int.ofNat_sub (by omega)
  have hX : ((x - gap : ℕ) : ℤ) = (x : ℤ)-gap := Int.ofNat_sub hx
  have hcancelZ := Int.ofNat_le.mpr hcancel
  push_cast [hM, hX] at hcancelZ
  have hfirstZ := Int.ofNat_le.mpr hfirst
  push_cast at hfirstZ
  have secondZ : ((m : ℤ)*82024 - ((m : ℤ)-1)*gap)*x ≥
      ((m : ℤ)-1)*82024*gap := by
    nlinarith only [hcancelZ]
  have firstZ : ((m : ℤ)-(cap : ℤ))*x ≤ (cap : ℤ)*82024 := by
    nlinarith only [hfirstZ]
  by_contra! h
  have hbadZ : (82024 : ℤ)*cap + gap < (gap : ℤ)*m := by exact_mod_cast h
  have hbad : (cap : ℤ)*82024 < ((m : ℤ)-1)*gap := by nlinarith only [hbadZ]
  have hxpos : 0 < (x : ℤ) := by omega
  have cmp : (m : ℤ)*82024 - ((m : ℤ)-1)*gap < ((m : ℤ)-(cap : ℤ))*82024 := by
    linarith only [hbad]
  have left := mul_lt_mul_of_pos_right cmp hxpos
  have right := mul_le_mul_of_nonneg_right firstZ (by norm_num : (0 : ℤ) ≤ 82024)
  have impossible := secondZ.trans_lt (left.trans_le (show
      ((m : ℤ)-(cap : ℤ))*82024*x ≤ (cap : ℤ)*82024*82024 from by
        convert right using 1
        ring))
  have bigger := mul_lt_mul_of_pos_right hbad (by norm_num : (0 : ℤ) < 82024)
  nlinarith only [impossible, bigger]

/-- A uniform occupancy cap on the nonpersistent nodes gives the fixed-word
bound with the actual degree parameter in the agreement gap. -/
theorem section_capacity {w T s d} (h : FixedWord w T s d) (hd : d < 180120) (cap : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ T, (s γ).eval (node i) ≠ w i) →
      (T.filter fun γ => (s γ).eval (node i) = w i).card ≤ cap) :
    (180120 - d) * T.card ≤ 82024 * cap + (180120 - d) := by
  classical
  by_cases hm : T.card ≤ 1
  · have hb := Nat.mul_le_mul_left (180120 - d) hm
    simp only [Nat.mul_one] at hb
    omega
  let hits (γ : K) : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
  let common : Finset I := univ.filter fun i => ∀ γ ∈ T, (s γ).eval (node i) = w i
  let nodes : Finset I := univ \ common
  have common_le (γ : K) (hγ : γ ∈ T) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : K) (hγ : γ ∈ T) : 180120 ≤ (hits γ).card := by
    obtain ⟨B, hB, hval⟩ := h.hits γ hγ
    exact hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hval i hi⟩)
  have pair_count (a : K) (ha : a ∈ T) (b : K) (hb : b ∈ T) (hab : a ≠ b) :
      (hits a ∩ hits b).card ≤ d := by
    let P := s a - s b
    have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (h.distinct ha hb eq)
    refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
      P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (h.degree a ha) (h.degree b hb)))
    intro i hi
    change ((s a) - (s b)).eval (node i) = 0
    rw [eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < T.card)
  have hcommon : common.card ≤ d :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x := 180120 - common.card
  let t := d - common.card
  have ht : t = x - (180120 - d) := by dsimp [t, x]; omega
  have hx : 180120 - d ≤ x := by dsimp [x]; omega
  have hnodes : nodes.card = x + 82024 := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    dsimp [x]
    omega
  have exists_trim (γ : K) : ∃ B : Finset I, γ ∈ T → B ⊆ hits γ \ common ∧ B.card = x := by
    by_cases hγ : γ ∈ T
    · have hc := hit_count γ hγ
      have hsize : x ≤ (hits γ \ common).card := by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨B, hB, hcard⟩ := exists_subset_card_eq hsize
      exact ⟨B, fun _ => ⟨hB, hcard⟩⟩
    · exact ⟨∅, fun h => (hγ h).elim⟩
  choose B hB using exists_trim
  have into_nodes (γ : K) (hγ : γ ∈ T) : B γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hB γ hγ).1 hi)).2⟩
  have overlap (a : K) (ha : a ∈ T) (b : K) (hb : b ∈ T) (hab : a ≠ b) :
      (B a ∩ B b).card ≤ t := by
    have cover : (B a ∩ B b) ∪ common ⊆ hits a ∩ hits b := by
      intro i hi
      rcases mem_union.mp hi with hi | hi
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hB a ha).1 (mem_inter.mp hi).1)).1,
          (mem_sdiff.mp ((hB b hb).1 (mem_inter.mp hi).2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hi, common_le b hb hi⟩
    have disj : Disjoint (B a ∩ B b) common := disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc := (card_le_card cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i : I) (hi : i ∈ nodes) : (T.filter fun γ => i ∈ B γ).card ≤ cap := by
    have proper : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i := by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, hc⟩)
    refine (card_le_card ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ, hi⟩ := mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ, (mem_filter.mp (mem_sdiff.mp ((hB γ hγ).1 hi)).1).2⟩
  obtain ⟨second, first⟩ := occupancy T nodes B x t cap
    (fun γ hγ => ⟨into_nodes γ hγ, (hB γ hγ).2⟩) overlap occ_le
  rw [hnodes, ht] at second
  rw [hnodes] at first
  exact incidence_arithmetic _ _ _ _ (by omega) (by omega) hx second first


section LinearGeometry
open MvPolynomial

private theorem card_le_sum_cover {α β : Type*} (U : Finset α) (Ps : Finset β)
    (part : β → Finset α) (h : ∀ γ ∈ U, ∃ P ∈ Ps, γ ∈ part P) :
    U.card ≤ ∑ P ∈ Ps, (part P).card := by
  classical
  exact (card_le_card fun γ hγ => mem_biUnion.mpr (h γ hγ)).trans card_biUnion_le

def curveFactor (d : ℕ) : ℕ := 82024 / (180120 - d) + 1

private def linearSlice {T s d e b} (C : LinearCover T s d e b)
    (U : Finset K) (P : Ideal (LinearRing d e b)) : Finset K := by
  classical
  exact U.filter fun γ => C.point γ ∈ zeroLocus ClosedField P

private def linearSection {T s d e b} (C : LinearCover T s d e b)
    (P : Ideal (LinearRing d e b)) (x a : K) : Finset (Ideal (LinearRing d e b)) :=
  (P ⊔ Ideal.span {C.cut x a}).minimalPrimesFinset

/-- A nonpersistent value section is a proper linear cut. Its minimal
primes cover the hitting marks and spend at most the parent's degree. -/
private theorem linearCutData {T s d e b} (C : LinearCover T s d e b) {U : Finset K}
    (hU : U ⊆ T) {P : Ideal (LinearRing d e b)} (hP : P.IsPrime)
    (hpoints : ∀ γ ∈ U, C.point γ ∈ zeroLocus ClosedField P)
    {x a : K} (hmiss : ∃ γ ∈ U, (s γ).eval x ≠ a) :
    (let V := U.filter fun γ => (s γ).eval x = a
     V.card ≤ ∑ Q ∈ linearSection C P x a, (linearSlice C V Q).card) ∧
    (∀ Q ∈ linearSection C P x a, Q.IsPrime ∧
      (affineHilbertPolynomial Q).natDegree + 1 = (affineHilbertPolynomial P).natDegree) ∧
    (∑ Q ∈ linearSection C P x a, affineDegree Q) ≤ affineDegree P := by
  classical
  let prime := hP
  have hproper : C.cut x a ∉ P := by
    obtain ⟨γ, hγ, hv⟩ := hmiss
    intro hp
    exact hv ((C.cut_eval γ (hU hγ) x a).mp (hpoints γ hγ _ hp))
  refine ⟨?_, ?_, ?_⟩
  · dsimp only
    apply card_le_sum_cover
    intro γ hγ
    obtain ⟨hγU, hv⟩ := mem_filter.mp hγ
    have hp : C.point γ ∈ zeroLocus ClosedField (P ⊔ Ideal.span {C.cut x a}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hpoints γ hγU, (C.cut_eval γ (hU hγU) x a).mpr hv⟩
    obtain ⟨Q, hQ, hγQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hp (by simp)
    exact ⟨Q, Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
      mem_filter.mpr ⟨hγ, hγQ⟩⟩
  · intro Q hQ
    have hmin := Ideal.mem_minimalPrimesFinset.mp hQ
    exact ⟨hmin.isPrime, principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin⟩
  · simpa only [linearSection, Nat.cast_one, one_mul] using
      principalCut_sum_affineDegree_minimalPrimes_le hproper (C.cut_degree x a)

private theorem linearZeroCount {T s d e b} (C : LinearCover T s d e b)
    {U : Finset K} (hU : U ⊆ T) (P : Ideal (LinearRing d e b))
    (hP : (affineHilbertPolynomial P).natDegree = 0)
    (hpoints : ∀ γ ∈ U, C.point γ ∈ zeroLocus ClosedField P) : (U.card : ℚ) ≤ affineDegree P := by
  classical
  let image := U.image C.point
  have hc : image.card = U.card := card_image_of_injOn (C.injective.mono hU)
  have hsub : (image : Set _) ⊆ zeroLocus ClosedField P := by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hx
    exact hpoints γ hγ
  obtain ⟨hfinite, hdegree⟩ := finite_zeroLocus_and_ncard_le_affineDegree (K := ClosedField) P hP
  have hn := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, hc] at hn
  exact (Nat.cast_le.mpr hn).trans hdegree

/-- In dimension one the leading coefficient is the difference of two
successive integer Hilbert-function values, and is positive for a prime. -/
private theorem curve_degree_nat {k σ : Type*} [Field k] [Finite σ]
    (P : Ideal (MvPolynomial σ k)) (hP : P.IsPrime)
    (hdim : (affineHilbertPolynomial P).natDegree = 1) :
    ∃ δ : ℕ, 0 < δ ∧ affineDegree P = (δ : ℚ) := by
  let H := affineHilbertPolynomial P
  have hlin : H = Polynomial.C (H.coeff 0) + Polynomial.C (H.coeff 1) * Polynomial.X := by
    have hH : H.natDegree < 2 := by change (affineHilbertPolynomial P).natDegree < 2; omega
    simpa [Finset.sum_range_succ] using H.as_sum_range_C_mul_X_pow' hH
  have evalH (u : ℚ) : H.eval u = H.coeff 0 + H.coeff 1 * u := by
    conv_lhs => rw [hlin]
    simp
  obtain ⟨N, hN⟩ := exists_eval_affineHilbertPolynomial P
  let m := affineHilbertFunction P (N + 1)
  let n := affineHilbertFunction P N
  have hdiff : affineDegree P = (m : ℚ) - (n : ℚ) := by
    rw [affineDegree, hdim, Nat.factorial_one, Nat.cast_one, one_mul, Polynomial.leadingCoeff, hdim]
    dsimp only [m, n]
    rw [← hN (N+1) (by omega), ← hN N le_rfl]
    change H.coeff 1 = H.eval ((N+1 : ℕ) : ℚ) - H.eval (N : ℚ)
    rw [evalH, evalH, Nat.cast_add, Nat.cast_one]
    ring
  have hmn : n < m := by
    have hpos := affineDegree_pos hP.ne_top
    rw [hdiff] at hpos
    exact_mod_cast sub_pos.mp hpos
  exact ⟨m-n, Nat.sub_pos_of_lt hmn, hdiff.trans (Nat.cast_sub hmn.le).symm⟩

private theorem linearCurveCount {T s d e b w} (C : LinearCover T s d e b)
    {U : Finset K} (hU : U ⊆ T) (hword : FixedWord w U s d) (hd : d < 180120)
    (P : Ideal (LinearRing d e b)) (hP : P.IsPrime)
    (hdim : (affineHilbertPolynomial P).natDegree = 1)
    (hpoints : ∀ γ ∈ U, C.point γ ∈ zeroLocus ClosedField P) :
    (U.card : ℚ) ≤ (curveFactor d : ℚ) * affineDegree P := by
  classical
  obtain ⟨δ, hδ, hδdeg⟩ := curve_degree_nat P hP hdim
  have hsection (i : I) (hi : ∃ γ ∈ U, (s γ).eval (node i) ≠ w i) :
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ δ := by
    let V := U.filter fun γ => (s γ).eval (node i) = w i
    let Qs := linearSection C P (node i) (w i)
    obtain ⟨hsum, dims, degree⟩ := linearCutData C hU hP hpoints hi
    have hone (Q : Ideal (LinearRing d e b)) (hQ : Q ∈ Qs) :
        ((linearSlice C V Q).card : ℚ) ≤ affineDegree Q := by
      have hQdim := (dims Q hQ).2
      rw [hdim] at hQdim
      exact linearZeroCount C ((filter_subset _ _).trans ((filter_subset _ _).trans hU))
        Q (by omega) (fun _ hγ => (mem_filter.mp hγ).2)
    have hsumQ : (V.card : ℚ) ≤ ∑ Q ∈ Qs, ((linearSlice C V Q).card : ℚ) := by
      exact_mod_cast hsum
    have hbound := hsumQ.trans ((sum_le_sum hone).trans (degree.trans_eq hδdeg))
    exact_mod_cast hbound
  have hcount := section_capacity hword hd δ hsection
  let gap := 180120 - d
  have hgap : 0 < gap := Nat.sub_pos_of_lt hd
  have hfactor : 82024 < gap * curveFactor d := by
    change 82024 < gap * (82024 / gap + 1)
    rw [Nat.mul_add, Nat.mul_one]
    have heq := Nat.mod_add_div 82024 gap
    have hr := Nat.mod_lt 82024 hgap
    omega
  suffices hcard : U.card ≤ curveFactor d * δ by
    rw [hδdeg, ← Nat.cast_mul]
    exact_mod_cast hcard
  by_contra! hbad
  have hstep := Nat.mul_le_mul_left gap (show curveFactor d * δ + 1 ≤ U.card by omega)
  rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc] at hstep
  have hstrict := Nat.mul_lt_mul_of_pos_right hfactor hδ
  change gap * U.card ≤ 82024 * δ + gap at hcount
  omega

private theorem linearSurfaceCount {T s d e b w} (C : LinearCover T s d e b)
    {U : Finset K} (hU : U ⊆ T) (hword : FixedWord w U s d) (hd : d < 180120)
    (P : Ideal (LinearRing d e b)) (hP : P.IsPrime)
    (hdim : (affineHilbertPolynomial P).natDegree = 2)
    (hpoints : ∀ γ ∈ U, C.point γ ∈ zeroLocus ClosedField P) :
    ((180120 - d : ℕ) : ℚ) * U.card ≤
      82024 * (curveFactor d : ℚ) * affineDegree P + ((180120 - d : ℕ) : ℚ) := by
  classical
  let r := (curveFactor d : ℚ) * affineDegree P
  have hr : 0 ≤ r := mul_nonneg (Nat.cast_nonneg _) (affineDegree_nonneg P)
  have hsection (i : I) (hi : ∃ γ ∈ U, (s γ).eval (node i) ≠ w i) :
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ ⌊r⌋₊ := by
    apply (Nat.le_floor_iff hr).mpr
    let V := U.filter fun γ => (s γ).eval (node i) = w i
    let Qs := linearSection C P (node i) (w i)
    obtain ⟨hsum, dims, degree⟩ := linearCutData C hU hP hpoints hi
    have hone (Q : Ideal (LinearRing d e b)) (hQ : Q ∈ Qs) :
        ((linearSlice C V Q).card : ℚ) ≤ (curveFactor d : ℚ) * affineDegree Q := by
      obtain ⟨hpr, hdimQ⟩ := dims Q hQ
      rw [hdim] at hdimQ
      have hVU : linearSlice C V Q ⊆ U := (filter_subset _ _).trans (filter_subset _ _)
      exact linearCurveCount C (hVU.trans hU) (hword.mono hVU) hd Q hpr (by omega)
        (fun _ hγ => (mem_filter.mp hγ).2)
    have hsumQ : (V.card : ℚ) ≤ ∑ Q ∈ Qs, ((linearSlice C V Q).card : ℚ) := by
      exact_mod_cast hsum
    refine hsumQ.trans ((sum_le_sum hone).trans ?_)
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left degree (Nat.cast_nonneg _)
  have hcount := section_capacity hword hd ⌊r⌋₊ hsection
  have hcountQ : ((180120 - d : ℕ) : ℚ) * U.card ≤
      82024 * (⌊r⌋₊ : ℚ) + ((180120 - d : ℕ) : ℚ) := by exact_mod_cast hcount
  have hfloor := Nat.floor_le hr
  dsimp only [r] at hfloor
  linarith only [hcountQ, hfloor]

/-- Sum the fixed-word bound over the regular source components, with one
additive allowance for each component and one shared mixed degree budget. -/
theorem linearCoverCount {T s d e b w} (C : LinearCover T s d e b)
    (hword : FixedWord w T s d) (hd : d < 180120) :
    (180120 - d) * T.card ≤ 82024 * curveFactor d * mixedDegree d e b + (180120 - d) * e := by
  classical
  let gap : ℕ := 180120 - d
  have hcover : T.card ≤ ∑ P ∈ C.components, (linearSlice C T P).card := by
    apply card_le_sum_cover
    intro γ hγ
    obtain ⟨P, hP, hpoint⟩ := C.covers γ hγ
    exact ⟨P, hP, mem_filter.mpr ⟨hγ, hpoint⟩⟩
  have hcoverQ : (T.card : ℚ) ≤ ∑ P ∈ C.components, ((linearSlice C T P).card : ℚ) := by
    exact_mod_cast hcover
  have hone (P : Ideal (LinearRing d e b)) (hP : P ∈ C.components) :
      (gap : ℚ) * ((linearSlice C T P).card : ℚ) ≤
        82024 * (curveFactor d : ℚ) * affineDegree P + (gap : ℚ) :=
    linearSurfaceCount C (filter_subset _ _) (hword.mono (filter_subset _ _)) hd
      P (C.is_prime P hP) (C.dimension P hP) (fun _ hγ => (mem_filter.mp hγ).2)
  have hcount : (gap : ℚ) * T.card ≤
      82024 * (curveFactor d : ℚ) * (mixedDegree d e b : ℚ) + (gap : ℚ) * e := by
    calc
      _ ≤ (gap : ℚ) * ∑ P ∈ C.components, ((linearSlice C T P).card : ℚ) :=
        mul_le_mul_of_nonneg_left hcoverQ (Nat.cast_nonneg _)
      _ = ∑ P ∈ C.components, (gap : ℚ) * ((linearSlice C T P).card : ℚ) := mul_sum ..
      _ ≤ ∑ P ∈ C.components, (82024 * (curveFactor d : ℚ) * affineDegree P + (gap : ℚ)) :=
        sum_le_sum hone
      _ = 82024 * (curveFactor d : ℚ) * (∑ P ∈ C.components, affineDegree P) +
          (gap : ℚ) * (C.components.card : ℚ) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_comm (C.components.card : ℚ)]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left C.degree_sum (by positivity))
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr C.component_count) (Nat.cast_nonneg _))
  exact_mod_cast hcount


end LinearGeometry

def simplePrice (d e v : ℕ) : ℕ :=
  let gap := 180120-d
  let total := 82024 * curveFactor d * mixedDegree d e v
  (total + (gap - 1)) / gap + e

def singularDegree (e v : ℕ) : ℕ := (2*e-1)*v

def retainedPrice (d e v : ℕ) : ℕ := simplePrice d e v + (p+1)*singularDegree e v

section Singular

/-- Each term of the determinant uses one entry from each column. -/
private theorem det_degree {n b : ℕ} (A : Matrix (Fin n) (Fin n) Seeds)
    (h : ∀ i j, (A i j).totalDegree ≤ b) : A.det.totalDegree ≤ n*b := by
  classical
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro π _
  have hp : (∏ i, A (π i) i).totalDegree ≤ n*b := by
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    calc
      _ ≤ ∑ _i : Fin n, b := Finset.sum_le_sum fun i _ => h (π i) i
      _ = _ := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hh | hh <;> simpa [hh] using hp

private theorem resultant_degree {m n b : ℕ} {f g : Equation}
    (hf : SeedBound f b) (hg : SeedBound g b) :
    (f.resultant g m n).totalDegree ≤ (m+n)*b := by
  apply det_degree
  intro i j
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
    split
    · apply hg
    · simp
  · intro k
    simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
    split
    · apply hf
    · simp

private theorem derivative_seedBound {f : Equation} {b : ℕ} (hf : SeedBound f b) :
    SeedBound f.derivative b := by
  intro i
  rw [coeff_derivative]
  have hc : (↑i + 1 : Seeds) = MvPolynomial.C (↑i + 1 : FX) := by simp
  rw [hc]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simpa only [MvPolynomial.totalDegree_C, Nat.add_zero] using hf (i+1)

/-- A single nonzero polynomial in the formal seeds vanishes whenever the
specialized actual ordinate is a common root of f and its Y derivative. -/
private theorem separant_certificate {f : Equation} {e v : ℕ}
    (hpos : 0 < f.natDegree) (hy : f.natDegree ≤ e)
    (hsep : (f.map (algebraMap Seeds (FractionRing Seeds))).Separable)
    (hs : SeedBound f v) :
    ∃ Δ : Seeds, Δ ≠ 0 ∧ Δ.totalDegree ≤ singularDegree e v ∧
      ∀ (z : K) (S : K[X]), atMark f z S = 0 → atMark f.derivative z S = 0 →
        graphEval z Δ = 0 := by
  let ι := algebraMap Seeds (FractionRing Seeds)
  have hi := IsFractionRing.injective Seeds (FractionRing Seeds)
  have hcop : IsCoprime (f.map ι) (f.derivative.map ι) := by
    simpa only [Separable, ← derivative_map] using hsep
  have hne := resultant_ne_zero _ _ hcop
  rw [natDegree_map_eq_of_injective hi, natDegree_map_eq_of_injective hi,
    resultant_map_map] at hne
  refine ⟨f.resultant f.derivative, fun h => hne (by simp [h]), ?_, ?_⟩
  · apply (resultant_degree hs (derivative_seedBound hs)).trans
    apply Nat.mul_le_mul_right
    have := natDegree_derivative_le f
    omega
  · intro z S hzero hder
    obtain ⟨a, b, _, _, hbez⟩ := exists_mul_add_mul_eq_C_resultant f f.derivative
      (le_refl _) (le_refl _) (Or.inl hpos.ne')
    have ev := congrArg (eval₂RingHom (graphEval z) (atX S)) hbez
    change f.eval₂ _ _ = 0 at hzero
    change f.derivative.eval₂ _ _ = 0 at hder
    simpa [eval₂_add, eval₂_mul, hzero, hder] using ev.symm


/-- The separant resultant pays all singular labels at the admitted actual ordinate and seed caps. -/
theorem singular_count {f : Equation} {e v : ℕ} {T : Finset K} {z : K → K} {s : K → K[X]}
    (hlabel : Set.InjOn z (T : Set K)) (hpos : 0 < f.natDegree)
    (hy : f.natDegree ≤ e) (hsep : (f.map (algebraMap Seeds (FractionRing Seeds))).Separable)
    (hseed : SeedBound f v) (hchar : singularDegree e v < p)
    (hroot : ∀ γ ∈ T, atMark f (z γ) (s γ) = 0)
    (hsing : ∀ γ ∈ T, atMark f.derivative (z γ) (s γ) = 0) :
    T.card ≤ (p+1)*singularDegree e v := by
  classical
  obtain ⟨Δ, hne, hdegree, hz⟩ := separant_certificate hpos hy hsep hseed
  let S := T.image z
  let emb : K ↪ FX := ⟨seedEmbedding, seedEmbedding.injective⟩
  have hb := frobenius_coefficient_exception_count p (singularDegree e v) (singularDegree e v)
    (by decide) Δ hne ((Δ.degreeOf_le_totalDegree 0).trans hdegree)
    hchar ((Δ.degreeOf_le_totalDegree 1).trans hdegree)
    (S.map emb) (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp ha
      exact hz _ _ (hroot γ hγ) (hsing γ hγ))
  rw [Finset.card_map, Finset.card_image_of_injOn hlabel] at hb
  simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm (singularDegree e v)] using hb

end Singular

/-- The original Taylor and linearization geometry, with the new fixed-word incidence calculation. -/
theorem simple_count {f : Equation} {d e v : ℕ} {T : Finset K} {z : K → K} {s : K → K[X]}
    {w : I → K} (hword : FixedWord w T s d) (hlabel : Set.InjOn z (T : Set K))
    (hd0 : 0 < d) (hd : d < 180120) (hv : 0 < v)
    (hpos : 0 < f.natDegree) (hy : f.natDegree ≤ e)
    (hprimitive : f.IsPrimitive) (hsep : (f.map (algebraMap Seeds (FractionRing Seeds))).Separable)
    (hseed : SeedBound f v)
    (hroots : ∀ γ ∈ T, atMark f (z γ) (s γ) = 0 ∧ atMark f.derivative (z γ) (s γ) ≠ 0) :
    T.card ≤ simplePrice d e v := by
  have hdp : d < p := hd.trans (by decide)
  obtain ⟨C, hC⟩ := K1_14_6_1.proof d e v hd0 hdp f hpos hy hseed
  obtain ⟨cover⟩ := K1_14_6_2.proof d e v hd0 hv f hpos hy hprimitive hsep hseed
    T z s hlabel hroots C (fun γ hγ => hC _ _ (hword.degree γ hγ) (hroots γ hγ).1 (hroots γ hγ).2)
  have hcount := linearCoverCount cover hword hd
  let gap := 180120-d
  let total := 82024 * curveFactor d * mixedDegree d e v
  have hgap : 0 < gap := Nat.sub_pos_of_lt hd
  change gap * T.card ≤ total + gap * e at hcount
  change T.card ≤ (total + (gap - 1)) / gap + e
  have hmul : (T.card - e) * gap ≤ total + (gap - 1) := by
    rw [Nat.sub_mul, Nat.mul_comm T.card, Nat.mul_comm e]
    omega
  have hdiv := (Nat.le_div_iff_mul_le hgap).mpr hmul
  omega

/-- The equation covers the retained set with a common adaptive ordinate and seed tariff. -/
theorem retained_charge {f : Equation} {d e v : ℕ} {T : Finset K} {z : K → K} {s : K → K[X]}
    {w : I → K} (hword : FixedWord w T s d) (hlabel : Set.InjOn z (T : Set K))
    (hd0 : 0 < d) (hd : d < 180120) (hv : 0 < v)
    (hpos : 0 < f.natDegree) (hy : f.natDegree ≤ e)
    (hprimitive : f.IsPrimitive) (hsep : (f.map (algebraMap Seeds (FractionRing Seeds))).Separable)
    (hseed : SeedBound f v) (hchar : singularDegree e v < p)
    (hroot : ∀ γ ∈ T, atMark f (z γ) (s γ) = 0) :
    T.card ≤ retainedPrice d e v := by
  classical
  let singular := T.filter fun γ => atMark f.derivative (z γ) (s γ) = 0
  have hsub : singular ⊆ T := Finset.filter_subset _ _
  have hsimp : T \ singular ⊆ T := Finset.sdiff_subset
  have hs := singular_count (hlabel.mono hsub) hpos hy hsep hseed hchar
    (fun γ hγ => hroot γ (hsub hγ)) (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hr := simple_count (hword.mono hsimp) (hlabel.mono hsimp) hd0 hd hv hpos hy
    hprimitive hsep hseed (fun γ hγ => by
      obtain ⟨hT, hn⟩ := Finset.mem_sdiff.mp hγ
      exact ⟨hroot γ hT, fun hz => hn (Finset.mem_filter.mpr ⟨hT,hz⟩)⟩)
  have hpartition := Finset.card_sdiff_add_card_eq_card hsub
  unfold retainedPrice
  omega

end
end HighPrice6921
