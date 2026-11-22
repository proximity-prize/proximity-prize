import ProximityPrize.SubmissionLower.FrontBranch3
import ProximityPrize.SubmissionLower.FrontRank482200 -- serialize candidate build
set_option autoImplicit true
section
namespace P1_5
noncomputable section
open Polynomial P1
structure Direction (u : Words) (deleted : Finset I) where
  den : K[X]
  U : K[X]
  V : K[X]
  A : Fin 2 → K[X]
  out : Fin 2 → Fin 2 → K[X]
  den_nodes : ∀ i, den.eval (node i) ≠ 0
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  U_dvd : U ∣ den
  coprime : IsCoprime U V
  phase : U * den.map twist = V * den
  degrees_eq : V.natDegree = U.natDegree
  primitive : IsCoprime (A 0) (A 1)
  height : U.natDegree + amplitudeDegree (A 0) (A 1) + deleted.card ≤ heightCap
  out_degree : ∀ i j, (out i j).degree <
    (k + U.natDegree + amplitudeDegree (A 0) (A 1) : ℕ)
  nodes : ∀ x ∉ deleted, ∀ i j, (out i j).eval (node x) =
    U.eval (node x) * ((A i).map twist).eval (node x) * u j x -
    V.eval (node x) * (A j).eval (node x) * twist (u i x)
variable {u : Words} {deleted : Finset I}
def Direction.s (F : Direction u deleted) := amplitudeDegree (F.A 0) (F.A 1)
def Direction.amp (F : Direction u deleted) (γ : K) := F.A 0 + C γ * F.A 1
structure Regular (F : Direction u deleted) (γ : K) : Prop where
  amp_ne : F.amp γ ≠ 0
  degree_eq : (F.amp γ).natDegree = F.s
  adjacent : IsCoprime (F.amp γ) ((F.amp γ).map twist)
  content_unit : IsCoprime (F.amp γ) F.U
  node_unit : ∀ i ∉ deleted, (F.amp γ).eval (node i) ≠ 0
def excluded (F : Direction u deleted) (Γ : Finset K) : Finset K := by
  classical exact Γ.filter (fun γ => ¬ Regular F γ)
structure CrossLift (F : Direction u deleted) where
  G : K[X]
  L : K[X]
  monic : G.Monic
  left : G ∣ F.U
  right : G.map twist ∣ F.V
  degree_lt : L.degree < (k + F.s + G.natDegree : ℕ)
  nodes : ∀ i ∉ deleted, L.eval (node i) = G.eval (node i) *
    ((F.A 0).eval (node i) * u 1 i - (F.A 1).eval (node i) * u 0 i)
structure Offset (F : Direction u deleted) {η : K} (anchor : BadMark u η) where
  pencil : K[X]
  pencil_degree : pencil.degree < k
  E : K[X]
  Q : K[X]
  E_monic : E.Monic
  left : E ∣ F.U
  right : E.map twist ∣ F.V
  proper : Q.degree < E.degree
  reduced : IsCoprime Q E
  raw : I → K
  raw_fixed : ∀ i ∉ deleted, twist (raw i) = raw i
  first : ∀ i ∉ deleted, u 0 i + η * u 1 i - anchor.decoder.eval (node i) =
    (F.amp η).eval (node i) * raw i / F.den.eval (node i)
  second : ∀ i ∉ deleted, u 1 i - pencil.eval (node i) =
    Q.eval (node i) / E.eval (node i) + (F.A 1).eval (node i) * raw i / F.den.eval (node i)
end
end P1_5
end
section
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
namespace P1_5
noncomputable section
open Polynomial P1
open ProximityPrize.Benchmark
open scoped BigOperators
variable {u : Words} {deleted : Finset I}
private theorem coprime_amplitudes (F : Direction u deleted) {γ δ : K} (hne : γ ≠ δ) :
    IsCoprime (F.amp γ) (F.amp δ) := by
  have hd : F.amp δ - F.amp γ * 1 = C (δ - γ) * F.A 1 := by
    simp only [Direction.amp, mul_one, map_sub]
    ring
  have hunit : IsUnit (C (δ - γ)) :=
    isUnit_C.mpr (sub_ne_zero.mpr hne.symm).isUnit
  apply (IsCoprime.sub_mul_left_right_iff (x := F.amp γ) (y := F.amp δ) (z := 1)).mp
  rw [hd, isCoprime_mul_unit_left_right hunit]
  exact F.primitive.add_mul_right_left _
private theorem card_of_failed_coprime (F : Direction u deleted) (S : Finset K)
    (Q : K → K[X]) {P : K[X]} (hP : P ≠ 0)
    (hbad : ∀ γ ∈ S, ¬ IsCoprime (F.amp γ) (Q γ))
    (hdiv : ∀ γ ∈ S, GCDMonoid.gcd (F.amp γ) (Q γ) ∣ P) :
    S.card ≤ P.natDegree := by
  classical
  let g (γ : K) := GCDMonoid.gcd (F.amp γ) (Q γ)
  have hne (γ : K) (hγ : γ ∈ S) : g γ ≠ 0 := by
    intro hz
    obtain ⟨H, hH⟩ := hdiv γ hγ
    change P = g γ * H at hH
    exact hP (by simpa only [hz, zero_mul] using hH)
  have hpos (γ : K) (hγ : γ ∈ S) : 1 ≤ (g γ).natDegree := by
    by_contra! h
    have hd : (g γ).natDegree = 0 := by omega
    have hu : IsUnit (g γ) := isUnit_iff_degree_eq_zero.mpr (by
      rw [degree_eq_natDegree (hne γ hγ), hd]
      rfl)
    exact hbad γ hγ ((gcd_isUnit_iff _ _).mp hu)
  have hpairs : (S : Set K).Pairwise (fun γ δ => IsCoprime (g γ) (g δ)) := by
    intro γ _ δ _ hne
    exact (coprime_amplitudes F hne).mono (gcd_dvd_left _ _) (gcd_dvd_left _ _)
  have hprod : (∏ γ ∈ S, g γ) ∣ P := Finset.prod_dvd_of_coprime hpairs hdiv
  calc
    S.card = ∑ γ ∈ S, (1 : ℕ) := by simp
    _ ≤ ∑ γ ∈ S, (g γ).natDegree := Finset.sum_le_sum hpos
    _ = (∏ γ ∈ S, g γ).natDegree := (natDegree_prod S g hne).symm
    _ ≤ P.natDegree := natDegree_le_of_dvd hprod hP
private def eliminant (F : Direction u deleted) (q : ℕ) (σ : K →+* K) : K[X] :=
  ((F.A 0).map σ) * F.A 1 ^ q - (F.A 0 ^ q) * ((F.A 1).map σ)
private theorem gcd_dvd_eliminant (F : Direction u deleted) (q : ℕ) [ExpChar K q]
    (σ : K →+* K) (hσ : ∀ γ, σ γ = γ ^ q) (hq : q ≠ 0) (γ : K) :
    GCDMonoid.gcd (F.amp γ) ((F.amp γ).map σ) ∣ eliminant F q σ := by
  have hpow : (F.amp γ)^q = F.A 0 ^ q + C (σ γ) * F.A 1 ^ q := by
    rw [Direction.amp, add_pow_expChar _ _ q, mul_pow, ← C_pow, ← hσ γ]
  have heq : eliminant F q σ =
      ((F.amp γ).map σ) * F.A 1 ^ q - (F.amp γ)^q * ((F.A 1).map σ) := by
    rw [hpow]
    simp only [eliminant, Direction.amp, Polynomial.map_add, Polynomial.map_mul, map_C]
    ring
  have hd : GCDMonoid.gcd (F.amp γ) ((F.amp γ).map σ) ∣ F.amp γ :=
    gcd_dvd_left _ _
  rw [heq]
  exact dvd_sub ((gcd_dvd_right _ _).mul_right _)
    ((hd.trans (dvd_pow_self _ hq)).mul_right _)
private theorem degree_zero_of_power_dvd_map {q : ℕ} (hq : 2 ≤ q) {σ : K →+* K}
    {P : K[X]} (hdiv : P ^ q ∣ P.map σ) : P.natDegree = 0 := by
  by_cases hP : P = 0
  · simp [hP]
  have h := natDegree_le_of_dvd hdiv (Polynomial.map_ne_zero hP)
  rw [natDegree_pow, natDegree_map_eq_of_injective σ.injective] at h
  have htwo := (Nat.mul_le_mul_right P.natDegree hq).trans h
  omega
private theorem eliminant_ne (F : Direction u deleted) {q : ℕ} (hq : 2 ≤ q)
    (σ : K →+* K) (hs : F.s ≠ 0) : eliminant F q σ ≠ 0 := by
  intro hz
  have hcross : ((F.A 0).map σ) * F.A 1 ^ q = F.A 0 ^ q * ((F.A 1).map σ) :=
    sub_eq_zero.mp hz
  have hp : IsCoprime (F.A 0 ^ q) (F.A 1 ^ q) := F.primitive.pow
  have h0 : F.A 0 ^ q ∣ (F.A 0).map σ := hp.dvd_of_dvd_mul_right
    (by rw [hcross]; exact dvd_mul_right _ _)
  have h1 : F.A 1 ^ q ∣ (F.A 1).map σ := hp.symm.dvd_of_dvd_mul_left
    (by rw [← hcross]; exact dvd_mul_left _ _)
  exact hs (by simp [Direction.s, amplitudeDegree, degree_zero_of_power_dvd_map hq h0,
    degree_zero_of_power_dvd_map hq h1])
private theorem eliminant_degree (F : Direction u deleted) (q : ℕ) (σ : K →+* K) :
    (eliminant F q σ).natDegree ≤ (q + 1) * F.s := by
  have h0 : (F.A 0).natDegree ≤ F.s := le_max_left _ _
  have h1 : (F.A 1).natDegree ≤ F.s := le_max_right _ _
  rw [eliminant, Nat.add_mul, one_mul]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [add_comm]
    exact natDegree_mul_le_of_le (natDegree_map_le.trans h0) (natDegree_pow_le_of_le q h1)
  · exact natDegree_mul_le_of_le (natDegree_pow_le_of_le q h0) (natDegree_map_le.trans h1)
private theorem same_label {a b γ δ : K} (hpair : a ≠ 0 ∨ b ≠ 0)
    (hγ : a + γ * b = 0) (hδ : a + δ * b = 0) : γ = δ := by
  have hb : b ≠ 0 := by
    intro hz
    exact hpair.elim (fun ha => ha (by simpa [hz] using hγ)) (fun hb => hb hz)
  apply sub_eq_zero.mp
  refine (mul_eq_zero.mp (show (γ - δ) * b = 0 from ?_)).resolve_right hb
  linear_combination hγ - hδ
private theorem top_pair (F : Direction u deleted) :
    (F.A 0).coeff F.s ≠ 0 ∨ (F.A 1).coeff F.s ≠ 0 := by
  have at_top (P : K[X]) (hp : P ≠ 0) (hd : P.natDegree = F.s) :
      P.coeff F.s ≠ 0 := by
    rw [← hd, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp
  by_cases h0 : F.A 0 = 0
  · exact Or.inr (at_top _ (F.primitive.ne_zero_or_ne_zero.resolve_left (by simp [h0]))
      (by simp [Direction.s, amplitudeDegree, h0]))
  by_cases h1 : F.A 1 = 0
  · exact Or.inl (at_top _ h0 (by simp [Direction.s, amplitudeDegree, h1]))
  rcases le_total (F.A 0).natDegree (F.A 1).natDegree with h | h
  · exact Or.inr (at_top _ h1 (max_eq_right h).symm)
  · exact Or.inl (at_top _ h0 (max_eq_left h).symm)
private theorem amp_degree_le (F : Direction u deleted) (γ : K) :
    (F.amp γ).natDegree ≤ F.s :=
  natDegree_add_le_of_degree_le (le_max_left _ _)
    ((natDegree_C_mul_le _ _).trans (le_max_right _ _))
private theorem card_node_failures (F : Direction u deleted) (S : Finset K)
    (hS : ∀ γ ∈ S, ∃ i : I, (F.amp γ).eval (node i) = 0) : S.card ≤ blockLength := by
  classical
  choose f hf using fun γ : S => hS γ γ.property
  rw [blockLength, ← IRSProfile.card_index, ← Fintype.card_coe]
  apply Fintype.card_le_of_injective f
  intro γ δ he
  apply Subtype.ext
  have hγ := hf γ
  have hδ := hf δ
  rw [← he] at hδ
  exact same_label
    ((F.primitive.map (evalRingHom (node (f γ)))).ne_zero_or_ne_zero)
    (by simpa [Direction.amp] using hγ)
    (by simpa [Direction.amp] using hδ)
theorem excluded_card_le (F : Direction u deleted) (Γ : Finset K) :
    (excluded F Γ).card ≤ (p + 1) * F.s + F.U.natDegree + blockLength + 1 := by
  classical
  let A := Γ.filter (fun γ => F.amp γ ≠ 0 ∧ ¬ IsCoprime (F.amp γ) ((F.amp γ).map twist))
  let U := Γ.filter (fun γ => ¬ IsCoprime (F.amp γ) F.U)
  let N := Γ.filter (fun γ => ∃ i : I, (F.amp γ).eval (node i) = 0)
  let L := Γ.filter (fun γ => (F.amp γ).coeff F.s = 0)
  have ha : A.card ≤ (p + 1) * F.s := by
    by_cases hs : F.s = 0
    · have hempty : A = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro γ hγ
        obtain ⟨hamp, hbad⟩ := (Finset.mem_filter.mp hγ).2
        have hd := amp_degree_le F γ
        rw [hs, Nat.le_zero] at hd
        have hunit : IsUnit (F.amp γ) := isUnit_iff_degree_eq_zero.mpr (by
          rw [degree_eq_natDegree hamp, hd]
          rfl)
        exact hbad (by simpa only [mul_one] using
          (isCoprime_mul_unit_left_left hunit 1 _).mpr isCoprime_one_left)
      simp [hempty]
    · exact (card_of_failed_coprime F A (fun γ => (F.amp γ).map twist)
        (eliminant_ne F (by decide : 2 ≤ p) twist hs)
        (fun _ hγ => (Finset.mem_filter.mp hγ).2.2)
        (fun γ _ => gcd_dvd_eliminant F p twist (fun _ => rfl) (by decide) γ)).trans
          (eliminant_degree F p twist)
  have hu : U.card ≤ F.U.natDegree :=
    card_of_failed_coprime F U (fun _ => F.U) F.U_ne
      (fun _ hγ => (Finset.mem_filter.mp hγ).2) (fun _ _ => gcd_dvd_right _ _)
  have hn : N.card ≤ blockLength :=
    card_node_failures F N (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hl : L.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro γ hγ δ hδ
    exact same_label (top_pair F)
      (by simpa only [Direction.amp, coeff_add, coeff_C_mul] using (Finset.mem_filter.mp hγ).2)
      (by simpa only [Direction.amp, coeff_add, coeff_C_mul] using (Finset.mem_filter.mp hδ).2)
  have hsub : excluded F Γ ⊆ ((A ∪ U) ∪ N) ∪ L := by
    intro γ hγ
    obtain ⟨hΓ, hbad⟩ := Finset.mem_filter.mp hγ
    by_contra h
    simp only [Finset.mem_union, A, U, N, L, Finset.mem_filter, hΓ, true_and,
      not_or] at h
    obtain ⟨⟨⟨hA, hU⟩, hN⟩, hL⟩ := h
    have hne : F.amp γ ≠ 0 := by
      intro hz
      exact hL (by simp [hz])
    exact hbad ⟨hne, natDegree_eq_of_le_of_coeff_ne_zero (amp_degree_le F γ) hL,
      not_not.mp (fun hbadA => hA ⟨hne, hbadA⟩), not_not.mp hU,
      fun i _ hi => hN ⟨i, hi⟩⟩
  have hcount := Finset.card_le_card hsub
  have hAU := Finset.card_union_le A U
  have hAUN := Finset.card_union_le (A ∪ U) N
  have hAUNL := Finset.card_union_le ((A ∪ U) ∪ N) L
  omega
end
end P1_5
end
section
set_option maxRecDepth 8000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace P1_5
noncomputable section
open Polynomial P1
open K1_12 (eq_on_puncture natDegree_lt_of_degree_lt_pos eval_unit_of_dvd)
open private cancel_pair from ProximityPrize.SubmissionLower.Fast068
theorem eval_twist (P : K[X]) (i : I) :
    (P.map twist).eval (node i) = twist (P.eval (node i)) :=
  K1_12.eval_twist P i
theorem cross_lift {u deleted} (F : Direction u deleted) : Nonempty (CrossLift F) := by
  classical
  let d := k + F.U.natDegree + F.s
  let w (i : I) := (F.A 0).eval (node i) * u 1 i - (F.A 1).eval (node i) * u 0 i
  let A' (j : Fin 2) := (F.A j).map twist
  let P (j : Fin 2) := F.A 0 * F.out j 1 - F.A 1 * F.out j 0
  let P' (j : Fin 2) := A' 1 * F.out 0 j - A' 0 * F.out 1 j
  have hheight := F.height
  change F.U.natDegree + F.s + deleted.card ≤ heightCap at hheight
  have hmargin : k + 3 * heightCap ≤ blockLength := by decide
  have hroom : d + 2 * F.s + deleted.card ≤ blockLength := by
    dsimp only [d]
    omega
  have hk : 0 < k := by decide
  have hpos : 0 < d := by dsimp only [d]; omega
  have ha (j : Fin 2) : (F.A j).natDegree ≤ F.s := by
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have ha' (j : Fin 2) : (A' j).natDegree ≤ F.s := natDegree_map_le.trans (ha j)
  have hout (i j : Fin 2) : (F.out i j).natDegree < d :=
    natDegree_lt_of_degree_lt_pos hpos (F.out_degree i j)
  have hprod {a : K[X]} (ha : a.natDegree ≤ F.s) (i j : Fin 2) :
      (a * F.out i j).natDegree < d + F.s :=
    natDegree_mul_le.trans_lt (by have := hout i j; omega)
  obtain ⟨leftLift,hY,hYn⟩ := cancel_pair deleted (fun i => F.U.eval (node i)*w i) A' P d F.s
    (by simp only [A', natDegree_map_eq_of_injective twist.injective]; rfl)
    (F.primitive.map (Polynomial.mapRingHom twist)) hpos hroom
    (fun j => (natDegree_sub_le _ _).trans_lt (max_lt (hprod (ha 0) j 1) (hprod (ha 1) j 0)))
    (by intro i hi j; simp only [P, A', w, eval_sub, eval_mul, F.nodes i hi]; ring)
  obtain ⟨rightLift,hZ,hZn⟩ := cancel_pair deleted (fun i => F.V.eval (node i)*twist (w i)) F.A P' d F.s
    rfl F.primitive hpos hroom
    (fun j => (natDegree_sub_le _ _).trans_lt (max_lt (hprod (ha' 1) 0 j) (hprod (ha' 0) 1 j)))
    (by intro i hi j
        simp only [P', A', w, eval_sub, eval_mul, F.nodes i hi, eval_twist, map_sub, map_mul]
        ring)
  let f : RatFunc K := algebraMap K[X] (RatFunc K) leftLift / algebraMap K[X] (RatFunc K) F.U
  have heq : f.num * F.U = leftLift * f.denom := (RatFunc.num_mul_eq_mul_denom_iff F.U_ne).mpr rfl
  have hn (i : I) (hi : i ∉ deleted) : f.num.eval (node i) = f.denom.eval (node i) * w i := by
    have h := congrArg (eval (node i)) heq
    simp only [eval_mul, hYn i hi] at h
    apply mul_left_cancel₀ (eval_unit_of_dvd F.U_dvd (F.den_nodes i))
    linear_combination h
  have hleft : f.denom ∣ F.U := RatFunc.denom_div_dvd _ _
  have hdegG := natDegree_le_of_dvd hleft F.U_ne
  have hnf : f.num.natDegree < k + F.s + f.denom.natDegree := by
    by_cases hzero : f.num = 0
    · simp [hzero]
    have hy : leftLift ≠ 0 := by
      intro hz
      rw [hz,zero_mul] at heq
      exact mul_ne_zero hzero F.U_ne heq
    have h := congrArg natDegree heq
    rw [natDegree_mul hzero F.U_ne, natDegree_mul hy f.denom_ne_zero] at h
    dsimp [d] at hY
    omega
  have heq' : f.denom.map twist * rightLift = f.num.map twist * F.V := by
    apply eq_on_puncture (deleted := deleted) (d := d + F.U.natDegree)
    · change d + F.U.natDegree + deleted.card ≤ blockLength
      dsimp only [d]
      omega
    · apply natDegree_mul_le.trans_lt
      have hg : (f.denom.map twist).natDegree ≤ f.denom.natDegree := natDegree_map_le
      omega
    · apply natDegree_mul_le.trans_lt
      have hg : (f.num.map twist).natDegree ≤ f.num.natDegree := natDegree_map_le
      have hh := F.degrees_eq
      dsimp [d]
      omega
    · intro i hi
      simp only [eval_mul, eval_twist, hn i hi, hZn i hi, map_mul]
      ring
  have hcop : IsCoprime (f.denom.map twist) (f.num.map twist) :=
    f.isCoprime_num_denom.symm.map (Polynomial.mapRingHom twist)
  exact ⟨⟨f.denom, f.num, f.monic_denom, hleft,
    hcop.dvd_of_dvd_mul_left (by rw [← heq']; exact dvd_mul_right _ _),
    degree_le_natDegree.trans_lt (by exact_mod_cast hnf), hn⟩⟩
end
end P1_5
end
section
set_option maxRecDepth 8000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace P1_5_2
noncomputable section
open Polynomial P1 FrobeniusLocator ProximityPrize.Benchmark
open P1_5 (Direction Regular Offset eval_twist)
open K1_12 (eval_unit_of_dvd invariant_multiple)
open private coprime_factor_of_label from ProximityPrize.SubmissionLower.Fast068
variable {u : Words} {deleted : Finset I} {F : Direction u deleted} {η γ : K}
  {anchor : BadMark u η}
private def translated (O : Offset F anchor) (m : BadMark u γ) :=
  m.decoder - anchor.decoder - C (γ-η) * O.pencil
private def numerator (O : Offset F anchor) (m : BadMark u γ) :=
  O.E * translated O m - C (γ-η) * O.Q
private theorem E_nodes (O : Offset F anchor) (i : I) : O.E.eval (node i) ≠ 0 :=
  eval_unit_of_dvd (O.left.trans F.U_dvd) (F.den_nodes i)
private theorem translated_degree (O : Offset F anchor) (m : BadMark u γ) :
    (translated O m).degree < k := by
  unfold translated
  rw [C_mul']
  exact Principal.degree_sub_lt (Principal.degree_sub_lt m.degree anchor.degree)
    (Principal.degree_smul_lt _ O.pencil_degree)
private theorem numerator_degree (O : Offset F anchor) (m : BadMark u γ) :
    (numerator O m).natDegree < k + O.E.natDegree := by
  have hQ := O.proper.trans_le (degree_le_natDegree (p := O.E))
  by_cases hz : numerator O m = 0
  · simpa only [hz, natDegree_zero] using
      (Nat.lt_of_lt_of_le (show 0 < k by decide) (Nat.le_add_right k O.E.natDegree))
  apply (natDegree_lt_iff_degree_lt hz).mpr
  apply Principal.degree_sub_lt (Strata.degree_mul_lt_add O.E (translated O m)
    O.E.natDegree k le_rfl (translated_degree O m))
  rw [C_mul']
  exact Principal.degree_smul_lt _ (hQ.trans_le (by exact_mod_cast Nat.le_add_left _ _))
private theorem hits (O : Offset F anchor) (W : K[X]) (hW : F.den = O.E * W)
    (m : BadMark u γ) (avoid : Disjoint m.support deleted) (i : I) (hi : i ∈ m.support) :
    W.eval (node i) * (numerator O m).eval (node i) = (F.amp γ).eval (node i) * O.raw i := by
  have hd := Finset.disjoint_left.mp avoid hi
  have he := E_nodes O i
  have hf := O.first i hd
  have hs := O.second i hd
  have hn := F.den_nodes i
  have hw : F.den.eval (node i) = O.E.eval (node i) * W.eval (node i) := by rw [hW, eval_mul]
  simp only [Direction.amp, eval_add, eval_C, eval_mul] at hf ⊢
  rw [eq_div_iff hn] at hf
  have hs' : O.E.eval (node i) * F.den.eval (node i) * (u 1 i - O.pencil.eval (node i)) =
      F.den.eval (node i) * O.Q.eval (node i) + O.E.eval (node i) * ((F.A 1).eval (node i) * O.raw i) := by
    rw [hs]
    field_simp [he, hn]
  simp only [numerator, translated, eval_sub, eval_mul, eval_C, m.hits i hi]
  apply mul_left_cancel₀ he
  rw [← mul_assoc, ← hw]
  linear_combination O.E.eval (node i) * hf + (γ - η) * hs'
private theorem fixed_numerator (O : Offset F anchor) (W : K[X]) (hW : F.den = O.E * W)
    (m : BadMark u γ) (avoid : Disjoint m.support deleted) (reg : Regular F γ) :
    ∃ N : K[X], numerator O m = F.amp γ * N ∧ (W*N).map twist = W*N := by
  classical
  obtain ⟨l, hl⟩ := O.left
  obtain ⟨r, hr⟩ := O.right
  have hl0 : l ≠ 0 := fun hz => F.U_ne (by simp [hl, hz])
  have hr0 : r ≠ 0 := fun hz => F.V_ne (by simp [hr, hz])
  have hWnodes (i : I) : W.eval (node i) ≠ 0 :=
    eval_unit_of_dvd (hW ▸ dvd_mul_left W O.E) (F.den_nodes i)
  have hEσ : O.E.map twist ≠ 0 := (O.E_monic.map twist).ne_zero
  have hphase : l * W.map twist = r * W := by
    apply mul_left_cancel₀ (mul_ne_zero O.E_monic.ne_zero hEσ)
    have h := F.phase
    rw [hl, hr, hW, Polynomial.map_mul] at h
    linear_combination h
  let a := F.amp γ
  let P := numerator O m
  let diff := l * a.map twist * P - r * a * P.map twist
  have zero_at (i : I) (hi : i ∈ m.support) : diff.eval (node i) = 0 := by
    have hrw := O.raw_fixed i (Finset.disjoint_left.mp avoid hi)
    have h1 := hits O W hW m avoid i hi
    have h2 := congrArg twist h1
    simp only [map_mul, hrw] at h2
    have h3 := congrArg (eval (node i)) hphase
    simp only [eval_mul, eval_twist] at h3
    simp only [diff, eval_sub, eval_mul, eval_twist]
    change W.eval (node i) * P.eval (node i) = a.eval (node i) * O.raw i at h1
    change twist (W.eval (node i)) * twist (P.eval (node i)) =
      twist (a.eval (node i)) * O.raw i at h2
    apply (mul_eq_zero.mp (show W.eval (node i) * _ = 0 from ?_)).resolve_left (hWnodes i)
    linear_combination l.eval (node i) * twist (a.eval (node i)) * h1 -
      l.eval (node i) * a.eval (node i) * h2 +
      a.eval (node i) * twist (P.eval (node i)) * h3
  have ident : diff = 0 := by
    by_contra hne
    have hroot := Strata.root_nodes_card_le node IRSProfile.domain.injective diff hne m.support zero_at
    have hld : O.E.natDegree + l.natDegree = F.U.natDegree := by
      rw [hl, natDegree_mul O.E_monic.ne_zero hl0]
    have hrd : O.E.natDegree + r.natDegree = F.U.natDegree := by
      rw [← F.degrees_eq, hr, natDegree_mul hEσ hr0, natDegree_map_eq_of_injective twist.injective]
    have hP := numerator_degree O m
    have hA := reg.degree_eq
    have hheight := F.height
    change F.U.natDegree + F.s + deleted.card ≤ heightCap at hheight
    have hmargin : k + heightCap ≤ agreement := by
      change 164399 ≤ 179944
      decide
    have hdeg : diff.natDegree ≤ max (l.natDegree + a.natDegree + P.natDegree)
        (r.natDegree + a.natDegree + P.natDegree) := by
      apply (natDegree_sub_le _ _).trans
      exact max_le_max
        (natDegree_mul_le.trans (Nat.add_le_add_right
          (natDegree_mul_le.trans (Nat.add_le_add_left natDegree_map_le _)) _))
        (natDegree_mul_le.trans (Nat.add_le_add natDegree_mul_le natDegree_map_le))
    change P.natDegree < _ at hP
    change a.natDegree = _ at hA
    have hcount := m.agreement
    omega
  have eqn : l * a.map twist * P = r * a * P.map twist := sub_eq_zero.mp ident
  have hlU : l ∣ F.U := hl ▸ dvd_mul_left l O.E
  have cop : IsCoprime a (l * a.map twist) :=
    (reg.content_unit.of_isCoprime_of_dvd_right hlU).mul_right reg.adjacent
  have hdvd : a ∣ P := by
    apply cop.dvd_of_dvd_mul_left
    rw [eqn]
    exact (dvd_mul_left a r).mul_right _
  obtain ⟨N, hN⟩ := hdvd
  refine ⟨N, hN, ?_⟩
  have hred : l*N = r*N.map twist := by
    apply mul_left_cancel₀ (mul_ne_zero reg.amp_ne ((Polynomial.map_ne_zero_iff twist.injective).mpr reg.amp_ne))
    rw [hN, Polynomial.map_mul] at eqn
    linear_combination eqn
  rw [Polynomial.map_mul]
  apply mul_left_cancel₀ hl0
  linear_combination N.map twist * hphase - W * hred
end
end P1_5_2
end
