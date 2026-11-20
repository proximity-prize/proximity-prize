import ProximityPrize.SubmissionLower.FrontBranch3
set_option Elab.async false
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
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace P1_5
noncomputable section
open Polynomial P1 FrobeniusLocator
open private column column_ne column_bound column_dvd firstColumn_normal threeU_fun tight_pair
  slice_bound relationOn_fun outputs nodes_of_columns from ProximityPrize.SubmissionLower.PortFrontB
private def leftCoeff {u T R D} (B : RankThree u T R D) (l : Fin 2) : K[X] :=
  B.a * (B.β l).map twist
private def rightCoeff {u T R D} (B : RankThree u T R D) (j : Fin 2) : K[X] :=
  -(B.b * B.α j)
private theorem left_eq {u T R D} (B : RankThree u T R D) :
    threeU B.a B.β = column p (leftCoeff B) := by
  rw [threeU_fun]
  exact (firstColumn_normal p B.a B.β).trans (congrArg (column p)
    (show (fun j => B.a * (B.β j).map twist) = leftCoeff B by rfl))
private theorem right_eq {u T R D} (B : RankThree u T R D) :
    threeV B.b B.α = column 1 (rightCoeff B) := by
  simp only [threeV, rightCoeff, column, liftX, seed, Polynomial.map_mul, Polynomial.map_neg, pow_one]
  ring
private theorem plane_of_rankThree {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} (B : RankThree u T R D) :
    Nonempty (K1_10.Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B)) := by
  let U := leftCoeff B
  let V := rightCoeff B
  have amp_ne (v : Fin 2 → K[X]) (hv : IsCoprime (v 0) (v 1)) : ∃ j, v j ≠ 0 := by
    by_contra! hz
    obtain ⟨a,b,hab⟩ := hv
    simp [hz] at hab
  obtain ⟨l,hl⟩ := amp_ne B.β B.β_primitive
  obtain ⟨j,hj⟩ := amp_ne B.α B.α_primitive
  have hU : ∃ l, U l ≠ 0 :=
    ⟨l, mul_ne_zero B.a_ne ((Polynomial.map_ne_zero_iff twist.injective).mpr hl)⟩
  have hV : ∃ j, V j ≠ 0 := ⟨j, neg_ne_zero.mpr (mul_ne_zero B.b_ne hj)⟩
  have hu : amplitudeDegree (U 0) (U 1) ≤ D.height := by
    unfold amplitudeDegree
    apply max_le
    all_goals
      apply natDegree_mul_le.trans
      apply le_trans _ B.first_degree
      apply Nat.add_le_add_left
      rw [natDegree_map_eq_of_injective twist.injective]
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hv : amplitudeDegree (V 0) (V 1) ≤ D.height := by
    unfold amplitudeDegree
    apply max_le
    all_goals
      simp only [V, rightCoeff, natDegree_neg]
      apply natDegree_mul_le.trans
      apply le_trans _ B.second_degree
      apply Nat.add_le_add_left
    · exact le_max_left _ _
    · exact le_max_right _ _
  let φ := algebraMap K[X] Frac
  have hinj : Function.Injective φ := IsFractionRing.injective K[X] Frac
  have hd (P : Bivar) : (extendSeed P).natDegree = P.natDegree := natDegree_map_eq_of_injective hinj _
  have hn {P : Bivar} (hp : P ≠ 0) : extendSeed P ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hp
  have hdir := B.same_direction
  rw [sameDirection, left_eq, right_eq] at hdir
  have he := congrArg (Polynomial.map φ) hdir
  simp only [Polynomial.map_mul] at he
  have hdom := max_le_max (column_bound p U) (column_bound 1 V)
  obtain ⟨htight,hcp⟩ := tight_pair (extendSeed D.U) (extendSeed D.V)
    (extendSeed (column p U)) (extendSeed (column 1 V))
    (hn D.U_ne) (hn D.V_ne) (hn (column_ne (by decide : p ≠ 0) hU)) D.coprime he
    (by simp only [hd, D.max_degree]; exact hdom.trans (max_le hu hv))
  simp only [hd, D.max_degree] at htight
  refine ⟨⟨outputs p B.output, hU, hV, ?_, ?_, ?_, ?_⟩⟩
  · exact le_antisymm (max_le hu hv) (htight ▸ hdom)
  · intro f hfU hfV
    have hunit := hcp.isUnit_of_dvd'
      ((mapRingHom φ).map_dvd (column_dvd p U f hfU))
      ((mapRingHom φ).map_dvd (column_dvd 1 V f hfV))
    apply isUnit_iff_degree_eq_zero.mpr
    change IsUnit ((f.map Polynomial.C).map φ) at hunit
    simpa only [degree_map_eq_of_injective hinj,
      degree_map_eq_of_injective Polynomial.C_injective] using isUnit_iff_degree_eq_zero.mp hunit
  · intro j l
    apply degree_le_natDegree.trans_lt
    have ht : B.output.natDegree < k + D.height := by
      by_cases hz : B.output = 0
      · simp [hz]
      · exact (natDegree_lt_iff_degree_lt hz).mpr B.output_degree
    exact_mod_cast (slice_bound B.output _).trans_lt ht
  · apply nodes_of_columns p (by decide) u (fixedNodes R) U V B.output
    have h := B.nodes
    rwa [relationOn_fun, left_eq, right_eq] at h
private theorem coprime_contents {u T R D} (B : RankThree u T R D)
    (P : K1_10.Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B)) :
    IsCoprime B.a B.b := by
  apply (gcd_isUnit_iff _ _).mp
  apply P.primitive
  · intro i
    exact (gcd_dvd_left B.a B.b).trans (dvd_mul_right _ _)
  · intro j
    rw [rightCoeff, dvd_neg]
    exact (gcd_dvd_right B.a B.b).trans (dvd_mul_right _ _)
private theorem plane_height {u T R D} (B : RankThree u T R D)
    (P : K1_10.Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B))
    (par : Parallel B) (hdeg : B.b.natDegree = B.a.natDegree) :
    D.height = B.a.natDegree + amplitudeDegree (B.α 0) (B.α 1) := by
  let s := amplitudeDegree (B.α 0) (B.α 1)
  have hA (i : Fin 2) : (B.α i).natDegree ≤ s := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hL (i : Fin 2) : (leftCoeff B i).natDegree ≤ B.a.natDegree + s := by
    change B.α = B.β at par
    unfold leftCoeff
    rw [← par]
    exact natDegree_mul_le_of_le le_rfl (natDegree_map_le.trans (hA i))
  have hR (j : Fin 2) : (rightCoeff B j).natDegree ≤ B.a.natDegree + s := by
    rw [rightCoeff, natDegree_neg, ← hdeg]
    exact natDegree_mul_le_of_le le_rfl (hA j)
  have hmax := max_le (max_le (hL 0) (hL 1)) (max_le (hR 0) (hR 1))
  exact le_antisymm (P.height_eq ▸ hmax) (hdeg ▸ B.second_degree)
private theorem plane_nodes {u T R D} (B : RankThree u T R D)
    (P : K1_10.Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B))
    (par : Parallel B) (x : I) (hx : x ∉ fixedNodes R) (i j : Fin 2) :
    (P.output j i).eval (node x) =
      B.a.eval (node x) * ((B.α i).map twist).eval (node x) * u j x -
      B.b.eval (node x) * (B.α j).eval (node x) * twist (u i x) := by
  change B.α = B.β at par
  simpa only [leftCoeff, rightCoeff, eval_mul, eval_neg, neg_mul,
    ← sub_eq_add_neg, ← par, twist, frobenius_def] using (P.nodes x hx j i).symm
theorem direction_of_rankThree {u T R D} (hu : FrontRemainder u)
    (B : RankThree u T R D) (par : Parallel B) (hnorm : UnitNorm B) :
    Nonempty (Direction u (fixedNodes R)) := by
  obtain ⟨P⟩ := plane_of_rankThree B
  change K1.sixNorm B.a = K1.sixNorm B.b at hnorm
  obtain ⟨den, hden, hphase, hnodes⟩ := K1_12_1.denominator B.b_ne hnorm
  have hden' : den.map twist ≠ 0 := (Polynomial.map_ne_zero_iff twist.injective).mpr hden
  have hdeg := congrArg (fun Q : K[X] => Q.natDegree) hphase
  change (B.a * den.map twist).natDegree = (B.b * den).natDegree at hdeg
  rw [natDegree_mul B.a_ne hden', natDegree_mul B.b_ne hden,
    natDegree_map_eq_of_injective twist.injective] at hdeg
  have hdeg' : B.b.natDegree = B.a.natDegree := by omega
  have hcop := coprime_contents B P
  have hheight := plane_height B P par hdeg'
  have hdvd : B.a ∣ den := hcop.dvd_of_dvd_mul_left
    (hphase ▸ dvd_mul_right B.a (den.map twist))
  have hbudget := relation_height_le hu T
  exact ⟨{
    den := den
    U := B.a
    V := B.b
    A := B.α
    out := fun i j => P.output j i
    den_nodes := hnodes
    U_ne := B.a_ne
    V_ne := B.b_ne
    U_dvd := hdvd
    coprime := hcop
    phase := hphase
    degrees_eq := hdeg'
    primitive := B.α_primitive
    height := by rwa [← hheight, D.height_eq]
    out_degree := by
      intro i j
      simpa only [hheight, ← Nat.add_assoc] using P.output_degree j i
    nodes := plane_nodes B P par
  }⟩
end
end P1_5
end
section
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace P1_5
noncomputable section
open Polynomial P1 FrobeniusLocator
def c1 : Prop :=
  ∀ {u deleted} (F : Direction u deleted) (_H : CrossLift F)
    {η : K} (m : BadMark u η), Disjoint m.support deleted → Regular F η →
    Nonempty (Offset F m)
def c2 : Prop :=
  ∀ {u deleted} (F : Direction u deleted) (Γ : Finset K),
    (∀ γ ∈ Γ, Regular F γ) → ∀ (m : ∀ g : Γ, BadMark u g.val),
    (∀ g, Disjoint (m g).support deleted) →
    ∀ (η ζ : Γ), ζ.val ≠ η.val → ∀ O : Offset F (m η),
    ∃ M : AnchorModel u deleted,
      M.shift = η.val ∧ M.pencil₀ = (m η).decoder ∧ M.pencil₁ = O.pencil ∧
      M.E = O.E ∧ M.Q = O.Q ∧
      ∃ S : Γ → K[X], ∃ marks : ∀ g : Γ, AnchorMark M g.val (S g),
        ∀ g, (marks g).bad = m g
private theorem other_hits {u deleted} {M : AnchorModel u deleted} {γ δ : K} {S : K[X]}
    (m : AnchorMark M γ S) (n : AnchorMark M δ S) (i : I) (hi : i ∈ m.bad.support) :
    n.bad.decoder.eval (node i) = u 0 i + δ * u 1 i := by
  have hd := Finset.disjoint_left.mp m.avoids_deleted hi
  have h0 := M.first_word i hd
  have h1 := M.second_word i hd
  have h := congrArg (eval (node i)) n.identity
  simp only [ModelAt.decoder, ModelAt.amplitude, ModelAt.label, eval_sub,
    eval_mul, eval_C, eval_add, m.scalar_hits i hi] at h
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show M.E.eval (node i) * _ = 0 from ?_)).resolve_left (M.E_nodes i)
  linear_combination h - h0 - (δ - M.shift) * h1
private theorem same_scalar_label {u deleted} {M : AnchorModel u deleted} {γ δ : K} {S : K[X]}
    (m : AnchorMark M γ S) (n : AnchorMark M δ S) : γ = δ := by
  by_contra hne
  let V := (δ-γ)⁻¹ • (n.bad.decoder - m.bad.decoder)
  have hd : δ-γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hV : V.degree < k := Principal.degree_smul_lt _
    (Principal.degree_sub_lt n.bad.degree m.bad.degree)
  have hv (i : I) (hi : i ∈ m.bad.support) : V.eval (node i) = u 1 i := by
    simp only [V, eval_smul, eval_sub, smul_eq_mul, other_hits m n i hi, m.bad.hits i hi]
    field_simp [hd]
    ring
  apply m.bad.nonjoint
  refine ⟨⟨m.bad.decoder - γ • V, Principal.degree_sub_lt m.bad.degree
    (Principal.degree_smul_lt _ hV), ?_⟩, ⟨V, hV, hv⟩⟩
  intro i hi
  simp only [eval_sub, eval_smul, smul_eq_mul, m.bad.hits i hi, hv i hi]
  ring
theorem of_children (h1 : c1) (h2 : c2) : P1.c5 := by
  classical
  intro u hu T R D B _ par unit Γ bad normal
  by_cases hsmall : Γ.card ≤ anchorFee
  · exact Or.inl hsmall
  right
  obtain ⟨F⟩ := direction_of_rankThree hu B par unit
  let book := excluded F Γ
  have hbook : book ⊆ Γ := Finset.filter_subset _ _
  have hcard : book.card ≤ (p + 1) * F.s + F.U.natDegree + blockLength + 1 :=
    excluded_card_le F Γ
  have hbudget : book.card + 1 ≤ anchorFee := by
    have height := F.height
    change F.U.natDegree + F.s + (fixedNodes R).card ≤ heightCap at height
    have hprod := Nat.mul_le_mul_left p (show F.s ≤ heightCap by omega)
    rw [Nat.add_mul, one_mul] at hcard
    rw [← anchor_fee_exact]
    omega
  let Δ := Γ \ book
  have hbig : 1 < Δ.card := by
    have hpart := Finset.card_sdiff_add_card_eq_card hbook
    change Δ.card + book.card = Γ.card at hpart
    omega
  have regular (δ : K) (hd : δ ∈ Δ) : Regular F δ := by
    obtain ⟨hin, hout⟩ := Finset.mem_sdiff.mp hd
    by_contra h
    exact hout (Finset.mem_filter.mpr ⟨hin, h⟩)
  let m (g : Δ) := Classical.choice (bad_mark u Γ bad g.val (Finset.mem_sdiff.mp g.property).1)
  have avoid (g : Δ) : Disjoint (m g).support (fixedNodes R) := by
    apply Finset.disjoint_left.mpr
    intro i hi hid
    exact (D.deleted_error g.val (normal g.val (Finset.mem_sdiff.mp g.property).1) (m g) i hid)
      ((m g).hits i hi)
  obtain ⟨η, hη, ζ, hζ, hne⟩ := Finset.one_lt_card.mp hbig
  let a : Δ := ⟨η, hη⟩
  let b : Δ := ⟨ζ, hζ⟩
  obtain ⟨lift⟩ := cross_lift F
  obtain ⟨O⟩ := h1 F lift (m a) (avoid a) (regular η hη)
  obtain ⟨M, _, _, _, _, _, S, marks, _⟩ := h2 F Δ regular m avoid a b hne.symm O
  let scalar (γ : K) : K[X] := if h : γ ∈ Δ then S ⟨γ, h⟩ else 0
  have hmarked (γ : K) (hγ : γ ∈ Δ) : AnchorMark M γ (scalar γ) := by
    simpa only [scalar, dite_eq_left hγ] using marks ⟨γ, hγ⟩
  refine ⟨book, hbook, by omega, M, ⟨⟨scalar, hmarked, ?_⟩⟩⟩
  intro γ hγ δ hδ he
  exact same_scalar_label (hmarked γ hγ) (he ▸ hmarked δ hδ)
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
theorem proof : P1_5.c2 := by
  intro u deleted F Γ reg m avoid η ζ hne O
  classical
  obtain ⟨W,hW⟩ := O.left.trans F.U_dvd
  have hWn (i : I) : W.eval (node i) ≠ 0 :=
    eval_unit_of_dvd (hW ▸ dvd_mul_left W O.E) (F.den_nodes i)
  obtain ⟨L,c,hL,hLf,hLn,hsplit⟩ := invariant_multiple W hWn
  change L.map twist = L at hLf
  have hcn (i : I) : c.eval (node i) ≠ 0 :=
    eval_unit_of_dvd (hL ▸ dvd_mul_left c W) (hLn i)
  have hscalar (g : Γ) : ∃ S : K[X], S.map twist = S ∧
      numerator O (m g) = c * F.amp g.val * S := by
    obtain ⟨N, hN, hfix⟩ := fixed_numerator O W hW (m g) (avoid g) (reg g.val g.property)
    obtain ⟨S,hS,hNS⟩ := hsplit N hfix
    exact ⟨S,hS,by rw [hN,hNS]; ring⟩
  choose S hS ident using hscalar
  let word (i : I) := if i ∈ deleted then 0 else O.raw i / L.eval (node i)
  have hword (i : I) (hi : i ∉ deleted) : word i = O.raw i / L.eval (node i) := by simp [word, hi]
  have hden (i : I) : F.den.eval (node i) = O.E.eval (node i) * W.eval (node i) := by
    rw [hW, eval_mul]
  have hLval (i : I) : L.eval (node i) = W.eval (node i) * c.eval (node i) := by rw [hL, eval_mul]
  have hs : amplitudeDegree (F.amp η.val) (F.A 1) = F.s := by
    unfold amplitudeDegree
    rw [(reg η.val η.property).degree_eq]
    exact max_eq_left (le_max_right _ _)
  have hcop : IsCoprime O.E c := coprime_factor_of_label (sub_ne_zero.mpr hne) O.reduced (ident ζ)
  let M : AnchorModel u deleted := {
    shift := η.val
    pencil₀ := (m η).decoder
    pencil₁ := O.pencil
    pencil₀_degree := (m η).degree
    pencil₁_degree := O.pencil_degree
    E := O.E
    factor := c
    Q := O.Q
    A₀ := F.amp η.val
    A₁ := F.A 1
    word := word
    word_fixed := by
      intro i
      by_cases hi : i ∈ deleted
      · simp [word,hi]
      · rw [hword i hi, map_div₀, O.raw_fixed i hi, ← eval_twist L i, hLf]
    word_deleted := fun i hi => by simp [word, hi]
    E_monic := O.E_monic
    E_nodes := E_nodes O
    factor_nodes := fun i _ => hcn i
    coprime_factor := hcop
    offset_proper := O.proper
    offset_reduced := O.reduced
    adjacent_coprime := F.coprime.mono O.left O.right
    amplitudes_primitive := by
      obtain ⟨x,y,hxy⟩ := F.primitive
      exact ⟨x,y - x*C η.val,by unfold Direction.amp; linear_combination hxy⟩
    first_amplitude_unit := (reg η.val η.property).content_unit.of_isCoprime_of_dvd_right O.left
    height_bound := by
      rw [hs]
      have h := F.height
      change F.U.natDegree + F.s + deleted.card ≤ heightCap at h
      have hd := natDegree_le_of_dvd O.left F.U_ne
      omega
    first_word := by
      intro i hi
      rw [O.first i hi, hword i hi]
      field_simp [F.den_nodes i, hLn i]
      rw [hden, hLval]
      ring
    second_word := by
      intro i hi
      rw [O.second i hi, hword i hi]
      field_simp [E_nodes O i, F.den_nodes i, hLn i]
      rw [hden, hLval]
      ring }
  have amp_eq (g : Γ) : ModelAt.amplitude M g.val = F.amp g.val := by
    change F.amp η.val + C (g.val-η.val) * F.A 1 = F.amp g.val
    simp only [Direction.amp, map_sub]
    ring
  let marks (g : Γ) : AnchorMark M g.val (S g) := by
    have hreg := reg g.val g.property
    refine {
      bad := m g
      avoids_deleted := avoid g
      scalar_fixed := hS g
      scalar_degree := ?_
      scalar_hits := ?_
      pole_unit := ?_
      identity := ?_ }
    · by_cases hz : S g = 0
      · exact Or.inl hz
      right
      have hc : c ≠ 0 := fun h => hcn 0 (by rw [h, eval_zero])
      have hd := numerator_degree O (m g)
      rw [ident g, natDegree_mul (mul_ne_zero hc hreg.amp_ne) hz,
        natDegree_mul hc hreg.amp_ne, hreg.degree_eq] at hd
      change (S g).natDegree ≤ (k : ℤ) - 1 + (O.E.natDegree - c.natDegree -
        (amplitudeDegree (F.amp η.val) (F.A 1) : ℤ))
      rw [hs]
      omega
    · intro i hi
      have hits := hits O W hW (m g) (avoid g) i hi
      rw [ident g, eval_mul, eval_mul] at hits
      change (S g).eval (node i) = word i
      have hd := Finset.disjoint_left.mp (avoid g) hi
      rw [hword i hd, eq_div_iff (hLn i), hLval]
      apply mul_left_cancel₀ (hreg.node_unit i hd)
      linear_combination hits
    · rw [amp_eq g]
      exact hreg.content_unit.of_isCoprime_of_dvd_right O.left
    · rw [amp_eq g]
      exact ident g
  exact ⟨M, rfl, rfl, rfl, rfl, rfl, S, marks, fun g => rfl⟩
end
end P1_5_2
end
section
set_option maxRecDepth 8000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace P1_5_1
noncomputable section
open Polynomial P1 P1_5 FrobeniusLocator ProximityPrize.Benchmark
open K1_12 (eq_on_puncture natDegree_lt_of_degree_lt_pos eval_unit_of_dvd)
private theorem offset_of_anchor {u deleted} (F : Direction u deleted) (H : CrossLift F)
    {η : K} (m : BadMark u η) (avoid : Disjoint m.support deleted) (reg : Regular F η) :
    Nonempty (Offset F m) := by
  classical
  let a := F.amp η
  let w (i : I) := u 0 i + η * u 1 i
  let r (j : Fin 2) := F.out 0 j + C (twist η) * F.out 1 j
  let out := r 0 + C η * r 1
  let d := k + F.U.natDegree + F.s
  have hheight := F.height
  change F.U.natDegree + F.s + deleted.card ≤ heightCap at hheight
  have hk : 0 < k := by
    change 0 < 131072
    decide
  have hagMargin : k + heightCap ≤ agreement := by
    change 164399 ≤ 179944
    decide
  have hdetMargin : k + 2 * heightCap ≤ blockLength := by
    change 197726 ≤ 262144
    decide
  have hpos : 0 < d := by dsimp only [d]; omega
  have hA1 : (F.A 1).natDegree ≤ F.s := le_max_right _ _
  have ha : a.natDegree = F.s := reg.degree_eq
  have ha' : (a.map twist).natDegree ≤ F.s := natDegree_map_le.trans ha.le
  have hr (j : Fin 2) : (r j).natDegree < d := by
    apply (natDegree_add_le _ _).trans_lt
    exact max_lt (natDegree_lt_of_degree_lt_pos hpos (F.out_degree 0 j))
      ((natDegree_C_mul_le _ _).trans_lt (natDegree_lt_of_degree_lt_pos hpos (F.out_degree 1 j)))
  have hout : out.natDegree < d := (natDegree_add_le _ _).trans_lt
    (max_lt (hr 0) ((natDegree_C_mul_le _ _).trans_lt (hr 1)))
  have hrn (j : Fin 2) (i : I) (hi : i ∉ deleted) : (r j).eval (node i) =
      F.U.eval (node i) * (a.map twist).eval (node i) * u j i -
      F.V.eval (node i) * (F.A j).eval (node i) * twist (w i) := by
    simp only [r, w, a, Direction.amp, eval_twist, eval_add, eval_mul, eval_C,
      F.nodes i hi, map_add, map_mul]
    ring
  have hspec (i : I) (hi : i ∉ deleted) : out.eval (node i) =
      F.U.eval (node i) * (a.map twist).eval (node i) * w i -
      F.V.eval (node i) * a.eval (node i) * twist (w i) := by
    simp only [out, eval_add, eval_mul, eval_C, hrn _ i hi, a, Direction.amp, w, eval_add,
      eval_mul, eval_C]
    ring
  have hp := natDegree_lt_of_degree_lt_pos hk m.degree
  have ident : F.U * a.map twist * m.decoder - F.V * a * m.decoder.map twist = out := by
    let left := F.U * a.map twist * m.decoder - F.V * a * m.decoder.map twist
    have hdeg : left.natDegree < d := by
      apply (natDegree_sub_le _ _).trans_lt (max_lt ?_ ?_)
      · apply natDegree_mul_le.trans_lt
        have h : (F.U * a.map twist).natDegree ≤ F.U.natDegree + (a.map twist).natDegree :=
          natDegree_mul_le
        dsimp only [d]; omega
      · apply natDegree_mul_le.trans_lt
        have h : (F.V * a).natDegree ≤ F.V.natDegree+a.natDegree := natDegree_mul_le
        have h' : (m.decoder.map twist).natDegree ≤ m.decoder.natDegree := natDegree_map_le
        have := F.degrees_eq
        dsimp only [d]; omega
    apply sub_eq_zero.mp
    by_contra hne
    have hc := Strata.root_nodes_card_le node IRSProfile.domain.injective (left-out) hne m.support
      (by intro i hi
          rw [eval_sub, hspec i (Finset.disjoint_left.mp avoid hi)]
          simp only [left, eval_sub, eval_mul, eval_twist, m.hits i hi, w, sub_self])
    have hd := natDegree_sub_le left out
    have hag : agreement ≤ m.support.card := m.agreement
    dsimp only [d] at hdeg hout
    omega
  have hG := natDegree_le_of_dvd H.left F.U_ne
  have hLd := natDegree_lt_of_degree_lt_pos (by omega : 0 < k + F.s + H.G.natDegree) H.degree_lt
  have determinant : H.G * (a * r 1 - F.A 1 * out) = F.U * a.map twist * H.L := by
    apply eq_on_puncture (deleted := deleted) (d := d + F.s + H.G.natDegree)
    · change d + F.s + H.G.natDegree + deleted.card ≤ blockLength
      dsimp only [d]
      omega
    · apply natDegree_mul_le.trans_lt
      have h1 := @natDegree_mul_le _ _ a (r 1)
      have h2 := @natDegree_mul_le _ _ (F.A 1) out
      have h3 := natDegree_sub_le (a * r 1) (F.A 1 * out)
      have := hr 1
      omega
    · apply natDegree_mul_le.trans_lt
      have h := @natDegree_mul_le _ _ F.U (a.map twist)
      dsimp only [d]; omega
    · intro i hi
      simp only [eval_mul, eval_sub, hrn 1 i hi, hspec i hi, H.nodes i hi, a, Direction.amp,
        eval_add, eval_mul, eval_C, w]
      ring
  have div : a ∣ H.L + H.G * F.A 1 * m.decoder := by
    have cop : IsCoprime a (F.U * a.map twist) :=
      reg.content_unit.mul_right reg.adjacent
    apply cop.dvd_of_dvd_mul_left
    refine ⟨H.G * (r 1 + F.A 1 * F.V * m.decoder.map twist), ?_⟩
    linear_combination H.G * F.A 1 * ident - determinant
  obtain ⟨J, hJ⟩ := div
  have hjd : J.natDegree < k + H.G.natDegree := by
    by_cases hj : J = 0
    · simp [hj]
    have h := natDegree_add_le H.L (H.G * F.A 1 * m.decoder)
    rw [hJ, natDegree_mul reg.amp_ne hj, ha] at h
    have h1 := @natDegree_mul_le _ _ H.G (F.A 1)
    have h2 := @natDegree_mul_le _ _ (H.G * F.A 1) m.decoder
    omega
  let f : RatFunc K := algebraMap K[X] (RatFunc K) J / algebraMap K[X] (RatFunc K) H.G
  have hfrac : f.num * H.G = J * f.denom := (RatFunc.num_mul_eq_mul_denom_iff H.monic.ne_zero).mpr rfl
  have hE : f.denom ∣ H.G := RatFunc.denom_div_dvd _ _
  let Q := f.num %ₘ f.denom
  let pencil := f.num /ₘ f.denom
  have division : Q + f.denom * pencil = f.num := modByMonic_add_div _ _
  have hn : f.num.natDegree < k + f.denom.natDegree := by
    by_cases hn : f.num = 0
    · simp [hn]
    have hj : J ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hfrac
      exact mul_ne_zero hn H.monic.ne_zero hfrac
    have h := congrArg natDegree hfrac
    rw [natDegree_mul hn H.monic.ne_zero, natDegree_mul hj f.denom_ne_zero] at h
    omega
  have hpencil : pencil.degree < k := by
    have hd : pencil.natDegree < k := by
      rw [show pencil.natDegree = f.num.natDegree - f.denom.natDegree from
        natDegree_divByMonic _ f.monic_denom]
      omega
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hd)
  let raw (i : I) := F.den.eval (node i) * (w i - m.decoder.eval (node i)) / a.eval (node i)
  have hUn (i : I) := eval_unit_of_dvd F.U_dvd (F.den_nodes i)
  have hfixed (i : I) (hi : i ∉ deleted) : twist (raw i) = raw i := by
    have h1 := congrArg (eval (node i)) ident
    simp only [eval_sub, eval_mul, eval_twist, hspec i hi] at h1
    have h2 := congrArg (eval (node i)) F.phase
    simp only [eval_mul, eval_twist] at h2
    have ha0 : a.eval (node i) ≠ 0 := reg.node_unit i hi
    have haσ : twist (a.eval (node i)) ≠ 0 := (map_ne_zero twist).mpr ha0
    simp only [raw, map_div₀, map_mul, map_sub]
    apply (div_eq_div_iff haσ ha0).mpr
    apply mul_left_cancel₀ (hUn i)
    linear_combination F.den.eval (node i) * h1 +
      a.eval (node i) * (twist (w i) - twist (m.decoder.eval (node i))) * h2
  refine ⟨{
    pencil := pencil
    pencil_degree := hpencil
    E := f.denom
    Q := Q
    E_monic := f.monic_denom
    left := hE.trans H.left
    right := (map_dvd (Polynomial.mapRingHom twist) hE).trans H.right
    proper := degree_modByMonic_lt _ f.monic_denom
    reduced := ?_
    raw := raw
    raw_fixed := hfixed
    first := ?_
    second := ?_ }⟩
  · obtain ⟨x, y, h⟩ := f.isCoprime_num_denom
    rw [← division] at h
    exact ⟨x, x * pencil + y, by linear_combination h⟩
  · intro i hi
    change w i - m.decoder.eval (node i) = a.eval (node i) * raw i / F.den.eval (node i)
    have ha0 : a.eval (node i) ≠ 0 := reg.node_unit i hi
    simp only [raw]
    field_simp [ha0, F.den_nodes i]
  · intro i hi
    have h1 := congrArg (eval (node i)) hJ
    simp only [eval_add, eval_mul, H.nodes i hi] at h1
    have h2 := congrArg (eval (node i)) hfrac
    simp only [eval_mul, ← division, eval_add, eval_mul] at h2
    have hEn := eval_unit_of_dvd ((hE.trans H.left).trans F.U_dvd) (F.den_nodes i)
    have hGn := eval_unit_of_dvd (H.left.trans F.U_dvd) (F.den_nodes i)
    have ha0 : a.eval (node i) ≠ 0 := reg.node_unit i hi
    change u 1 i - pencil.eval (node i) = Q.eval (node i) / f.denom.eval (node i) +
      (F.A 1).eval (node i) * raw i / F.den.eval (node i)
    simp only [raw]
    field_simp [F.den_nodes i, hEn, ha0]
    apply mul_left_cancel₀ hGn
    have h3 : a.eval (node i) = (F.A 0).eval (node i) + η * (F.A 1).eval (node i) := by
      simp only [a, Direction.amp, eval_add, eval_mul, eval_C]
    dsimp [w]
    linear_combination f.denom.eval (node i) * h1 - a.eval (node i) * h2 +
      f.denom.eval (node i) * H.G.eval (node i) * u 1 i * h3
theorem proof : P1_5.c1 := by
  intro u deleted F H η m avoid reg
  exact offset_of_anchor F H m avoid reg
end
end P1_5_1
end
