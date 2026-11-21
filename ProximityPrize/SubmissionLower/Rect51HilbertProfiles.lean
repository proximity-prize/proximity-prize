import ProximityPrize.SubmissionLower.Rect51HilbertLayers
import ProximityPrize.SubmissionLower.HighCore82706Tangent

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000

namespace Rect51Hilbert
noncomputable section
open K1_14 (FX)
open HighCore82706_5_2_2 (rv)
open MvPolynomial
open scoped BigOperators
open private comp_card from ProximityPrize.SubmissionLower.HighCore82706Tangent

def rootFree (B : Block) : Finset (Fin 2) :=
  Finset.univ.filter fun i => Sum.inl i ∈ B.free
def seedFree₀ (B : Block) : Finset (Fin 2) :=
  Finset.univ.filter fun i => seed₀ i ∈ B.free
def seedFree₁ (B : Block) : Finset (Fin 2) :=
  Finset.univ.filter fun i => seed₁ i ∈ B.free
def ramp {R : Type} [Semiring R] (r : ℕ) (s : R) : R :=
  if r = 0 then 0 else if r = 1 then 1 else s

private def velocities (B : Block) (b : ℕ) : Finset ℕ :=
  if v₀ ∈ B.free then (if v₁ ∈ B.free then Finset.range (b+1) else {b})
  else if v₁ ∈ B.free then {0} else ∅
private theorem mem_velocities (B : Block) {b j : ℕ} (hb : 0 < b) :
    j ∈ velocities B b ↔ j ≤ b ∧ (v₀ ∉ B.free → j = 0) ∧
      (v₁ ∉ B.free → b-j = 0) := by
  by_cases h₀' : v₀ ∈ B.free <;> by_cases h₁' : v₁ ∈ B.free <;>
    simp [velocities, h₀', h₁'] <;> omega
private theorem mem_comp {n d : ℕ} {F : Finset (Fin n)} {f : Fin n →₀ ℕ} :
    f ∈ F.finsuppAntidiag d ↔ (∑ i, f i) = d ∧ ∀ i ∉ F, f i = 0 := by
  rw [Finset.mem_finsuppAntidiag', Finsupp.sum_fintype _ _ (fun _ => rfl)]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · exact fun h i hi => Finsupp.notMem_support_iff.mp (fun hm => hi (h hm))
  · intro h i hi
    by_contra hf
    exact (Finsupp.mem_support_iff.mp hi) (h i hf)
private def project {n : ℕ} (m : Exponent) (f : Fin n → CoxVar) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m (f i))
private def pack (r : Fin 2 →₀ ℕ) (j b : ℕ) (z₀ z₁ : Fin 2 →₀ ℕ) : Exponent :=
  Finsupp.equivFunOnFinite.symm (Sum.elim r (Sum.elim ![j,b-j] (Sum.elim z₀ z₁)))
private abbrev Increments (B : Block) (d : Degree) :=
  {m : Exponent // (∀ i ∉ B.free, m i = 0) ∧ Finsupp.weight coxWeight m = d}
private def enum (B : Block) (a b c f : ℕ) (hb : 0 < b) :
    Increments B (nefDegree a b c f) ≃
      (Σ j : velocities B b, (rootFree B).finsuppAntidiag (a+2*j.val)) ×
        (seedFree₀ B).finsuppAntidiag c × (seedFree₁ B).finsuppAntidiag f where
  toFun m := by
    have hz := m.prop.1
    have hw := m.prop.2
    rw [weight_coordinates] at hw
    have ha := congrArg Prod.fst hw
    have hv := congrArg (fun d : Degree => d.2.1) hw
    have hc := congrArg (fun d : Degree => d.2.2.1) hw
    have hf := congrArg (fun d : Degree => d.2.2.2) hw
    change m.val h₀ + m.val h₁ + 2*m.val v₁ = a+2*b at ha
    change m.val v₀ + m.val v₁ = b at hv
    change m.val (seed₀ 0) + m.val (seed₀ 1) = c at hc
    change m.val (seed₁ 0) + m.val (seed₁ 1) = f at hf
    refine ⟨⟨⟨m.val v₀, (mem_velocities B hb).mpr ⟨by omega, hz _, ?_⟩⟩,
      ⟨project m.val Sum.inl, mem_comp.mpr ⟨?_, ?_⟩⟩⟩,
      ⟨project m.val seed₀, mem_comp.mpr ⟨?_, ?_⟩⟩,
      ⟨project m.val seed₁, mem_comp.mpr ⟨?_, ?_⟩⟩⟩
    · intro h
      have := hz v₁ h
      omega
    · rw [Fin.sum_univ_two]
      change m.val h₀ + m.val h₁ = a+2*m.val v₀
      omega
    · exact fun i hi => hz (Sum.inl i) (by simpa [rootFree] using hi)
    · rw [Fin.sum_univ_two]
      exact hc
    · exact fun i hi => hz (seed₀ i) (by simpa [seedFree₀] using hi)
    · rw [Fin.sum_univ_two]
      exact hf
    · exact fun i hi => hz (seed₁ i) (by simpa [seedFree₁] using hi)
  invFun p := by
    rcases p with ⟨⟨j, r⟩, z₀, z₁⟩
    have hj := ((mem_velocities B hb).mp j.prop).1
    have hj₀ := ((mem_velocities B hb).mp j.prop).2.1
    have hj₁ := ((mem_velocities B hb).mp j.prop).2.2
    have hr := (mem_comp.mp r.prop).1
    have hrz := (mem_comp.mp r.prop).2
    have hs₀ := (mem_comp.mp z₀.prop).1
    have hsz₀ := (mem_comp.mp z₀.prop).2
    have hs₁ := (mem_comp.mp z₁.prop).1
    have hsz₁ := (mem_comp.mp z₁.prop).2
    rw [Fin.sum_univ_two] at hr hs₀ hs₁
    refine ⟨pack r.val j.val b z₀.val z₁.val, ?_, ?_⟩
    · intro i hi
      rcases i with i | (i | (i | i))
      · exact hrz i (by simpa [rootFree] using hi)
      · fin_cases i
        · exact hj₀ hi
        · exact hj₁ hi
      · exact hsz₀ i (fun h => hi (Finset.mem_filter.mp h).2)
      · exact hsz₁ i (fun h => hi (Finset.mem_filter.mp h).2)
    · rw [weight_coordinates]
      change (r.val 0+r.val 1+2*(b-j.val), j.val+(b-j.val),
        z₀.val 0+z₀.val 1, z₁.val 0+z₁.val 1) = (a+2*b,b,c,f)
      rw [hr, hs₀, hs₁]
      congr 1
      · omega
      · congr 1
        omega
  left_inv m := by
    have hw := m.prop.2
    rw [weight_coordinates] at hw
    have hv := congrArg (fun d : Degree => d.2.1) hw
    change m.val v₀ + m.val v₁ = b at hv
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    rcases i with i | (i | (i | i))
    · rfl
    · fin_cases i
      · rfl
      · change b-m.val v₀ = m.val v₁
        omega
    · rfl
    · rfl
  right_inv p := by
    rcases p with ⟨⟨j,r⟩,z₀,z₁⟩
    apply Prod.ext
    · exact Sigma.ext (Subtype.ext rfl) (heq_of_eq (Subtype.ext (Finsupp.ext fun _ => rfl)))
    · apply Prod.ext <;> exact Subtype.ext (Finsupp.ext fun _ => rfl)

private def shift (B : Block) (d e : Degree) (hw : Finsupp.weight coxWeight B.base + d = e) :
    Increments B d ≃ {m : Exponent // m ∈ B.exponents ∧ Finsupp.weight coxWeight m = e} :=
  Equiv.ofBijective (fun m => ⟨B.base + m.val, ⟨m.val, m.prop.1, rfl⟩, by
    rw [map_add, m.prop.2, hw]⟩) (by
      constructor
      · intro m n h
        exact Subtype.ext (add_left_cancel (congrArg Subtype.val h))
      · rintro ⟨_, ⟨m, hm, rfl⟩, h⟩
        rw [map_add, ← hw] at h
        exact ⟨⟨m, hm, add_left_cancel h⟩, rfl⟩)
private theorem sum_widths (a b : ℕ) :
    (∑ j ∈ Finset.range (b+1), (a+2*j+1)) = (b+1)*(a+b+1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih]
    ring
private theorem root_velocity_card (B : Block) {a b : ℕ} (ha : 0 < a) :
    (∑ j ∈ velocities B b, ((rootFree B).finsuppAntidiag (a+2*j)).card) =
      rv (rootFree B).card (v₀ ∈ B.free) (v₁ ∈ B.free)
        (b+1) (a+1) (a+b+1) (a+2*b+1) := by
  have hR : (rootFree B).card ≤ 2 := (Finset.card_le_univ _).trans (by simp)
  have hc (j : ℕ) := comp_card (rootFree B) (n := a+2*j) (by omega) (hR.trans (by decide))
  simp_rw [hc]
  interval_cases h : (rootFree B).card <;>
    by_cases h₀' : v₀ ∈ B.free <;> by_cases h₁' : v₁ ∈ B.free <;>
    simp [rv, velocities, h₀', h₁', sum_widths]
private theorem rectangular_card (S : Finset (Fin 2)) {a : ℕ} (ha : 0 < a) :
    (S.finsuppAntidiag a).card = ramp S.card (a+1) := by
  have hS : S.card ≤ 2 := (Finset.card_le_univ _).trans (by simp)
  rw [comp_card S ha (hS.trans (by decide))]
  interval_cases h : S.card <;> simp [ramp, h]

theorem fibre_card (B : Block) {a b c f : ℕ} {e : Degree}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hf : 0 < f)
    (hw : Finsupp.weight coxWeight B.base + nefDegree a b c f = e) :
    exponentCount B.exponents e =
      rv (rootFree B).card (v₀ ∈ B.free) (v₁ ∈ B.free)
        (b+1) (a+1) (a+b+1) (a+2*b+1) *
      (ramp (seedFree₀ B).card (c+1) * ramp (seedFree₁ B).card (f+1)) := by
  classical
  change Nat.card {m : Exponent // m ∈ B.exponents ∧ Finsupp.weight coxWeight m = e} = _
  rw [Nat.card_congr ((shift B _ _ hw).symm.trans (enum B a b c f hb)),
    Nat.card_prod, Nat.card_prod, Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  change (∑ j ∈ (velocities B b).attach, ((rootFree B).finsuppAntidiag (a+2*j.val)).card) * _ = _
  rw [Finset.sum_attach (velocities B b) (fun j : ℕ => ((rootFree B).finsuppAntidiag (a+2*j)).card),
    root_velocity_card B ha, rectangular_card _ hc, rectangular_card _ hf]

private abbrev Exp := Fin 4 →₀ ℕ
private theorem coeff_add_apply (p q : HilbertPoly) (m : Exp) :
    (p+q).coeff m = p.coeff m + q.coeff m := by simp
private theorem coeff_nonneg {p : HilbertPoly} (hp : NonnegativeTop p)
    {m : Exp} (hm : p.totalDegree ≤ m.degree) : 0 ≤ p.coeff m := by
  rcases lt_or_eq_of_le hm with h | h
  · rw [coeff_eq_zero_of_totalDegree_lt h]
  · exact hp m h.symm
private theorem top_add_right {p q : HilbertPoly} (hp : NonnegativeTop p)
    (hq : NonnegativeTop q) (hq' : q ≠ 0) (h : p.totalDegree ≤ q.totalDegree) :
    NonnegativeTop (p+q) := by
  obtain ⟨m, hm, hd⟩ := Finset.exists_mem_eq_sup q.support (support_nonempty.mpr hq')
    (fun m => m.degree)
  change q.totalDegree = m.degree at hd
  have hpos : 0 < q.coeff m :=
    lt_of_le_of_ne (hq m hd.symm) (ne_comm.mp (MvPolynomial.mem_support_iff.mp hm))
  have hm' : m ∈ (p+q).support := by
    rw [MvPolynomial.mem_support_iff, coeff_add_apply]
    exact (add_pos_of_nonneg_of_pos (coeff_nonneg hp (h.trans_eq hd)) hpos).ne'
  have hd' : (p+q).totalDegree = q.totalDegree :=
    le_antisymm ((totalDegree_add _ _).trans (max_eq_right h).le)
      (hd.trans_le (le_totalDegree hm'))
  intro n hn
  change n.degree = (p+q).totalDegree at hn
  rw [coeff_add_apply]
  exact add_nonneg (coeff_nonneg hp (h.trans_eq (hn.trans hd').symm)) (hq n (hn.trans hd'))
private theorem top_add {p q : HilbertPoly} (hp : NonnegativeTop p)
    (hq : NonnegativeTop q) : NonnegativeTop (p+q) := by
  by_cases hp' : p = 0
  · simpa [hp'] using hq
  by_cases hq' : q = 0
  · simpa [hq'] using hp
  rcases le_total p.totalDegree q.totalDegree with h | h
  · exact top_add_right hp hq hq' h
  · rw [add_comm]
    exact top_add_right hq hp hp' h
private theorem top_zero : NonnegativeTop (0 : HilbertPoly) := by
  intro m _
  simp
private theorem top_mul {p q : HilbertPoly} (hp : NonnegativeTop p)
    (hq : NonnegativeTop q) : NonnegativeTop (p*q) := by
  classical
  by_cases hp' : p = 0
  · simpa [hp'] using top_zero
  by_cases hq' : q = 0
  · simpa [hq'] using top_zero
  intro m hm
  change m.degree = (p*q).totalDegree at hm
  rw [totalDegree_mul_of_isDomain hp' hq'] at hm
  rw [coeff_mul]
  apply Finset.sum_nonneg
  rintro ⟨a,b⟩ hab
  have he : a+b = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  have hd : a.degree+b.degree = m.degree := by rw [← map_add, he]
  by_cases ha : p.totalDegree < a.degree
  · simp [coeff_eq_zero_of_totalDegree_lt ha]
  by_cases hb : q.totalDegree < b.degree
  · simp [coeff_eq_zero_of_totalDegree_lt hb]
  exact mul_nonneg (hp a (by change a.degree = p.totalDegree; omega))
    (hq b (by change b.degree = q.totalDegree; omega))
private theorem top_C (r : ℚ) (hr : 0 ≤ r) : NonnegativeTop (C r : HilbertPoly) := by
  intro m _
  rw [coeff_C]
  split_ifs
  · exact hr
  · exact le_rfl
private theorem top_one : NonnegativeTop (1 : HilbertPoly) := by
  simpa only [map_one] using top_C 1 zero_le_one
private def affine (i j : Fin 4) (r b : ℚ) : HilbertPoly :=
  MvPolynomial.X i + C r * MvPolynomial.X j + C b
private theorem top_affine (i j : Fin 4) {r : ℚ} (hr : 0 ≤ r) (b : ℚ) :
    NonnegativeTop (affine i j r b) := by
  classical
  have hX (k : Fin 4) (m : Exp) : 0 ≤ (MvPolynomial.X k : HilbertPoly).coeff m := by
    rw [coeff_X]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  let p : HilbertPoly := MvPolynomial.X i + C r * MvPolynomial.X j
  have hp (m : Exp) : 0 ≤ p.coeff m := by
    change 0 ≤ (MvPolynomial.X i + C r * MvPolynomial.X j : HilbertPoly).coeff m
    rw [coeff_add_apply, coeff_C_mul]
    exact add_nonneg (hX i m) (mul_nonneg hr (hX j m))
  have hm : Finsupp.single i 1 ∈ p.support := by
    rw [MvPolynomial.mem_support_iff]
    change (MvPolynomial.X i + C r * MvPolynomial.X j : HilbertPoly).coeff (Finsupp.single i 1) ≠ 0
    rw [coeff_add_apply, coeff_C_mul, show (MvPolynomial.X i : HilbertPoly).coeff (Finsupp.single i 1) = 1 by
      simp [coeff_X]]
    exact (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr (hX j _))).ne'
  have hd := le_totalDegree hm
  change (Finsupp.single i 1).degree ≤ p.totalDegree at hd
  rw [Finsupp.degree_single] at hd
  intro m hm
  change m.degree = (p + C b).totalDegree at hm
  have hd' : (C b : HilbertPoly).totalDegree < p.totalDegree := by
    rw [totalDegree_C]
    omega
  rw [totalDegree_add_eq_left_of_totalDegree_lt hd'] at hm
  change 0 ≤ (p + C b).coeff m
  have hm' : (C b : HilbertPoly).totalDegree < m.degree := by rwa [hm]
  rw [coeff_add_apply, coeff_eq_zero_of_totalDegree_lt hm', add_zero]
  exact hp m
private def baseDegree (B : Block) : Degree := Finsupp.weight coxWeight B.base
private def profile (B : Block) : HilbertPoly :=
  let (u,v,w,z) := baseDegree B
  rv (rootFree B).card (v₀ ∈ B.free) (v₁ ∈ B.free)
    (affine 1 1 0 (1-v)) (affine 0 0 0 (1+2*v-u))
    (affine 0 1 1 (1+v-u)) (affine 0 1 2 (1-u)) *
  (ramp (seedFree₀ B).card (affine 2 2 0 (1-w)) *
    ramp (seedFree₁ B).card (affine 3 3 0 (1-z)))
private theorem profile_top (B : Block) : NonnegativeTop (profile B) := by
  apply top_mul
  · unfold rv
    split_ifs <;> first
      | exact top_zero
      | exact top_one
      | exact top_affine _ _ (by norm_num) _
      | exact top_mul (top_affine _ _ (by norm_num) _) top_one
      | exact top_mul (top_affine _ _ (by norm_num) _) (top_affine _ _ (by norm_num) _)
  · apply top_mul <;> unfold ramp <;> split_ifs <;> first
      | exact top_zero
      | exact top_one
      | exact top_affine _ _ (by norm_num) _

private def threshold (B : Block) : ℕ :=
  let (u,v,w,z) := baseDegree B
  u+v+w+z+1
private theorem profile_eval (B : Block) (h t s₀ s₁ : ℕ)
    (hh : threshold B ≤ h) (ht : threshold B ≤ t)
    (hs₀ : threshold B ≤ s₀) (hs₁ : threshold B ≤ s₁) :
    (exponentCount B.exponents (nefDegree h t s₀ s₁) : ℚ) = evalHilbert (profile B) h t s₀ s₁ := by
  rcases hbase : baseDegree B with ⟨u,v,w,z⟩
  have hw : Finsupp.weight coxWeight B.base = (u,v,w,z) := hbase
  simp only [threshold, hbase] at hh ht hs₀ hs₁
  let a := h+2*v-u
  let b := t-v
  let c := s₀-w
  let f := s₁-z
  have ha : 0 < a := by dsimp [a]; omega
  have hb : 0 < b := by dsimp [b]; omega
  have hc : 0 < c := by dsimp [c]; omega
  have hf : 0 < f := by dsimp [f]; omega
  have hweight : Finsupp.weight coxWeight B.base + nefDegree a b c f = nefDegree h t s₀ s₁ := by
    rw [hw]
    change (u+(a+2*b), v+b, w+c,z+f) = (h+2*t,t,s₀,s₁)
    dsimp [a,b,c,f]
    congr 1
    · omega
    · congr 1
      · omega
      · congr 1 <;> omega
  rw [fibre_card B ha hb hc hf hweight, Nat.cast_mul, Nat.cast_mul]
  let E := MvPolynomial.eval ![(h : ℚ),(t : ℚ),(s₀ : ℚ),(s₁ : ℚ)]
  unfold evalHilbert profile
  rw [hbase]
  change _ = E (_ * _)
  rw [map_mul, map_mul]
  congr 1
  · unfold rv
    split_ifs <;> simp [E, affine, a, b, Nat.cast_sub (show u ≤ h+2*v by omega),
      Nat.cast_sub (show v ≤ t by omega)] <;> ring
  · congr 1
    · unfold ramp
      split_ifs <;> simp [E, affine, c, Nat.cast_sub (show w ≤ s₀ by omega)] <;> ring
    · unfold ramp
      split_ifs <;> simp [E, affine, f, Nat.cast_sub (show z ≤ s₁ by omega)] <;> ring

theorem ambient_count (h t s₀ s₁ : ℕ) (hh : 1 ≤ h) (ht : 1 ≤ t)
    (hs₀ : 1 ≤ s₀) (hs₁ : 1 ≤ s₁) :
    (exponentCount Set.univ (nefDegree h t s₀ s₁) : ℚ) = evalHilbert ambient h t s₀ s₁ := by
  let B : Block := ⟨0, Finset.univ⟩
  have exponents : B.exponents = Set.univ := by
    ext m
    simp only [Set.mem_univ, iff_true]
    exact ⟨m, by simp [B], by simp [B]⟩
  have base : baseDegree B = 0 := by simp [baseDegree, B]
  have hB : threshold B = 1 := by simp [threshold, base]
  have poly : profile B = ambient := by
    unfold profile
    rw [base]
    simp [rv, B, rootFree, seedFree₀, seedFree₁, ramp, affine, ambient, mul_assoc]
  rw [← exponents, ← poly]
  exact profile_eval B h t s₀ s₁ (hB ▸ hh) (hB ▸ ht) (hB ▸ hs₀) (hB ▸ hs₁)

private theorem sum_top (blocks : Finset Block) : NonnegativeTop (∑ B ∈ blocks, profile B) := by
  classical
  induction blocks using Finset.induction_on with
  | empty => simpa using top_zero
  | insert B _ hB ih => rw [Finset.sum_insert hB]; exact top_add (profile_top B) ih

theorem block_profile (blocks : Finset Block) :
    ∃ p : HilbertPoly, NonnegativeTop p ∧
      EventuallyInChamber (fun h t s₀ s₁ => (blockCount blocks (nefDegree h t s₀ s₁) : ℚ) =
        evalHilbert p h t s₀ s₁) := by
  let N := ∑ B ∈ blocks, threshold B
  refine ⟨∑ B ∈ blocks, profile B, sum_top blocks, N, fun h t s₀ s₁ hh ht hs₀ hs₁ => ?_⟩
  change ((∑ B ∈ blocks, exponentCount B.exponents (nefDegree h t s₀ s₁) : ℕ) : ℚ) =
    MvPolynomial.eval ![(h : ℚ),(t : ℚ),(s₀ : ℚ),(s₁ : ℚ)] (∑ B ∈ blocks, profile B)
  rw [Nat.cast_sum, map_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hN : threshold B ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hB
  exact profile_eval B h t s₀ s₁ (hN.trans hh) (hN.trans ht) (hN.trans hs₀) (hN.trans hs₁)

end
end Rect51Hilbert
