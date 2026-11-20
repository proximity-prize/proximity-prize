import ProximityPrize.SubmissionLower.Fast072
import ProximityPrize.SubmissionLower.Fast073
import ProximityPrize.SubmissionLower.Fast074
import ProximityPrize.SubmissionLower.Fast076
set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

namespace LowFat6921

open K1 K1_13 K1_13_4 K1_13_4_2 K1_13_4_2_1 Finset
open scoped Polynomial BigOperators

noncomputable section

abbrev firstMixedOrder : ℕ := 6951000
abbrev secondMixedOrder : ℕ := 2289994
abbrev newFirstCut : ℕ := 5000 * 180169 - firstMixedOrder

theorem secondCut_eq : secondCut = 5000 * 180169 - secondMixedOrder := by decide

def newCut : Bank → ℕ
  | .first => newFirstCut
  | .second => secondCut

private def newRawBase (b : Bank) : ℕ := newCut b + 1 - 131071 * b.box.b

private def newWidth (b : Bank) (h q k l : ℕ) : ℕ :=
  newRawBase b + 131071 * (b.box.b - q) + (l + 2 * k) + (2300 + (b.box.b - q)) * h

private theorem newCut_large (b : Bank) : 131071 * b.box.b ≤ newCut b + 1 := by
  cases b <;> decide

private def moment (B c a d e : ℕ) : ℕ :=
  jetSum B fun q k l => c + a * (l + 2 * k) + d * (B - q) + e * (B - q) ^ 2

private def raw (b : Bank) : ℕ := moment b.box.b (newRawBase b) 1 131071 0
private def extra (B : ℕ) : ℕ := moment B 0 0 2300 1
private def credit (B : ℕ) : ℕ := jetSum B fun q _ _ => 2300 + (B - q)

private theorem grade_sum (B : ℕ) (f : ℕ → ℕ) :
    jetSum B (fun q _ _ => f q) =
      ∑ q ∈ range (B + 1), gradeCount ⟨B, 2300, 1150⟩ q * f q := by
  simp only [jetSum, gradeCount, Nat.reduceDiv, min_self, sum_mul, sum_const,
    card_range, Nat.nsmul_eq_mul]

private theorem pole_eq (b : Bank) : poleDebit b.box = 70001 * credit b.box.b + extra b.box.b := by
  have hb : b.box = ⟨b.box.b, 2300, 1150⟩ := by cases b <;> rfl
  have hgrade (q : ℕ) : gradeCount b.box q = gradeCount ⟨b.box.b, 2300, 1150⟩ q :=
    congrArg (fun a => gradeCount a q) hb
  calc
    _ = jetSum b.box.b (fun q _ _ => (2300 + (b.box.b - q)) * (70001 + (b.box.b - q))) := by
      rw [grade_sum, poleDebit]
      apply sum_congr rfl
      intro q hq
      have hq' := mem_range.mp hq
      have he : b.box.b + b.box.j - q = 2300 + (b.box.b - q) := by
        rw [box_index]
        omega
      rw [hgrade, he]
      ring
    _ = _ := by
      simp only [credit, extra, moment, jetSum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun q _ => sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
      ring

private theorem volume_eq (b : Bank) (h : ℕ) :
    jetSum b.box.b (newWidth b h) = raw b + credit b.box.b * h := by
  simp only [newWidth, raw, moment, credit, jetSum, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun q _ => sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  ring

private abbrev Triple := Σ _ : ℕ, Σ _ : ℕ, ℕ

private def byGrade (B : ℕ) : Finset Triple :=
  (range (B + 1)).sigma fun q => (range (min q 1150 + 1)).sigma fun k =>
    range (min (q - k) (2300 - 2 * k) + 1)

private def byDeficit (B : ℕ) : Finset Triple :=
  (range 1151).sigma fun k => (range (2300 - 2 * k + 1)).sigma fun l =>
    range (B - (k + l) + 1)

set_option linter.constructorNameAsVariable false in
/-- Fix the middle and top exponents first, then sum the deficit from the total cap. -/
private theorem jetSum_deficit {M : Type*} [AddCommMonoid M] {B : ℕ} (hB : 2300 ≤ B)
    (f : ℕ → ℕ → ℕ → M) :
    jetSum B (fun q k l => f k l (B - q)) =
      ∑ k ∈ range 1151, ∑ l ∈ range (2300 - 2 * k + 1),
        ∑ r ∈ range (B - (k + l) + 1), f k l r := by
  calc
    _ = ∑ t ∈ byGrade B, f t.2.1 t.2.2 (B - t.1) := by
      simp only [jetSum, byGrade, sum_sigma]
    _ = ∑ t ∈ byDeficit B, f t.1 t.2.1 t.2.2 := by
      refine sum_nbij' (fun t : Triple => ⟨t.2.1, t.2.2, B - t.1⟩)
        (fun t : Triple => ⟨B - t.2.2, t.1, t.2.1⟩) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · rintro ⟨q, k, l⟩ h
        simp only [byGrade, byDeficit, mem_sigma, mem_range, Nat.lt_succ_iff, le_min_iff] at *
        omega
      · rintro ⟨k, l, r⟩ h
        simp only [byGrade, byDeficit, mem_sigma, mem_range, Nat.lt_succ_iff, le_min_iff] at *
        omega
      · rintro ⟨q, k, l⟩ h
        simp only [byGrade, mem_sigma, mem_range] at h
        rw [show B - (B - q) = q by omega]
      · rintro ⟨k, l, r⟩ h
        simp only [byDeficit, mem_sigma, mem_range] at h
        rw [show B - (B - r) = r by omega]
    _ = _ := by simp only [byDeficit, sum_sigma]

/-- Twelve times the sum of a cubic over the initial interval of length n. -/
private def cubicSum (c d e f n : ℤ) : ℤ :=
  12 * c * n + 6 * d * n * (n - 1) + 2 * e * n * (n - 1) * (2 * n - 1) +
    3 * f * n ^ 2 * (n - 1) ^ 2

private theorem sum_cubic (c d e f : ℤ) (n : ℕ) :
    12 * (∑ i ∈ range n, (c + d * (i : ℤ) + e * i ^ 2 + f * i ^ 3)) =
      cubicSum c d e f n := by
  induction n with
  | zero => simp [cubicSum]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    unfold cubicSum
    ring

/-- After summing over the deficit, the summand is a cubic in the middle exponent.
The two scaled summations give a factor of 144. -/
private def slice (B c a d e k : ℤ) : ℤ :=
  let N := B - k + 1
  let C := c + 2 * a * k
  cubicSum
    (12 * N * C + 6 * d * N * (N - 1) + 2 * e * N * (N - 1) * (2 * N - 1))
    (12 * N * a - 12 * C + 6 * d * (1 - 2 * N) + 2 * e * (-6 * N ^ 2 + 6 * N - 1))
    (-12 * a + 6 * d + 2 * e * (6 * N - 3))
    (-4 * e)
    (2301 - 2 * k)

private theorem sum_slice {B k : ℕ} (hB : 2300 ≤ B) (hk : k < 1151) (c a d e : ℤ) :
    144 * (∑ l ∈ range (2300 - 2 * k + 1), ∑ r ∈ range (B - (k + l) + 1),
      (c + a * ((l : ℤ) + 2 * k) + d * (r : ℤ) + e * (r : ℤ) ^ 2)) =
      slice B c a d e k := by
  let N : ℤ := (B : ℤ) - k + 1
  let C : ℤ := c + 2 * a * k
  have hn : ((2300 - 2 * k + 1 : ℕ) : ℤ) = 2301 - 2 * (k : ℤ) := by omega
  unfold slice
  rw [← hn, ← sum_cubic]
  rw [show (144 : ℤ) = 12 * 12 by decide, mul_assoc, mul_sum]
  congr 1
  apply sum_congr rfl
  intro l hl
  have hl' := mem_range.mp hl
  have hlen : ((B - (k + l) + 1 : ℕ) : ℤ) = N - l := by dsimp [N]; omega
  have hi := sum_cubic (c + a * ((l : ℤ) + 2 * k)) d e 0 (B - (k + l) + 1)
  simp only [zero_mul, add_zero] at hi
  rw [hi, hlen]
  dsimp [N, C, cubicSum]
  ring

/-- The successive terms are the forward differences of f at zero,
multiplied by 120 times the corresponding binomial polynomials. -/
private def antidifference (f : ℤ → ℤ) (n : ℤ) : ℤ :=
  n * (120 * f 0 + (n - 1) * (60 * (f 1 - f 0) +
    (n - 2) * (20 * (f 2 - 2 * f 1 + f 0) +
      (n - 3) * (5 * (f 3 - 3 * f 2 + 3 * f 1 - f 0) +
        (n - 4) * (f 4 - 4 * f 3 + 6 * f 2 - 4 * f 1 + f 0)))))

private theorem sum_slices (B c a d e : ℤ) (n : ℕ) :
    120 * (∑ k ∈ range n, slice B c a d e k) =
      antidifference (slice B c a d e) n := by
  have hstep (x : ℤ) :
      antidifference (slice B c a d e) (x + 1) =
        antidifference (slice B c a d e) x + 120 * slice B c a d e x := by
    unfold antidifference slice cubicSum
    ring
  induction n with
  | zero => simp [antidifference]
  | succ n ih => rw [Nat.cast_succ, hstep, sum_range_succ, mul_add, ih]

private theorem evaluate (B c a d e : ℕ) (hB : 2300 ≤ B) :
    17280 * (moment B c a d e : ℤ) =
      antidifference (slice B c a d e) 1151 := by
  have hs : 144 * (moment B c a d e : ℤ) = ∑ k ∈ range 1151, slice B c a d e k := by
    unfold moment
    rw [jetSum_deficit hB (fun k l r => c + a * (l + 2 * k) + d * r + e * r ^ 2)]
    simp only [Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [mul_sum]
    exact sum_congr rfl fun k hk => sum_slice hB (mem_range.mp hk) _ _ _ _
  rw [show (17280 : ℤ) = 120 * 144 by decide, mul_assoc, hs, sum_slices]
  exact congrArg (antidifference (slice B c a d e))
    (show ((1151 : ℕ) : ℤ) = 1151 from by decide)

private theorem moment_eq (B c a d e value : ℕ) (hB : 2300 ≤ B)
    (cert : antidifference (slice B c a d e) 1151 = 17280 * (value : ℤ)) :
    moment B c a d e = value := by
  have h := (evaluate B c a d e hB).trans cert
  omega

set_option maxHeartbeats 300000 in
private theorem bank_moments :
    raw .first = 2810732118875241660 ∧ raw .second = 2845830394728456187 ∧
      extra 6789 = 129644787051371740 ∧ extra 6820 = 131501361258434295 := by
  have h₁ := moment_eq 6789 4052982 1 131071 0 2810732118875241660 (by decide) (by decide)
  have h₂ := moment_eq 6820 4650787 1 131071 0 2845830394728456187 (by decide) (by decide)
  have h₃ := moment_eq 6789 0 0 2300 1 129644787051371740 (by decide) (by decide)
  have h₄ := moment_eq 6820 0 0 2300 1 131501361258434295 (by decide) (by decide)
  have r₁ : newRawBase .first = 4052982 := by decide
  have r₂ : newRawBase .second = 4650787 := by decide
  have e₁ : raw .first = moment 6789 4052982 1 131071 0 :=
    congrArg (fun base => moment 6789 base 1 131071 0) r₁
  have e₂ : raw .second = moment 6820 4650787 1 131071 0 :=
    congrArg (fun base => moment 6820 base 1 131071 0) r₂
  exact ⟨e₁.trans h₁, e₂.trans h₂, h₃, h₄⟩

set_option maxHeartbeats 300000 in
private theorem endpoint (b : Bank) :
    b.targetRank + 262144 * (70001 * b.nodeRank) + 2447 * extra b.box.b ≤ 70001 * raw b := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := bank_moments
  cases b
  · have hB : Bank.first.box.b = 6789 := rfl
    have he := (congrArg extra hB).trans h₃
    have ha : (1 : ℕ) + 262144 * (70001 * 10697571688375) + 2447 * 129644787051371740 ≤
        70001 * 2810732118875241660 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      Bank.first.targetRank + 262144 * (70001 * Bank.first.nodeRank) + 2447 * x ≤ 70001 * y)
      he h₁).mpr ha
  · have hB : Bank.second.box.b = 6820 := rfl
    have he := (congrArg extra hB).trans h₄
    have ha : (2561085868844197170227 : ℕ) + 262144 * (70001 * 10697783317215) +
        2447 * 131501361258434295 ≤ 70001 * 2845830394728456187 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      Bank.second.targetRank + 262144 * (70001 * Bank.second.nodeRank) + 2447 * x ≤ 70001 * y)
      he h₂).mpr ha

/-- The height-dependent credit cancels before bounding the remaining debit. -/
theorem budget (b : Bank) (h : ℕ) (hh : h ≤ 2447) :
    b.targetRank + 262144 * (70001 * b.nodeRank) + h * poleDebit b.box ≤
      70001 * jetSum b.box.b (newWidth b h) := by
  have he := endpoint b
  have hm := Nat.mul_le_mul_right (extra b.box.b) hh
  rw [pole_eq, volume_eq, Nat.mul_add, Nat.mul_add]
  have hc : h * (70001 * credit b.box.b) = 70001 * (credit b.box.b * h) := by ring
  omega

private def netRank (r n e v : ℕ) : ℕ :=
  70001 * v - (r + 262144 * (70001 * n) + 2447 * e)

/-- At the maximum overhead, these are the exact margins after the target rank and both debits. -/
theorem rank_margin_at_maximum (b : Bank) :
    70001 * jetSum b.box.b (newWidth b 2447) -
      (b.targetRank + 262144 * (70001 * b.nodeRank) + 2447 * poleDebit b.box) =
      (match b with
       | .first => 132717667822087417879
       | .second => 20119708272540447135) := by
  trans netRank b.targetRank b.nodeRank (extra b.box.b) (raw b)
  · have hcancel : 2447 * (70001 * credit b.box.b) = 70001 * (credit b.box.b * 2447) := by ring
    rw [volume_eq, pole_eq, Nat.mul_add, Nat.mul_add, hcancel]
    have hsub (r v n e c : ℕ) :
        70001 * v + c - (r + 262144 * (70001 * n) + (c + 2447 * e)) =
          netRank r n e v := by unfold netRank; omega
    exact hsub b.targetRank (raw b) b.nodeRank (extra b.box.b) (70001 * (credit b.box.b * 2447))
  obtain ⟨h₁, h₂, h₃, h₄⟩ := bank_moments
  cases b
  · have hB : Bank.first.box.b = 6789 := rfl
    have he := (congrArg extra hB).trans h₃
    exact (congrArg₂ (fun e v =>
      netRank Bank.first.targetRank Bank.first.nodeRank e v = 132717667822087417879)
      he h₁).mpr (by decide)
  · have hB : Bank.second.box.b = 6820 := rfl
    have he := (congrArg extra hB).trans h₄
    exact (congrArg₂ (fun e v =>
      netRank Bank.second.targetRank Bank.second.nodeRank e v = 20119708272540447135)
      he h₂).mpr (by decide)

private abbrev Column (b : Bank) (h : ℕ) :=
  Σ q : Fin (b.box.b + 1), Σ k : Fin (min q.val 1150 + 1),
    Σ l : Fin (min (q.val - k.val) (2300 - 2 * k.val) + 1),
      Fin (newWidth b h q.val k.val l.val) × Fin 70001

private def exponent (u i l k : ℕ) : SeedVar →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => j.elim u (![i, l, k] ·))

@[simp] private theorem exponent_none (u i l k : ℕ) : exponent u i l k none = u := by
  simp [exponent]

@[simp] private theorem exponent_zero (u i l k : ℕ) : exponent u i l k (some 0) = i := by
  simp [exponent]

@[simp] private theorem exponent_one (u i l k : ℕ) : exponent u i l k (some 1) = l := by
  simp [exponent]

@[simp] private theorem exponent_two (u i l k : ℕ) : exponent u i l k (some 2) = k := by
  simp [exponent]

private def colExp {b : Bank} {h : ℕ} (c : Column b h) : SeedVar →₀ ℕ :=
  exponent c.2.2.2.2.val (c.1.val - c.2.1.val - c.2.2.1.val) c.2.2.1.val c.2.1.val

private def colX {b : Bank} {h : ℕ} (c : Column b h) : ℕ := c.2.2.2.1.val

private theorem column_injective (b : Bank) (h : ℕ) :
    Function.Injective (fun c : Column b h => (colExp c, colX c)) := by
  rintro ⟨q,k,l,x,u⟩ ⟨q',k',l',x',u'⟩ he
  have he₀ := congrArg (fun p : (SeedVar →₀ ℕ) × ℕ => p.1 (some 0)) he
  have he₁ := congrArg (fun p : (SeedVar →₀ ℕ) × ℕ => p.1 (some 1)) he
  have he₂ := congrArg (fun p : (SeedVar →₀ ℕ) × ℕ => p.1 (some 2)) he
  have heu := congrArg (fun p : (SeedVar →₀ ℕ) × ℕ => p.1 none) he
  have hex := congrArg Prod.snd he
  simp only [colExp, colX, exponent_zero, exponent_one, exponent_two, exponent_none] at *
  have hk := k.isLt
  have hl := l.isLt
  have hk' := k'.isLt
  have hl' := l'.isLt
  simp only [Nat.lt_succ_iff, le_min_iff] at hk hl hk' hl'
  have hq : q = q' := Fin.ext (by omega)
  subst q'
  have hkk : k = k' := Fin.ext he₂
  subst k'
  have hll : l = l' := Fin.ext he₁
  subst l'
  have hxx : x = x' := Fin.ext hex
  have huu : u = u' := Fin.ext heu
  subst x'
  subst u'
  rfl

private def coordinate (e : SeedVar →₀ ℕ) (x : ℕ) : PhysicalRow →ₗ[Geom] Geom :=
  (Polynomial.lcoeff Geom x).comp ((MvPolynomial.lcoeff Geom[X] e).restrictScalars Geom)

private def column {b : Bank} {h : ℕ} (c : Column b h) : PhysicalRow :=
  MvPolynomial.monomial (colExp c) (Polynomial.monomial (colX c) 1)

private theorem coordinate_column {b : Bank} {h : ℕ} (c : Column b h)
    (e : SeedVar →₀ ℕ) (x : ℕ) :
    coordinate e x (column c) = if colExp c = e ∧ colX c = x then 1 else 0 := by
  classical
  change ((column c).coeff e).coeff x = _
  by_cases he : colExp c = e <;> simp [column, he, Polynomial.coeff_monomial]

private theorem column_li (b : Bank) (h : ℕ) :
    LinearIndependent Geom (column (b := b) (h := h)) := by
  classical
  let L : PhysicalRow →ₗ[Geom] (Column b h → Geom) :=
    LinearMap.pi (fun c : Column b h => coordinate (colExp c) (colX c))
  apply LinearIndependent.of_comp L
  have he : L ∘ column = (Pi.basisFun Geom (Column b h) : Column b h → Column b h → Geom) := by
    funext c d
    rw [Function.comp_apply, Pi.basisFun_apply, Pi.single_apply]
    change coordinate (colExp d) (colX d) (column c) = _
    simp only [coordinate_column, ← Prod.mk.injEq, (column_injective b h).eq_iff, eq_comm]
  rw [he]
  exact (Pi.basisFun Geom (Column b h)).linearIndependent

private def space (b : Bank) (h : ℕ) : Submodule Geom PhysicalRow :=
  Submodule.span Geom (Set.range (column (b := b) (h := h)))

private theorem occurs_in_column {b : Bank} {h : ℕ} {F : PhysicalRow}
    (hF : F ∈ space b h) {e : SeedVar →₀ ℕ} {x : ℕ} (hne : (F.coeff e).coeff x ≠ 0) :
    ∃ c : Column b h, colExp c = e ∧ colX c = x := by
  classical
  by_contra! hn
  have hle : space b h ≤ LinearMap.ker (coordinate e x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    change coordinate e x (column c) = 0
    rw [coordinate_column, ite_eq_right]
    exact fun hc => (hn c hc.1 hc.2).elim
  exact hne (LinearMap.mem_ker.mp (hle hF))

private theorem column_bounds {b : Bank} {h : ℕ} (c : Column b h) :
    let e := colExp c
    Finsupp.weight (fun i : SeedVar => i.elim 0 (fun _ => 1)) e ≤ b.box.b ∧
    Finsupp.weight (fun i : SeedVar => i.elim 0 Fin.val) e ≤ b.box.j ∧
    e (some 2) ≤ b.box.t ∧ e none ≤ 70000 ∧
    colX c + e.sum (fun i n => i.elim 0 (fun j => (131071 + h - j.val) * n)) ≤
      newCut b + (b.box.b + b.box.j) * h := by
  rcases c with ⟨q,k,l,x,u⟩
  have hq := q.isLt
  have hk := k.isLt
  have hl := l.isLt
  have hx := x.isLt
  have hu := u.isLt
  simp only [Nat.lt_succ_iff, le_min_iff] at hq hk hl
  have hs : q.val - k.val - l.val + l.val + k.val = q.val := by omega
  have hi : l.val + 2 * k.val ≤ 2300 := by omega
  have hraw : newRawBase b + 131071 * b.box.b = newCut b + 1 := by
    unfold newRawBase
    have := newCut_large b
    omega
  have hcredit : (2300 + (b.box.b - q.val)) * h + h * q.val = (b.box.b + 2300) * h := by
    rw [mul_comm h q.val, ← Nat.add_mul]
    congr 1
    omega
  have hweight :
      (131071 + h - 0) * (q.val - k.val - l.val) +
        (131071 + h - 1) * l.val + (131071 + h - 2) * k.val + (l.val + 2 * k.val) =
      131071 * q.val + h * q.val := by
    have h₁ : 131071 + h - 1 + 1 = 131071 + h := by omega
    have h₂ : 131071 + h - 2 + 2 = 131071 + h := by omega
    calc
      _ = (131071 + h) * (q.val - k.val - l.val) +
          (131071 + h - 1 + 1) * l.val + (131071 + h - 2 + 2) * k.val := by
        simp only [Nat.sub_zero]
        ring
      _ = _ := by rw [h₁, h₂, ← Nat.mul_add, ← Nat.mul_add, hs, Nat.add_mul]
  have hsum :
      (exponent u.val (q.val - k.val - l.val) l.val k.val).sum
        (fun i n => i.elim 0 (fun j => (131071 + h - j.val) * n)) =
      (131071 + h - 0) * (q.val - k.val - l.val) +
        (131071 + h - 1) * l.val + (131071 + h - 2) * k.val := by
    rw [Finsupp.sum_fintype _ _ (fun i => by cases i <;> simp),
      Fintype.sum_option, Fin.sum_univ_three]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option, Fin.sum_univ_succ,
      colExp, smul_eq_mul, ← Nat.add_assoc, hs] using hq
  · simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option, Fin.sum_univ_succ,
      colExp, smul_eq_mul, Nat.mul_comm] using hi
  · simpa [colExp] using hk.2
  · simpa [colExp] using Nat.le_of_lt_succ hu
  · change x.val + (exponent u.val (q.val - k.val - l.val) l.val k.val).sum
      (fun i n => i.elim 0 (fun j => (131071 + h - j.val) * n)) ≤
        newCut b + (b.box.b + b.box.j) * h
    rw [hsum, box_index]
    change x.val < newWidth b h q.val k.val l.val at hx
    unfold newWidth at hx
    omega

private theorem space_bounds (b : Bank) (h : ℕ) (F : PhysicalRow) (hF : F ∈ space b h) :
    Caps b.box F ∧ TrueCut h (newCut b + (b.box.b + b.box.j) * h) F := by
  have he (e : SeedVar →₀ ℕ) (hm : e ∈ F.support) :
      ∃ c : Column b h, colExp c = e ∧ colX c = (F.coeff e).natDegree := by
    exact occurs_in_column hF (by
      rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
      exact MvPolynomial.mem_support_iff.mp hm)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · apply Finset.sup_le
    intro e hm
    obtain ⟨c, rfl, _⟩ := he e hm
    exact (column_bounds c).1
  · apply Finset.sup_le
    intro e hm
    obtain ⟨c, rfl, _⟩ := he e hm
    exact (column_bounds c).2.1
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e hm
    obtain ⟨c, rfl, _⟩ := he e hm
    exact (column_bounds c).2.2.1
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e hm
    obtain ⟨c, rfl, _⟩ := he e hm
    exact (column_bounds c).2.2.2.1
  · intro e hm
    obtain ⟨c, rfl, hx⟩ := he e hm
    rw [← hx]
    exact (column_bounds c).2.2.2.2

/-- The true ambient space, with the full independent seed cap. -/
theorem ambient (b : Bank) (h : ℕ) :
    ∃ V : Submodule Geom PhysicalRow, Module.Finite Geom V ∧
      (∀ F ∈ V, Caps b.box F ∧ TrueCut h (newCut b + (b.box.b + b.box.j) * h) F) ∧
      Module.finrank Geom V = 70001 * jetSum b.box.b (newWidth b h) := by
  refine ⟨space b h, Module.Finite.span_of_finite _ (Set.finite_range _), space_bounds b h, ?_⟩
  rw [space, finrank_span_eq_card (column_li b h)]
  simp only [Column, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Nat.mul_comm _ 70001]
  unfold jetSum
  simp only [Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Fin.sum_univ_eq_sum_range]

private theorem rank_lt_of_le {V U : Submodule Geom PhysicalRow} [Module.Finite Geom V]
    (h : U ≤ V) : Module.rank Geom U < Cardinal.aleph0 :=
  (Submodule.rank_mono h).trans_lt (Module.rank_lt_aleph0 Geom ↥V)

private theorem codim_inf_le (V U W : Submodule Geom PhysicalRow) [Module.Finite Geom V] :
    codimIn V (U ⊓ W) ≤ codimIn V U + codimIn V W := by
  have he : (V ⊓ U) ⊓ (V ⊓ W) = V ⊓ (U ⊓ W) := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left)
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left))
        (le_inf inf_le_left (inf_le_right.trans inf_le_right))
  have h := Submodule.rank_sup_add_rank_inf_eq (V ⊓ U) (V ⊓ W)
  rw [he] at h
  have hle : (V ⊓ U) ⊔ (V ⊓ W) ≤ V := sup_le inf_le_left inf_le_left
  have hdim := congrArg Cardinal.toNat h
  rw [Cardinal.toNat_add (rank_lt_of_le hle) (rank_lt_of_le inf_le_left),
    Cardinal.toNat_add (rank_lt_of_le inf_le_left) (rank_lt_of_le inf_le_left)] at hdim
  change Module.finrank Geom ((V ⊓ U) ⊔ (V ⊓ W) : Submodule Geom PhysicalRow) +
    Module.finrank Geom (V ⊓ (U ⊓ W) : Submodule Geom PhysicalRow) =
      Module.finrank Geom (V ⊓ U : Submodule Geom PhysicalRow) +
      Module.finrank Geom (V ⊓ W : Submodule Geom PhysicalRow) at hdim
  have hsup := Submodule.finrank_mono hle
  unfold codimIn
  omega

private theorem codim_finset_inf_le {ι : Type*} (V : Submodule Geom PhysicalRow)
    [Module.Finite Geom V] (T : Finset ι) (U : ι → Submodule Geom PhysicalRow) (r : ℕ)
    (hr : ∀ i ∈ T, codimIn V (U i) ≤ r) :
    codimIn V (T.inf U) ≤ T.card * r := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.inf_empty, Finset.card_empty, zero_mul, codimIn, inf_top_eq, Nat.sub_self]
  | insert i T hi ih =>
    rw [Finset.inf_insert, Finset.card_insert_of_notMem hi, Nat.succ_mul]
    have hi' := hr i (Finset.mem_insert_self i T)
    have hT := ih fun j hj => hr j (Finset.mem_insert_of_mem hj)
    exact (codim_inf_le V (U i) (T.inf U)).trans
      (by simpa only [add_comm] using Nat.add_le_add hi' hT)

private theorem codim_antitone (V : Submodule Geom PhysicalRow) [Module.Finite Geom V]
    {U W : Submodule Geom PhysicalRow} (h : U ≤ W) : codimIn V W ≤ codimIn V U :=
  Nat.sub_le_sub_left
    (Cardinal.toNat_le_toNat (Submodule.rank_mono (inf_le_inf_left V h))
      (rank_lt_of_le (show V ⊓ W ≤ V from inf_le_left))) _

private theorem separable_rank (h3 : K1_13_4_2.c3) {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (a : Shape) (V : Submodule Geom PhysicalRow) [hV : Module.Finite Geom V]
    (hcap : ∀ F ∈ V, Caps a F) (hsep : P.H.Separable) :
    codimIn V (poleCondition P L a (liftX P.H)) ≤ P.H.natDegree * poleDebit a := by
  classical
  let T : Finset Geom := ⟨P.H.roots, Polynomial.nodup_roots hsep⟩
  have hcard : T.card = P.H.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hroot (α : Geom) (hα : α ∈ T) : P.H.IsRoot α :=
    (Polynomial.mem_roots P.monic.ne_zero).mp hα
  have hprod : (∏ α ∈ T, localPole α) = liftX P.H := by
    have he : (∏ α ∈ T, (Polynomial.X - Polynomial.C α)) = P.H :=
      ((IsAlgClosed.splits P.H).eq_prod_roots_of_monic P.monic).symm
    change _ = Polynomial.mapRingHom (algebraMap Geom GenericSeed) P.H
    rw [← he, map_prod]
    simp [localPole]
  let W : Geom → Submodule Geom PhysicalRow := fun α => poleCondition P L a (localPole α)
  have hlocal (α : Geom) (hα : α ∈ T) : codimIn V (W α) ≤ poleDebit a := by
    apply h3 Γ s P L a α V hV hcap (hroot α hα)
    exact hsep.eval₂_derivative_ne_zero (RingHom.id Geom) (hroot α hα)
  have hsub : T.inf W ≤ poleCondition P L a (liftX P.H) := by
    intro F hF
    have hd (α : Geom) (hα : α ∈ T) :
        (MvPolynomial.C (localPole α) : RawRow) ^ (a.b + a.j) ∣ restore P L F := by
      have hle : T.inf W ≤ W α := Finset.inf_le hα
      exact (mem_poleCondition P L a _ _).mp (hle hF)
    have hcop (α β : Geom) (hne : α ≠ β) :
        IsCoprime ((MvPolynomial.C (localPole α) : RawRow) ^ (a.b + a.j))
          ((MvPolynomial.C (localPole β) : RawRow) ^ (a.b + a.j)) := by
      apply IsCoprime.pow
      apply IsCoprime.map (f := MvPolynomial.C)
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr ((FaithfulSMul.algebraMap_injective Geom GenericSeed).ne hne)).isUnit
    have h := Finset.prod_dvd_of_coprime (t := T) (fun α _ β _ hne => hcop α β hne) hd
    rw [Finset.prod_pow, ← map_prod MvPolynomial.C, hprod] at h
    exact (mem_poleCondition P L a _ _).mpr h
  have hdim := codim_finset_inf_le V T W (poleDebit a) hlocal
  rw [hcard] at hdim
  exact (codim_antitone V hsub).trans hdim

private theorem dimension_of_debits {ambient kept required physical pole : ℕ}
    (hsize : required + physical + pole ≤ ambient)
    (hcodim : ambient - kept ≤ physical + pole) : required ≤ kept := by
  omega

private theorem rank_of_bounds (h2 : K1_13_4_2.c2) (h3 : K1_13_4_2.c3) (h4 : K1_13_4_2.c4)
    (b : Bank) (w : I → K) {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (hsmall : P.H.natDegree ≤ 2447) :
    HasRank w P L b.box (newCut b) b.targetRank := by
  classical
  obtain ⟨V, hV, hbox, hdimV⟩ := ambient b P.H.natDegree
  have hsize := budget b P.H.natDegree hsmall
  rw [← hdimV] at hsize
  let : Module.Finite Geom V := hV
  have hcap : ∀ F ∈ V, Caps b.box F := fun F hF => (hbox F hF).1
  let A : I → Submodule Geom PhysicalRow := fun i => contactAt (embed (node i)) (embed (w i))
  let U : Submodule Geom PhysicalRow := ⨅ i, A i
  let W : Submodule Geom PhysicalRow := poleCondition P L b.box (liftX P.H)
  have hU : codimIn V U ≤ 262144 * (70001 * b.nodeRank) := by
    have hA (i : I) (_ : i ∈ Finset.univ) : codimIn V (A i) ≤ 70001 * b.nodeRank :=
      h2 b (embed (node i)) (embed (w i)) V hV hcap
    have h := codim_finset_inf_le V (Finset.univ : Finset I) A (70001 * b.nodeRank) hA
    have hc : (Finset.univ : Finset I).card = 262144 := Fintype.card_fin (2 ^ 18)
    rw [hc, Finset.inf_univ_eq_iInf] at h
    exact h
  have hW : codimIn V W ≤ P.H.natDegree * poleDebit b.box := by
    apply h4 Γ s P L b.box V _ hV
    intro P' L' _ hdeg hsep
    rw [← hdeg]
    exact separable_rank h3 P' L' b.box V hcap hsep
  have hdebit := (codim_inf_le V U W).trans (Nat.add_le_add hU hW)
  let S : Submodule Geom PhysicalRow := V ⊓ (U ⊓ W)
  have hdim : b.targetRank ≤ Module.finrank Geom S := dimension_of_debits hsize hdebit
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := Geom) (M := ↥S) hdim
  let e : Fin b.targetRank → PhysicalRow := fun i => (f i).val
  refine ⟨e, hf.map_injOn S.subtype Subtype.val_injective.injOn, ?_⟩
  intro i
  have hm := Submodule.mem_inf.mp (f i).property
  have hUW : e i ∈ U ⊓ W := hm.2
  have hb := hbox (e i) hm.1
  refine ⟨hb.1, hb.2, ?_, (mem_poleCondition P L b.box _ _).mp (Submodule.mem_inf.mp hUW).2⟩
  intro j
  have hmem : e i ∈ A j := (Submodule.mem_iInf A).mp (Submodule.mem_inf.mp hUW).1 j
  exact (mem_contactAt (embed (node j)) (embed (w j)) (e i)).mp hmem


private theorem contact_bound : K1_13_4_2.c2 :=
  K1_13_4_2_2.of_children K1_13_4_2_2_1.proof K1_13_4_2_2_2.proof
    K1_13_4_2_2_3.proof K1_13_4_2_2_4.proof K1_13_4_2_2_5.proof K1_13_4_2_2_6.proof

private theorem simple_pole_bound : K1_13_4_2.c3 :=
  K1_13_4_2_3.of_children K1_13_4_2_3_1.proof K1_13_4_2_3_2.proof

private theorem shifted_pole_bound : K1_13_4_2.c4 :=
  K1_13_4_2_4.of_children K1_13_4_2_4_1.proof K1_13_4_2_4_2.proof

theorem source_pair_rank (w : I → K) {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (hsmall : P.H.natDegree ≤ 2447) :
    (∃ F, F ≠ 0 ∧ Source w P L firstBox newFirstCut F) ∧
    HasRank w P L secondBox secondCut 2561085868844197170227 := by
  have hfirst := rank_of_bounds contact_bound simple_pole_bound shifted_pole_bound .first w P L hsmall
  have hsecond := rank_of_bounds contact_bound simple_pole_bound shifted_pole_bound .second w P L hsmall
  obtain ⟨e, he, hsource⟩ := hfirst
  let i : Fin Bank.first.targetRank := ⟨0, by decide⟩
  exact ⟨⟨e i, he.ne_zero i, hsource i⟩, hsecond⟩

end
end LowFat6921
