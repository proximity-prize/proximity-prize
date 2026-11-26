import ProximityPrize.SubmissionBinaryLower.B6401T4Rows

set_option Elab.async false
set_option maxHeartbeats 800000

/-!
# Universal Standardized 5-Bucket Table 4 Grid Checker & Soundness (`B6401T4Grid`)

Every bin across ALL 120 Table 4 branches (`B6401CertsT4a`, `B6401CertsT4b1`, `B6401CertsT4b2`)
strictly uses either:
1. The single trivial bucket `[0/1, 1/1]` (`SINGLE`), OR
2. The universal 5-bucket grid `STD5 = [(0, 1/100), (1/100, 3/100), (3/100, 3/50), (3/50, 1/10), (1/10, 1)]`.

Because every branch's bucket at slot `r ∈ Fin 5` is bounded by the uniform per-slot cap
`(STD5_C1 r, STD5_C0 r, STD5_Q2 r)` whose sum across `r = 0..4` is `< 2^64` even for two `(1+1)`
Table 4 factors (`c1 * 3850 + 2 * c0 < 1.826e19 < 1.844e19`), `B6401FactorBound` can mix ANY
combination of the 120 branches across `z ∈ S_clean` with zero algebraic `Z`-specialization proofs!
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401T4Grid

open B6401Params B6401IntFarkas B6401T4Rows

def T4_START_N : Nat := 5 * wY - 1
def T4_START_D : Nat := wY
def T4_END_N : Nat := 28
def T4_END_D : Nat := 5

def SINGLE_C1 : Nat := 568181562293398
def SINGLE_C0 : Nat := 14826852660816514
def SINGLE_Q2 : Nat := 2217152712661728740

/-- Exact universal 5-bucket grid `(loGNum, loGDen, hiGNum, hiGDen)` for `r ∈ Fin 5`. -/
def std5Bounds : Fin 5 → Nat × Nat × Nat × Nat
  | ⟨0, _⟩ => (0, 1, 1, 100)
  | ⟨1, _⟩ => (1, 100, 3, 100)
  | ⟨2, _⟩ => (3, 100, 3, 50)
  | ⟨3, _⟩ => (3, 50, 1, 10)
  | ⟨4, _⟩ => (1, 10, 1, 1)

def std5C1 : Fin 5 → Nat
  | ⟨0, _⟩ => 1831831292304511
  | ⟨1, _⟩ => 2062802537751712
  | ⟨2, _⟩ => 691225347295235
  | ⟨3, _⟩ => 27125133064475
  | ⟨4, _⟩ => 18731711645034

def std5C0 : Fin 5 → Nat
  | ⟨0, _⟩ => 86105259530173353
  | ⟨1, _⟩ => 94353836948897909
  | ⟨2, _⟩ => 31181839677614463
  | ⟨3, _⟩ => 720781716071225
  | ⟨4, _⟩ => 474989838930275

def std5Q2 : Fin 5 → Nat
  | ⟨0, _⟩ => 7224760994135413703
  | ⟨1, _⟩ => 8130497443628658756
  | ⟨2, _⟩ => 2723581265697445768
  | ⟨3, _⟩ => 105873325238714493
  | ⟨4, _⟩ => 73067066488101832

def T4_C1_SUM : Nat := 4631716022060967
def T4_C0_SUM : Nat := 212836707711687225
def T4_Q2_SUM : Nat := 18257780095188334552

lemma sum_std5C1 : (∑ r : Fin 5, std5C1 r) = T4_C1_SUM := by decide
lemma sum_std5C0 : (∑ r : Fin 5, std5C0 r) = T4_C0_SUM := by decide
lemma sum_std5Q2 : (∑ r : Fin 5, std5Q2 r) = T4_Q2_SUM := by decide
lemma single_le_sum : SINGLE_C1 ≤ T4_C1_SUM ∧ SINGLE_C0 ≤ T4_C0_SUM ∧ SINGLE_Q2 ≤ T4_Q2_SUM := by decide

/-- Check one bucket against expected `(loN, loD, hiN, hiD)` and per-slot `(c1Cap, c0Cap, q2Cap)`. -/
def checkGridBucket (nv : Nat)
    (rowBuilder : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Array SparseRow × Array SparseRow)
    (cLoNum cLoDen cHiNum cHiDen loN loD hiN hiD c1Cap c0Cap q2Cap : Nat) (b : T4BucketCert) : Bool :=
  (b.loGNum == loN) && (b.loGDen == loD) && (b.hiGNum == hiN) && (b.hiGDen == hiD) &&
  let (ub, eq) := rowBuilder cLoNum cLoDen cHiNum cHiDen loN loD hiN hiD
  checkT4Bucket nv ub eq cLoNum cLoDen cHiNum cHiDen b &&
  (b.m == 0 ||
    (b.cap1.c1Bkt ≤ c1Cap && b.cap1.c0Bkt ≤ c0Cap && b.cap2.c1Bkt * 3850 + b.cap2.c0Bkt ≤ q2Cap))

/-- Check that a `T4BinCert` uses either `SINGLE` (`[0/1, 1/1]`) OR the exact universal `STD5` 5-bucket grid,
with every bucket passing `checkT4Bucket` and its universal per-slot cap! -/
def checkT4GridBin (nv : Nat)
    (rowBuilder : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Array SparseRow × Array SparseRow)
    (bin : T4BinCert) : Bool :=
  match bin.buckets with
  | [b] =>
      checkGridBucket nv rowBuilder bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen
        0 1 1 1 SINGLE_C1 SINGLE_C0 SINGLE_Q2 b
  | [b0, b1, b2, b3, b4] =>
      checkGridBucket nv rowBuilder bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen
        0 1 1 100 (std5C1 0) (std5C0 0) (std5Q2 0) b0 &&
      checkGridBucket nv rowBuilder bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen
        1 100 3 100 (std5C1 1) (std5C0 1) (std5Q2 1) b1 &&
      checkGridBucket nv rowBuilder bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen
        3 100 3 50 (std5C1 2) (std5C0 2) (std5Q2 2) b2 &&
      checkGridBucket nv rowBuilder bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen
        3 50 1 10 (std5C1 3) (std5C0 3) (std5Q2 3) b3 &&
      checkGridBucket nv rowBuilder bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen
        1 10 1 1 (std5C1 4) (std5C0 4) (std5Q2 4) b4
  | _ => false

/-- Check that a list of `T4BinCert`s contiguously covers `[startN/startD, endN/endD]` and every bin
passes `checkT4GridBin`! -/
def checkT4GridBranch (nv : Nat)
    (rowBuilder : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Array SparseRow × Array SparseRow)
    (startN startD endN endD : Nat) (bins : List T4BinCert) : Bool :=
  let rec go (curN curD : Nat) : List T4BinCert → Bool
    | [] => curN * endD == endN * curD
    | bin :: rest =>
      if bin.cLoDen == 0 || bin.cHiDen == 0 then false
      else if curN * bin.cLoDen != bin.cLoNum * curD then false
      else if !checkT4GridBin nv rowBuilder bin then false
      else go bin.cHiNum bin.cHiDen rest
  go startN startD bins

/-! ### Soundness Lemmas -/

lemma checkGridBucket_spec {nv : Nat}
    {rowBuilder : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Array SparseRow × Array SparseRow}
    {cLoNum cLoDen cHiNum cHiDen loN loD hiN hiD c1Cap c0Cap q2Cap : Nat} {b : T4BucketCert}
    (h : checkGridBucket nv rowBuilder cLoNum cLoDen cHiNum cHiDen loN loD hiN hiD c1Cap c0Cap q2Cap b = true) :
    b.loGNum = loN ∧ b.loGDen = loD ∧ b.hiGNum = hiN ∧ b.hiGDen = hiD ∧
    (let rows := rowBuilder cLoNum cLoDen cHiNum cHiDen loN loD hiN hiD
     checkT4Bucket nv rows.1 rows.2 cLoNum cLoDen cHiNum cHiDen b = true) ∧
    (b.m = 0 ∨ (b.cap1.c1Bkt ≤ c1Cap ∧ b.cap1.c0Bkt ≤ c0Cap ∧ b.cap2.c1Bkt * 3850 + b.cap2.c0Bkt ≤ q2Cap)) := by
  unfold checkGridBucket at h
  dsimp only at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, h6⟩
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  rcases h6 with hm0 | ⟨⟨hc1, hc0⟩, hq2⟩
  · exact Or.inl hm0
  · exact Or.inr ⟨hc1, hc0, hq2⟩

/-- Unpack `checkT4GridBin = true` into either a single `[0, 1]` bucket OR an indexed `Fin 5 → T4BucketCert`
matching `std5Bounds` and `(std5C1, std5C0, std5Q2)`! -/
theorem checkT4GridBin_cases {nv : Nat}
    {rowBuilder : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Array SparseRow × Array SparseRow}
    {bin : T4BinCert} (h : checkT4GridBin nv rowBuilder bin = true) :
    (∃ b : T4BucketCert,
      b.loGNum = 0 ∧ b.loGDen = 1 ∧ b.hiGNum = 1 ∧ b.hiGDen = 1 ∧
      (let rows := rowBuilder bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen 0 1 1 1
       checkT4Bucket nv rows.1 rows.2 bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen b = true) ∧
      (b.m = 0 ∨ (b.cap1.c1Bkt ≤ SINGLE_C1 ∧ b.cap1.c0Bkt ≤ SINGLE_C0 ∧
        b.cap2.c1Bkt * 3850 + b.cap2.c0Bkt ≤ SINGLE_Q2))) ∨
    (∀ r : Fin 5, ∃ b : T4BucketCert,
      let bd := std5Bounds r
      b.loGNum = bd.1 ∧ b.loGDen = bd.2.1 ∧ b.hiGNum = bd.2.2.1 ∧ b.hiGDen = bd.2.2.2 ∧
      (let rows := rowBuilder bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen bd.1 bd.2.1 bd.2.2.1 bd.2.2.2
       checkT4Bucket nv rows.1 rows.2 bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen b = true) ∧
      (b.m = 0 ∨ (b.cap1.c1Bkt ≤ std5C1 r ∧ b.cap1.c0Bkt ≤ std5C0 r ∧
        b.cap2.c1Bkt * 3850 + b.cap2.c0Bkt ≤ std5Q2 r))) := by
  unfold checkT4GridBin at h
  rcases hbk : bin.buckets with _ | ⟨b0, r0⟩
  · simp [hbk] at h
  · rcases r0 with _ | ⟨b1, r1⟩
    · simp only [hbk] at h
      exact Or.inl ⟨b0, checkGridBucket_spec h⟩
    · rcases r1 with _ | ⟨b2, r2⟩
      · simp [hbk] at h
      · rcases r2 with _ | ⟨b3, r3⟩
        · simp [hbk] at h
        · rcases r3 with _ | ⟨b4, r4⟩
          · simp [hbk] at h
          · rcases r4 with _ | ⟨b5, r5⟩
            · simp only [hbk, Bool.and_eq_true] at h
              rcases h with ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩
              right; intro r
              fin_cases r
              · exact ⟨b0, checkGridBucket_spec h0⟩
              · exact ⟨b1, checkGridBucket_spec h1⟩
              · exact ⟨b2, checkGridBucket_spec h2⟩
              · exact ⟨b3, checkGridBucket_spec h3⟩
              · exact ⟨b4, checkGridBucket_spec h4⟩
            · simp [hbk] at h

/-- Any `cVal ∈ [startN/startD, endN/endD]` belongs to some bin `bin ∈ bins` passing `checkT4GridBin`! -/
theorem exists_bin_of_checkT4GridBranch {nv : Nat}
    {rowBuilder : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Array SparseRow × Array SparseRow}
    {startN startD endN endD : Nat} {bins : List T4BinCert}
    (hstartD : 0 < startD) (hendD : 0 < endD)
    (hstart_lt : startN * endD < endN * startD)
    (hchk : checkT4GridBranch nv rowBuilder startN startD endN endD bins = true)
    (cVal : ℚ)
    (hlo : (startN : ℚ) / (startD : ℚ) ≤ cVal) (hhi : cVal ≤ (endN : ℚ) / (endD : ℚ)) :
    ∃ bin ∈ bins,
      0 < bin.cLoDen ∧ 0 < bin.cHiDen ∧
      (bin.cLoNum : ℚ) / (bin.cLoDen : ℚ) ≤ cVal ∧ cVal ≤ (bin.cHiNum : ℚ) / (bin.cHiDen : ℚ) ∧
      checkT4GridBin nv rowBuilder bin = true := by
  have hgo : ∀ (L : List T4BinCert) (curN curD : Nat), 0 < curD →
      checkT4GridBranch.go nv rowBuilder endN endD curN curD L = true →
      ((curN : ℚ) / (curD : ℚ) < cVal ∨ ((curN : ℚ) / (curD : ℚ) = cVal ∧ L ≠ [])) →
      ∃ bin ∈ L,
        0 < bin.cLoDen ∧ 0 < bin.cHiDen ∧
        (bin.cLoNum : ℚ) / (bin.cLoDen : ℚ) ≤ cVal ∧ cVal ≤ (bin.cHiNum : ℚ) / (bin.cHiDen : ℚ) ∧
        checkT4GridBin nv rowBuilder bin = true := by
    intro L
    induction L with
    | nil =>
        intro curN curD hcurD h hcur
        unfold checkT4GridBranch.go at h
        have heq : curN * endD = endN * curD := beq_iff_eq.mp h
        have hrat : (curN : ℚ) / (curD : ℚ) = (endN : ℚ) / (endD : ℚ) := by
          have hcQ : (curD : ℚ) ≠ 0 := by exact_mod_cast hcurD.ne'
          have heQ : (endD : ℚ) ≠ 0 := by exact_mod_cast hendD.ne'
          rw [div_eq_div_iff hcQ heQ]; exact_mod_cast heq
        rcases hcur with hlt | ⟨_, hne⟩
        · linarith
        · exact absurd rfl hne
    | cons bin rest ih =>
        intro curN curD hcurD h hcur
        unfold checkT4GridBranch.go at h
        by_cases h1 : (bin.cLoDen == 0 || bin.cHiDen == 0) = true
        · rw [if_pos h1] at h; cases h
        rw [if_neg h1] at h
        by_cases h2 : (curN * bin.cLoDen != bin.cLoNum * curD) = true
        · rw [if_pos h2] at h; cases h
        rw [if_neg h2] at h
        by_cases h3 : (!checkT4GridBin nv rowBuilder bin) = true
        · rw [if_pos h3] at h; cases h
        rw [if_neg h3] at h
        have hloD : 0 < bin.cLoDen := by by_contra h0; simp [show bin.cLoDen = 0 by omega] at h1
        have hhiD : 0 < bin.cHiDen := by by_contra h0; simp [show bin.cHiDen = 0 by omega] at h1
        have hcross : curN * bin.cLoDen = bin.cLoNum * curD := by
          by_contra hne
          have : (curN * bin.cLoDen != bin.cLoNum * curD) = true := bne_iff_ne.mpr hne
          exact h2 this
        have hbin_ok : checkT4GridBin nv rowBuilder bin = true := by
          cases hb : checkT4GridBin nv rowBuilder bin
          · simp [hb] at h3
          · rfl
        have hlo_eq : (curN : ℚ) / (curD : ℚ) = (bin.cLoNum : ℚ) / (bin.cLoDen : ℚ) := by
          have h1Q : (curD : ℚ) ≠ 0 := by exact_mod_cast hcurD.ne'
          have h2Q : (bin.cLoDen : ℚ) ≠ 0 := by exact_mod_cast hloD.ne'
          rw [div_eq_div_iff h1Q h2Q]; exact_mod_cast hcross
        have hcur_le : (bin.cLoNum : ℚ) / (bin.cLoDen : ℚ) ≤ cVal := by
          rw [← hlo_eq]; rcases hcur with hlt | ⟨heq, _⟩ <;> linarith
        rcases le_or_gt cVal ((bin.cHiNum : ℚ) / (bin.cHiDen : ℚ)) with hle | hgt
        · exact ⟨bin, List.mem_cons_self, hloD, hhiD, hcur_le, hle, hbin_ok⟩
        · obtain ⟨b', hb', h1', h2', h3', h4', h5'⟩ := ih bin.cHiNum bin.cHiDen hhiD h (Or.inl hgt)
          exact ⟨b', List.mem_cons_of_mem _ hb', h1', h2', h3', h4', h5'⟩
  have hne : bins ≠ [] := by
    rintro rfl
    unfold checkT4GridBranch checkT4GridBranch.go at hchk
    have heq : startN * endD = endN * startD := beq_iff_eq.mp hchk
    omega
  exact hgo bins startN startD hstartD hchk (lt_or_eq_of_le hlo |>.elim Or.inl fun h => Or.inr ⟨h, hne⟩)

end B6401T4Grid
end ProximityPrize.SubmissionBinaryLower
