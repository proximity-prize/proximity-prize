import ProximityPrize.SubmissionLower.Fast072
import ProximityPrize.SubmissionLower.Fast074
import ProximityPrize.SubmissionLower.PortBase
set_option autoImplicit true
section
namespace P0_10
noncomputable section
open Polynomial
open P0 (AnchorModel AnchoredFamily K k p node twist agreement t heightCap highPrefix)
open K1_14 (L FX Seeds Equation Jet Shape Band Banks liftPoly graphEval atX
  triangle slots shapeSum sourceDebit seedHasse SeedBound)
open K1_14_3 (Surface Parent NoMovingCommon Compatible RowCaps ProjectedProduct)
open scoped BigOperators
def AdjacentChart {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (H : L[X]) : Prop :=
  let σ := frobenius L p
  let H' := H.map σ
  H.Monic ∧ H.natDegree = M.overhead.toNat ∧ H ∣ liftPoly M.E ∧
  H'.Monic ∧ H'.natDegree = M.overhead.toNat ∧ H' ∣ liftPoly (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i, H.eval (algebraMap K L (node i)) ≠ 0 ∧ H'.eval (algebraMap K L (node i)) ≠ 0) ∧
  IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H ∧
  IsCoprime ((liftPoly (M.Q * M.factor * M.A₀)).map σ) H' ∧
  ∀ γ ∈ Γ,
    let z := algebraMap K L (M.label γ)
    let D := liftPoly (M.factor * M.amplitude γ)
    let S := liftPoly (F.scalar γ)
    IsCoprime D H ∧ IsCoprime (D.map σ) H' ∧
    H ∣ D * S + C z * liftPoly M.Q ∧
    H' ∣ D.map σ * S + C (z ^ p) * (liftPoly M.Q).map σ
def band (w : ℤ) : Band :=
  if w ≤ 3554 then ⟨3554,6,188,1024,1422,290,28962⟩
  else if w ≤ 8249 then ⟨8249,4,96,582,809,165,11805⟩
  else if w ≤ 23999 then ⟨23999,4,46,582,809,165,8216⟩
  else ⟨heightCap, 4,35,582,809,165,7295⟩
def freeShape (w : ℤ) (i : Fin 2) : Shape :=
  if w ≤ 3554 then ![⟨55,76,17,1036⟩,⟨82,113,25,1601⟩] i
  else ![⟨34,47,10,515⟩,⟨58,80,17,940⟩] i
def movingShape (w : ℤ) (i : Fin 2) : Shape :=
  if w ≤ 3554 then ![⟨138,191,39,4990⟩,⟨203,282,58,7726⟩] i
  else ![⟨67,93,18,1857⟩,⟨124,172,35,3138⟩] i
def reserve (i : Fin 2) : ℕ := ![0,5] i
def terminalShape (w : ℤ) : Shape :=
  let b := band w
  ⟨b.multiplicity, b.jetBound, b.vBound, b.subbankSeeds⟩
def fullShape (w : ℤ) : Shape :=
  { terminalShape w with U := if w ≤ 3554 then 141471 else 59515 }
def scheduled (w : ℤ) : List Shape :=
  [freeShape w 0, movingShape w 0, freeShape w 1, movingShape w 1,
    fullShape w, terminalShape w]
def fullCutoff (s : Shape) : ℕ := s.m * agreement - 1
def reserveCutoff (w : ℤ) (s : Shape) (i : Fin 2) : ℕ :=
  fullCutoff s - 2 * w.toNat * reserve i
structure JetSource {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (rows : Banks) : Prop where
  nested : ∀ s ∈ scheduled M.overhead, ∀ s' ∈ scheduled M.overhead,
    s.m = s'.m → s.B = s'.B → s.J = s'.J → s.U ≤ s'.U →
    ∀ W W', W ≤ W' → rows s W ≤ rows s' W'
  necessary : ∀ s ∈ scheduled M.overhead, ∀ W, W < s.m * agreement → ∀ P ∈ rows s W,
    ∀ γ ∈ Γ, K1_14.jetAt P (M.label γ) (F.scalar γ) = 0
  shape : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, RowCaps P s
  leading : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, P ≠ 0 →
    (P.leadingCoeff.natDegree + P.natDegree) * (131071 - M.overhead.toNat) ≤ W + P.natDegree
  shift : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, ∀ i r,
    seedHasse i r P ∈ rows s (W + 2 * M.overhead.toNat * r)
  floor_bound : ∀ s ∈ scheduled M.overhead, ∀ W, W < s.m * agreement →
    (∀ q ≤ s.B, ∀ j ≤ min q s.J, q * (131071 - M.overhead.toNat) ≤ W + 1 + j) →
    triangle s.U * shapeSum s (fun q j => W + 1 + j - q * (131071 - M.overhead.toNat)) ≤
      sourceDebit M.overhead.toNat s + ∑ t ∈ Finset.range (W + 1), Module.finrank FX (rows s t)
structure BufferedPair (w : ℤ) (rows : Banks) (i : Fin 2) where
  free : Jet
  moving : Jet
  free_ne : free ≠ 0
  moving_ne : moving ≠ 0
  free_mem : free ∈ rows (freeShape w i) (reserveCutoff w (freeShape w i) i)
  moving_mem : moving ∈ rows (movingShape w i) (reserveCutoff w (movingShape w i) i)
  no_moving : NoMovingCommon free moving
def BankVanishes (rows : Banks) (s : Shape) (q : Surface) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), P ∈ q.asIdeal
def PairPass {w : ℤ} {rows : Banks} {i : Fin 2} (pair : BufferedPair w rows i)
    (q : Surface) : Prop :=
  BankVanishes rows (freeShape w i) q ∧
  BankVanishes rows (movingShape w i) q ∧ Compatible pair.free pair.moving q
def MarkOn {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (q : Surface) (γ : K) : Prop :=
  q.asIdeal ≤ RingHom.ker
    (eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
      (atX (F.scalar γ).derivative))
def ReducedEquation (w : ℤ) (f : Equation) : Prop :=
  0 < f.natDegree ∧ f.natDegree ≤ (band w).yBound ∧ f.IsPrimitive ∧
    (f.map (algebraMap Seeds (FractionRing Seeds))).Separable
def rawWidth (w : ℤ) (q j : ℕ) : ℕ :=
  (band w).multiplicity * agreement + j - q * (131071 - w.toNat)
def rawVolume (w : ℤ) : ℕ :=
  triangle (band w).subbankSeeds * shapeSum (terminalShape w) (rawWidth w)
def subbankDebit (w : ℤ) : ℕ := sourceDebit w.toNat (terminalShape w)
def forcedPower (w : ℤ) (W j : ℕ) : ℕ :=
  1 + (fullCutoff (terminalShape w) - W) / (2 * w.toNat) - j
def TerminalDivisibility (w : ℤ) (rows : Banks) (f : Equation) : Prop :=
  ∀ W < (band w).multiplicity * agreement, ∀ P ∈ rows (terminalShape w) W, P ≠ 0 →
    f ^ forcedPower w W P.natDegree ∣ P.leadingCoeff
def TerminalMass (w : ℤ) (f : Equation) : Prop :=
  let b := band w
  ∃ V : ℕ → Submodule FX Jet,
    rawVolume w ≤ subbankDebit w +
      ∑ W ∈ Finset.range (b.multiplicity * agreement), Module.finrank FX (V W) ∧
    ∀ W < b.multiplicity * agreement, ∀ P ∈ V W, P ≠ 0 →
      let j := P.natDegree
      let i := P.leadingCoeff.natDegree
      j ≤ b.vBound ∧ i + j ≤ b.jetBound ∧ (i + j) * (131071 - w.toNat) ≤ W + j ∧
        SeedBound P.leadingCoeff b.subbankSeeds ∧ f ^ forcedPower w W j ∣ P.leadingCoeff
def seedGain (w : ℤ) : ℕ :=
  let b := band w
  let U := b.subbankSeeds
  let v := b.seedBound + 1
  shapeSum (terminalShape w) fun q j => ∑ r ∈ Finset.range (U / v + 1),
    (slots U (r * v) - slots U ((r + 1) * v)) * (rawWidth w q j - 2 * w.toNat * (j + r))
def curveFactor (d : ℕ) : ℕ := t / (agreement - d) + 1
def simplePrice (w : ℤ) : ℕ :=
  let b := band w
  let d := k - 1 + b.endpoint
  let gap := agreement - d
  (t * curveFactor d * K1_14_6.mixedDegree d b.yBound b.seedBound + (gap - 1)) / gap + b.yBound
def singularDegree (w : ℤ) : ℕ :=
  (2 * (band w).yBound - 1) * (band w).seedBound
structure RetainedCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} (pairs : ∀ i : Fin 2, BufferedPair M.overhead rows i) where
  kept : Finset K
  subset : kept ⊆ Γ
  paid : (Γ \ kept).card ≤ highPrefix M.overhead
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  initial : ∀ q ∈ parents, (pairs 0).free ∈ q.asIdeal ∧ (pairs 0).moving ∈ q.asIdeal
  survives : ∀ q ∈ parents, PairPass (pairs 1) q
  terminal : ∀ q ∈ parents, BankVanishes rows (fullShape M.overhead) q
  covers : ∀ γ ∈ kept, ∃ q ∈ parents, MarkOn M F q γ
  equation : Equation
  projected : ProjectedProduct parents equation
  y_bound : equation.natDegree ≤ (band M.overhead).yBound
  divides : TerminalDivisibility M.overhead rows equation
end
end P0_10
end
section
namespace P0_10
noncomputable section
open Polynomial
open P0 (AnchorModel AnchoredFamily K p node twist agreement highRetained)
open K1_14 (L FX Seeds Equation Banks liftPoly graphEval atX atMark
  seedEmbedding SeedBound frobenius_coefficient_exception_count)
open private resultant_degree derivative_seedBound from ProximityPrize.SubmissionLower.Fast023
open scoped BigOperators
theorem adjacent_chart {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) :
    ∃ H, AdjacentChart M F H := by
  let φ := algebraMap K L
  let σ := frobenius L p
  have hsmall : M.overhead.toNat ≤ (liftPoly M.E).natDegree := by
    rw [liftPoly, natDegree_map]
    unfold AnchorModel.overhead
    omega
  obtain ⟨H, hm, hdeg, hd⟩ := K1_14.trim _ _ hsmall
  have hd' : H.map σ ∣ liftPoly (M.E.map twist) := by
    change H.map σ ∣ liftPoly (M.E.map K1.twist)
    rw [K1_14.twist_lift]
    exact Polynomial.map_dvd σ hd
  have hcop : IsCoprime H (H.map σ) := by
    have ha := M.adjacent_coprime.map (Polynomial.mapRingHom φ)
    exact (ha.of_isCoprime_of_dvd_left hd).of_isCoprime_of_dvd_right hd'
  have hunit : IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H :=
    (((M.offset_reduced.mul_left M.coprime_factor.symm).mul_left M.first_amplitude_unit).map
      (Polynomial.mapRingHom φ)).of_isCoprime_of_dvd_right hd
  refine ⟨H, hm, hdeg, hd, hm.map σ, (natDegree_map σ).trans hdeg, hd', hcop, ?_,
    hunit, hunit.map (Polynomial.mapRingHom σ), ?_⟩
  · intro i
    have h₀ : H.eval (φ (node i)) ≠ 0 := by
      intro hz
      have hb : (liftPoly M.E).eval (φ (node i)) = 0 := by
        obtain ⟨J, hj⟩ := hd
        simp [hj, eval_mul, hz]
      exact M.E_nodes i (φ.injective (by simpa [liftPoly, φ] using hb))
    have hx : σ (φ (node i)) = φ (node i) := by
      change φ (node i) ^ p = _
      rw [← map_pow, FrobeniusLocator.Native.native_domain_fixed]
    refine ⟨h₀, ?_⟩
    rw [← hx, eval_map_apply]
    exact (map_ne_zero σ).mpr h₀
  · intro γ hγ
    let z := M.label γ
    let B := F.mark γ hγ
    have ha : IsCoprime (liftPoly (M.factor * M.amplitude γ)) H :=
      ((M.coprime_factor.symm.mul_left B.pole_unit).map
        (Polynomial.mapRingHom φ)).of_isCoprime_of_dvd_right hd
    have hid : M.E ∣ (M.factor * M.amplitude γ) * F.scalar γ + C z * M.Q :=
      ⟨M.decoder B.bad, by rw [← B.identity]; ring⟩
    have hres : H ∣ liftPoly (M.factor * M.amplitude γ) * liftPoly (F.scalar γ) +
        C (φ z) * liftPoly M.Q := by
      simpa only [liftPoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        using hd.trans (Polynomial.map_dvd φ hid)
    have hfix : (liftPoly (F.scalar γ)).map σ = liftPoly (F.scalar γ) := by
      rw [← K1_14.twist_lift]
      exact congrArg liftPoly B.scalar_fixed
    refine ⟨ha, ha.map (Polynomial.mapRingHom σ), hres, ?_⟩
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hfix,
      σ, frobenius_def] using (Polynomial.map_dvd σ hres)
private theorem terminal_mem (w : ℤ) : terminalShape w ∈ scheduled w := by
  simp [scheduled]
private theorem terminal_width (w : ℤ) (hw : 2481 ≤ w) {q : ℕ}
    (hq : q ≤ (terminalShape w).B) :
    q * (131071 - w.toNat) ≤ (terminalShape w).m * agreement := by
  calc
    _ ≤ (terminalShape w).B * 128590 := Nat.mul_le_mul hq (by omega)
    _ ≤ _ := by unfold terminalShape band; split_ifs <;> decide
theorem terminalMass_of_source {u del} {M : AnchorModel u del} {Γ}
    {F : AnchoredFamily M Γ} {rows : Banks} (hr : JetSource M F rows)
    (hlo : 2481 ≤ M.overhead) {f : Equation}
    (hd : TerminalDivisibility M.overhead rows f) : TerminalMass M.overhead f := by
  let w := M.overhead
  let s := terminalShape w
  have hs := terminal_mem w
  have htop : 0 < s.m * agreement := by
    unfold s terminalShape band
    split_ifs <;> decide
  have hent : s.m * agreement - 1 + 1 = s.m * agreement := by omega
  refine ⟨rows s, ?_, ?_⟩
  · have h := hr.floor_bound s hs (s.m*agreement-1) (by omega) (by
      intro q hq j _
      have hq' : q * (131071 - M.overhead.toNat) ≤ s.m * agreement := terminal_width w hlo hq
      rw [hent]
      exact hq'.trans (Nat.le_add_right _ _))
    rw [hent] at h
    exact h
  · intro W hW P hP hne
    have hlc := leadingCoeff_ne_zero.mpr hne
    have htopcoeff : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree ≠ 0 :=
      leadingCoeff_ne_zero.mpr hlc
    obtain ⟨hb, hj, _⟩ := hr.shape s hs W P hP _ _ htopcoeff
    refine ⟨hj, hb, hr.leading s hs W P hP hne, ?_, hd W hW P hP hne⟩
    intro i
    by_cases h : P.leadingCoeff.coeff i = 0
    · simp [h]
    · exact (hr.shape s hs W P hP _ _ h).2.2
theorem separant_certificate {w : ℤ} {f : Equation} (hf : ReducedEquation w f)
    (hs : SeedBound f (band w).seedBound) :
    ∃ Δ : Seeds, Δ ≠ 0 ∧ Δ.totalDegree ≤ singularDegree w ∧
      ∀ (z : K) (S : K[X]), atMark f z S = 0 → atMark f.derivative z S = 0 →
        graphEval z Δ = 0 := by
  obtain ⟨hpos, hy, _, hsep⟩ := hf
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
theorem singular_degree_lt (w : ℤ) : singularDegree w < p := by
  unfold singularDegree band
  split_ifs <;> decide
theorem singular_count {u del} (M : AnchorModel u del) {w : ℤ} {f : Equation}
    (hf : ReducedEquation w f) (hs : SeedBound f (band w).seedBound)
    (Γ : Finset K) (S : K → K[X])
    (hroot : ∀ γ ∈ Γ, atMark f (M.label γ) (S γ) = 0)
    (hsing : ∀ γ ∈ Γ, atMark f.derivative (M.label γ) (S γ) = 0) :
    Γ.card ≤ (p+1)*singularDegree w := by
  classical
  obtain ⟨Δ, hne, hdegree, hz⟩ := separant_certificate hf hs
  let emb : K ↪ FX :=
    ⟨fun γ => seedEmbedding (M.label γ), fun a b h =>
      sub_left_inj.mp (seedEmbedding.injective h)⟩
  have hb := frobenius_coefficient_exception_count p (singularDegree w) (singularDegree w)
    (by decide) Δ hne ((Δ.degreeOf_le_totalDegree 0).trans hdegree)
    (singular_degree_lt w) ((Δ.degreeOf_le_totalDegree 1).trans hdegree)
    (Γ.map emb) (by
      intro x hx
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_map.mp hx
      exact hz _ _ (hroot γ hγ) (hsing γ hγ))
  simpa only [Finset.card_map, Nat.add_mul, Nat.one_mul, Nat.add_comm (singularDegree w)]
    using hb
set_option maxRecDepth 12000 in
theorem retained_price (w : ℤ) :
    (p+1)*singularDegree w + simplePrice w = highRetained w := by
  by_cases h₁ : w ≤ 3554
  · simp only [singularDegree, simplePrice, band, highRetained, ite_eq_left h₁]
    decide
  by_cases h₂ : w ≤ 8249
  · simp only [singularDegree, simplePrice, band, highRetained, ite_eq_right h₁, ite_eq_left h₂]
    decide
  by_cases h₃ : w ≤ 23999
  · simp only [singularDegree, simplePrice, band, highRetained, ite_eq_right h₁, ite_eq_right h₂, ite_eq_left h₃]
    decide
  · simp only [singularDegree, simplePrice, band, highRetained, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃]
    decide
end
end P0_10
end
section
namespace P0_10
noncomputable section
open Finset Polynomial
open P0 (agreement)
open K1_14 (FX Jet Equation shapeSum slots triangle SeedBound)
open K1_14_4 (gradeWidth seedDegree seedDegree_le_iff seedDegree_pow rank_multiples_le)
open private shapeSum_swap gradeWidth_card position_sum from ProximityPrize.SubmissionLower.Fast072
open private gradeMap mem_filtered finrank_le_grades from ProximityPrize.SubmissionLower.Fast069
private def gradeCapacity (w : ℤ) (W j : ℕ) : ℕ :=
  let b := band w
  gradeWidth (131071 - w.toNat) b.jetBound W j *
    slots b.subbankSeeds (forcedPower w W j * (b.seedBound + 1))
private def cutoffCapacity (w : ℤ) (W : ℕ) : ℕ :=
  ∑ j ∈ range ((band w).vBound + 1), gradeCapacity w W j
private theorem cutoffCapacity_eq (w : ℤ) (W : ℕ) (hk : 0 < 131071 - w.toNat) :
    cutoffCapacity w W =
      shapeSum (terminalShape w) (fun q j =>
        if q * (131071 - w.toNat) ≤ W + j then
          slots (band w).subbankSeeds (forcedPower w W j * ((band w).seedBound + 1))
        else 0) := by
  rw [← shapeSum_swap]
  unfold cutoffCapacity
  apply sum_congr rfl
  intro j _
  rw [gradeCapacity, gradeWidth_card _ _ _ _ hk, sum_mul]
  apply sum_congr rfl
  intro q _
  split_ifs <;> simp
theorem sum_cutoffCapacity_add_seedGain (w : ℤ) (hlo : 2481 ≤ w) (hhi : w ≤ 32766) :
    (∑ W ∈ range ((band w).multiplicity * agreement), cutoffCapacity w W) + seedGain w =
      rawVolume w := by
  let b := band w
  let k := 131071 - w.toNat
  let top := b.multiplicity * agreement
  have hk : 0 < k := by dsimp [k]; omega
  have hs : 0 < 2 * w.toNat := by omega
  have hswap (F : ℕ → ℕ → ℕ → ℕ) :
      (∑ W ∈ range top, shapeSum (terminalShape w) (F W)) =
        shapeSum (terminalShape w) (fun q j => ∑ W ∈ range top, F W q j) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  change (∑ W ∈ range top, cutoffCapacity w W) + seedGain w = rawVolume w
  simp_rw [cutoffCapacity_eq w _ hk]
  rw [hswap]
  simp only [seedGain, rawVolume, shapeSum, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
  have hjk : j ≤ q * k := hjq.trans (by
    simpa using Nat.mul_le_mul_left q (show 1 ≤ k by omega))
  exact position_sum top (2 * w.toNat) (q * k) j b.subbankSeeds (b.seedBound + 1)
    hjk hs (by omega)
private theorem ranks_lt_gradeWidth {d j k B W : ℕ} (hk : 0 < k)
    (hB : d + j ≤ B) (hW : (d + j) * k ≤ W + j) :
    d < gradeWidth k B W j := by
  have hd := (Nat.le_div_iff_mul_le hk).2 hW
  unfold gradeWidth
  omega
private theorem ranks_range_rank_at (k v B U s W j : ℕ) (e : ℕ → ℕ) (V : Submodule FX Jet)
    {f : Equation} (hf : f ≠ 0) (hv : s + 1 ≤ seedDegree f)
    (hk : 0 < k)
    (hV : ∀ P ∈ V, P ≠ 0 →
      P.natDegree ≤ v ∧
      P.leadingCoeff.natDegree + P.natDegree ≤ B ∧
      (P.leadingCoeff.natDegree + P.natDegree) * (k) ≤ W + P.natDegree ∧
      SeedBound P.leadingCoeff U ∧
      f ^ e P.natDegree ∣ P.leadingCoeff) :
    Module.rank FX (gradeMap (F := FX) (A := Equation) V j).range ≤
      (↑(gradeWidth k B W j * slots U (e j * (s + 1))) : Cardinal) := by
  apply rank_multiples_le _ (pow_ne_zero (e j) hf)
  · rw [seedDegree_pow hf]
    exact Nat.mul_le_mul_left _ hv
  · rintro c ⟨⟨P, hP⟩, rfl⟩ hc
    change P.coeff j ≠ 0 at hc
    obtain ⟨hpV, hd⟩ := mem_filtered.mp hP
    have hp : P ≠ 0 := by
      intro hz
      exact hc (by simp [hz])
    have hj : P.natDegree = j :=
      le_antisymm (Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hp).2 hd))
        (le_natDegree_of_ne_zero hc)
    obtain ⟨_, hB, hwidth, hseed, hdvd⟩ := hV P hpV hp
    rw [hj] at hB hwidth hdvd
    change (P.coeff j).natDegree < _ ∧ SeedBound (P.coeff j) _ ∧ _ ∣ P.coeff j
    rw [← hj, coeff_natDegree, hj]
    exact ⟨ranks_lt_gradeWidth hk hB hwidth, hseed, hdvd⟩
private theorem gradeMap_range_rank (w : ℤ) (W j : ℕ) (V : Submodule FX Jet)
    {f : Equation} (hf : f ≠ 0) (hv : (band w).seedBound + 1 ≤ seedDegree f)
    (hk : 0 < 131071 - w.toNat)
    (hV : ∀ P ∈ V, P ≠ 0 →
      P.natDegree ≤ (band w).vBound ∧
      P.leadingCoeff.natDegree + P.natDegree ≤ (band w).jetBound ∧
      (P.leadingCoeff.natDegree + P.natDegree) * (131071 - w.toNat) ≤ W + P.natDegree ∧
      SeedBound P.leadingCoeff (band w).subbankSeeds ∧
      f ^ forcedPower w W P.natDegree ∣ P.leadingCoeff) :
    Module.rank FX (gradeMap (F := FX) (A := Equation) V j).range ≤
      (↑(gradeCapacity w W j) : Cardinal) := by
  exact ranks_range_rank_at (131071 - w.toNat) (band w).vBound (band w).jetBound
    (band w).subbankSeeds (band w).seedBound W j (forcedPower w W) V hf hv hk hV
theorem cutoff_finrank_le (w : ℤ) (W : ℕ) (V : Submodule FX Jet)
    {f : Equation} (hf : f ≠ 0) (hv : (band w).seedBound + 1 ≤ seedDegree f)
    (hk : 0 < 131071 - w.toNat)
    (hV : ∀ P ∈ V, P ≠ 0 →
      P.natDegree ≤ (band w).vBound ∧
      P.leadingCoeff.natDegree + P.natDegree ≤ (band w).jetBound ∧
      (P.leadingCoeff.natDegree + P.natDegree) * (131071 - w.toNat) ≤ W + P.natDegree ∧
      SeedBound P.leadingCoeff (band w).subbankSeeds ∧
      f ^ forcedPower w W P.natDegree ∣ P.leadingCoeff) :
    Module.finrank FX V ≤ cutoffCapacity w W := by
  unfold cutoffCapacity
  refine finrank_le_grades (F := FX) (A := Equation) V (gradeCapacity w W)
    ((band w).vBound + 1) ?_ ?_
  · intro j
    exact gradeMap_range_rank w W j V (f := f) hf hv hk hV
  · intro P hp
    by_cases hn : P = 0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hV P hp hn).1)
theorem oversized_seed_loss (w : ℤ) (hlo : 2481 ≤ w) (hhi : w ≤ 32766)
    (f : Equation) (hf : ReducedEquation w f) (hm : TerminalMass w f)
    (hbad : ¬ SeedBound f (band w).seedBound) : seedGain w ≤ subbankDebit w := by
  obtain ⟨V, hfloor, hrows⟩ := hm
  have hne : f ≠ 0 := by
    intro h
    have hd := hf.1
    simp [h] at hd
  have hv : (band w).seedBound + 1 ≤ seedDegree f :=
    Nat.succ_le_of_lt (Nat.lt_of_not_ge (fun h => hbad ((seedDegree_le_iff _ _).mp h)))
  have hk : 0 < 131071 - w.toNat := by omega
  have hceil :
      (∑ W ∈ range ((band w).multiplicity * agreement), Module.finrank FX (V W)) ≤
        ∑ W ∈ range ((band w).multiplicity * agreement), cutoffCapacity w W :=
    sum_le_sum fun W hW => cutoff_finrank_le w W (V W) hne hv hk (hrows W (mem_range.mp hW))
  have h := sum_cutoffCapacity_add_seedGain w hlo hhi
  omega
end
end P0_10
end
section
namespace P0_10
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P0 (K I node agreement)
open private occupancy from ProximityPrize.SubmissionLower.Fast055
structure FixedWord (w : I → K) (T : Finset K) (s : K → K[X]) (d : ℕ) : Prop where
  distinct : Set.InjOn s (T : Set K)
  degree : ∀ γ ∈ T, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ T, ∃ B : Finset I, agreement ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
theorem FixedWord.mono {w T s d} (h : FixedWord w T s d) {U : Finset K} (hU : U ⊆ T) :
    FixedWord w U s d :=
  ⟨h.distinct.mono hU, fun γ hγ => h.degree γ (hU hγ), fun γ hγ => h.hits γ (hU hγ)⟩
private theorem incidence_arithmetic (errors m x gap cap : ℕ)
    (hm : 0 < m) (hg : 0 < gap) (hx : gap ≤ x) (he : 0 < errors)
    (hsecond : (m*x)^2 ≤ (x+errors) * (m * (x + (m-1)*(x-gap))))
    (hfirst : m*x ≤ (x+errors)*cap) :
    gap*m ≤ errors*cap + gap := by
  have hcancel : m*x^2 ≤ (x+errors) * (x + (m-1)*(x-gap)) := by
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
  have secondZ : ((m : ℤ)*errors - ((m : ℤ)-1)*gap)*x ≥
      ((m : ℤ)-1)*errors*gap := by
    nlinarith only [hcancelZ]
  have firstZ : ((m : ℤ)-(cap : ℤ))*x ≤ (cap : ℤ)*errors := by
    nlinarith only [hfirstZ]
  by_contra! h
  have hbadZ : (errors : ℤ)*cap + gap < (gap : ℤ)*m := by exact_mod_cast h
  have hbad : (cap : ℤ)*errors < ((m : ℤ)-1)*gap := by nlinarith only [hbadZ]
  have hxpos : 0 < (x : ℤ) := by omega
  have cmp : (m : ℤ)*errors - ((m : ℤ)-1)*gap < ((m : ℤ)-(cap : ℤ))*errors := by
    linarith only [hbad]
  have left := mul_lt_mul_of_pos_right cmp hxpos
  have right := mul_le_mul_of_nonneg_right firstZ (Int.natCast_nonneg errors)
  have impossible := secondZ.trans_lt (left.trans_le (show
      ((m : ℤ)-(cap : ℤ))*errors*x ≤ (cap : ℤ)*errors*errors from by
        convert right using 1
        ring))
  have bigger := mul_lt_mul_of_pos_right hbad (Int.ofNat_lt.mpr he)
  nlinarith only [impossible, bigger]
theorem section_capacity {w T s d} (h : FixedWord w T s d) (hd : d < agreement) (cap : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ T, (s γ).eval (node i) ≠ w i) →
      (T.filter fun γ => (s γ).eval (node i) = w i).card ≤ cap) :
    (agreement - d) * T.card ≤ P0.t * cap + (agreement - d) := by
  classical
  by_cases hm : T.card ≤ 1
  · have hb := Nat.mul_le_mul_left (agreement - d) hm
    simp only [Nat.mul_one] at hb
    omega
  let hits (γ : K) : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
  let common : Finset I := univ.filter fun i => ∀ γ ∈ T, (s γ).eval (node i) = w i
  let nodes : Finset I := univ \ common
  have common_le (γ : K) (hγ : γ ∈ T) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : K) (hγ : γ ∈ T) : agreement ≤ (hits γ).card := by
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
  let x := agreement - common.card
  let t := d - common.card
  have ht : t = x - (agreement - d) := by dsimp [t, x]; omega
  have hx : agreement - d ≤ x := by dsimp [x]; omega
  have hnodes : nodes.card = x + P0.t := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    change 262144 - common.card = (180217 - common.card) + 81927
    have hbound : common.card ≤ 180217 := hcommon.trans hd.le
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
  exact incidence_arithmetic P0.t _ _ _ _ (by omega) (by omega) hx (by decide) second first
end
end P0_10
end
section
namespace P0_10
noncomputable section
open Finset MvPolynomial
open P0 (K I node agreement)
open K1_14_6 (LinearCover LinearRing ClosedField mixedDegree)
open private card_le_sum_cover curve_degree_nat LinearCover.slice LinearCover.section
  LinearCover.cut_data LinearCover.zero_dim_count from ProximityPrize.SubmissionLower.Fast055
open scoped BigOperators Polynomial
private theorem curve_count {T s d e b w} (C : LinearCover T s d e b)
    {U : Finset K} (hU : U ⊆ T) (hword : FixedWord w U s d) (hd : d < agreement)
    (P : Ideal (LinearRing d e b)) (hP : P.IsPrime)
    (hdim : (affineHilbertPolynomial P).natDegree = 1)
    (hpoints : ∀ γ ∈ U, C.point γ ∈ zeroLocus ClosedField P) :
    (U.card : ℚ) ≤ (curveFactor d : ℚ) * affineDegree P := by
  classical
  obtain ⟨δ, hδ, hδdeg⟩ := curve_degree_nat P hP hdim
  have hsection (i : I) (hi : ∃ γ ∈ U, (s γ).eval (node i) ≠ w i) :
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ δ := by
    let V := U.filter fun γ => (s γ).eval (node i) = w i
    let Qs := LinearCover.section C P (node i) (w i)
    obtain ⟨hsum, dims, degree⟩ := LinearCover.cut_data C hU hP hpoints hi
    have hone (Q : Ideal (LinearRing d e b)) (hQ : Q ∈ Qs) :
        ((LinearCover.slice C V Q).card : ℚ) ≤ affineDegree Q := by
      have hQdim := (dims Q hQ).2
      rw [hdim] at hQdim
      exact LinearCover.zero_dim_count C ((filter_subset _ _).trans ((filter_subset _ _).trans hU))
        Q (by omega) (fun _ hγ => (mem_filter.mp hγ).2)
    have hsumQ : (V.card : ℚ) ≤ ∑ Q ∈ Qs, ((LinearCover.slice C V Q).card : ℚ) := by
      exact_mod_cast hsum
    have hbound := hsumQ.trans ((sum_le_sum hone).trans (degree.trans_eq hδdeg))
    exact_mod_cast hbound
  have hcount := section_capacity hword hd δ hsection
  let gap := agreement - d
  have hgap : 0 < gap := Nat.sub_pos_of_lt hd
  have hfactor : P0.t < gap * curveFactor d := by
    change P0.t < gap * (P0.t / gap + 1)
    rw [Nat.mul_add, Nat.mul_one]
    have heq := Nat.mod_add_div P0.t gap
    have hr := Nat.mod_lt P0.t hgap
    omega
  suffices hcard : U.card ≤ curveFactor d * δ by
    rw [hδdeg, ← Nat.cast_mul]
    exact_mod_cast hcard
  by_contra! hbad
  have hstep := Nat.mul_le_mul_left gap (show curveFactor d * δ + 1 ≤ U.card by omega)
  rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc] at hstep
  have hstrict := Nat.mul_lt_mul_of_pos_right hfactor hδ
  change gap * U.card ≤ P0.t * δ + gap at hcount
  omega
private theorem surface_count {T s d e b w} (C : LinearCover T s d e b)
    {U : Finset K} (hU : U ⊆ T) (hword : FixedWord w U s d) (hd : d < agreement)
    (P : Ideal (LinearRing d e b)) (hP : P.IsPrime)
    (hdim : (affineHilbertPolynomial P).natDegree = 2)
    (hpoints : ∀ γ ∈ U, C.point γ ∈ zeroLocus ClosedField P) :
    ((agreement - d : ℕ) : ℚ) * U.card ≤
      P0.t * (curveFactor d : ℚ) * affineDegree P + ((agreement - d : ℕ) : ℚ) := by
  classical
  let r := (curveFactor d : ℚ) * affineDegree P
  have hr : 0 ≤ r := mul_nonneg (Nat.cast_nonneg _) (affineDegree_nonneg P)
  have hsection (i : I) (hi : ∃ γ ∈ U, (s γ).eval (node i) ≠ w i) :
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ ⌊r⌋₊ := by
    apply (Nat.le_floor_iff hr).mpr
    let V := U.filter fun γ => (s γ).eval (node i) = w i
    let Qs := LinearCover.section C P (node i) (w i)
    obtain ⟨hsum, dims, degree⟩ := LinearCover.cut_data C hU hP hpoints hi
    have hone (Q : Ideal (LinearRing d e b)) (hQ : Q ∈ Qs) :
        ((LinearCover.slice C V Q).card : ℚ) ≤ (curveFactor d : ℚ) * affineDegree Q := by
      obtain ⟨hpr, hdimQ⟩ := dims Q hQ
      rw [hdim] at hdimQ
      have hVU : LinearCover.slice C V Q ⊆ U := (filter_subset _ _).trans (filter_subset _ _)
      exact curve_count C (hVU.trans hU) (hword.mono hVU) hd Q hpr (by omega)
        (fun _ hγ => (mem_filter.mp hγ).2)
    have hsumQ : (V.card : ℚ) ≤ ∑ Q ∈ Qs, ((LinearCover.slice C V Q).card : ℚ) := by
      exact_mod_cast hsum
    refine hsumQ.trans ((sum_le_sum hone).trans ?_)
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left degree (Nat.cast_nonneg _)
  have hcount := section_capacity hword hd ⌊r⌋₊ hsection
  have hcountQ : ((agreement - d : ℕ) : ℚ) * U.card ≤
      P0.t * (⌊r⌋₊ : ℚ) + ((agreement - d : ℕ) : ℚ) := by exact_mod_cast hcount
  have hfloor := mul_le_mul_of_nonneg_left (Nat.floor_le hr) (Nat.cast_nonneg P0.t)
  simpa only [r, mul_assoc] using hcountQ.trans (add_le_add hfloor (le_refl _))
theorem linearCover_count {T s d e b w} (C : LinearCover T s d e b)
    (hword : FixedWord w T s d) (hd : d < agreement) :
    (agreement - d) * T.card ≤ P0.t * curveFactor d * mixedDegree d e b + (agreement - d) * e := by
  classical
  let gap : ℕ := agreement - d
  have hcover : T.card ≤ ∑ P ∈ C.components, (LinearCover.slice C T P).card := by
    apply card_le_sum_cover
    intro γ hγ
    obtain ⟨P, hP, hpoint⟩ := C.covers γ hγ
    exact ⟨P, hP, mem_filter.mpr ⟨hγ, hpoint⟩⟩
  have hcoverQ : (T.card : ℚ) ≤ ∑ P ∈ C.components, ((LinearCover.slice C T P).card : ℚ) := by
    exact_mod_cast hcover
  have hone (P : Ideal (LinearRing d e b)) (hP : P ∈ C.components) :
      (gap : ℚ) * ((LinearCover.slice C T P).card : ℚ) ≤
        P0.t * (curveFactor d : ℚ) * affineDegree P + (gap : ℚ) :=
    surface_count C (filter_subset _ _) (hword.mono (filter_subset _ _)) hd
      P (C.is_prime P hP) (C.dimension P hP) (fun _ hγ => (mem_filter.mp hγ).2)
  have hcount : (gap : ℚ) * T.card ≤
      P0.t * (curveFactor d : ℚ) * (mixedDegree d e b : ℚ) + (gap : ℚ) * e := by
    calc
      _ ≤ (gap : ℚ) * ∑ P ∈ C.components, ((LinearCover.slice C T P).card : ℚ) :=
        mul_le_mul_of_nonneg_left hcoverQ (Nat.cast_nonneg _)
      _ = ∑ P ∈ C.components, (gap : ℚ) * ((LinearCover.slice C T P).card : ℚ) := mul_sum ..
      _ ≤ ∑ P ∈ C.components, (P0.t * (curveFactor d : ℚ) * affineDegree P + (gap : ℚ)) :=
        sum_le_sum hone
      _ = P0.t * (curveFactor d : ℚ) * (∑ P ∈ C.components, affineDegree P) +
          (gap : ℚ) * (C.components.card : ℚ) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_comm (C.components.card : ℚ)]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left C.degree_sum (by positivity))
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr C.component_count) (Nat.cast_nonneg _))
  exact_mod_cast hcount
end
end P0_10
end
section
namespace P0_10
noncomputable section
open P0
open K1_14 (Equation SeedBound atMark)
open K1_14_6 (mixedDegree)
theorem simple_count {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hhi : M.overhead ≤ (heightCap : ℤ)) {f : Equation}
    (hf : ReducedEquation M.overhead f) (hseed : SeedBound f (band M.overhead).seedBound)
    (T : Finset K) (hT : T ⊆ Γ)
    (hroots : ∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0 ∧
      atMark f.derivative (M.label γ) (F.scalar γ) ≠ 0) :
    T.card ≤ simplePrice M.overhead := by
  let w := M.overhead
  let d := 131071 + (band w).endpoint
  let e := (band w).yBound
  let b := (band w).seedBound
  have hend : w ≤ ((band w).endpoint : ℤ) := by
    unfold band
    split_ifs with hfirst hsecond hthird
    · exact hfirst
    · exact hsecond
    · exact hthird
    · exact hhi
  have hd0 : 0 < d := by dsimp only [d]; omega
  have hd : d < agreement := by
    dsimp only [d, band]
    split_ifs <;> decide
  have hdp : d < p := hd.trans (by decide)
  have hb0 : 0 < b := by
    dsimp only [b, band]
    split_ifs <;> decide
  obtain ⟨hf0, hfe, hprimitive, hsep⟩ := hf
  have hword : FixedWord M.word T F.scalar d := by
    refine ⟨F.distinct.mono hT, ?_, ?_⟩
    · intro γ hγ
      rcases (F.mark γ (hT hγ)).scalar_degree with hzero | hdeg
      · simp [hzero]
      · have hcast : ((F.scalar γ).natDegree : ℤ) ≤ (d : ℤ) := by
          dsimp only [d]
          push_cast
          exact hdeg.trans (add_le_add_right hend _)
        exact_mod_cast hcast
    · intro γ hγ
      let m := F.mark γ (hT hγ)
      exact ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩
  have hlabel : Set.InjOn M.label (T : Set K) := by
    intro γ _ η _ h
    exact sub_left_inj.mp h
  obtain ⟨C, hC⟩ := K1_14_6_1.proof d e b hd0 hdp f hf0 hfe hseed
  obtain ⟨cover⟩ := K1_14_6_2.proof d e b hd0 hb0 f hf0 hfe hprimitive hsep hseed T M.label F.scalar
    hlabel hroots C (fun γ hγ => hC _ _ (hword.degree γ hγ) (hroots γ hγ).1 (hroots γ hγ).2)
  have hcount := linearCover_count cover hword hd
  let gap := agreement - d
  let total := P0.t * curveFactor d * mixedDegree d e b
  have hgap : 0 < gap := Nat.sub_pos_of_lt hd
  change gap * T.card ≤ total + gap * e at hcount
  change T.card ≤ (total + (gap - 1)) / gap + e
  have hmul : (T.card - e) * gap ≤ total + (gap - 1) := by
    rw [Nat.sub_mul, Nat.mul_comm T.card, Nat.mul_comm e]
    omega
  have hdiv := (Nat.le_div_iff_mul_le hgap).mpr hmul
  omega
end
end P0_10
end
section
set_option backward.isDefEq.respectTransparency false
namespace P0_10_1
noncomputable section
open P0 (AnchorModel AnchoredFamily K p)
open P0_10 (AdjacentChart)
open K1_14 (L liftPoly)
open K1_14_1 Polynomial
open scoped Polynomial
open private blockContribution from ProximityPrize.SubmissionLower.Fast065
set_option maxHeartbeats 800000 in
theorem crt_lift {h : ℕ} (D : PoleData h) : Nonempty (CRTLift D) := by
  choose d N hN using blockContribution D
  exact ⟨⟨d, N, fun i => (hN i).1, fun i => (hN i).2.1, fun i => (hN i).2.2.1,
    fun i => (hN i).2.2.2.1, fun i => (hN i).2.2.2.2⟩⟩
end
end P0_10_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P0_10_1
noncomputable section
open K1 (I K node)
open K1_14 (L Shape Jet liftPoly jetAt shapeSum)
open K1_14_1 K1_14_1_5 Polynomial
open K1_14_1_2 (span_vanish composed composed_degree specialized_poles composed_contact)
open scoped Polynomial BigOperators
open private finrank_ambient trueWidth trueWidth_eq_add from ProximityPrize.SubmissionLower.Fast065
private theorem zero_of_poles_and_hits {h A : ℕ} {D : PoleData h}
    (hnode : ∀ i k, (D.block i).eval (nodeL k) ≠ 0)
    {s : Shape} {W : ℕ} {Q : L[X]}
    (hdeg : Q.natDegree ≤ W+(s.B+s.J)*(2*h))
    (hpole : poleProduct D ^ (s.B+s.J) ∣ Q)
    (hits : Finset I) (hcard : A ≤ hits.card)
    (hcontact : ∀ k ∈ hits, (Polynomial.X-C (nodeL k)) ^ s.m ∣ Q)
    (hW : W < s.m*A) : Q = 0 := by
  by_contra hne
  obtain ⟨T, hT⟩ := hpole
  have hTne : T ≠ 0 := by intro he; simp [hT, he] at hne
  have hmonic : (poleProduct D).Monic := (D.monic 0).mul (D.monic 1)
  have hDdeg : (poleProduct D).natDegree = 2*h := by
    rw [poleProduct, natDegree_mul (D.monic 0).ne_zero (D.monic 1).ne_zero, D.degree, D.degree]
    omega
  have hTdeg : T.natDegree ≤ W := by
    rw [hT, natDegree_mul (pow_ne_zero _ hmonic.ne_zero) hTne, natDegree_pow, hDdeg] at hdeg
    omega
  have hroot (k : I) : IsCoprime (Polynomial.X-C (nodeL k)) (poleProduct D) := by
    refine (irreducible_X_sub_C _).coprime_iff_not_dvd.mpr ?_
    rw [dvd_iff_isRoot]
    simpa [IsRoot, poleProduct] using mul_ne_zero (hnode 0 k) (hnode 1 k)
  have hcontacts (k : I) (hk : k ∈ hits) : (Polynomial.X-C (nodeL k)) ^ s.m ∣ T :=
    ((hroot k).pow.dvd_of_dvd_mul_left (hT ▸ hcontact k hk))
  have hinj : Function.Injective nodeL := (algebraMap K L).injective.comp node.injective
  have hh := K1_11.eq_zero_of_many_contacts hits nodeL hinj s.m T hcontacts
    (hTdeg.trans_lt (hW.trans_le (Nat.mul_le_mul_left _ hcard)))
  exact hTne hh
theorem contact_vanish {h A : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (hnode : ∀ i k, (D.block i).eval (nodeL k) ≠ 0)
    (z : K) (S : K[X]) (hres : MarkResidues D z S)
    (hdeg : (liftPoly S).natDegree ≤ 131071+h)
    (hits : Finset I) (hcard : A ≤ hits.card)
    (hhits : ∀ k ∈ hits, (liftPoly S).eval (nodeL k) = word k)
    (s : Shape) (W : ℕ) (hW : W < s.m*A) (P : Jet)
    (hP : P ∈ evaluated Crt word s W) : jetAt P z S = 0 := by
  apply span_vanish z S _ hP
  intro Q hQ
  obtain ⟨⟨ha, hc⟩, hp⟩ := hQ
  exact zero_of_poles_and_hits hnode (composed_degree ha _ _ hdeg)
    (specialized_poles Crt hres hp) hits hcard
    (fun k hk => composed_contact hc _ _ k (hhits k hk)) hW
theorem ambient_bound {h : ℕ} (hhi : h ≤ 131071) (s : Shape) (W : ℕ)
    (hw : rawWidthCond h s W) :
    rawVolumeAt h s W + poleCredit h s ≤ Module.finrank L (ambient h s W) := by
  rw [finrank_ambient]
  have hsum : shapeSum s (trueWidth h s W) =
      shapeSum s (fun q j => W + 1 + j - q * (131071 - h)) +
        2 * h * shapeSum s (fun q _ => s.B + s.J - q) := by
    unfold shapeSum
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro j hj
    exact trueWidth_eq_add hhi hw (by simpa using hq) (by simpa using hj)
  simp only [hsum, rawVolumeAt, poleCredit, Nat.mul_add, Nat.mul_assoc, Nat.le_refl]
end
end P0_10_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P0_10_1
noncomputable section
open K1 (I)
open K1_14 (L Shape Jet)
open K1_14_1 Polynomial
open K1_14_1_4 (Bounded forward_apply rawBlock_degree quotient_positions rawOrdinate rawVelocity
  substitute_C substitute_X)
open scoped Polynomial BigOperators
open private bounded_mono bounded_add bounded_sum bounded_mul bounded_jetConstant
  bounded_y bounded_v bounded_pow crt_degree ambient_degree from ProximityPrize.SubmissionLower.Fast065
open private rawPosition specialized_center specialized_leading specialized doubleMap
  from ProximityPrize.SubmissionLower.Fast065
private theorem forward_bounded {h} (hpos : 0 < h) (hh : h ≤ 131070) {D : PoleData h} (Crt : CRTLift D)
    {s W P} (hp : P ∈ ambient h s W) :
    Bounded (131071-h) (131071-h-1) (W+(s.B+s.J)*(2*h)) (forward Crt P) := by
  let u := 131071-h
  let v := u-1
  have huv : v+1 = u := by dsimp [u, v]; omega
  have hd : 131071+h = 2*h+u := by dsimp [u]; omega
  have hy : Bounded u v (2*h+u) (rawOrdinate D Crt) :=
    bounded_add (bounded_mul (bounded_jetConstant (rawBlock_degree D).le) (bounded_y u v))
      (bounded_jetConstant ((crt_degree D Crt).trans (by omega)))
  have hv : Bounded u v (2*h+v) (rawVelocity D Crt) := by
    have hh' : (rawBlock D).derivative.natDegree ≤ 2*h-1 :=
      (natDegree_derivative_le _).trans (by rw [rawBlock_degree])
    refine bounded_add (bounded_add
      (bounded_mul (bounded_jetConstant (rawBlock_degree D).le) (bounded_v u v)) ?_) ?_
    · exact bounded_mono (bounded_mul (bounded_jetConstant hh') (bounded_y u v)) (by omega)
    · exact bounded_jetConstant (((natDegree_derivative_le _).trans
        (Nat.sub_le_sub_right (crt_degree D Crt) 1)).trans (by omega))
  change Bounded u v _ (forward Crt P)
  rw [forward_apply, P.as_sum_support_C_mul_X_pow, map_sum]
  apply bounded_sum
  intro j hj
  rw [map_mul, map_pow, (P.coeff j).as_sum_support_C_mul_X_pow]
  simp only [substitute_C, substitute_X]
  simp only [map_sum, map_mul, map_pow, Finset.sum_mul]
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_X, RingHom.comp_apply]
  apply bounded_sum
  intro i hi
  have hdeg := ambient_degree hp (mem_support_iff.mp hi)
  have hw : ((P.coeff j).coeff i).natDegree + (2*h+u)*i + (2*h+v)*j ≤
      W+(s.B+s.J)*(2*h) := by
    have hjmul : j*(2*h+u) = (2*h+v)*j+j := by
      rw [show 2*h+u = (2*h+v)+1 by omega, Nat.mul_add, Nat.mul_one, Nat.mul_comm j (2*h+v)]
    rw [hd, Nat.add_mul, hjmul, Nat.mul_comm i (2*h+u)] at hdeg
    omega
  apply bounded_mono (bounded_mul (bounded_mul ?_ (bounded_pow hy i)) (bounded_pow hv j)) hw
  exact bounded_jetConstant natDegree_map_le
private theorem rawPosition_zero {h} (hpos : 0 < h) (hh : h ≤ 131070) {D : PoleData h} (Crt : CRTLift D)
    (word : I → L) {s W P} (hP : P ∈ evaluated Crt word s W) (j i : ℕ)
    (hw : W < (131071-h)*i+(131071-h-1)*j) : rawPosition Crt j i P = 0 := by
  have hsub : evaluated Crt word s W ≤ LinearMap.ker (rawPosition Crt j i) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A, hA, rfl⟩
    apply LinearMap.mem_ker.mpr
    rcases hA.2 with ⟨Q, hQ⟩
    have hz := quotient_positions s W (forward_bounded hpos hh Crt hA.1.1) hQ j i hw
    change ((specialized Crt (centerEval A)).coeff j).coeff i = 0
    rw [specialized_center, hQ]
    simp only [map_mul, doubleMap, coe_mapRingHom, Polynomial.map_C, jetConstant,
      RingHom.comp_apply, coeff_C_mul, coeff_map, hz, map_zero, mul_zero]
  exact LinearMap.mem_ker.mp (hsub hP)
theorem leading_bound {h : ℕ} (hl : 0 < h) (hh : h ≤ 131070)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (s : Shape) (W : ℕ)
    (P : Jet) (hP : P ∈ evaluated Crt word s W) (hn : P ≠ 0) :
    (P.leadingCoeff.natDegree + P.natDegree)*(131071-h) ≤ W+P.natDegree := by
  let j := P.natDegree
  let i := P.leadingCoeff.natDegree
  change (i+j)*(131071-h) ≤ W+j
  have huv : 131071-h = (131071-h-1)+1 := by omega
  have he : (i+j)*(131071-h) = (131071-h)*i+(131071-h-1)*j+j := by
    have hj : j*(131071-h) = (131071-h-1)*j+j := by
      calc
        j*(131071-h) = j*((131071-h-1)+1) := congrArg (j*·) huv
        _ = (131071-h-1)*j+j := by ring
    rw [Nat.add_mul, hj, Nat.mul_comm i]
    omega
  rw [he]
  by_contra! hw
  have hz := rawPosition_zero hl hh Crt word hP j i (by omega)
  obtain ⟨hj, hi, hn'⟩ := specialized_leading Crt hn
  change ((specialized Crt P).coeff j).coeff i = 0 at hz
  have hj' : (specialized Crt P).natDegree = j := hj
  have hi' : (specialized Crt P).leadingCoeff.natDegree = i := hi
  rw [← hj', coeff_natDegree, ← hi', coeff_natDegree] at hz
  exact (leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn')) hz
end
end P0_10_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P0_10_1
noncomputable section
open K1 (I)
open K1_14 (L FX Shape Jet shapeSum triangle seedHasse)
open K1_14_1 K1_14_1_3 Polynomial
open scoped Polynomial BigOperators
open private Low.mk localSpan generators K1_14_1_6.nodeMap localSpan_finrank from ProximityPrize.SubmissionLower.Fast065
open private evaluatedHasse evaluatedHasse_eq centerEval_clear from ProximityPrize.SubmissionLower.Fast065
theorem physical_bound (h : ℕ) (word : I → L) (s : Shape) (W : ℕ) :
    Module.finrank L (ambient h s W) ≤
      physicalDebit s + Module.finrank L (contacted h word s W) := by
  classical
  by_cases hzero : Module.finrank L (ambient h s W) = 0
  · simp [hzero]
  have : Module.Finite L (ambient h s W) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hzero)
  have : Module.Finite L (localSpan s) :=
    Module.Finite.span_of_finite L (Set.finite_range (generators s))
  let f : ambient h s W →ₗ[L] (I → localSpan s) :=
    LinearMap.pi (K1_14_1_6.nodeMap h word s W)
  let g : LinearMap.ker f →ₗ[L] contacted h word s W :=
    LinearMap.codRestrict (contacted h word s W)
      ((ambient h s W).subtype.comp (LinearMap.ker f).subtype) (by
        intro P
        refine ⟨P.val.property, ?_⟩
        intro i a b j e hab
        have hz := LinearMap.mem_ker.mp P.property
        exact congrArg (fun z : I → localSpan s => (z i).val (Low.mk j b a e hab)) hz)
  have hg : Function.Injective g := by
    intro P Q hPQ
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun R : contacted h word s W => R.val) hPQ
  have hle : contacted h word s W ≤ ambient h s W := inf_le_left
  have : Module.Finite L (contacted h word s W) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hker := LinearMap.finrank_le_finrank_of_injective hg
  have hnull := f.finrank_range_add_finrank_ker
  have htarget : Module.finrank L (I → localSpan s) ≤ physicalDebit s := by
    rw [Module.finrank_pi_fintype]
    calc
      (∑ _ : I, Module.finrank L (localSpan s)) ≤
          ∑ _ : I, (shapeSum s (fun q k => s.m + min q s.J - (q + 2*k))) * triangle s.U :=
        Finset.sum_le_sum (fun _ _ => localSpan_finrank s)
      _ = physicalDebit s := by
        rw [Finset.sum_const, Finset.card_univ, ProximityPrize.Benchmark.IRSProfile.card_index,
          smul_eq_mul, physicalDebit]
        ac_rfl
  have hrange := (LinearMap.range f).finrank_le.trans htarget
  omega
theorem evaluated_shift {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {s : Shape} {W : ℕ} {P : Jet} (hP : P ∈ evaluated Crt word s W) (i : Fin 2) (r : ℕ) :
    seedHasse i r P ∈ evaluated Crt word s (W+2*h*r) := by
  let target := evaluated Crt word s (W+2*h*r)
  have hsub : evaluated Crt word s W ≤ target.comap (evaluatedHasse i r) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨Q, hQ, rfl⟩
      change evaluatedHasse i r (centerEval Q) ∈ target
      have hmem : cleared D i r Q ∈ complete Crt word s (W+2*h*r) :=
        ⟨⟨ambient_cleared D hQ.1.1 i r, K1_14_1_3_1.proof h D word s Q hQ.1.2 i r⟩,
          K1_14_1_3_2.proof h D Crt s Q hQ.2 i r⟩
      have he : centerEval (cleared D i r Q) ∈ target :=
        Submodule.subset_span ⟨cleared D i r Q, hmem, rfl⟩
      rw [centerEval_clear] at he
      have hn : algebraMap L[X] FX (D.block i ^ (2*r)) ≠ 0 := by
        rw [← map_zero (algebraMap L[X] FX)]
        exact (IsFractionRing.injective L[X] FX).ne (pow_ne_zero (2*r) (D.monic i).ne_zero)
      exact (target.smul_mem_iff hn).mp he)
  rw [← evaluatedHasse_eq]
  exact hsub hP
end
end P0_10_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P0_10_1_1
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 K1_14_1_7_3 Polynomial
open scoped BigOperators Polynomial
open private simple_rank_le from ProximityPrize.SubmissionLower.Fast065
open private generic_den generic_centre from ProximityPrize.SubmissionLower.Fast065
private theorem regular_deformation {h : ℕ} (hh : 0 < h) (hp : h < K1.p)
    (D : PoleData h) (Crt : CRTLift D) : Nonempty (RegularDeformation D Crt) := by
  let B : ∀ i, BlockLift D Crt i := blockLift hh D Crt
  let den := (B 0).den * (B 1).den
  let num := C (B 1).den * (B 0).num + C (B 0).den * (B 1).num
  have hden : specialSeed den ≠ 0 := by
    dsimp only [den]
    rw [map_mul]
    exact mul_ne_zero (B 0).specialDen (B 1).specialDen
  have hmonic : (movingProduct D).Monic :=
    (movingBlock_degree hh D 0).monic.mul (movingBlock_degree hh D 1).monic
  refine ⟨⟨movingProduct D, num, den, hmonic, ?_, hden, ?_, generic_den hden, ?_⟩⟩
  · rw [movingProduct, Polynomial.map_mul, movingBlock_spec, movingBlock_spec, poleProduct]
  · dsimp only [num, den]
    rw [liftAt_add _ _ _ _ _ (B 0).specialDen (B 1).specialDen,
      (B 0).specialLift, (B 1).specialLift, crtPolynomial, Fin.sum_univ_two]
  · apply simplePoles hh hp D _
    intro i α hr hb
    dsimp only [num, den]
    rw [liftAt_add _ _ _ _ _ (generic_den (B 0).specialDen) (generic_den (B 1).specialDen)]
    simpa only [Fin.sum_univ_two] using generic_centre B i α hr hb
end
end P0_10_1_1
end
section
namespace P0_10_5
open K1_14 (Shape slots shapeSum sourceDebit)
open K1_14_5 (nodeCost poleSlope)
open Finset
open scoped BigOperators
open private sum_arithmetic shape_sum_flip debit_eq from ProximityPrize.SubmissionLower.Fast063
def cut (s : Shape) (v lo t : ℕ) : ℕ :=
  min (s.B + 1)
    ((s.m * P0.agreement + (t - min t (s.U / v)) - 2 * lo * t - 1) / (131071 - lo) + 1)
def weight (s : Shape) (v r : ℕ) : ℕ :=
  slots s.U (r*v) - slots s.U ((r+1)*v)
end P0_10_5
end
section
namespace P0_10_5
open K1_14 (Shape slots triangle)
open K1_14_5 (nodeCost poleSlope)
open Finset
open scoped BigOperators
open private nodeRow from ProximityPrize.SubmissionLower.Fast063
private def ValidCut (s : Shape) (v lo t : ℕ) : Prop :=
  let k := cut s v lo t
  min t s.J ≤ k ∧ (k-1) * (131071-lo) + 2*lo*t < s.m*P0.agreement + (t - min t (s.U/v))
private instance (s : Shape) (v lo t : ℕ) : Decidable (ValidCut s v lo t) := by
  unfold ValidCut
  infer_instance
private def moments (s : Shape) (v i : ℕ) : ℕ × ℕ × ℕ :=
  let R := s.U / v
  let n := min R i
  let a := weight s v 0
  let b := v*v
  let s₁ := n*(n-1)/2
  let s₂ := n*(n-1)*(2*n-1)/6
  let last := if R < i then slots s.U (R*v) else 0
  ⟨a*n - b*s₁ + last, a*s₁ - b*s₂ + last*R, a*s₂ - b*s₁*s₁ + last*R*R⟩
private def MomentStep (s : Shape) (v r : ℕ) : Prop :=
  let w := weight s v r
  let p := moments s v r
  let q := moments s v (r+1)
  q.1 = p.1 + w ∧ q.2.1 = p.2.1 + w*r ∧ q.2.2 = p.2.2 + w*r*r
private instance (s : Shape) (v r : ℕ) : Decidable (MomentStep s v r) := by
  unfold MomentStep
  infer_instance
structure Row where
  ok : Bool
  base : ℤ
  slope : ℤ
def Row.add (x y : Row) : Row := ⟨x.ok && y.ok, x.base + y.base, x.slope + y.slope⟩
theorem Row.eq_of_check {x y : Row}
    (h : ((x.ok == y.ok) && (x.base == y.base) && (x.slope == y.slope)) = true) : x = y := by
  cases x
  cases y
  simp only [Bool.and_eq_true, beq_iff_eq, Row.mk.injEq] at h ⊢
  tauto
def scan (f : ℕ → Row) (a : ℕ) : ℕ → Row
  | 0 => ⟨true, 0, 0⟩
  | n+1 => (scan f a n).add (f (a+n))
private theorem scan_add (f : ℕ → Row) (a n m : ℕ) :
    scan f a (n+m) = (scan f a n).add (scan f (a+n) m) := by
  induction m with
  | zero => cases scan f a n; simp [scan, Row.add]
  | succ m ih =>
    change (scan f a (n+m)).add (f (a+(n+m))) =
      (scan f a n).add ((scan f (a+n) m).add (f ((a+n)+m)))
    rw [ih]
    simp only [Row.add, Bool.and_assoc, add_assoc]
theorem joinRows {f : ℕ → Row} (a n m : ℕ) (x y : Row) {z : Row}
    (hx : scan f a n = x) (hy : scan f (a+n) m = y) (hz : x.add y = z) :
    scan f a (n+m) = z := by rw [scan_add, hx, hy, hz]
private theorem scan_sum (f : ℕ → Row) (a n : ℕ) (slope : Bool) :
    (if slope then (scan f a n).slope else (scan f a n).base) =
      ∑ i ∈ range n, if slope then (f (a+i)).slope else (f (a+i)).base := by
  cases slope <;> induction n with
  | zero => simp [scan]
  | succ n ih => simp_all only [scan, Row.add, Bool.false_eq_true, ite_false, ite_true,
      sum_range_succ]
end P0_10_5
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace K1_14_2_2_2_5_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2_5 Polynomial
open K1_14_3 (Slice)
open K1_14_2_2_3 (seedPresentation specializeJets mapGenericJets_eq)
local instance : Algebra (MvPolynomial (Fin 2) Seeds) FibreRing :=
  MvPolynomial.algebraMvPolynomial
end
end K1_14_2_2_2_5_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 600000
namespace K1_14_2_2_2_5_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2_2_5
open K1_14_3_2 (ProperPair)
private theorem properPair_height {P Q : Jet} (h : ProperPair P Q)
    (I : Ideal Jet) [I.IsPrime] (hP : P ∈ I) (hQ : Q ∈ I) : 2 ≤ I.height := by
  have hne : I ≠ ⊥ := fun e => h.left_ne (by simpa [e] using hP)
  obtain ⟨D, hD, hp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹I.IsPrime› hne
  let J : Ideal Jet := Ideal.span {D}
  have : J.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hJ₀ : J ≠ ⊥ := fun e => hp.ne_zero (Ideal.span_singleton_eq_bot.mp e)
  have hJ₁ : 1 ≤ J.height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hJ₀)
  have hJI : J < I := by
    refine lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem I).mpr hD) ?_
    intro e
    exact h.no_common D hp.irreducible
      (Ideal.mem_span_singleton.mp (e ▸ hP : P ∈ J))
      (Ideal.mem_span_singleton.mp (e ▸ hQ : Q ∈ J))
  calc
    2 = 1 + 1 := by decide
    _ ≤ J.height + 1 := add_le_add hJ₁ le_rfl
    _ ≤ I.height := Ideal.height_add_one_le_of_lt_of_isPrime hJI
end
end K1_14_2_2_2_5_1
end
