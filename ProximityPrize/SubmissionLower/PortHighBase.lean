import ProximityPrize.SubmissionLower.Fast072
import ProximityPrize.SubmissionLower.Fast074
import ProximityPrize.SubmissionLower.PortBase
set_option Elab.async false
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
def PrefixCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} (pairs : ∀ i : Fin 2, BufferedPair M.overhead rows i) : Prop :=
  Γ.card ≤ highPrefix M.overhead ∨ Nonempty (RetainedCover M F pairs)
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
namespace P0_10
noncomputable section
open P0 Polynomial
open K1_14 (Banks SeedBound atMark)
def c1 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    lowCutoff + 1 ≤ M.overhead → M.overhead ≤ (heightCap : ℤ) →
    ∀ H, AdjacentChart M F H → ∃ rows : Banks, JetSource M F rows
def c2 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    lowCutoff + 1 ≤ M.overhead → M.overhead ≤ (heightCap : ℤ) →
    ∀ rows, JetSource M F rows →
    Nonempty (∀ i : Fin 2, BufferedPair M.overhead rows i)
def c3 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    lowCutoff + 1 ≤ M.overhead → M.overhead ≤ 3554 → M.shift ∉ Γ →
    ∀ H, AdjacentChart M F H → ∀ rows, JetSource M F rows →
    ∀ pairs : ∀ i : Fin 2, BufferedPair M.overhead rows i, PrefixCover M F pairs
def c4 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    3555 ≤ M.overhead → M.overhead ≤ (heightCap : ℤ) → M.shift ∉ Γ →
    ∀ H, AdjacentChart M F H → ∀ rows, JetSource M F rows →
    ∀ pairs : ∀ i : Fin 2, BufferedPair M.overhead rows i, PrefixCover M F pairs
def c5 : Prop :=
  ∀ w : ℤ, lowCutoff + 1 ≤ w → w ≤ (heightCap : ℤ) → subbankDebit w < seedGain w
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) : P0.c10 := by
  classical
  intro u del M Γ F hlo hhi
  let regular := Γ.erase M.shift
  have hreg : regular ⊆ Γ := Finset.erase_subset _ _
  have hshift : M.shift ∉ regular := Finset.notMem_erase _ _
  let G : AnchoredFamily M regular :=
    ⟨F.scalar, fun γ hγ => F.mark γ (hreg hγ), F.distinct.mono hreg⟩
  suffices hcard : regular.card ≤ highPrefix M.overhead + highRetained M.overhead by
    have herase : Γ.card - 1 ≤ regular.card := Finset.pred_card_le_card_erase
    omega
  obtain ⟨H, hH⟩ := adjacent_chart M G
  obtain ⟨rows, hrows⟩ := h1 u del M regular G hlo hhi H hH
  obtain ⟨pairs⟩ := h2 u del M regular G hlo hhi rows hrows
  have hcover : PrefixCover M G pairs := by
    by_cases h : M.overhead ≤ 3554
    · exact h3 u del M regular G hlo h hshift H hH rows hrows pairs
    · exact h4 u del M regular G (by omega) hhi hshift H hH rows hrows pairs
  obtain hshort | hlong := hcover
  · exact hshort.trans (Nat.le_add_right _ _)
  obtain ⟨cover⟩ := hlong
  have hf : ReducedEquation M.overhead cover.equation :=
    ⟨cover.projected.positive, cover.y_bound, cover.projected.primitive, cover.projected.separable⟩
  have hseed : SeedBound cover.equation (band M.overhead).seedBound := by
    by_contra hbad
    have hm := terminalMass_of_source hrows hlo cover.divides
    exact (h5 _ hlo hhi).not_ge (oversized_seed_loss _ hlo hhi _ hf hm hbad)
  have hroots : ∀ γ ∈ cover.kept, atMark cover.equation (M.label γ) (G.scalar γ) = 0 := by
    intro γ hγ
    obtain ⟨q, hq, hmark⟩ := cover.covers γ hγ
    have hz := RingHom.mem_ker.mp (hmark (cover.projected.vanishes q hq))
    simpa only [coe_eval₂RingHom, eval₂_C, atMark] using hz
  let singular := cover.kept.filter fun γ => atMark cover.equation.derivative (M.label γ) (G.scalar γ) = 0
  have hsubset : singular ⊆ cover.kept := Finset.filter_subset _ _
  have hexception := singular_count M hf hseed singular G.scalar
    (fun γ hγ => hroots γ (hsubset hγ)) (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hsimple := simple_count M G hhi hf hseed (cover.kept \ singular)
    (Finset.sdiff_subset.trans cover.subset) (by
      intro γ hγ
      obtain ⟨hk, hn⟩ := Finset.mem_sdiff.mp hγ
      exact ⟨hroots γ hk, fun hz => hn (Finset.mem_filter.mpr ⟨hk, hz⟩)⟩)
  have hpartition := Finset.card_sdiff_add_card_eq_card hsubset
  have htotal := Finset.card_sdiff_add_card_eq_card cover.subset
  have hpaid := cover.paid
  rw [← retained_price M.overhead]
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
theorem chart_poles {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (H : L[X]) (hH : AdjacentChart M F H) :
    ∃ D : PoleData M.overhead.toNat,
      (∀ i k, (D.block i).eval (nodeL k) ≠ 0) ∧
      ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ) := by
  let σ := frobenius L p
  rcases hH with ⟨hm, hd, _, hm', hd', _, hcop, hnode, hdet, hdet', hmarks⟩
  let A := liftPoly (M.factor * M.A₀)
  let B := liftPoly (M.factor * M.A₁)
  let Q := liftPoly M.Q
  have hdet0 : IsCoprime (Q * A) H := by
    simpa [Q, A, liftPoly, mul_assoc] using hdet
  have hdet1 : IsCoprime (Q.map σ * A.map σ) (H.map σ) := by
    simpa [Q, A, liftPoly, mul_assoc, σ, Polynomial.map_mul] using hdet'
  let D : PoleData M.overhead.toNat :=
    ⟨![H, H.map σ], ![Q, Q.map σ], ![A, A.map σ], ![B, B.map σ],
      fun i => by fin_cases i <;> first | exact hm | exact hm',
      fun i => by fin_cases i <;> first | exact hd | exact hd',
      hcop, fun i => by fin_cases i <;> first | exact hdet0 | exact hdet1⟩
  refine ⟨D, ?_, ?_⟩
  · intro i k
    fin_cases i
    · exact (hnode k).1
    · exact (hnode k).2
  · intro γ hγ i
    let z := algebraMap K L (M.label γ)
    have hz : liftPoly (M.factor * M.amplitude γ) = A + (@Polynomial.C L _) z * B := by
      simp [A, B, z, AnchorModel.amplitude, liftPoly, mul_add, mul_left_comm]
    obtain ⟨h₀, h₁, hr₀, hr₁⟩ := hmarks γ hγ
    fin_cases i
    · change IsCoprime (A + (@Polynomial.C L _) z * B) H ∧
        H ∣ (A + (@Polynomial.C L _) z * B) * liftPoly (F.scalar γ) + (@Polynomial.C L _) z * Q
      rw [← hz]
      exact ⟨h₀, hr₀⟩
    · have hσ : (liftPoly (M.factor * M.amplitude γ)).map σ =
          A.map σ + (@Polynomial.C L _) (z^p) * B.map σ := by
        rw [hz, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        rfl
      change IsCoprime (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) (H.map σ) ∧
        H.map σ ∣ (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) * liftPoly (F.scalar γ) +
          (@Polynomial.C L _) (z^p) * Q.map σ
      rw [← hσ]
      exact ⟨h₁, hr₁⟩
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
namespace P0_10_1
noncomputable section
open P0 (K I agreement heightCap)
open K1_14 (L FX liftPoly)
open K1_14_1
open P0_10 (JetSource)
open Polynomial
open scoped BigOperators
def c1 : Prop :=
  ∀ h : ℕ, 2481 ≤ h → h ≤ heightCap →
    ∀ (D : PoleData h) (Crt : CRTLift D) (word : I → L) (s : K1_14.Shape) (W : ℕ),
      Module.finrank L (contacted h word s W) ≤
        poleCredit h s + poleSeedDebit h s + Module.finrank L (complete Crt word s W)
def c2 : Prop :=
  ∀ h : ℕ, 2481 ≤ h → h ≤ heightCap →
    ∀ (D : PoleData h) (Crt : CRTLift D) (word : I → L) (s : K1_14.Shape) (W : ℕ),
      Module.finrank L (complete Crt word s W) ≤
        ∑ t ∈ Finset.range (W+1), Module.finrank FX (evaluated Crt word s t)
theorem of_children (h₁ : c1) (h₂ : c2) : P0_10.c1 := by
  intro u del M Γ F hlo hhi H hH
  have lo : 2481 ≤ M.overhead.toNat := by
    change 2481 ≤ M.overhead at hlo
    omega
  have hi : M.overhead.toNat ≤ heightCap := by
    change M.overhead ≤ 32766 at hhi
    change M.overhead.toNat ≤ 32766
    omega
  obtain ⟨D, hnode, hres⟩ := P0_10_1.chart_poles M F H hH
  obtain ⟨Crt⟩ := crt_lift D
  let word : I → L := fun i => algebraMap K L (M.word i)
  refine ⟨evaluated Crt word, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro s _ s' _ hm hB hJ hU W W' hW
    exact evaluated_mono Crt word hm hB hJ hU hW
  · intro s _ W hW P hP γ hγ
    let B := F.mark γ hγ
    have hdegree : (liftPoly (F.scalar γ)).natDegree ≤ 131071 + M.overhead.toNat := by
      rw [liftPoly, Polynomial.natDegree_map]
      rcases B.scalar_degree with hzero | hd
      · simp [hzero]
      · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at hd
        omega
    refine contact_vanish Crt word hnode _ _ (hres γ hγ) hdegree B.bad.support
      B.bad.agreement ?_ s W hW P hP
    intro i hit
    rw [liftPoly, nodeL, Polynomial.eval_map, Polynomial.eval₂_hom, B.scalar_hits i hit]
  · intro s _ W P hP j i hne
    exact evaluated_shape Crt word hP j i hne
  · intro s _ W P hP hne
    exact leading_bound (by omega) (hi.trans (by decide)) Crt word s W P hP hne
  · intro s _ W P hP i r
    exact evaluated_shift Crt word hP i r
  · intro s _ W _ hW
    have hvol := ambient_bound (hi.trans (by decide)) s W hW
    have hcontact := physical_bound M.overhead.toNat word s W
    have hpole := h₁ _ lo hi D Crt word s W
    have hsum := h₂ _ lo hi D Crt word s W
    change rawVolumeAt M.overhead.toNat s W ≤
      (physicalDebit s + poleSeedDebit M.overhead.toNat s) +
        ∑ t ∈ Finset.range (W+1), Module.finrank FX (evaluated Crt word s t)
    omega
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
theorem proof : P0_10_1.c1 := by
  classical
  intro h hlo hhi D Crt word s W
  have hpos : 0 < h := by omega
  have hcap : P0.heightCap < K1.p := by
    change 32766 < 2130706433
    decide
  obtain ⟨E⟩ := regular_deformation hpos (hhi.trans_lt hcap) D Crt
  let A := contacted h word s W
  let _ : Module.Finite L A := contacted_finite h word s W
  let d := Module.finrank L A
  let basis := Module.finBasis L A
  let P : Fin d → Source := fun k => basis k
  have hP (k : Fin d) : Shaped s (P k) := contacted_shaped (basis k).property
  obtain ⟨n, M, hs, hg⟩ := K1_14_1_7_4.proof E s (Fin d) P hP
  have hlocal : K1_14_1_7.c2 :=
    K1_14_1_7_2.of_children K1_14_1_7_2_1.proof K1_14_1_7_2_2.proof
  have hgen := simple_rank_le K1_14_1_7_1.proof hlocal E.genericPoles s _
    (fun k => shaped_map (genericPoint.comp (Polynomial.C (R := L))) (hP k)) _ hg
  have hrank := (specialization_rank_le M).trans hgen
  let f := (M.map specialPoint).mulVecLin
  have hf : ∀ v : Fin d → L,
      Fintype.linearCombination L P v = ((basis.equivFun.symm v : A) : Source) := by
    intro v
    rw [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]
    symm
    simpa only [map_smul, Submodule.subtype_apply, P] using
      map_sum A.subtype (fun k => v k • basis k) Finset.univ
  have hk (v : LinearMap.ker f) :
      ((basis.equivFun.symm (v : Fin d → L) : A) : Source) ∈ complete Crt word s W := by
    have hv := (hs v.val).mp (LinearMap.mem_ker.mp v.property)
    rw [hf] at hv
    exact ⟨(basis.equivFun.symm v.val).property, hv⟩
  let g : LinearMap.ker f →ₗ[L] complete Crt word s W :=
    LinearMap.codRestrict _ ((A.subtype.comp basis.equivFun.symm.toLinearMap).comp
      (LinearMap.ker f).subtype) hk
  let _ : Module.Finite L (complete Crt word s W) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left)
      (Submodule.inclusion_injective _)
  have hginj : Function.Injective g := by
    intro v w hvw
    apply Subtype.ext
    apply basis.equivFun.symm.injective
    apply Subtype.ext
    exact congrArg (fun x : complete Crt word s W => (x : Source)) hvw
  have hkd := LinearMap.finrank_le_finrank_of_injective hginj
  have hdf := f.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, Fintype.card_fin] at hdf
  change Module.finrank L (LinearMap.range f) ≤ _ at hrank
  change d ≤ _
  omega
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
def supportCount (s : Shape) (v lo j r : ℕ) : ℕ := cut s v lo (j + r) - j
def blockValue (s : Shape) (j r n : ℕ) (h : ℤ) : ℤ :=
  (n : ℤ) * (2*((s.m : ℤ)*P0.agreement+j) - (2*(j : ℤ)+n-1)*(131071-h) -
    4*((j : ℤ)+r)*h)
def blockSlope (j r n : ℕ) : ℤ :=
  (n : ℤ) * ((2*(j : ℤ)+n-1) - 4*((j : ℤ)+r))
private def signedWidth (s : Shape) (h : ℤ) (q j r : ℕ) : ℤ :=
  (s.m : ℤ)*P0.agreement + j - q*(131071-h) - 2*h*((j : ℤ)+r)
private def width (s : Shape) (h q j r : ℕ) : ℕ :=
  s.m*P0.agreement + j - q*(131071-h) - 2*h*(j+r)
def weight (s : Shape) (v r : ℕ) : ℕ :=
  slots s.U (r*v) - slots s.U ((r+1)*v)
private theorem width_ge_signed (s : Shape) {h : ℕ} (hh : h ≤ 131071) (q j r : ℕ) :
    signedWidth s h q j r ≤ (width s h q j r : ℤ) := by
  have cast_sub_le (a b : ℕ) : (a : ℤ) - b ≤ ((a-b : ℕ) : ℤ) := by omega
  have h₁ := cast_sub_le (s.m*P0.agreement+j) (q*(131071-h))
  have h₂ := cast_sub_le (s.m*P0.agreement+j-q*(131071-h)) (2*h*(j+r))
  unfold signedWidth width
  push_cast [Nat.cast_sub hh] at h₁ h₂ ⊢
  linarith only [h₁, h₂]
private theorem blockValue_eq_sum (s : Shape) (h : ℤ) (j r n : ℕ) :
    blockValue s j r n h = ∑ t ∈ range n, 2 * signedWidth s h (j+t) j r := by
  calc
    _ = ∑ t ∈ range n,
        (2 * signedWidth s h j j r - 2*(131071-h)*(t : ℤ)) := by
      rw [sum_arithmetic]
      unfold blockValue signedWidth
      ring
    _ = _ := by
      apply sum_congr rfl
      intro t _
      unfold signedWidth
      push_cast
      ring
private theorem block_le (s : Shape) (v lo j r : ℕ) {h : ℕ} (hh : h ≤ 131071) :
    (weight s v r : ℤ) * blockValue s j r (supportCount s v lo j r) h ≤
      ∑ q ∈ Ico j (s.B+1), 2 * (weight s v r : ℤ) * (width s h q j r : ℤ) := by
  let n := supportCount s v lo j r
  let term (q : ℕ) := 2 * (weight s v r : ℤ) * (width s h q j r : ℤ)
  have hn : n ≤ s.B+1-j := Nat.sub_le_sub_right (Nat.min_le_left _ _) _
  rw [blockValue_eq_sum, mul_sum]
  calc
    _ ≤ ∑ t ∈ range n, term (j+t) := by
      apply sum_le_sum
      intro t _
      have ht := width_ge_signed s hh (j+t) j r
      unfold term
      rw [← mul_assoc, mul_comm (weight s v r : ℤ) 2]
      exact mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ ∑ t ∈ range (s.B+1-j), term (j+t) :=
      sum_le_sum_of_subset_of_nonneg (range_mono hn) (by intros; positivity)
    _ = _ := (sum_Ico_eq_sum_range term j (s.B+1)).symm
def weightedSum (s : Shape) (v : ℕ) (f : ℕ → ℕ → ℤ) : ℤ :=
  ∑ j ∈ range (s.J+1), ∑ r ∈ range (s.U/v+1), (weight s v r : ℤ) * f j r
def supportBase (s : Shape) (v lo : ℕ) : ℤ :=
  weightedSum s v fun j r => blockValue s j r (supportCount s v lo j r) lo
def supportSlope (s : Shape) (v lo : ℕ) : ℤ :=
  weightedSum s v fun j r => blockSlope j r (supportCount s v lo j r)
private def gain (s : Shape) (v h : ℕ) : ℕ :=
  shapeSum s fun q j => ∑ r ∈ range (s.U/v+1), weight s v r * width s h q j r
private theorem support_le_gain (s : Shape) (v lo : ℕ) {h : ℕ} (hh : h ≤ 131071) :
    supportBase s v lo + ((h : ℤ)-lo) * supportSlope s v lo ≤ 2 * (gain s v h : ℤ) := by
  have hline : supportBase s v lo + ((h : ℤ)-lo) * supportSlope s v lo =
      weightedSum s v (fun j r => blockValue s j r (supportCount s v lo j r) h) := by
    unfold supportBase supportSlope weightedSum
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro r _
    unfold blockValue blockSlope
    ring
  rw [hline]
  unfold gain shapeSum weightedSum
  push_cast
  simp only [mul_sum, ← mul_assoc]
  rw [shape_sum_flip]
  apply sum_le_sum
  intro j _
  rw [sum_comm]
  exact sum_le_sum fun r _ => block_le s v lo j r hh
def PositiveSupport (s : Shape) (v lo : ℕ) : Prop :=
  2 * ((nodeCost s : ℤ) + lo * (poleSlope s : ℤ)) < supportBase s v lo ∧
  2 * (poleSlope s : ℤ) ≤ supportSlope s v lo
theorem test_of_support (w : ℤ) {s : Shape} {v lo : ℕ}
    (hshape : P0_10.terminalShape w = s) (hv : (P0_10.band w).seedBound + 1 = v)
    (hlo : (lo : ℤ) ≤ w) (hhi : w ≤ 131071) (htest : PositiveSupport s v lo) :
    P0_10.subbankDebit w < P0_10.seedGain w := by
  have hw : w.toNat ≤ 131071 := by omega
  have hlo' : 0 ≤ (w.toNat : ℤ) - lo := by omega
  have hg : P0_10.seedGain w = gain s v w.toNat := by
    have hU : (P0_10.band w).subbankSeeds = s.U := congrArg Shape.U hshape
    have hm : (P0_10.band w).multiplicity = s.m := congrArg Shape.m hshape
    simp only [P0_10.seedGain, gain, weight, width, P0_10.rawWidth, hshape, hv, hU, hm]
  have hplane := support_le_gain s v lo hw
  obtain ⟨hbase, hslope⟩ := htest
  have hinc := mul_le_mul_of_nonneg_left hslope hlo'
  rw [hg, P0_10.subbankDebit, hshape, debit_eq]
  have hcast : ((nodeCost s + w.toNat * poleSlope s : ℕ) : ℤ) < (gain s v w.toNat : ℤ) := by
    push_cast
    nlinarith only [hplane, hinc, hbase]
  exact_mod_cast hcast
end P0_10_5
end
section
namespace P0_10_5
open K1_14 (Shape slots triangle)
open K1_14_5 (nodeCost poleSlope)
open Finset
open scoped BigOperators
open private nodeRow from ProximityPrize.SubmissionLower.Fast063
private theorem sum_diagonals (J R : ℕ) (f : ℕ → ℕ → ℤ) :
    (∑ j ∈ range (J+1), ∑ r ∈ range (R+1), f j r) =
      ∑ t ∈ range (J+R+1), ∑ r ∈ Ico (t-J) (min t R+1), f (t-r) r := by
  calc
    _ = ∑ r ∈ range (R+1), ∑ j ∈ range (J+1), f j r := sum_comm
    _ = ∑ r ∈ range (R+1), ∑ t ∈ Ico r (r+(J+1)), f (t-r) r := by
      apply sum_congr rfl
      intro r _
      rw [sum_Ico_eq_sum_range]
      simp
    _ = ∑ r ∈ range (R+1), ∑ t ∈ range (J+R+1),
        if r ≤ t ∧ t-r ≤ J then f (t-r) r else 0 := by
      apply sum_congr rfl
      intro r hr
      have hr' := mem_range.mp hr
      rw [← sum_filter]
      congr 1
      ext t
      simp only [mem_Ico, mem_filter, mem_range]
      omega
    _ = ∑ t ∈ range (J+R+1), ∑ r ∈ range (R+1),
        if r ≤ t ∧ t-r ≤ J then f (t-r) r else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro t _
      rw [← sum_filter]
      congr 1
      ext r
      simp only [mem_Ico, mem_filter, mem_range, Nat.lt_succ_iff, le_min_iff]
      omega
private def A (s : Shape) (lo t : ℕ) (slope : Bool) : ℤ :=
  if slope then -4*(t : ℤ) else 2*((s.m : ℤ)*P0.agreement) - 4*(t : ℤ)*lo
private def B (slope : Bool) : ℤ := if slope then 0 else 2
private def C (lo : ℕ) (slope : Bool) : ℤ := if slope then 1 else -(131071-(lo : ℤ))
private def cell (s : Shape) (v lo : ℕ) (slope : Bool) (j r : ℕ) : ℤ :=
  let n : ℤ := supportCount s v lo j r
  (weight s v r : ℤ) * (n * (A s lo (j+r) slope + B slope*j +
    C lo slope*(2*(j : ℤ)+n-1)))
private theorem cells (s : Shape) (v lo : ℕ) (slope : Bool) :
    (if slope then supportSlope s v lo else supportBase s v lo) =
      ∑ j ∈ range (s.J+1), ∑ r ∈ range (s.U/v+1), cell s v lo slope j r := by
  cases slope <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, supportBase, supportSlope, weightedSum]
  all_goals
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro r _
    simp only [cell, A, B, C, blockValue, blockSlope, Bool.false_eq_true, ite_false,
      ite_true, Nat.cast_add]
    ring
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
private def primitive (s : Shape) (v r : ℕ) (x y z : ℤ) : ℤ :=
  x*(moments s v r).1 + y*(moments s v r).2.1 + z*(moments s v r).2.2
private theorem primitive_step (s : Shape) (v r : ℕ) (x y z : ℤ) (h : MomentStep s v r) :
    primitive s v (r+1) x y z = primitive s v r x y z +
      (weight s v r : ℤ)*(x+y*r+z*r*r) := by
  obtain ⟨h0,h1,h2⟩ := h
  simp only [primitive, h0, h1, h2, Nat.cast_add, Nat.cast_mul]
  ring
private theorem telescope (f p : ℕ → ℤ) (a n : ℕ)
    (h : ∀ i < n, p (a+i+1) = p (a+i)+f (a+i)) :
    (∑ i ∈ range n, f (a+i)) = p (a+n)-p a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih (fun i hi => h i (by omega))]
    rw [← Nat.add_assoc, h n (by omega)]
    ring
private def primitiveAt (s : Shape) (v lo t : ℕ) (slope : Bool) (r : ℕ) : ℤ :=
  let k : ℤ := cut s v lo t
  let u := k-(t : ℤ)
  let a := A s lo t slope
  let b := B slope
  let c := C lo slope
  let e := a + b*t + c*((t : ℤ)+k-1)
  primitive s v r (u*e) (e-u*(b+c)) (-(b+c))
private def diagValue (s : Shape) (v lo t : ℕ) (slope : Bool) : ℤ :=
  primitiveAt s v lo t slope (min t (s.U/v)+1) -
    primitiveAt s v lo t slope (t-s.J)
private theorem one_diagonal (s : Shape) (v lo t : ℕ) (slope : Bool)
    (ht : t < s.J+s.U/v+1) (hc : ValidCut s v lo t)
    (hm : ∀ r < s.U/v+1, MomentStep s v r) :
    (∑ r ∈ Ico (t-s.J) (min t (s.U/v)+1), cell s v lo slope (t-r) r) =
      diagValue s v lo t slope := by
  let a := t-s.J
  let b := min t (s.U/v)+1
  have hab : a ≤ b := by
    change t-s.J ≤ min t (s.U/v)+1
    exact Nat.le.step (le_min (Nat.sub_le ..) (Nat.sub_le_iff_le_add'.2 (Nat.le_of_lt_succ ht)))
  change (∑ r ∈ Ico a b, _) = primitiveAt s v lo t slope b -
    primitiveAt s v lo t slope a
  rw [sum_Ico_eq_sum_range]
  conv_rhs => rw [← Nat.add_sub_of_le hab]
  apply telescope (fun r => cell s v lo slope (t-r) r) (primitiveAt s v lo t slope) a (b-a)
  intro i hi
  let r := a+i
  have hmem : r ∈ Ico (t-s.J) (min t (s.U/v)+1) := by
    change r ∈ Ico a b
    exact mem_Ico.mpr ⟨by dsimp [r]; omega, by dsimp [r]; omega⟩
  obtain ⟨_, he⟩ := mem_Ico.mp hmem
  have hr : r ≤ t := by omega
  have hjk : t-r ≤ cut s v lo t :=
    (le_min (Nat.sub_le ..) (by have := (mem_Ico.mp hmem).1; omega)).trans hc.1
  change primitiveAt s v lo t slope (r+1) =
    primitiveAt s v lo t slope r + cell s v lo slope (t-r) r
  simp only [primitiveAt, primitive_step _ _ r _ _ _ (hm r (by omega))]
  congr 1
  simp only [cell, supportCount, Nat.sub_add_cancel hr, Nat.cast_sub hjk, Nat.cast_sub hr]
  ring
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
private theorem scan_ok (f : ℕ → Row) (a n : ℕ) (h : (scan f a n).ok = true) :
    ∀ i < n, (f (a+i)).ok = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi' | rfl
    · exact ih hl i hi'
    · exact hr
private theorem scan_sum (f : ℕ → Row) (a n : ℕ) (slope : Bool) :
    (if slope then (scan f a n).slope else (scan f a n).base) =
      ∑ i ∈ range n, if slope then (f (a+i)).slope else (f (a+i)).base := by
  cases slope <;> induction n with
  | zero => simp [scan]
  | succ n ih => simp_all only [scan, Row.add, Bool.false_eq_true, ite_false, ite_true,
      sum_range_succ]
def diagonalRow (s : Shape) (v lo t : ℕ) : Row :=
  ⟨decide (ValidCut s v lo t) && (if t < s.U/v+1 then decide (MomentStep s v t) else true),
    diagValue s v lo t false, diagValue s v lo t true⟩
private theorem support_eq (s : Shape) (v lo : ℕ) (slope : Bool)
    (h : (scan (diagonalRow s v lo) 0 (s.J+s.U/v+1)).ok = true) :
    (if slope then supportSlope s v lo else supportBase s v lo) =
      if slope then (scan (diagonalRow s v lo) 0 (s.J+s.U/v+1)).slope
      else (scan (diagonalRow s v lo) 0 (s.J+s.U/v+1)).base := by
  have checked i (hi : i < s.J+s.U/v+1) :
      decide (ValidCut s v lo i) = true ∧
        (if i < s.U/v+1 then decide (MomentStep s v i) else true) = true := by
    apply Bool.and_eq_true_iff.mp
    simpa only [Nat.zero_add, diagonalRow] using scan_ok _ _ _ h i hi
  have hm r (hr : r < s.U/v+1) : MomentStep s v r := by
    have h := (checked r (by omega)).2
    simpa only [ite_eq_left hr, decide_eq_true_eq] using h
  rw [cells, sum_diagonals, scan_sum]
  apply sum_congr rfl
  intro t ht
  have ht := mem_range.mp ht
  have hc : ValidCut s v lo t := of_decide_eq_true (checked t ht).1
  rw [one_diagonal s v lo t slope ht hc hm]
  cases slope <;> simp [diagonalRow]
def debitRow (m B J q : ℕ) : Row :=
  ⟨true, (nodeRow (min q J+1) (m+min q J-q) : ℤ),
    ((min q J+1)*((B+J-q)*(B-q)) : ℕ)⟩
theorem certify (s : Shape) (v lo : ℕ) {base slope nodes poles : ℤ}
    (hs : scan (diagonalRow s v lo) 0 (s.J+s.U/v+1) = ⟨true, base, slope⟩)
    (hd : scan (debitRow s.m s.B s.J) 0 (s.B+1) = ⟨true, nodes, poles⟩)
    (hbase : 2*((triangle s.U : ℤ)*262144*nodes + lo*(2*((s.U+1 : ℕ) : ℤ)*poles)) < base)
    (hslope : 2*(2*((s.U+1 : ℕ) : ℤ)*poles) ≤ slope) :
    PositiveSupport s v lo := by
  have hok := congrArg Row.ok hs
  have hb := support_eq s v lo false hok
  have ha := support_eq s v lo true hok
  rw [hs] at hb ha
  have hn := (scan_sum (debitRow s.m s.B s.J) 0 (s.B+1) false).symm
  have hp := (scan_sum (debitRow s.m s.B s.J) 0 (s.B+1) true).symm
  rw [hd] at hn hp
  simp only [Bool.false_eq_true, ite_false, ite_true, Nat.zero_add, debitRow] at hn hp hb ha
  unfold PositiveSupport nodeCost poleSlope
  push_cast [Nat.cast_sum] at hp hbase hslope ⊢
  rw [hn, hp, hb, ha]
  exact ⟨hbase, hslope⟩
end P0_10_5
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_2_5
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 Polynomial
open K1_14_3 (Slice ClearedEquation liftEquation clearedDx ordinaryCutter IsClearing)
open K1_14_3_2 (ordinarySeedDegree)
open scoped BigOperators
theorem ordinary_row_caps (f : Equation) (J : ℕ) :
    RowCaps (C f) ⟨0, f.natDegree, J, ordinarySeedDegree f⟩ := by
  intro v y hv
  cases v with
  | zero =>
    rw [coeff_C_zero] at hv ⊢
    exact ⟨by simpa using le_natDegree_of_ne_zero hv, Nat.zero_le _,
      Finset.le_sup (f := fun i => (f.coeff i).totalDegree)
        (Polynomial.mem_support_iff.mpr hv)⟩
  | succ v =>
    simp only [coeff_C_succ, coeff_zero, ne_eq, not_true_eq_false] at hv
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
private theorem cutter_reading (g : ClearedEquation) :
    ordinaryCutter g = K1_14_3R.chainCutter g ∨
    ordinaryCutter g = C (liftEquation (clearedDx g) +
      (Polynomial.X : Equation) * liftEquation g.derivative) := by
  first
  | apply Or.inr
    change C (liftEquation (clearedDx g)) +
      (C (Polynomial.X (R := Seeds)) : Jet) * C (liftEquation g.derivative) = _
    rw [map_add, map_mul]
  | exact Or.inl rfl
theorem ordinary_cutter_caps {f : Equation} (hf : f ≠ 0)
    {g : ClearedEquation} {a : L[X]} (hg : IsClearing f g a) :
    RowCaps (ordinaryCutter g) ⟨0, f.natDegree, 1, ordinarySeedDegree f⟩ := by
  let Q := K1_14_3R.chainCutter g
  have hQ : RowCaps Q ⟨0, f.natDegree, 1, ordinarySeedDegree f⟩ :=
    K1_14_3R.chainCutter_caps_of_dvd (C_ne_zero.mpr hf) (ordinary_row_caps f 1)
      le_rfl (dvd_refl (C f : Jet)) hg
  rcases cutter_reading g with h | h
  · exact h ▸ hQ
  rw [h]
  let A := liftEquation (clearedDx g)
  let D := liftEquation g.derivative
  have hA (y : ℕ) : (Q.coeff 0).coeff y = A.coeff y := by simp [Q, A, K1_14_3R.chainCutter]
  have hD (y : ℕ) : (Q.coeff 1).coeff y = D.coeff y := by simp [Q, D, K1_14_3R.chainCutter]
  have ha (y : ℕ) (hy : A.coeff y ≠ 0) :
      y ≤ f.natDegree ∧ (A.coeff y).totalDegree ≤ ordinarySeedDegree f := by
    obtain ⟨hB, _, hU⟩ := hQ 0 y (by rwa [hA])
    rw [hA] at hU
    exact ⟨by simpa using hB, hU⟩
  have hd (y : ℕ) (hy : D.coeff y ≠ 0) :
      y + 1 ≤ f.natDegree ∧ (D.coeff y).totalDegree ≤ ordinarySeedDegree f := by
    obtain ⟨hB, _, hU⟩ := hQ 1 y (by rwa [hD])
    rw [hD] at hU
    exact ⟨hB, hU⟩
  intro v y hy
  cases v with
  | succ v =>
    simp only [coeff_C_succ, coeff_zero, ne_eq, not_true_eq_false] at hy
  | zero =>
    change ((C (A + (Polynomial.X : Equation) * D) : Jet).coeff 0).coeff y ≠ 0 at hy
    change y + 0 ≤ f.natDegree ∧ 0 ≤ 1 ∧
      (((C (A + (Polynomial.X : Equation) * D) : Jet).coeff 0).coeff y).totalDegree ≤
        ordinarySeedDegree f
    simp only [coeff_C_zero, coeff_add, Nat.add_zero] at hy ⊢
    cases y with
    | zero =>
      simp only [coeff_X_mul_zero, add_zero] at hy ⊢
      exact ⟨(ha 0 hy).1, Nat.zero_le _, (ha 0 hy).2⟩
    | succ y =>
      simp only [coeff_X_mul] at hy ⊢
      refine ⟨?_, Nat.zero_le _, (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)⟩
      · by_cases hz : A.coeff (y+1) = 0
        · simp only [hz, zero_add] at hy
          exact (hd y hy).1
        · exact (ha (y+1) hz).1
      · by_cases hz : A.coeff (y+1) = 0
        · simp [hz]
        · exact (ha (y+1) hz).2
      · by_cases hz : D.coeff y = 0
        · simp [hz]
        · exact (hd y hz).2
private def seedMap (s : Slice) : Seeds →+* Plane (SliceField s) :=
  (sliceEval s).comp (rootIncl.comp rootSeeds)
private def yImage (s : Slice) : Plane (SliceField s) := sliceEval s (MvPolynomial.X 2)
private def vImage (s : Slice) : Plane (SliceField s) := sliceEval s (MvPolynomial.X 3)
private theorem seedMap_eq_eval (s : Slice) :
    seedMap s = MvPolynomial.eval₂Hom ((sliceEval s).comp MvPolynomial.C)
      (fun i => seedMap s (MvPolynomial.X i)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [seedMap, rootIncl, rootSeeds]
  · intro i
    simp
private theorem row_expansion (s : Slice) (P : Jet) :
    sliceRow s P =
      ∑ j ∈ P.support, (∑ i ∈ (P.coeff j).support,
        seedMap s ((P.coeff j).coeff i) * yImage s ^ i) * vImage s ^ j := by
  have hx : rootIncl (MvPolynomial.X 2) = MvPolynomial.X 2 := by simp [rootIncl]
  simp only [sliceRow, toJet, coe_eval₂RingHom, Polynomial.eval₂_eq_sum,
    Polynomial.sum_def, RingHom.comp_apply, toRoot, seedMap, yImage, vImage,
    map_sum, map_mul, map_pow, hx]
private theorem measure_eval {s : Slice} (m : Plane (SliceField s) → ℕ)
    (hzero : m 0 = 0) (hone : m 1 = 0)
    (hadd : ∀ a b, m (a + b) ≤ max (m a) (m b))
    (hmul : ∀ a b, m (a * b) ≤ m a + m b)
    (hC : ∀ c : FX, m (sliceEval s (MvPolynomial.C c)) = 0)
    {t y v n : ℕ} (ht : ∀ k : Fin 2, m (seedMap s (MvPolynomial.X k)) ≤ t)
    (hy : m (yImage s) ≤ y) (hv : m (vImage s) ≤ v)
    (P : Jet) (hP : ∀ j i, (P.coeff j).coeff i ≠ 0 →
      ((P.coeff j).coeff i).totalDegree * t + i * y + j * v ≤ n) :
    m (sliceRow s P) ≤ n := by
  classical
  have hsum {α : Type} (E : Finset α) (a : α → Plane (SliceField s)) (b : ℕ)
      (h : ∀ k ∈ E, m (a k) ≤ b) : m (∑ k ∈ E, a k) ≤ b := by
    induction E using Finset.cons_induction_on with
    | empty => simp [hzero]
    | cons k E hk ih =>
      rw [Finset.sum_cons]
      exact (hadd _ _).trans (max_le (h k (by simp)) (ih fun l hl => h l (by simp [hl])))
  have hpow (a : Plane (SliceField s)) (k b : ℕ) (ha : m a ≤ b) : m (a^k) ≤ k*b := by
    induction k with
    | zero => simp [hone]
    | succ k ih =>
      exact (by
        rw [pow_succ, Nat.succ_mul]
        exact (hmul _ _).trans (Nat.add_le_add ih ha))
  have hseeds (A : Seeds) : m (seedMap s A) ≤ A.totalDegree * t := by
    conv_lhs => rw [seedMap_eq_eval, MvPolynomial.as_sum A, map_sum]
    apply hsum
    intro e he
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, RingHom.comp_apply]
    apply (hmul _ _).trans
    rw [hC, zero_add]
    refine (e.support.apply_prod_le_sum_apply m hone.le hmul).trans ?_
    refine (Finset.sum_le_sum fun k _ => hpow _ _ _ (ht k)).trans ?_
    rw [← Finset.sum_mul]
    exact Nat.mul_le_mul_right _ (MvPolynomial.le_totalDegree he)
  rw [row_expansion]
  apply hsum
  intro j hj
  have hnj : j*v ≤ n := by
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (Polynomial.mem_support_iff.mp hj)
    exact (Nat.le_add_left _ _).trans (hP j i (Polynomial.mem_support_iff.mp hi))
  refine (hmul _ _).trans ((Nat.add_le_add (b := n-j*v) ?_ (hpow _ j v hv)).trans ?_)
  · apply hsum (b := n - j*v)
    intro i hi
    exact (hmul _ _).trans ((Nat.add_le_add (hseeds _) (hpow _ _ _ hy)).trans
      (Nat.le_sub_of_add_le (hP j i (Polynomial.mem_support_iff.mp hi))))
  · omega
private theorem scalar_image (s : Slice) (c : FX) :
    ∃ d : SliceField s, sliceEval s (MvPolynomial.C c) = MvPolynomial.C d := by
  cases s <;> exact ⟨algebraMap FX _ c, by
    simp [sliceEval, mapGenericSeed, mapGenericJets, sectionBase, lineElim,
      MvPolynomial.algebraMap_eq]⟩
private theorem degree_bound {s : Slice} (k : Fin 2) {t y v n : ℕ}
    (ht : ∀ l : Fin 2, MvPolynomial.degreeOf k (seedMap s (MvPolynomial.X l)) ≤ t)
    (hy : MvPolynomial.degreeOf k (yImage s) ≤ y)
    (hv : MvPolynomial.degreeOf k (vImage s) ≤ v)
    (P : Jet) (hP : ∀ j i, (P.coeff j).coeff i ≠ 0 →
      ((P.coeff j).coeff i).totalDegree * t + i*y + j*v ≤ n) :
    (sliceRow s P).degreeOf k ≤ n :=
  measure_eval (MvPolynomial.degreeOf k) (MvPolynomial.degreeOf_zero k)
    (MvPolynomial.degreeOf_one k) (MvPolynomial.degreeOf_add_le k)
    (MvPolynomial.degreeOf_mul_le k)
    (fun c => by obtain ⟨d, hd⟩ := scalar_image s c; rw [hd, MvPolynomial.degreeOf_C])
    ht hy hv P hP
private theorem degreeOf_affine {F : Type} [Field F] (c d : F) (k l : Fin 2) :
    MvPolynomial.degreeOf k (MvPolynomial.C c - MvPolynomial.C d * (MvPolynomial.X l : Plane F)) ≤
      MvPolynomial.degreeOf k (MvPolynomial.X l : Plane F) := by
  refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · simp [MvPolynomial.degreeOf_C]
  · exact MvPolynomial.degreeOf_C_mul_le _ _ _
private theorem seedMap_X (s : Slice) (i : Fin 2) :
    seedMap s (MvPolynomial.X i) = sliceEval s (MvPolynomial.X (Fin.castLE (by decide) i)) := by
  simp [seedMap, rootIncl, rootSeeds, Fin.castLE_castLE]
theorem seed_section_caps {P : Jet} {d : Shape} (h : RowCaps P d) :
    BidegreeLE (sliceRow .seed P) d.B d.J := by
  constructor
  · refine degree_bound (s := .seed) 0 (t := 0) (y := 1) (v := 0) ?_ ?_ ?_ P ?_
    · intro i
      rw [seedMap_X]
      fin_cases i <;> simp [sliceEval, mapGenericSeed, MvPolynomial.degreeOf_C]
    · simp [yImage, sliceEval, mapGenericSeed]
    · simp [vImage, sliceEval, mapGenericSeed, MvPolynomial.degreeOf_X]
    · intro j i hi
      simpa using (Nat.le_add_right i j).trans (h j i hi).1
  · refine degree_bound (s := .seed) 1 (t := 0) (y := 0) (v := 1) ?_ ?_ ?_ P ?_
    · intro i
      rw [seedMap_X]
      fin_cases i <;> simp [sliceEval, mapGenericSeed, MvPolynomial.degreeOf_C]
    · simp [yImage, sliceEval, mapGenericSeed, MvPolynomial.degreeOf_X]
    · simp [vImage, sliceEval, mapGenericSeed]
    · intro j i hi
      simpa using (h j i hi).2.1
private theorem line_seed_degree (mixed : Bool) (k : Fin 2) (i : Fin 2) :
    MvPolynomial.degreeOf k
      ((lineElim mixed) (sectionBase (MvPolynomial.X (Fin.castLE (by decide) i)))) ≤
      MvPolynomial.degreeOf k (MvPolynomial.X 0 : Plane SectionField) := by
  fin_cases i
  · simpa [sectionBase, lineElim] using degreeOf_affine (sliceParameter 2) (sliceParameter 0) k 0
  · simp [sectionBase, lineElim]
theorem ordinate_section_caps {P : Jet} {d : Shape} (h : RowCaps P d) :
    BidegreeLE (sliceRow .ordinate P) d.U d.J := by
  constructor
  · refine degree_bound (s := .ordinate) 0 (t := 1) (y := 0) (v := 0) ?_ ?_ ?_ P ?_
    · intro i
      rw [seedMap_X]
      simpa [sliceEval] using line_seed_degree false 0 i
    · simp [yImage, sliceEval, lineElim, sectionBase, MvPolynomial.degreeOf_C]
    · simp [vImage, sliceEval, lineElim, sectionBase, MvPolynomial.degreeOf_X]
    · intro j i hi
      simpa using (h j i hi).2.2
  · refine degree_bound (s := .ordinate) 1 (t := 0) (y := 0) (v := 1) ?_ ?_ ?_ P ?_
    · intro i
      rw [seedMap_X]
      simpa [sliceEval, MvPolynomial.degreeOf_X] using line_seed_degree false 1 i
    · simp [yImage, sliceEval, lineElim, sectionBase, MvPolynomial.degreeOf_C]
    · simp [vImage, sliceEval, lineElim, sectionBase]
    · intro j i hi
      simpa using (h j i hi).2.1
theorem mixed_section_caps {P : Jet} {d : Shape} (h : RowCaps P d) :
    BidegreeLE (sliceRow .mixed P) d.U d.B := by
  constructor
  · refine degree_bound (s := .mixed) 0 (t := 1) (y := 0) (v := 0) ?_ ?_ ?_ P ?_
    · intro i
      rw [seedMap_X]
      simpa [sliceEval] using line_seed_degree true 0 i
    · simpa [yImage, sliceEval, sectionBase, lineElim, MvPolynomial.algebraMap_eq,
        MvPolynomial.degreeOf_X] using degreeOf_affine (sliceParameter 3) (sliceParameter 1) 0 1
    · simp [vImage, sliceEval, sectionBase, lineElim, MvPolynomial.degreeOf_X]
    · intro j i hi
      simpa using (h j i hi).2.2
  · refine degree_bound (s := .mixed) 1 (t := 0) (y := 1) (v := 1) ?_ ?_ ?_ P ?_
    · intro i
      rw [seedMap_X]
      simpa [sliceEval, MvPolynomial.degreeOf_X] using line_seed_degree true 1 i
    · simpa [yImage, sliceEval, sectionBase, lineElim, MvPolynomial.algebraMap_eq] using
        degreeOf_affine (sliceParameter 3) (sliceParameter 1) 1 1
    · simp [vImage, sliceEval, sectionBase, lineElim]
    · intro j i hi
      simpa using (h j i hi).1
theorem jet_section_caps {P : Jet} {d : Shape} (h : RowCaps P d) :
    (sliceRow .jets P).totalDegree ≤ d.U := by
  refine measure_eval (s := .jets) MvPolynomial.totalDegree MvPolynomial.totalDegree_zero
    MvPolynomial.totalDegree_one MvPolynomial.totalDegree_add MvPolynomial.totalDegree_mul ?_
    (t := 1) (y := 0) (v := 0) ?_ ?_ ?_ P ?_
  · intro c
    obtain ⟨e, he⟩ := scalar_image .jets c
    rw [he, MvPolynomial.totalDegree_C]
  · intro i
    rw [seedMap_X]
    fin_cases i <;> simp [sliceEval, mapGenericJets, MvPolynomial.totalDegree_X]
  · simp [yImage, sliceEval, mapGenericJets, MvPolynomial.totalDegree_C]
  · simp [vImage, sliceEval, mapGenericJets, MvPolynomial.totalDegree_C]
  · intro j i hi
    simpa using (h j i hi).2.2
end
end K1_14_2_2_2_5
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace K1_14_2_2_2_5
noncomputable section
open MvPolynomial Polynomial
open scoped BigOperators
private abbrev BoxPlane (F : Type) [Field F] := MvPolynomial (Option (Fin 1)) F
private theorem principal_finite_is_unit {F : Type} [Field F] {D : BoxPlane F}
    (hfin : Module.Finite F (BoxPlane F ⧸ Ideal.span {D})) : IsUnit D := by
  let _ := hfin
  have hz : (affineHilbertPolynomial (Ideal.span {D})).natDegree = 0 := by
    rw [affineHilbertPolynomial_eq_C_finrank, Polynomial.natDegree_C]
  by_contra hu
  by_cases hD : D = 0
  · simp [hD, natDegree_affineHilbertPolynomial_bot] at hz
  · have h := natDegree_affineHilbertPolynomial_span_singleton_add_one hD
      (mt Ideal.span_singleton_eq_top.mp hu)
    simp [hz] at h
private theorem regular_plane_pair {F : Type} [Field F] {A B : BoxPlane F}
    (hfin : Module.Finite F (BoxPlane F ⧸ Ideal.span {A, B}))
    (hproper : Ideal.span ({A, B} : Set (BoxPlane F)) ≠ ⊤) :
    A ≠ 0 ∧ IsLeftRegular (Ideal.Quotient.mk (Ideal.span {A}) B) := by
  let J : Ideal (BoxPlane F) := Ideal.span {A, B}
  let I : Ideal (BoxPlane F) := Ideal.span {A}
  let _ := hfin
  have hAu : A ≠ 0 := by
    intro hz
    have he : J = Ideal.span {B} := by
      simp [J, hz, Ideal.span_pair_comm]
    have hf : Module.Finite F (BoxPlane F ⧸ Ideal.span {B}) := by
      rw [← he]
      exact hfin
    exact hproper (he.trans (Ideal.span_singleton_eq_top.mpr (principal_finite_is_unit hf)))
  let : UniqueFactorizationMonoid F := PrincipalIdealRing.to_uniqueFactorizationMonoid
  let : UniqueFactorizationMonoid (BoxPlane F) :=
    MvPolynomial.uniqueFactorizationMonoid (Option (Fin 1))
  have hprime : ∀ {D : BoxPlane F}, D ∣ A → D ∣ B → ¬ Prime D := by
    intro D ha hb hD
    have hle : J ≤ Ideal.span {D} := Ideal.span_le.mpr (by
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨Ideal.mem_span_singleton.mpr ha, Ideal.mem_span_singleton.mpr hb⟩)
    have hfin' := Module.Finite.of_surjective (Ideal.Quotient.factorₐ F hle).toLinearMap
      (Ideal.Quotient.factor_surjective hle)
    exact hD.not_isUnit (principal_finite_is_unit hfin')
  refine ⟨hAu, ?_⟩
  intro x y hxy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  let q := Ideal.Quotient.mk I
  have hd : A ∣ (x-y) * B := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q ((x-y) * B) = 0
    rw [mul_comm, map_mul, map_sub, mul_sub]
    exact sub_eq_zero.mpr hxy
  have he := UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors hAu @hprime hd
  change q x = q y
  rw [← sub_eq_zero, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr he)
private theorem box_length {F : Type} [Field F] {A B : BoxPlane F} {u b d : ℕ}
    (hu : 0 < u) (hd : 0 < d) (hfin : Module.Finite F (BoxPlane F ⧸ Ideal.span {A, B}))
    (hA : A ∈ restrictBidegree (Fin 1) F u b) (hB : B ∈ restrictBidegree (Fin 1) F u d) :
    Module.finrank F (BoxPlane F ⧸ Ideal.span {A, B}) ≤ u * (b + d) := by
  let I : Ideal (BoxPlane F) := Ideal.span {A}
  let J : Ideal (BoxPlane F) := Ideal.span {A, B}
  by_cases hJ : J = ⊤
  · let _ : Subsingleton (BoxPlane F ⧸ J) := Ideal.Quotient.subsingleton_iff.mpr hJ
    change Module.finrank F (BoxPlane F ⧸ J) ≤ _
    rw [Module.finrank_eq_zero_of_subsingleton]
    exact Nat.zero_le _
  obtain ⟨hAz, hreg⟩ := regular_plane_pair hfin hJ
  have hIJ : I ≤ J := Ideal.span_mono (by simp)
  have hI : I ≠ ⊤ := fun he => hJ (top_le_iff.mp (he ▸ hIJ))
  let e := bidegreeMap (Fin 1) F u d
  let h := bidegreeLift B hB
  have he : Function.Surjective e.toRingHom := bidegreeMap_surjective hu hd
  have hh : e h = B := bidegreeMap_bidegreeLift B hB
  let K := I.comap e.toRingHom
  let D := K ⊔ Ideal.span {h}
  have hDmap : D.map e.toRingHom = J := by
    change (I.comap e.toRingHom ⊔ Ideal.span {h}).map e.toRingHom = J
    rw [Ideal.map_sup, Ideal.map_comap_of_surjective _ he, Ideal.map_span, Set.image_singleton,
      show e.toRingHom h = B from hh, ← Ideal.span_union]
    congr 1
  have hD : J.comap e.toRingHom = D := by
    rw [← hDmap, Ideal.comap_map_of_surjective _ he, sup_eq_left]
    exact (Ideal.comap_mono bot_le : Ideal.comap e.toRingHom ⊥ ≤ K).trans le_sup_left
  let q := Ideal.quotientMapₐ J e hD.ge
  let q' := Ideal.quotientMapₐ I e (le_rfl : K ≤ I.comap e.toRingHom)
  let eq := AlgEquiv.ofBijective q ⟨Ideal.quotientMap_injective' (H := hD.ge) hD.le,
    Ideal.quotientMap_surjective (H := hD.ge) he⟩
  let _ := hfin
  let _ := Module.Finite.of_surjective eq.symm.toLinearMap eq.symm.surjective
  have hK : (affineHilbertPolynomial K).natDegree = 1 := by
    have ht := natDegree_affineHilbertPolynomial_comap_bidegreeMap_span_singleton hu hd hAz hI
    rw [← show ((Ideal.span {A}).comap (bidegreeMap (Fin 1) F u d)) = K from rfl]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using ht
  have hL : (affineHilbertPolynomial K).leadingCoeff ≤ (u * (b + d) : ℕ) := by
    have ht := affineDegree_comap_bidegreeMap_span_singleton_le hu hd hAz hA
    rw [show ((Ideal.span {A}).comap (bidegreeMap (Fin 1) F u d)) = K from rfl, affineDegree, hK]
      at ht
    simpa [Nat.mul_add, Nat.mul_comm, add_comm] using ht
  have hreg' : IsLeftRegular (Ideal.Quotient.mk K h) := by
    intro x y hxy
    apply (Ideal.quotientMap_injective (I := I) (f := e.toRingHom))
    change q' x = q' y
    apply hreg
    exact (by
      have heq := congrArg q' hxy
      simpa only [map_mul, q', Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, hh] using heq)
  have ht := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le hreg'
    (totalDegree_bidegreeLift_le_one B hB)).2
  change (affineHilbertPolynomial D).coeff ((affineHilbertPolynomial K).natDegree - 1) ≤ _ at ht
  rw [affineHilbertPolynomial_eq_C_finrank, hK] at ht
  have hdim := eq.toLinearEquiv.finrank_eq
  have hr : (Module.finrank F (BoxPlane F ⧸ J) : ℚ) ≤ (u * (b + d) : ℕ) := by
    rw [← hdim]
    exact (by simpa using ht : _ ≤ (affineHilbertPolynomial K).leadingCoeff).trans hL
  exact_mod_cast hr
private theorem one_variable {F : Type} [Field F] {A : Plane F} (hA : A.degreeOf 0 ≤ 0) :
    ∃ f : F[X], Polynomial.aeval (MvPolynomial.X 1 : Plane F) f = A := by
  classical
  refine ⟨∑ m ∈ A.support, Polynomial.monomial (m 1) (A.coeff m), ?_⟩
  conv_rhs => rw [MvPolynomial.as_sum A]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hz : m 0 = 0 := Nat.eq_zero_of_le_zero (MvPolynomial.degreeOf_le_iff.mp hA m hm)
  have he : m = Finsupp.single 1 (m 1) := by
    ext i
    fin_cases i
    · simpa using hz
    · simp
  rw [Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.C_mul_monomial, mul_one]
  exact congrArg (fun n => MvPolynomial.monomial n (A.coeff m)) he.symm
theorem rectangle_length {F : Type} [Field F] (A B : Plane F) (u b d : ℕ)
    (hd : 0 < d) (hfin : Module.Finite F (PlaneQuotient A B))
    (hA : BidegreeLE A u b) (hB : BidegreeLE B u d) :
    Module.finrank F (PlaneQuotient A B) ≤ u * (b + d) := by
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · obtain ⟨a, ha⟩ := one_variable hA.1
    obtain ⟨b', hb⟩ := one_variable hB.1
    let g : F[X] →+* Plane F := (Polynomial.aeval (MvPolynomial.X 1 : Plane F)).toRingHom
    change g a = A at ha
    change g b' = B at hb
    rw [← ha, ← hb] at hfin ⊢
    simp only [K1_14_3_2_4.univariate_plane_length_zero g a b' hfin, Nat.zero_mul, le_refl]
  let ρ := MvPolynomial.renameEquiv F (finSuccEquiv 1)
  have hbox {P : Plane F} {w : ℕ} (hP : BidegreeLE P u w) :
      ρ P ∈ restrictBidegree (Fin 1) F u w := by
    have h0 : (ρ P).degreeOf none ≤ u := by
      simpa only [ρ, renameEquiv_apply, ← show finSuccEquiv 1 0 = none from rfl,
        degreeOf_rename_of_injective (finSuccEquiv 1).injective] using hP.1
    have h1 : (ρ P).degreeOf (some 0) ≤ w := by
      simpa only [ρ, renameEquiv_apply, ← show finSuccEquiv 1 1 = some 0 from rfl,
        degreeOf_rename_of_injective (finSuccEquiv 1).injective] using hP.2
    refine mem_restrictBidegree.mpr fun m hm => ⟨degreeOf_le_iff.mp h0 m hm, ?_⟩
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_one] using degreeOf_le_iff.mp h1 m hm
  let q := Ideal.quotientEquivAlg (Ideal.span ({A, B} : Set (Plane F))) ρ (J :=
    Ideal.span {ρ A, ρ B}) (by
      simp [Ideal.map_span, Set.image_insert_eq, Set.image_singleton])
  let _ := hfin
  have hf := Module.Finite.of_surjective q.toLinearMap q.surjective
  have hq := q.toLinearEquiv.finrank_eq
  exact hq.trans_le (box_length hu hd hf (hbox hA) (hbox hB))
end
end K1_14_2_2_2_5
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_2_5
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 Polynomial
open K1_14_3 (Slice ordinaryCutter)
open K1_14_3_2 (ProperPair ordinarySeedDegree)
def c1 : Prop :=
  ∀ (P Q : Jet), ProperPair P Q → ∀ s : Slice,
    Module.Finite (SliceField s) (PlaneQuotient (sliceRow s P) (sliceRow s Q))
def c2 : Prop :=
  ∀ (I J : Ideal Ambient), I.IsPrime → J.IsPrime →
    ringKrullDim (CoordinateRing I) = 2 → ringKrullDim (CoordinateRing J) = 2 → I ≠ J →
    ∀ s : Slice, IsCoprime (I.map (sliceEval s)) (J.map (sliceEval s))
theorem of_children (h1 : c1) (h2 : c2) : K1_14_2_2_2.c5 := by
  intro f g a hirr hpos _ hclear hproper S hS
  let P : Jet := C f
  let Q : Jet := ordinaryCutter g
  let x := ordinarySeedDegree f
  let y := f.natDegree
  have hP : RowCaps P ⟨0, y, 0, x⟩ := ordinary_row_caps f 0
  have hQ : RowCaps Q ⟨0, y, 1, x⟩ := ordinary_cutter_caps hirr.ne_zero hclear
  have hfinite (s : Slice) := h1 P Q hproper s
  have hslice (s : Slice) := slice_budget hS s (hfinite s) fun I hi J hj hne =>
    h2 I J (hS I hi).1 (hS J hj).1 (hS I hi).2.1 (hS J hj).2.1 hne s
  refine ⟨fun I hi => sections_finite (fun s => (hslice s).1 I hi), ?_⟩
  intro k
  rw [mass_slice]
  fin_cases k
  · apply (hslice .seed).2.trans
    simpa [ordinaryBudget] using
      rectangle_length _ _ y 0 1 Nat.zero_lt_one (hfinite .seed)
        (seed_section_caps hP) (seed_section_caps hQ)
  · apply (hslice .ordinate).2.trans
    simpa [ordinaryBudget] using
      rectangle_length _ _ x 0 1 Nat.zero_lt_one (hfinite .ordinate)
        (ordinate_section_caps hP) (ordinate_section_caps hQ)
  · apply (hslice .mixed).2.trans
    have h := rectangle_length _ _ x y y hpos (hfinite .mixed)
      (mixed_section_caps hP) (mixed_section_caps hQ)
    rw [← Nat.two_mul y, ← Nat.mul_assoc, Nat.mul_comm x 2] at h
    exact h
  · apply (hslice .jets).2.trans
    simpa [ordinaryBudget, pow_two] using K1_14_3_2_4.planeBezout
      (sliceRow .jets P) (sliceRow .jets Q) x (hfinite .jets)
      (jet_section_caps hP) (jet_section_caps hQ)
end
end K1_14_2_2_2_5
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
private def jetSeed (i : Fin 2) : Jet := C (C (MvPolynomial.X i))
private def jetOrdinate : Jet := C (Polynomial.X (R := Seeds))
private def jetDerivative : Jet := Polynomial.X
private def fromAmbient : Ambient →+* Jet :=
  MvPolynomial.eval₂Hom (C.comp (C.comp MvPolynomial.C))
    ![jetSeed 0, jetSeed 1, jetOrdinate, jetDerivative]
private theorem toJet_fromAmbient : toJet.comp fromAmbient = RingHom.id Ambient := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [fromAmbient, toJet, toRoot, rootIncl, rootSeeds]
  · intro i
    fin_cases i <;> simp [fromAmbient, toJet, toRoot, rootIncl, rootSeeds,
      jetSeed, jetOrdinate, jetDerivative]
private theorem fromAmbient_toJet : fromAmbient.comp toJet = RingHom.id Jet := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp [fromAmbient, toJet, toRoot, rootIncl, rootSeeds]
      · intro i
        fin_cases i <;> simp [fromAmbient, toJet, toRoot, rootIncl, rootSeeds, jetSeed]
    · simp [fromAmbient, toJet, toRoot, rootIncl, jetOrdinate]
  · simp [fromAmbient, toJet, jetDerivative]
def jetEquiv : Jet ≃+* Ambient :=
  { toJet with
    invFun := fromAmbient
    left_inv := DFunLike.congr_fun fromAmbient_toJet
    right_inv := DFunLike.congr_fun toJet_fromAmbient }
private def swapBlocks : Fin 4 ≃ Fin 4 :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin 2) (Fin 2)).trans finSumFinEquiv)
private def swapVariables : Ambient ≃+* Ambient :=
  (MvPolynomial.renameEquiv FX swapBlocks).toRingEquiv
private theorem seed_eval_eq :
    mapGenericSeed = mapGenericJets.comp swapVariables.toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [swapVariables, mapGenericSeed, mapGenericJets]
  · intro i
    change mapGenericSeed (MvPolynomial.X i) =
      mapGenericJets (MvPolynomial.rename swapBlocks (MvPolynomial.X i))
    rw [MvPolynomial.rename_X]
    simp only [mapGenericSeed, mapGenericJets, MvPolynomial.eval₂Hom_X']
    fin_cases i <;> rfl
local instance : Algebra (MvPolynomial (Fin 2) Seeds) FibreRing :=
  MvPolynomial.algebraMvPolynomial
private theorem jets_height (p : Ideal FibreRing) :
    (p.comap mapGenericJets).height = p.height := by
  have hloc : (p.under (MvPolynomial (Fin 2) Seeds)).height = p.height :=
    IsLocalization.height_under ((nonZeroDivisors Seeds).map (MvPolynomial.C (σ := Fin 2))) p
  rw [mapGenericJets_eq, specializeJets, ← Ideal.comap_comap]
  change ((p.under (MvPolynomial (Fin 2) Seeds)).comap seedPresentation).height = p.height
  exact (seedPresentation.height_comap _).trans hloc
private def lineSlice (mixed : Bool) : Slice := if mixed then .mixed else .ordinate
private theorem line_eval (mixed : Bool) :
    ((lineElim mixed).toRingHom.comp sectionBase).comp toJet =
      (K1_14_3_2_4.sectionEval (lineSlice mixed)).toRingHom.comp K1_14_3.sectionMap := by
  cases mixed <;>
    apply Polynomial.ringHom_ext'
  all_goals
    first
    | apply Polynomial.ringHom_ext'
      · apply MvPolynomial.ringHom_ext
        · intro c
          simp [lineSlice, sectionBase, lineElim, toJet, toRoot, rootIncl, rootSeeds,
            K1_14_3.sectionMap, K1_14_3_2_4.sectionEval, MvPolynomial.algebraMap_eq]
        · intro i
          fin_cases i <;>
            simp [lineSlice, sectionBase, lineElim, toJet, toRoot, rootIncl, rootSeeds,
              sliceParameter, K1_14_3.sectionMap, K1_14_3_2_4.sectionEval,
              K1_14_3_2_4.seedValues, K1_14_3_2_4.parameter]
      · simp [lineSlice, sectionBase, lineElim, toJet, toRoot, rootIncl, sliceParameter,
          K1_14_3.sectionMap, K1_14_3_2_4.sectionEval, K1_14_3_2_4.ordinateValue,
          K1_14_3_2_4.parameter]
    | simp [lineSlice, sectionBase, lineElim, toJet, K1_14_3.sectionMap,
        K1_14_3_2_4.sectionEval, K1_14_3_2_4.derivativeValue]
private theorem line_height (mixed : Bool) (p : Ideal (Plane SectionField)) [p.IsPrime] :
    (p.comap ((lineElim mixed).toRingHom.comp sectionBase)).height ≤ p.height := by
  rw [← jetEquiv.height_comap (p.comap ((lineElim mixed).toRingHom.comp sectionBase))]
  change (((p.comap ((lineElim mixed).toRingHom.comp sectionBase)).comap toJet)).height ≤ _
  rw [Ideal.comap_comap, line_eval]
  exact K1_14_3_2_4_1.section_height_ge (lineSlice mixed) p
theorem slice_height_ge (s : Slice) (p : Ideal (Plane (SliceField s))) [p.IsPrime] :
    (p.comap (sliceEval s)).height ≤ p.height := by
  cases s
  · change (p.comap mapGenericSeed).height ≤ p.height
    rw [seed_eval_eq, ← Ideal.comap_comap]
    change ((p.comap mapGenericJets).comap swapVariables).height ≤ p.height
    exact ((swapVariables.height_comap _).trans (jets_height p)).le
  · exact line_height false p
  · exact line_height true p
  · exact (jets_height p).le
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
theorem proof : K1_14_2_2_2_5.c1 := by
  intro P Q hp s
  let F := SliceField s
  let A := Plane F
  let J : Ideal A := Ideal.span {sliceRow s P, sliceRow s Q}
  have hd : ringKrullDim A = 2 := by
    simp [A, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field]
  have : FiniteRingKrullDim A :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr (by rw [hd]; exact ⟨by decide, by decide⟩)
  have hz : Ring.KrullDimLE 0 (A ⧸ J) := by
    apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
    intro p hpmin
    have : p.IsPrime := hpmin.isPrime
    let q := p.comap (sliceEval s)
    let I := q.comap jetEquiv.toRingHom
    have : q.IsPrime := Ideal.comap_isPrime _ _
    have : I.IsPrime := Ideal.comap_isPrime _ _
    have hP : P ∈ I := by
      change sliceRow s P ∈ p
      exact hpmin.le (Ideal.subset_span (by simp))
    have hQ : Q ∈ I := by
      change sliceRow s Q ∈ p
      exact hpmin.le (Ideal.subset_span (by simp))
    have hI := properPair_height hp I hP hQ
    have hq : 2 ≤ q.height := (jetEquiv.height_comap q) ▸ hI
    have hlo : 2 ≤ p.height := hq.trans (slice_height_ge s p)
    have hhi := Ideal.height_le_ringKrullDim_of_isPrime (I := p)
    rw [hd] at hhi
    apply Ideal.isMaximal_of_height_eq_ringKrullDim
    rw [hd]
    exact congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞))
      (le_antisymm (WithBot.coe_le_coe.mp hhi) hlo)
  have : IsArtinianRing F := DivisionRing.instIsArtinianRing
  have : Algebra.FiniteType F (A ⧸ J) := Algebra.FiniteType.quotient F J
  exact (Module.finite_iff_krullDimLE_zero F (A ⧸ J)).mpr hz
end
end K1_14_2_2_2_5_1
end
