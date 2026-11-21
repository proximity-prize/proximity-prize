import ProximityPrize.SubmissionLower.PoleDebitDefs
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
set_option Elab.async false

/- 69.21 specialization of the high-overhead proof in PR 627. -/
section High_K1_14Defs
set_option autoImplicit true
namespace H21

noncomputable section

open K21 Polynomial
open scoped BigOperators

export _root_.K1_14 (L)
export _root_.K1_14 (FX)
export _root_.K1_14 (Seeds)
export _root_.K1_14 (Equation)

export _root_.K1_14 (liftPoly)
export _root_.K1_14 (atX)

export _root_.K1_14 (seedEmbedding)

export _root_.K1_14 (graphEval)

export _root_.K1_14 (atMark)

/-- The second block and all its residue data are coefficient conjugates
of the first, with the same polynomial ordinate on both blocks. -/
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

export _root_.K1_14 (Jet)

export _root_.K1_14 (Shape)

structure Band where
  endpoint : ℕ
  yBound : ℕ
  seedBound : ℕ
  multiplicity : ℕ
  jetBound : ℕ
  vBound : ℕ
  subbankSeeds : ℕ

/-- The smaller seed caps belong to the last full bank in each schedule. -/
def band (w : ℤ) : Band :=
  if w ≤ 3554 then ⟨3554, 14, 209, 3025, 4200, 890, 84000⟩
  else if w ≤ 8249 then ⟨8249, 5, 108, 358, 500, 105, 6798⟩
  else if w ≤ 23999 then ⟨23999, 3, 41, 358, 500, 105, 4860⟩
  else ⟨33068, 2, 28, 358, 500, 105, 3913⟩

export _root_.K1_14 (SeedBound)

def ReducedEquation (w : ℤ) (f : Equation) : Prop :=
  0 < f.natDegree ∧ f.natDegree ≤ (band w).yBound ∧ f.IsPrimitive ∧
    (f.map (algebraMap Seeds (FractionRing Seeds))).Separable

export _root_.K1_14 (triangle)

export _root_.K1_14 (slots)

export _root_.K1_14 (Banks)

export _root_.K1_14 (shapeSum)

export _root_.K1_14 (sourceDebit)

def terminalShape (w : ℤ) : Shape :=
  let b := band w
  ⟨b.multiplicity, b.jetBound, b.vBound, b.subbankSeeds⟩

def rawWidth (w : ℤ) (q j : ℕ) : ℕ :=
  (band w).multiplicity * 180071 + j - q * (131071 - w.toNat)

def rawVolume (w : ℤ) : ℕ :=
  triangle (band w).subbankSeeds * shapeSum (terminalShape w) (rawWidth w)

/-- The physical and full primary-pole debits in the M9 dimension floor. -/
def subbankDebit (w : ℤ) : ℕ := BankDebit.debit w.toNat (terminalShape w)

def forcedPower (w : ℤ) (W j : ℕ) : ℕ :=
  1 + ((band w).multiplicity * 180071 - 1 - W) / (2 * w.toNat) - j

/-- Simultaneous divisibility on the retained surfaces. It applies to every
nonzero row of the *same* smaller terminal bank. -/
def TerminalDivisibility (w : ℤ) (rows : Banks) (f : Equation) : Prop :=
  ∀ W < (band w).multiplicity * 180071, ∀ P ∈ rows (terminalShape w) W, P ≠ 0 →
    f ^ forcedPower w W P.natDegree ∣ P.leadingCoeff

/-- Only the filtered dimensions and their highest V coefficients enter the
seed-degree contradiction. The coefficient field contains the generic X. -/
def TerminalMass (w : ℤ) (f : Equation) : Prop :=
  let b := band w
  ∃ V : ℕ → Submodule FX Jet,
    rawVolume w ≤ subbankDebit w +
      ∑ W ∈ Finset.range (b.multiplicity * 180071), Module.finrank FX (V W) ∧
    ∀ W < b.multiplicity * 180071, ∀ P ∈ V W, P ≠ 0 →
      let j := P.natDegree
      let i := P.leadingCoeff.natDegree
      j ≤ b.vBound ∧ i+j ≤ b.jetBound ∧ (i+j)*(131071-w.toNat) ≤ W+j ∧
        SeedBound P.leadingCoeff b.subbankSeeds ∧ f ^ forcedPower w W j ∣ P.leadingCoeff

/-- Left sum of the strict test (T), with index r = l-1 in PAIR-CLOSURE. -/
def seedGain (w : ℤ) : ℕ :=
  let b := band w
  let U := b.subbankSeeds
  let v := b.seedBound + 1
  shapeSum (terminalShape w) fun q j => ∑ r ∈ Finset.range (U / v + 1),
    (slots U (r*v) - slots U ((r+1)*v)) * (rawWidth w q j - 2*w.toNat*(j+r))

/-- Exact integer ceiling of the simple-root Taylor/word charge, using
the indicated upper degree throughout the same height band. -/
def simplePrice (w : ℤ) : ℕ :=
  let b := band w
  let d := 131071 + b.endpoint
  let gap := 180071 - d
  let T := 2*d-1
  let a := 1+T*(b.yBound-1)
  let B := T*b.seedBound
  let D := b.yBound*B^2 + 2*b.seedBound*a*B
  (82073*(82073/gap+1)*D + (gap-1)) / gap + b.yBound

def singularDegree (w : ℤ) : ℕ :=
  (2*(band w).yBound-1)*(band w).seedBound

/-- Cheap/layered pairs in reserve order, then the final full bank and its
smaller seed-degree subbank. -/
def scheduled (w : ℤ) : List Shape :=
  let sub := terminalShape w
  if w ≤ 3554 then
    [⟨57,79,17,1160⟩, ⟨191,265,55,6963⟩, ⟨96,133,29,1557⟩, ⟨316,439,92,10562⟩, ⟨216,299,66,3130⟩, ⟨641,890,185,25837⟩, ⟨3025,4200,890,84000⟩, sub]
  else
    [⟨45,63,14,812⟩, ⟨84,118,24,2907⟩, ⟨57,80,18,1041⟩, ⟨114,160,33,3775⟩,
     ⟨81,114,26,1383⟩, ⟨144,203,42,5064⟩, ⟨123,173,40,2173⟩, ⟨231,325,67,8061⟩,
     ⟨358,500,105,66251⟩, sub]

theorem scheduled_shape {w : ℤ} {s : Shape} (hs : s ∈ scheduled w) :
    4 ≤ s.B ∧ s.B ≤ s.U := by
  unfold scheduled at hs
  split at hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | decide | simp [terminalShape, band, *]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | decide | simp [terminalShape, band, *]
    all_goals split <;> (first | decide | split <;> decide)

export _root_.K1_14 (jetAt)

export _root_.K1_14 (translateSeed)

export _root_.K1_14 (seedHasse)

/-- A single collection of evaluated filtered spaces over L(X). The rank
floor is telescoped over all cutoffs, not a rank claim at one fibre. -/
structure JetSource {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (rows : Banks) : Prop where
  nested : ∀ s ∈ scheduled M.overhead, ∀ s' ∈ scheduled M.overhead,
    s.m = s'.m → s.B = s'.B → s.J = s'.J → s.U ≤ s'.U →
    ∀ W W', W ≤ W' → rows s W ≤ rows s' W'
  necessary : ∀ s ∈ scheduled M.overhead, ∀ W, W < s.m*180071 → ∀ P ∈ rows s W,
    ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0
  shape : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, ∀ j i,
    ((P.coeff j).coeff i) ≠ 0 →
      i+j ≤ s.B ∧ j ≤ s.J ∧ ((P.coeff j).coeff i).totalDegree ≤ s.U
  leading : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, P ≠ 0 →
    (P.leadingCoeff.natDegree + P.natDegree)*(131071-M.overhead.toNat) ≤ W + P.natDegree
  shift : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, ∀ i r,
    seedHasse i r P ∈ rows s (W + 2*M.overhead.toNat*r)
  floor_bound : ∀ s ∈ scheduled M.overhead, ∀ W, W < s.m*180071 →
    (∀ q ≤ s.B, ∀ j ≤ min q s.J, q*(131071-M.overhead.toNat) ≤ W+1+j) →
    triangle s.U * shapeSum s (fun q j => W+1+j - q*(131071-M.overhead.toNat)) ≤
      BankDebit.debit M.overhead.toNat s + ∑ t ∈ Finset.range (W+1), Module.finrank FX (rows s t)

/-- The complement of the first-loss book satisfies a single reduced equation
in the original seed chart. The empty retained case needs no equation. -/
def PrefixCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) (rows : Banks) : Prop :=
  Γ.card ≤ highPrefix M.overhead ∨
    ∃ kept ⊆ Γ, (Γ \ kept).card ≤ highPrefix M.overhead ∧
      ∃ f : Equation, ReducedEquation M.overhead f ∧ TerminalDivisibility M.overhead rows f ∧
        ∀ γ ∈ kept, atMark f (M.label γ) (F.scalar γ) = 0

end
end H21
end High_K1_14Defs

section High_K1_14Separant
set_option autoImplicit true
namespace H21

noncomputable section

open K21 Polynomial
open scoped BigOperators

open private det_degree from ProximityPrize.SubmissionLower.Fast023

open private resultant_degree from ProximityPrize.SubmissionLower.Fast023

open private derivative_seedBound from ProximityPrize.SubmissionLower.Fast023

/-- A single nonzero polynomial in the formal seeds vanishes whenever the
specialized actual ordinate is a common root of f and its Y derivative. -/
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

/-- Count original labels by injecting the translated labels into the
coefficient field and applying the low-degree Frobenius-graph root bound. -/
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


end
end H21
end High_K1_14Separant

section High_K1_14Chart
set_option autoImplicit true
namespace H21

noncomputable section

open K21 Polynomial

export _root_.K1_14 (trim)

theorem twist_lift (P : K[X]) :
    liftPoly (P.map twist) = (liftPoly P).map (frobenius L p) := by
  simp only [liftPoly, Polynomial.map_map, twist, RingHom.frobenius_comm]

/-- The two projectivities use the original translated label and its
Frobenius, and impose divisibility on the same scalar polynomial. -/
theorem adjacent_chart {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) :
    ∃ H, AdjacentChart M F H := by
  let φ := algebraMap K L
  let σ := frobenius L p
  have hsmall : M.overhead.toNat ≤ (liftPoly M.E).natDegree := by
    rw [liftPoly, natDegree_map]
    unfold AnchorModel.overhead
    omega
  obtain ⟨H, hm, hdeg, hd⟩ := trim _ _ hsmall
  have hd' : H.map σ ∣ liftPoly (M.E.map twist) := by
    rw [twist_lift]
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
      rw [← twist_lift, B.scalar_fixed]
    refine ⟨ha, ha.map (Polynomial.mapRingHom σ), hres, ?_⟩
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hfix,
      σ, frobenius_def] using (Polynomial.map_dvd σ hres)

end
end H21
end High_K1_14Chart

section High_K1_14Terminal
set_option autoImplicit true
namespace H21

noncomputable section

open K21 Polynomial

private theorem terminal_mem (w : ℤ) : terminalShape w ∈ scheduled w := by
  unfold scheduled
  split <;> simp

private theorem terminal_width (w : ℤ) (hw : 2385 ≤ w) {q : ℕ}
    (hq : q ≤ (terminalShape w).B) :
    q * (131071 - w.toNat) ≤ (terminalShape w).m * 180071 := by
  calc
    _ ≤ (terminalShape w).B * 128687 := Nat.mul_le_mul hq (by omega)
    _ ≤ _ := by unfold terminalShape band; split_ifs <;> decide

/-- Extract the exact rectangular subbank floor and leading-coefficient
bounds once, for either surface schedule. -/
theorem terminalMass_of_source {u del} {M : AnchorModel u del} {Γ}
    {F : AnchoredFamily M Γ} {rows : Banks} (hr : JetSource M F rows)
    (hlo : 2385 ≤ M.overhead) {f : Equation}
    (hd : TerminalDivisibility M.overhead rows f) : TerminalMass M.overhead f := by
  let w := M.overhead
  let s := terminalShape w
  have hs := terminal_mem w
  have htop : 0 < s.m * 180071 := by
    unfold s terminalShape band
    split_ifs <;> decide
  have hent : s.m * 180071 - 1 + 1 = s.m * 180071 := by omega
  refine ⟨rows s, ?_, ?_⟩
  · have h := hr.floor_bound s hs (s.m*180071-1) (by omega) (by
      intro q hq j _
      have hq' : q * (131071 - M.overhead.toNat) ≤ s.m * 180071 := terminal_width w hlo hq
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

end
end H21
end High_K1_14Terminal

section High_K1_14Split
set_option autoImplicit true
namespace H21

noncomputable section

open K21 Polynomial

/-- The common true-jet source for the two adjacent primary blocks. -/
def c1 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    2385 ≤ M.overhead → M.overhead ≤ 33068 →
    ∀ H, AdjacentChart M F H → ∃ rows : Banks, JetSource M F rows

/-- Bridge prefix including its algebraic first-loss curve count. -/
def c2 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    2385 ≤ M.overhead → M.overhead ≤ 3554 →
    ∀ H, AdjacentChart M F H → ∀ rows, JetSource M F rows → PrefixCover M F rows

/-- Paired prefix with the direct Frobenius-graph loss price. -/
def c3 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    3555 ≤ M.overhead → M.overhead ≤ 33068 →
    ∀ H, AdjacentChart M F H → ∀ rows, JetSource M F rows → PrefixCover M F rows

/-- The dimension loss if the primitive projected equation exceeds the
tested total seed degree. -/
def c4 : Prop :=
  ∀ (w : ℤ), 2385 ≤ w → w ≤ 33068 → ∀ f : Equation,
    ReducedEquation w f → TerminalMass w f → ¬ SeedBound f (band w).seedBound →
      seedGain w ≤ subbankDebit w

/-- Strict test (T) for each native height, with all four subbank shapes. -/
def c5 : Prop :=
  ∀ (w : ℤ), 2385 ≤ w → w ≤ 33068 → subbankDebit w < seedGain w

/-- Count the actual simple polynomial roots via the Taylor map and
fixed-word incidence at this band's endpoint degree. -/
def c6 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    2385 ≤ M.overhead → M.overhead ≤ 33068 → ∀ f : Equation,
    ReducedEquation M.overhead f → SeedBound f (band M.overhead).seedBound →
    ∀ T ⊆ Γ, (∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0 ∧
        atMark f.derivative (M.label γ) (F.scalar γ) ≠ 0) →
      T.card ≤ simplePrice M.overhead


end
end H21
end High_K1_14Split
