import ProximityPrize.SubmissionLower.Fast069

/- Paper companion to the joint terminal count, using Dadon's PR 627 coefficient types. -/
namespace JointTerminal

set_option backward.isDefEq.respectTransparency false
open K1_14 K1_14_4 Polynomial
open scoped BigOperators

/-- The same divisor consumes ordinate positions and seed degree in each quotient. -/
theorem rank_of_divisible (C : Submodule FX Equation) {g : Equation} (hg : g ≠ 0)
    {a U y s : ℕ} (hy : y ≤ g.natDegree) (hs : s ≤ seedDegree g)
    (hc : ∀ c ∈ C, c ≠ 0 → c.natDegree < a ∧ SeedBound c U ∧ g ∣ c) :
    Module.rank FX C ≤ (↑((a - y) * slots U s) : Cardinal) := by
  classical
  by_cases hu : s ≤ U
  · let mul := LinearMap.mulLeft FX g
    let Q := C.comap mul
    have cover : C ≤ Q.map mul := by
      intro c h
      by_cases hz : c = 0
      · exact hz ▸ (Q.map mul).zero_mem
      obtain ⟨q, rfl⟩ := (hc c h hz).2.2
      exact ⟨q, h, rfl⟩
    have quot : ∀ q ∈ Q, q ≠ 0 →
        q.natDegree < a-y ∧ SeedBound q (U-s) ∧ (1 : Equation) ∣ q := by
      intro q hq hn
      obtain ⟨hdeg, hseed, _⟩ := hc (g*q) hq (mul_ne_zero hg hn)
      rw [natDegree_mul hg hn] at hdeg
      have := (seedDegree_le_iff _ _).mpr hseed
      rw [seedDegree_mul hg hn] at this
      exact ⟨by omega, (seedDegree_le_iff _ _).mp (by omega), one_dvd _⟩
    have bound := rank_multiples_le Q (g := 1) one_ne_zero (spent := 0)
      (Nat.zero_le _) quot
    exact (Submodule.rank_mono cover).trans ((rank_map_le mul Q).trans
      (by simpa [slots, hu] using bound))
  · exact (rank_multiples_le C hg hs hc).trans (by simp [slots, hu])

private theorem coefficient_rank {F A : Type} [Field F] [CommRing A] [Algebra F A]
    (V : Submodule F A[X]) (j : ℕ) :
    let c : V →ₗ[F] A := ((lcoeff A j).restrictScalars F).comp V.subtype
    Module.rank F V = Module.rank F c.range + Module.rank F c.ker := by
  dsimp only
  exact (LinearMap.rank_range_add_rank_ker _).symm

/-- Finite filtration by degree in V. Only the leading coefficient of each row
is assumed divisible. The equation and both degree charges apply to that coefficient. -/
theorem cutoff_capacity (V : Submodule FX Jet) {f : Equation} (hf : f ≠ 0)
    (U n ordinate seed : ℕ) (width power : ℕ → ℕ)
    (hy : ordinate ≤ f.natDegree) (hs : seed ≤ seedDegree f)
    (hV : ∀ P ∈ V, P ≠ 0 → P.natDegree < n ∧
      P.leadingCoeff.natDegree < width P.natDegree ∧ SeedBound P.leadingCoeff U ∧
      f ^ power P.natDegree ∣ P.leadingCoeff) :
    Module.rank FX V ≤ ↑(∑ j ∈ Finset.range n,
      (width j - power j * ordinate) * slots U (power j * seed)) := by
  classical
  induction n generalizing V with
  | zero =>
    have hz : V = ⊥ := by
      apply bot_unique
      intro P h
      by_contra hn
      exact Nat.not_lt_zero _ (hV P h hn).1
    rw [hz]
    simp
  | succ n ih =>
    let coeff : V →ₗ[FX] Equation := ((lcoeff Equation n).restrictScalars FX).comp V.subtype
    have hx : Module.rank FX (LinearMap.range coeff) ≤
        ↑((width n - power n * ordinate) * slots U (power n * seed)) := by
      apply rank_of_divisible _ (g := f ^ power n) (pow_ne_zero _ hf)
      · simpa [natDegree_pow, Nat.mul_comm] using Nat.mul_le_mul_left (power n) hy
      · rw [seedDegree_pow hf]
        exact Nat.mul_le_mul_left (power n) hs
      · rintro _ ⟨P, rfl⟩ hne
        change (P.val.coeff n) ≠ 0 at hne
        have hp : P.val ≠ 0 := fun hz => hne (by rw [hz, coeff_zero])
        obtain ⟨hlim, hwidth, hseed, hdiv⟩ := hV P.val P.property hp
        have hn : P.val.natDegree = n := by have := le_natDegree_of_ne_zero hne; omega
        change (P.val.coeff n).natDegree < _ ∧ SeedBound (P.val.coeff n) _ ∧ _ ∣ P.val.coeff n
        rw [← hn, coeff_natDegree]
        exact ⟨hwidth,hseed,hdiv⟩
    let K := coeff.ker.map V.subtype
    have hk : Module.rank FX coeff.ker = Module.rank FX K :=
      (rank_map_eq V.injective_subtype coeff.ker).symm
    have hind := ih K (by
      rintro P ⟨c, hc, rfl⟩ hne
      obtain ⟨hlim, hrest⟩ := hV c.val c.property hne
      have hz : c.val.coeff n = 0 := hc
      refine ⟨lt_of_le_of_ne (Nat.le_of_lt_succ hlim) ?_, hrest⟩
      intro he
      change c.val.natDegree = n at he
      rw [← he, coeff_natDegree] at hz
      exact (leadingCoeff_ne_zero.mpr hne) hz)
    have split : Module.rank FX V = Module.rank FX coeff.range + Module.rank FX coeff.ker :=
      coefficient_rank (F := FX) (A := Equation) V n
    rw [split, hk, Finset.sum_range_succ,
      Nat.cast_add, add_comm]
    exact add_le_add hind hx

/-- Apply the joint quotient count directly to the terminal bank. The width is
the number of ordinate positions at each (cutoff,V-degree) pair. The mass
lower bound is the source dimension after physical and pole constraints. -/
theorem seed_bound_of_bank (V : ℕ → Submodule FX Jet) {f : Equation} (hf : f ≠ 0)
    (top n U e v debit raw : ℕ) (width power : ℕ → ℕ → ℕ)
    (he : e ≤ f.natDegree)
    (hsource : raw ≤ debit + ∑ W ∈ Finset.range top, Module.finrank FX (V W))
    (hrows : ∀ W < top, ∀ P ∈ V W, P ≠ 0 → P.natDegree < n ∧
      P.leadingCoeff.natDegree < width W P.natDegree ∧ SeedBound P.leadingCoeff U ∧
      f ^ power W P.natDegree ∣ P.leadingCoeff)
    (hstrict : debit + (∑ W ∈ Finset.range top, ∑ j ∈ Finset.range n,
      (width W j - power W j * e) * slots U (power W j * (v+1))) < raw) :
    SeedBound f v := by
  apply (seedDegree_le_iff _ _).mp
  by_contra! bad
  have total := Finset.sum_le_sum (s := Finset.range top) fun W hW =>
    Module.finrank_le_of_rank_le (cutoff_capacity (V W) hf U n e (v+1) (width W)
      (power W) he bad (hrows W (Finset.mem_range.mp hW)))
  omega

end JointTerminal
