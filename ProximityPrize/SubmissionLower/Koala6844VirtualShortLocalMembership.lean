import ProximityPrize.SubmissionLower.Koala6844VirtualShortLocalExpansion
import ProximityPrize.SubmissionLower.Koala6844VirtualShortLocalSupport
import ProximityPrize.SubmissionLower.Koala6844VirtualShortPoleRank


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetLocal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3100000

variable {K : Type*} [Field K]

private abbrev P5 := Poly (K := K)

def flatContact : P5 (K := K) →ₐ[K] Target (K := K) :=
  (contact (K := K)).comp (flatEquiv (K := K)).toAlgHom

@[simp]
theorem flatContact_T : flatContact (K := K) (MvPolynomial.X 0) = Polynomial.X := by
  simp [flatContact, flatEquiv_X, contact_X]

def localRemainder (m : ℕ) : P5 (K := K) →ₗ[K] Target (K := K) :=
  ((Polynomial.modByMonicHom (Polynomial.X^m : Target (K := K))).restrictScalars K).comp
    (flatContact (K := K)).toLinearMap

private theorem contactMap_truncateOuter (m : ℕ) (P : Jet (Base (K := K))) :
    SecondJetRank.contactMap (K := K) m (truncateOuter (K := K) m P) =
      SecondJetRank.contactMap (K := K) m P := by
  have hP : (Polynomial.X : Jet (Base (K := K)))^m ∣ P - truncateOuter (K := K) m P := by
    change Polynomial.X ^ m ∣ P - P %ₘ Polynomial.X^m
    rw [Polynomial.modByMonic_eq_sub_mul_div]
    exact ⟨P /ₘ Polynomial.X^m, by ring⟩
  have hC := map_dvd (contact (K := K)).toRingHom hP
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, contact_X, map_sub] at hC
  have hz := (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mpr hC
  have hzero : SecondJetRank.contactMap (K := K) m (P-truncateOuter (K := K) m P) = 0 := by
    change contact (K := K) (P-truncateOuter (K := K) m P) %ₘ Polynomial.X^m = 0
    simpa only [map_sub] using hz
  exact (sub_eq_zero.mp (by simpa only [map_sub] using hzero)).symm

private abbrev pureCap : LocalCaps := ⟨0,0,0,0,0,0⟩

private theorem pure_mul {P Q : P5 (K := K)} (hP : FitsLocal pureCap P) (hQ : FitsLocal pureCap Q) :
    FitsLocal pureCap (P*Q) := by
  simpa [pureCap, LocalCaps.plus] using hP.mul hQ

private theorem pure_pow {P : P5 (K := K)} (hP : FitsLocal pureCap P) (q : ℕ) :
    FitsLocal pureCap (P^q) := by
  simpa [pureCap, LocalCaps.times] using hP.pow q

private theorem pure_neg {P : P5 (K := K)} (hP : FitsLocal pureCap P) :
    FitsLocal pureCap (-P) := by
  intro e he
  exact hP e (by simpa using he)

private theorem pure_natCast (c : ℕ) : FitsLocal pureCap (c : P5 (K := K)) := by
  rw [show (c : P5 (K := K)) = MvPolynomial.C (c : K) by simp]
  intro e he
  have heq := Finset.mem_singleton.mp (MvPolynomial.support_C_subset he)
  subst e
  simp

private theorem T_pow_noSeed (t h a r d : ℕ) (c : K) :
    (MvPolynomial.X 0)^d * noSeedMonomial t h a r c =
      noSeedMonomial (t+d) h a r c := by
  rw [noSeedMonomial, noSeedMonomial, MvPolynomial.X, MvPolynomial.monomial_pow,
    one_pow, MvPolynomial.monomial_mul_monomial, one_mul]
  apply congrArg (fun e : Fin 5 →₀ ℕ => MvPolynomial.monomial e c)
  ext i
  fin_cases i <;> simp [Finsupp.single_apply, Finsupp.add_apply, add_comm]

def localPoleSpace (m L B s U q : ℕ) (caps : ℕ → ℕ)
    (A C : P5 (K := K)) (j : Fin (q+1)) : Submodule K (Target (K := K)) :=
  (if j.val=0 then (SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps).range else
    (seedlessContactMap (K := K) (m-j.val) B s (U-j.val)).range).map
      (scaleContact m (flatContact (A^(q-j.val)*((MvPolynomial.X 0)*C)^j.val)))

theorem localized_monomial_mem_pole_spaces (m L B s U q : ℕ) (caps : ℕ → ℕ)
    (hcap : ∀ h ≤ s, U ≤ caps h)
    (t h a r d j : ℕ) (c : K)
    (lead base A num shift C : P5 (K := K))
    (hAeq : lead*MvPolynomial.X 4 = A-base)
    (hBeq : lead*num = MvPolynomial.X 0*C+A*shift)
    (hC : FitsLocal ⟨1,0,0,1,1,0⟩ C) (hA : FitsLocal ⟨0,0,0,0,1,1⟩ A)
    (hLead : FitsLocal pureCap lead) (hBase : FitsLocal pureCap base)
    (hShift : FitsLocal pureCap shift)
    (hat : a ≤ t) (hB : 2*h+r ≤ B) (hs : h ≤ s)
    (hU : h+a+r+j ≤ U) (hL : h+a+r+d ≤ L) (hj : j ≤ q) :
    localRemainder m (lead^(L+q)*A^(q-j)*(noSeedMonomial t h a r c*MvPolynomial.X 4^d)*num^j) ∈
      Finset.univ.sup (localPoleSpace m L B s U q caps A C) := by
  classical
  have hx := local_column_double_expansion lead base A (MvPolynomial.X 4) num shift
    (MvPolynomial.X 0) C (noSeedMonomial t h a r c) L q d j (by omega) hj hAeq hBeq
  rw [hx]
  simp_rw [map_sum]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro k hk
  have hi' := Finset.mem_range.mp hi
  have hk' := Finset.mem_range.mp hk
  let D := lead^(L-d+q-j)*(j.choose i : P5 (K := K))*(d.choose k : P5 (K := K))*
    shift^(j-i)*(-base)^(d-k)
  have hD : FitsLocal pureCap D :=
    pure_mul (pure_mul (pure_mul (pure_mul (pure_pow hLead _) (pure_natCast _))
      (pure_natCast _)) (pure_pow hShift _)) (pure_pow (pure_neg hBase) _)
  change localRemainder m (D*(A^(q-i+k)*(MvPolynomial.X 0)^i*C^i*noSeedMonomial t h a r c)) ∈ _
  by_cases hik : i ≤ k
  · let i₀ : Fin (q+1) := 0
    apply (Finset.le_sup (f := localPoleSpace m L B s U q caps A C) (Finset.mem_univ i₀))
    let E := noSeedMonomial (t+i) h a r c*C^i*A^(k-i)*D
    have hE := ordinary_local_term_mem m L B s U caps hcap t h a r i k d c C A D hC hA hD
      hat hB hs (by omega) hL hik (by omega)
    let e := truncateOuter (K := K) m (flatEquiv (K := K) E)
    have hp : D*(A^(q-i+k)*(MvPolynomial.X 0)^i*C^i*noSeedMonomial t h a r c) = A^q*E := by
      dsimp only [E]
      rw [show q-i+k = q+(k-i) by omega, pow_add, ← T_pow_noSeed]
      ring
    rw [hp]
    unfold localPoleSpace
    simp only [i₀, Fin.val_zero, Nat.sub_zero, pow_zero, mul_one]
    apply Submodule.mem_map.mpr
    refine ⟨SecondJetRank.contactMap (K := K) m e, ⟨⟨e, hE⟩, rfl⟩, ?_⟩
    dsimp only [e]
    rw [contactMap_truncateOuter]
    change scaleContact m (flatContact (A^q))
      (flatContact E %ₘ Polynomial.X^m) = localRemainder m (A^q*E)
    have hzero := scaleContact_eq_of_shorter_remainder m 0
      (flatContact (A^q)) (flatContact E) (by simp)
    rw [Nat.sub_zero] at hzero
    rw [hzero]
    simp [scaleContact, localRemainder]
  · let l := i-k
    have hl : 0 < l := by dsimp [l]; omega
    have hlq : l ≤ q := by dsimp [l]; omega
    let i₀ : Fin (q+1) := ⟨l, Nat.lt_succ_of_le hlq⟩
    apply (Finset.le_sup (f := localPoleSpace m L B s U q caps A C) (Finset.mem_univ i₀))
    let E := noSeedMonomial (t+k) h a r c*C^k*D
    let W := A^(q-l)*((MvPolynomial.X 0)*C)^l
    have hE := pole_local_term_mem m B s U t h a r i k c C D hC hD hat hB hs (by omega)
      (Nat.lt_of_not_ge hik)
    let e := truncateOuter (K := K) (m-l) (flatEquiv (K := K) E)
    have hp : D*(A^(q-i+k)*(MvPolynomial.X 0)^i*C^i*noSeedMonomial t h a r c) = W*E := by
      dsimp only [W,E]
      rw [← T_pow_noSeed, show q-i+k = q-l by (dsimp [l]; omega),
        show i = l+k by (dsimp [l]; omega), pow_add, pow_add, mul_pow]
      ring
    rw [hp]
    unfold localPoleSpace
    dsimp only [i₀]
    rw [ite_eq_right (Nat.ne_of_gt hl)]
    apply Submodule.mem_map.mpr
    refine ⟨SecondJetRank.contactMap (K := K) (m-l) e, ⟨⟨e, hE⟩, rfl⟩, ?_⟩
    dsimp only [e]
    rw [contactMap_truncateOuter]
    have hW : Polynomial.X^l ∣ flatContact W := by
      simp only [W, map_mul, map_pow, flatContact_T, mul_pow]
      exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
    change scaleContact m (flatContact W) (flatContact E %ₘ Polynomial.X^(m-l)) =
      localRemainder m (W*E)
    rw [scaleContact_eq_of_shorter_remainder _ _ _ _ hW]
    simp [scaleContact, localRemainder]

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
