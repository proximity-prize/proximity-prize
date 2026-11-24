import ProximityPrize.SubmissionLower.Shared50OrderDivision
import ProximityPrize.SubmissionLower.Shared50Multiplicity

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 750000
namespace KoalaFarBridge
noncomputable section
open K1_13 (Row Geom shape InBox indexDegree)
open K1_13_6 (GeoJets toGeneric genericCoeffs separant cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo)
open MvPolynomial
open scoped Polynomial BigOperators

private theorem deriv_ideal_pow {k : Type*} [Field k] {n : ℕ}
    (P : Ideal (MvPolynomial (Fin n) k)) (i : Fin n) (e : ℕ)
    {F : MvPolynomial (Fin n) k} (h : F ∈ P^(e+1)) : pderiv i F ∈ P^e := by
  induction e generalizing F with
  | zero => simp
  | succ e ih =>
    rw [pow_succ] at h
    refine Submodule.mul_induction_on h ?_ ?_
    · intro x hx y hy
      rw [pderiv_mul]
      have h₁ : pderiv i x * y ∈ P^(e+1) := by
        rw [pow_succ]
        exact Ideal.mul_mem_mul (ih hx) hy
      have h₂ : x * pderiv i y ∈ P^(e+1) := (P^(e+1)).mul_mem_right _ hx
      simpa only [mul_comm, add_comm] using (P^(e+1)).add_mem h₁ h₂
    · intro x y hx hy
      rw [map_add]
      exact (P^(e+1)).add_mem hx hy

/-- A coordinate derivation loses at most one local order, including at singular primes. -/
theorem deriv_order {k : Type*} [Field k] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) k))
    [P.IsPrime] {F : MvPolynomial (Fin n) k} (i : Fin n) {e : ℕ}
    (h : VanishesTo P F e) : VanishesTo P (pderiv i F) (e-1) := by
  cases e with
  | zero => simp [VanishesTo]
  | succ e =>
    let L := Localization.AtPrime P
    change algebraMap _ L F ∈ IsLocalRing.maximalIdeal L ^ (e+1) at h
    change algebraMap _ L (pderiv i F) ∈ IsLocalRing.maximalIdeal L ^ e
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P L, ← Ideal.map_pow,
      IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl L] at h ⊢
    obtain ⟨u, hu, hF⟩ := h
    refine ⟨u*u, P.primeCompl.mul_mem hu hu, ?_⟩
    have hD := deriv_ideal_pow P i e hF
    have hE : u*F ∈ P^e := Ideal.pow_le_pow_right (by omega) hF
    have hM := (P^e).sub_mem ((P^e).mul_mem_left u hD) ((P^e).mul_mem_left (pderiv i u) hE)
    convert hM using 1
    rw [pderiv_mul]
    ring

/-- The actual top separant has the smaller support paid by the numerical table. -/
theorem separant_box (f : Row 4) : InBox (shape (separant f))
    ⟨(shape f).b-1,(shape f).j-3,(shape f).t-1⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · change ((pderiv 3) f).totalDegree ≤ f.totalDegree - (1 : Fin 4 → ℕ) 3
    simpa only [weightedTotalDegree_one] using
      weightedTotalDegree_pderiv_le_sub (1 : Fin 4 → ℕ) (3 : Fin 4) f
  · change indexDegree ((pderiv 3) f) ≤ indexDegree f - (3 : Fin 4).val
    simpa only [← K1_13_1.indexDegree_eq] using
      weightedTotalDegree_pderiv_le_sub Fin.val (3 : Fin 4) f
  · exact degreeOf_pderiv_le_sub_one 3 f

theorem separant_proper {f : Row 4} (hf : f ≠ 0) (ht : 0 < f.degreeOf 3)
    (hchar : f.degreeOf 3 < K1.p) : ¬ f ∣ separant f := by
  have : CharP Geom K1.p := charP_of_injective_ringHom K1_13.embed.injective K1.p
  have : CharP (Polynomial Geom) K1.p := charP_of_injective_ringHom Polynomial.C_injective K1.p
  have hcast : (f.degreeOf 3 : (Polynomial Geom)) ≠ 0 := fun hz => (not_le_of_gt hchar)
    (Nat.le_of_dvd ht ((CharP.cast_eq_zero_iff (Polynomial Geom) K1.p _).mp hz))
  have hn : separant f ≠ 0 := pderiv_ne_zero_of_natCast_ne_zero 3 f hcast
  rintro ⟨g,hg⟩
  have hgz : g ≠ 0 := fun hz => hn (by simp [hg,hz])
  have hd := degreeOf_pderiv_le_sub_one (3 : Fin 4) f
  change (separant f).degreeOf 3 ≤ _ at hd
  rw [hg,degreeOf_mul_eq hf hgz] at hd
  omega

private theorem order_pow_mul (P : Ideal GeoJets) [P.IsPrime] {x y : GeoJets}
    {u v : ℕ} (hx : VanishesTo P x u) (hy : VanishesTo P y v) (m d : ℕ) :
    VanishesTo P (x^m * y^d) (m*u + d*v) := by
  let L := Localization.AtPrime P
  let I := IsLocalRing.maximalIdeal L
  change algebraMap _ L x ∈ I^u at hx
  change algebraMap _ L y ∈ I^v at hy
  change algebraMap _ L _ ∈ I^(m*u+d*v)
  rw [map_mul,map_pow,map_pow,pow_add,Nat.mul_comm m u,Nat.mul_comm d v,pow_mul,pow_mul]
  exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hx _) (Ideal.pow_mem_pow hy _)

private theorem congruent_cut {f c h S : Row 4} (m d : ℕ) :
    intersectionIdeal f ((c+f*h)^m*S^d) = intersectionIdeal f (c^m*S^d) := by
  have hd : f ∣ (c+f*h)^m*S^d - c^m*S^d := by
    rw [← sub_mul]
    apply dvd_mul_of_dvd_left _
    apply dvd_trans _ (sub_dvd_pow_sub_pow _ _ _)
    simp
  obtain ⟨w,hw⟩ := hd
  have he : (c+f*h)^m*S^d = c^m*S^d + f*w := by linear_combination hw
  rw [he]
  unfold intersectionIdeal toGeneric
  simp only [map_add,map_mul]
  rw [Ideal.span_pair_comm, mul_comm (MvPolynomial.map genericCoeffs f), Ideal.span_pair_add_mul_right,Ideal.span_pair_comm]


private theorem minimal_pair {f G : Row 4} {P : Ideal GeoJets} [P.IsPrime]
    (hf : Irreducible f) (hproper : ¬f∣G) (hP : P.height=2)
    (hF : toGeneric f∈P) (hG : toGeneric G∈P) :
    (intersectionIdeal f G).IsMinimalPrime P := by
  have hsub : intersectionIdeal f G ≤ P := by
    unfold intersectionIdeal
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl|rfl
    · exact hF
    · exact hG
  obtain ⟨P',hmin,hle⟩ := Ideal.exists_minimalPrimes_le hsub
  have hzero := K1_13_6_3_6.toGeneric_ne_zero hf.ne_zero
  have hrel := K1_13_7_1.proper_generic f G hf hproper
  have hht : P'.height=2 := K1_13_6_1_2.pair_height hzero hrel hmin
  let : P'.IsPrime := hmin.isPrime
  have heq : P'=P := by
    by_contra hne
    have hs := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
    rw [hht,hP] at hs
    exact (by decide : ¬(2:ℕ∞)+1≤2) hs
  exact heq ▸ hmin

private theorem mem_of_order {P : Ideal GeoJets} [P.IsPrime] {Q : GeoJets} {n : ℕ}
    (hn : 0<n) (hQ : VanishesTo P Q n) : Q∈P := by
  let L := Localization.AtPrime P
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L P _).mp
    ((Ideal.pow_le_self (Nat.ne_of_gt hn)) hQ)


/-- Properness of the cut and of each positive power used by the ordinary mixed cycle. -/
theorem cut_proper {f c : Row 4} (hf : Irreducible f) (hc : ¬ f ∣ c)
    (hs : ¬ f ∣ separant f) (m d k : ℕ) : ¬ f ∣ (c^m * (separant f)^d)^k := by
  intro hd
  rcases hf.prime.dvd_or_dvd (hf.prime.dvd_of_dvd_pow hd) with h | h
  · exact hc (hf.prime.dvd_of_dvd_pow h)
  · exact hs (hf.prime.dvd_of_dvd_pow h)

/-- Supply both the minimal prime and the scaled weight to the weighted count wrapper. -/
theorem power_charge {f c h : Row 4} {P : Ideal GeoJets} [P.IsPrime]
    {r a e m d n w : ℕ} (hf : Irreducible f) (hc : ¬ f ∣ c) (hs : ¬ f ∣ separant f)
    (hheight : P.height = 2) (hmem : toGeneric f ∈ P)
    (hl : VanishesTo P (toGeneric f) e) (he : ¬ VanishesTo P (toGeneric f) (e+1))
    (hv : VanishesTo P (toGeneric (f^a*(c+f*h))) r)
    (hn : 0 < n*w) (hpay : n*w ≤ e*(m*(r-e*a)+d*(e-1))) {k : ℕ} (hk : 0 < k) :
    ∃ hp : (intersectionIdeal f ((c^m*(separant f)^d)^k)).IsMinimalPrime P,
      ((k*n*w : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f ((c^m*(separant f)^d)^k)) P hp.isPrime := by
  let b := (m*k)*(r-e*a)+(d*k)*(e-1)
  have hb : k*(e*(m*(r-e*a)+d*(e-1))) = e*b := by dsimp [b]; ring
  have hnk : k*n*w ≤ e*b := by simpa [← hb,Nat.mul_assoc] using Nat.mul_le_mul_left k hpay
  have hbpos : 0 < b := by
    have hh : 0 < k*n*w := by rw [Nat.mul_assoc]; exact Nat.mul_pos hk hn
    exact Nat.pos_of_mul_pos_left (hh.trans_le hnk)
  have hq : VanishesTo P (toGeneric (c+f*h)) (r-e*a) := by
    apply Shared50OrderDivision.vanishesTo_of_pow_mul P he
    simpa only [toGeneric,map_mul,map_pow] using hv
  have hd : VanishesTo P (toGeneric (separant f)) (e-1) := by
    simpa only [toGeneric,separant,pderiv_map] using deriv_order P (3 : Fin 4) hl
  have hg : VanishesTo P (toGeneric ((c+f*h)^(m*k)*(separant f)^(d*k))) b := by
    simpa only [b,toGeneric,map_pow,map_mul] using order_pow_mul P hq hd (m*k) (d*k)
  have hh : ¬ f ∣ c+f*h := by
    rintro ⟨z,hz⟩
    exact hc ⟨z-h,by linear_combination hz⟩
  have hprop := cut_proper hf hh hs (m*k) (d*k) 1
  rw [pow_one] at hprop
  have hmin := minimal_pair hf hprop hheight hmem (mem_of_order hbpos hg)
  have hlen := Shared50Multiplicity.cycleLength_ge_product hheight hl hg
  rw [mul_pow, ← pow_mul, ← pow_mul, ← congruent_cut (h := h)]
  exact ⟨hmin, le_trans (by exact_mod_cast hnk) hlen⟩

#print axioms power_charge
#print axioms separant_proper
#print axioms separant_box
end
end KoalaFarBridge
