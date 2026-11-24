import ProximityPrize.SubmissionLower.Shared50OrderDivision
import ProximityPrize.SubmissionLower.R6960Low6960SharedTallyNew
import ProximityPrize.SubmissionLower.R6960Low6960WeightedTally
import ProximityPrize.SubmissionLower.R6960Low6960FastPrice

-- merged module KoalaSeparantCharge
section Merged_KoalaSeparantCharge
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
theorem cut_proper {f c : Row 4} (hf : Irreducible f) (hc : ¬ f ∣ c)
    (hs : ¬ f ∣ separant f) (m d k : ℕ) : ¬ f ∣ (c^m * (separant f)^d)^k := by
  intro hd
  rcases hf.prime.dvd_or_dvd (hf.prime.dvd_of_dvd_pow hd) with h | h
  · exact hc (hf.prime.dvd_of_dvd_pow h)
  · exact hs (hf.prime.dvd_of_dvd_pow h)
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

end Merged_KoalaSeparantCharge

-- merged module R6960Low6960WeightedCut
section Merged_R6960Low6960WeightedCut

set_option Elab.async false
set_option maxHeartbeats 1500000

namespace Low6960WeightedCut
noncomputable section

open K1_13 (Row Shape shape InBox)
open K1_13_6 (GeoJets toGeneric separant)
open K1_13_6_1_2 (VanishesTo)
open Low6960SharedPrice (Rate Surface surface surfaceScale weights coord)
open KoalaFarBridge (separant_box separant_proper power_charge cut_proper)
open Low6960SharedChooseCut (weighted_pow weight_coord)
open Low6960SharedCount (shape_valid)
open scoped ENat

def order (f : Row 4) (cap : ℕ) (P : Ideal GeoJets) : ℕ :=
  @Nat.findGreatest (fun e => ∃ hp : P.IsPrime, @VanishesTo _ _ P hp (toGeneric f) e)
    (Classical.decPred _) cap

theorem order_spec (f : Row 4) (cap : ℕ) (hcap : 0 < cap)
    (P : Ideal GeoJets) (hp : P.IsPrime) (hf : toGeneric f ∈ P) :
    1 ≤ order f cap P ∧ order f cap P ≤ cap ∧
      @VanishesTo _ _ P hp (toGeneric f) (order f cap P) := by
  letI := hp
  let R := Localization.AtPrime P
  have hf1 : VanishesTo P (toGeneric f) 1 := by
    change algebraMap GeoJets R (toGeneric f) ∈ IsLocalRing.maximalIdeal R ^ 1
    rw [pow_one]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R P _).mpr hf
  let P₀ := fun e => ∃ hp' : P.IsPrime, @VanishesTo _ _ P hp' (toGeneric f) e
  letI := Classical.decPred P₀
  have h₁ : 1 ≤ Nat.findGreatest P₀ cap := Nat.le_findGreatest hcap ⟨hp, hf1⟩
  have htop := Nat.findGreatest_le (P := P₀) cap
  obtain ⟨_, hh⟩ := Nat.findGreatest_of_ne_zero (P := P₀) (n := cap) rfl (by omega : Nat.findGreatest P₀ cap ≠ 0)
  exact ⟨h₁, htop, hh⟩

theorem order_exact (f : Row 4) (cap : ℕ) (P : Ideal GeoJets) [P.IsPrime]
    (hl : order f cap P < cap) : ¬ VanishesTo P (toGeneric f) (order f cap P + 1) := by
  let P₀ := fun e => ∃ hp : P.IsPrime, @VanishesTo _ _ P hp (toGeneric f) e
  letI := Classical.decPred P₀
  have h := Nat.findGreatest_is_greatest (P := P₀) (n := cap) (k := order f cap P + 1)
    (by change order f cap P < _; omega) (by omega)
  exact fun hx => h ⟨inferInstance, hx⟩

open Low6960WeightedRate (boxFee sepBox charge)

private theorem weighted_product {C T : Row 4} (hc : C ≠ 0) (ht : T ≠ 0) (m d : ℕ) (i : Fin 3) :
    coord (shape (C^m * T^d)) i = m * coord (shape C) i + d * coord (shape T) i := by
  simp only [weight_coord, MvPolynomial.weightedTotalDegree_mul _ _ _ (pow_ne_zero _ hc) (pow_ne_zero _ ht),
    weighted_pow _ hc, weighted_pow _ ht]

private theorem chamber_cost {C T : Row 4} (hc : C ≠ 0) (ht : T ≠ 0) {x y : Shape}
    (hC : InBox (shape C) x) (hT : InBox (shape T) y) (m d : ℕ) (w : Shape) :
    let q := (shape (C^m * T^d)).chamber
    w.b * q.b + w.j * q.j + w.t * q.t ≤ m * boxFee w x + d * boxFee w y := by
  let q := (shape (C^m * T^d)).chamber
  change w.b * q.b + w.j * q.j + w.t * q.t ≤ _
  have hB := weighted_product hc ht m d 0
  have hJ := weighted_product hc ht m d 1
  have hT' := weighted_product hc ht m d 2
  change (shape (C^m * T^d)).b = _ at hB
  change (shape (C^m * T^d)).j = _ at hJ
  change (shape (C^m * T^d)).t = _ at hT'
  have htC : (shape C).t ≤ min x.t (x.j / 3) := le_min hC.2.2
    (by apply (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr
        have hh : 3 * (shape C).t ≤ x.j := (K1_13_7_1.shape_chamber C).2.trans hC.2.1
        rwa [Nat.mul_comm])
  have htT : (shape T).t ≤ min y.t (y.j / 3) := le_min hT.2.2
    (by apply (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr
        have hh : 3 * (shape T).t ≤ y.j := (K1_13_7_1.shape_chamber T).2.trans hT.2.1
        rwa [Nat.mul_comm])
  have hb : q.b ≤ m * max x.b x.j + d * max y.b y.j := by
    change max (shape (C^m * T^d)).b (shape (C^m * T^d)).j ≤ _
    rw [hB, hJ]
    exact max_le (Nat.add_le_add (Nat.mul_le_mul_left _ (hC.1.trans (le_max_left _ _)))
      (Nat.mul_le_mul_left _ (hT.1.trans (le_max_left _ _))))
      (Nat.add_le_add (Nat.mul_le_mul_left _ (hC.2.1.trans (le_max_right _ _)))
        (Nat.mul_le_mul_left _ (hT.2.1.trans (le_max_right _ _))))
  have hj : q.j ≤ m * x.j + d * y.j := by
    change (shape (C^m * T^d)).j ≤ _
    rw [hJ]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ hC.2.1) (Nat.mul_le_mul_left _ hT.2.1)
  have htq : q.t ≤ m * min x.t (x.j / 3) + d * min y.t (y.j / 3) := by
    change (shape (C^m * T^d)).t ≤ _
    rw [hT']
    exact Nat.add_le_add (Nat.mul_le_mul_left _ htC) (Nat.mul_le_mul_left _ htT)
  calc
    _ ≤ w.b * _ + w.j * _ + w.t * _ := Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_left _ hj)) (Nat.mul_le_mul_left _ htq)
    _ = _ := by unfold boxFee; ring

/-- Normalize the two powers using the joint debit, so one row pays all surface orders. -/
theorem of_contact {f C H : Row 4} (hf : Low6960Prices.SmallFactor f) (hproper : ¬ f ∣ C)
    (u : Rate) (hfit : u.kind = .tilted → Low6960Prices.tiltedFits (shape f))
    (r a d : ℕ) (x : Shape) (hC : InBox (shape C) x)
    (surfaces : Finset (Ideal GeoJets))
    (hs : ∀ p ∈ surfaces, Low6960WeightedTally.Relevant f u (order f (u.split + 1)) p)
    (hV : ∀ p (hp : p ∈ surfaces), @VanishesTo _ _ p (hs p hp).1 (toGeneric (f^a*(C+f*H))) r)
    (hM : u.split ≤ surfaceScale u.kind * (u.split * u.amount))
    (hpay : ∀ e, 1 ≤ e → e ≤ u.split → 0 < charge r a d e ∧
      (u.split + 1 - e) * (24 * boxFee (weights u.kind (shape f)) x +
        d * boxFee (weights u.kind (shape f)) (sepBox (shape f))) ≤
        (surfaceScale u.kind * (u.split * u.amount)) * charge r a d e) :
    ∃ (n : ℕ) (G : Row 4), 0 < n ∧ (¬ f ∣ G) ∧
      (∀ N > 0, ∀ p ∈ surfaces, ∃ h : (K1_13_6.intersectionIdeal f (G^N)).IsMinimalPrime p,
        ((N * n * (u.split + 1 - order f (u.split + 1) p) : ℕ) : ℕ∞) ≤
          K1_13_6.cycleLength (K1_13_6.intersectionIdeal f (G^N)) p h.isPrime) ∧
      surface u.kind (shape f) (shape G).chamber ≤ surfaceScale u.kind * (u.split * u.amount) * n := by
  let M := surfaceScale u.kind * (u.split * u.amount)
  let w := weights u.kind (shape f)
  let z := 24 * boxFee w x + d * boxFee w (sepBox (shape f))
  let n := max 1 z
  let G := C^(24*M) * (separant f)^(d*M)
  have hSep : ¬ f ∣ separant f := separant_proper hf.1.ne_zero hf.2.1
    (hf.2.2.1.2.2.trans_lt (by decide))
  have hC0 : C ≠ 0 := fun h => hproper (by simp [h])
  have hS0 : separant f ≠ 0 := fun h => hSep (by simp [h])
  refine ⟨n, G, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), ?_, ?_, ?_⟩
  · simpa only [pow_one] using cut_proper hf.1 hproper hSep (24*M) (d*M) 1
  · intro N hN p hp
    have hP := hs p hp
    letI := hP.1
    let e := order f (u.split+1) p
    have hs' := order_spec f (u.split + 1) (by omega) p hP.1 hP.2.2.1
    have he : e ≤ u.split := hP.2.2.2
    have he' := order_exact f (u.split + 1) p (show e < u.split + 1 by omega)
    obtain ⟨hpos, hineq⟩ := hpay e hs'.1 he
    let v := u.split+1-e
    have hnp : 0 < n*v := Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) (by dsimp [v]; omega)
    have hscaled : n*v ≤ M*charge r a d e := by
      by_cases hz : z = 0
      · unfold n
        rw [hz, max_eq_left (by decide : 0 ≤ 1), one_mul]
        exact (show v ≤ u.split by dsimp [v]; omega).trans
          (hM.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left M hpos))
      · rw [show n = z from max_eq_right (Nat.pos_of_ne_zero hz), Nat.mul_comm z v]
        exact hineq
    have hfinal : n*v ≤ e*((24*M)*(r-e*a)+(d*M)*(e-1)) :=
      hscaled.trans (show M*charge r a d e ≤ _ by unfold charge; apply le_of_eq; ring)
    exact power_charge hf.1 hproper hSep hP.2.1 hP.2.2.1 hs'.2.2 he' (hV p hp) hnp hfinal hN
  · have hbound := chamber_cost hC0 hS0 hC (separant_box f) (24*M) (d*M) w
    have hlin : surface u.kind (shape f) (shape G).chamber =
        w.b * (shape G).chamber.b + w.j * (shape G).chamber.j + w.t * (shape G).chamber.t := by
      cases hu : u.kind with
      | ordinary => simpa only [w, hu] using Low6960SharedPrice.surface_ordinary_eq_weights (shape_valid hf) (shape G).chamber
      | tilted => simpa only [w, hu] using (Low6960SharedPrice.surface_tilted_eq_weights
          (shape_valid hf) (hfit hu) (shape G).chamber)
    rw [hlin]
    calc
      _ ≤ (24*M)*boxFee w x + (d*M)*boxFee w (sepBox (shape f)) := hbound
      _ = M*z := by unfold z; ring
      _ ≤ M*n := Nat.mul_le_mul_left _ (le_max_right _ _)

#print axioms of_contact
end
end Low6960WeightedCut

end Merged_R6960Low6960WeightedCut
