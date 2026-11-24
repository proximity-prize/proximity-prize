import ProximityPrize.SubmissionLower.R6960Low6960WeightedTally
import ProximityPrize.SubmissionLower.KoalaSeparantCharge
import ProximityPrize.SubmissionLower.R6960Low6960WeightedRate

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
