import ProximityPrize.SubmissionLower.R6960Low6960SharedCount

set_option Elab.async false
set_option maxHeartbeats 1500000

namespace Low6960WeightedTally
noncomputable section

open P3 (K)
open K1_13 (Row shape ceilDiv)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength)
open K1_13_6_1_2 (VanishesTo pair_height)
open Low6960Prices (Messages SmallFactor ActiveFits ProperCut)
open Low6960GeometryCut (CutInput)
open Low6960GeometryCut_2 (Branch)
open Low6960SharedPrice (Rate surface surfaceScale)
open Low6960SharedTally (Data)
open Low6960SharedTallyNew (tally)
open Low6960SharedTallyOld (orderCost auxiliaryCap continuedCap surfaceCap)
open Low6960SharedPersistent (Persistent)
open private le_ceil from ProximityPrize.SubmissionLower.R6960Low6960GeometryCut
open scoped Polynomial BigOperators ENat

variable {Γ : Finset K} {s : K → K[X]} {f Q : Row 4} {l : ℕ}
  {S : Set (Ideal GeoJets)}

def weighted (D : Data Γ s f Q l S) (F : Finset (Branch f Q l))
    (w : Ideal GeoJets → ℕ) : ℕ :=
  ∑ b ∈ F, w b.surface * (b.weight * (D.points b).card)

theorem tilted (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F ⊆ D.branches) (G : Row 4) (hproper : ¬ f ∣ G)
    (w : Ideal GeoJets → ℕ) (n limit : ℕ) (hn : 0 < n) (htilt : Low6960Prices.tiltedFits (shape f))
    (hcut : ∀ b ∈ F, ∃ h : (intersectionIdeal f G).IsMinimalPrime b.surface,
      ((n * w b.surface : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f G) b.surface h.isPrime)
    (hsize : surface .tilted (shape f) (shape G).chamber ≤ 1920 * limit * n) :
    weighted D F w ≤ limit := by
  let p := (shape f).chamber
  let q := (shape G).chamber
  have ht : 1 ≤ p.t := input.small.2.1
  have hq : Low48BentLattice.Chamber (q,0) :=
    ⟨(K1_13_7_1.shape_chamber G).1, (K1_13_7_1.shape_chamber G).2, Nat.zero_le _⟩
  have hfamily := Low6960SharedBentCaps.caps_chamber (K1_13_7_1.shape_chamber f).1 ht htilt.1 hq
  let R := Low48BentCycle.rawFamily (Low6960SharedBentCaps.caps p q)
  let B := Low48BentCycle.capFamily (Low6960SharedBentCaps.caps p q)
  have h := Low6960SharedCycleBound.bound_with_cut (R := R) (B := B)
    Low6960SharedBentCaps.ordinary_doubled f Q G l input.small hproper (fun P => n * w P)
    (Low48BentCycle.old_section ⟨le_max_left _ _, le_rfl, le_rfl⟩)
    (Low48BentCycle.old_section ⟨le_max_left _ _, le_rfl, le_rfl⟩)
    F D.points (fun b hb => D.bent input (Low6960SharedBentCaps.chart q ht) b (hF hb)) hcut
  have hh := (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℚ) ≤ 60 * 32)).trans
    (Low6960SharedBentCaps.ordinary_budget hfamily)
  have hnum : 1920 * n * weighted D F w ≤ surface .tilted (shape f) (shape G).chamber := by
    norm_num only [show (60 : ℚ) * 32 = 1920 by norm_num] at hh
    apply (Nat.cast_le (α := ℚ)).mp
    simpa only [weighted, Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, ← Finset.mul_sum,
      mul_comm, mul_left_comm, mul_assoc, surface] using hh
  apply Nat.le_of_mul_le_mul_left _ (Nat.mul_pos (by decide : 0 < 1920) hn)
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnum.trans hsize

def Relevant (f : Row 4) (u : Rate) (order : Ideal GeoJets → ℕ) (P : Ideal GeoJets) : Prop :=
  P.IsPrime ∧ P.height = 2 ∧ toGeneric f ∈ P ∧ order P ≤ u.split

def Cut {Γ : Finset K} {s : K → K[X]} (f : Row 4) (u : Rate)
    (order : Ideal GeoJets → ℕ) : Prop :=
  ∀ (P : Finset (Ideal GeoJets)), (∀ p ∈ P, Persistent Γ s p) →
    (∀ p ∈ P, Relevant f u order p) →
    ∃ (n : ℕ) (G : Row 4), 0 < n ∧ (¬ f ∣ G) ∧
      (∀ N > 0, ∀ p ∈ P, ∃ h : (intersectionIdeal f (G^N)).IsMinimalPrime p,
        ((N * n * (u.split + 1 - order p) : ℕ) : ℕ∞) ≤
          cycleLength (intersectionIdeal f (G^N)) p h.isPrime) ∧
      surface u.kind (shape f) (shape G).chamber ≤ surfaceScale u.kind * (u.split * u.amount) * n

private theorem deficit_bound (data : Data Γ s f Q l {P | Persistent Γ s P})
    (input : CutInput Γ s f Q l) (u : Rate)
    (hk : u.kind = .tilted) (ht : Low6960Prices.tiltedFits (shape f))
    (order : Ideal GeoJets → ℕ) (cut : Cut (Γ := Γ) (s := s) f u order) :
    weighted data data.branches (fun p => u.split + 1 - order p) ≤ u.split * u.amount := by
  classical
  let F := data.branches.filter (fun b => order b.surface ≤ u.split)
  let P := F.image Branch.surface
  have hp : ∀ p ∈ P, Persistent Γ s p := by
    intro p hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
    exact data.allowed b (Finset.mem_filter.mp hb).1
  have hs : ∀ p ∈ P, Relevant f u order p := by
    intro p hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨b.base.isPrime,
      pair_height (K1_13_6_3_6.toGeneric_ne_zero input.small.1.ne_zero)
        (K1_13_7_1.proper_generic f Q input.small.1 input.proper) b.base,
      b.base.le (Ideal.subset_span (by simp)), (Finset.mem_filter.mp hb).2⟩
  obtain ⟨n, G, hn, hproper, hlength, hsize⟩ := cut P hp hs
  let w (p : Ideal GeoJets) := u.split + 1 - order p
  have cutLength (N : ℕ) (hN : 0 < N) (b : Branch f Q l) (hb : b ∈ F) :=
    hlength N hN b.surface (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  have hF : weighted data F w ≤ u.split * u.amount := by
    exact tilted data input F (Finset.filter_subset _ _) G hproper w n (u.split * u.amount) hn ht
      (fun b hb => by simpa only [pow_one, one_mul] using cutLength 1 (by decide) b hb)
      (by simpa only [hk, surfaceScale] using hsize)
  refine le_trans ?_ hF
  unfold weighted F
  rw [Finset.sum_filter]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : order b.surface ≤ u.split
  · simp only [if_pos hb, w]
  · have hz : u.split + 1 - order b.surface = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp only [if_neg hb, hz, Nat.zero_mul]

theorem count {w} (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f)
    (cap : ℕ) (hcap : ActiveFits f cap) (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ)))
    (l : ℕ) (hl : 0 < l) (hproper : ProperCut f Γ s l) (u : Rate)
    (hk : u.kind = .tilted) (ht : Low6960Prices.tiltedFits (shape f)) (order : Ideal GeoJets → ℕ)
    (horder : ∀ p (hp : p.IsPrime), toGeneric f ∈ p → order p ≤ u.split + 1 ∧
      @VanishesTo _ _ p hp (toGeneric f) (order p))
    (cut : Cut (Γ := Γ) (s := s) f u order) :
    Γ.card ≤ Low6960SharedPrice.price (shape f) l cap u := by
  classical
  obtain ⟨Q, hQprop, hbox, hweight, hQ, hcontact⟩ := hproper
  have input : CutInput Γ s f Q l := ⟨hm.distinct, hm.degree, hf, hon, hl, hQprop, hbox, hweight, hcontact⟩
  let data : Data Γ s f Q l {P | Persistent Γ s P} := Low6960SharedTally.build _
  obtain ⟨a, c, d, hCard, ha, hc, hd⟩ := Low6960SharedCount.cover_counts hm input data
  let G := tally data data.branches
  let W := weighted data data.branches order
  let E := weighted data data.branches (fun p => u.split + 1 - order p)
  have hs : ∀ b ∈ data.branches, order b.surface ≤ u.split + 1 ∧
      @VanishesTo _ _ b.surface b.base.isPrime (toGeneric f) (order b.surface) := by
    intro b _
    exact horder _ _ (b.base.le (Ideal.subset_span (by simp)))
  have hsum : (u.split + 1) * G = W + E := by
    unfold G W E tally weighted
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← Nat.add_mul, Nat.add_sub_of_le ((hs b hb).1)]
  let weight (p : Ideal GeoJets) := l * order p
  have hweightCharge : l * W ≤ orderCost data weight := by
    unfold W weighted orderCost weight
    rw [Finset.mul_sum]
    exact le_of_eq (Finset.sum_congr rfl (fun _ _ => by ring))
  have hlength : ∀ b ∈ data.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime := by
    intro b hb
    letI := b.base.isPrime
    rw [show weight b.surface = order b.surface * l by simp [weight, Nat.mul_comm]]
    exact Shared50Multiplicity.cycleLength_ge_product_of_minimal b.base
      (K1_13_6_3_6.toGeneric_ne_zero hf.1.ne_zero)
      (K1_13_7_1.proper_generic f Q hf.1 hQprop) (hs b hb).2
      (Low6960SharedPersistent.local_order (data.allowed b hb) input.box input.order)
  have hphys := Low6960SharedTallyOld.physical_bound data input cap hcap hQ weight
    hlength ha hc hd hweightCharge
  have hbase := Low6960SharedTallyOld.additive_le hl ha hc hd
  have hgap : E ≤ u.split * u.amount := deficit_bound data input u hk ht order cut
  refine hCard.trans (Nat.add_le_add_right ?_ _)
  apply le_ceil (by omega)
  calc
    (a + c + d + G) * (u.split + 1) =
        (a + c + d + W) + u.split * (a + c + d) + E := by
      calc
        _ = (a + c + d) + u.split * (a + c + d) + (u.split + 1) * G := by ring
        _ = _ := by rw [hsum]; ring
    _ ≤ Low6960Prices.physicalPrice (shape f) l cap + u.split * Low6960SharedPrice.additiveBase (shape f) l
        + u.split * u.amount := Nat.add_le_add (Nat.add_le_add hphys (Nat.mul_le_mul_left _ hbase)) hgap
    _ ≤ _ := Nat.le_add_right _ _

#print axioms tilted
#print axioms count
end
end Low6960WeightedTally
