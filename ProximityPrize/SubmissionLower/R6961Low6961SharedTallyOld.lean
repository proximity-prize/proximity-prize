import ProximityPrize.SubmissionLower.R6961Low6961SharedTally
import ProximityPrize.SubmissionLower.R6961Low6961ActiveCycleMixed
import ProximityPrize.SubmissionLower.R6961Low6961SharedPrice

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
namespace Low6961SharedTallyOld
noncomputable section

open P3 (K)
open K1_13 (Row Shape shape InBox ceilDiv mixed32 chart)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength)
open K1_13_6_2_4 (oldEmbedding)
open Low6961GeometryCut (CutInput auxCurves32 auxPoints32 membershipDegree)
open Low6961GeometryCut_2 (Branch budget4 budget5)
open Low6961Prices (primaryBox taylorLength physicalPrice physicalPriceOld physicalPriceTilted
  physicalPriceActive surfaceNumerator32 tiltedSurface tiltedSurfaceActive)
open Low6961ActiveCycle (caps caps_chamber caps_active ordinary_doubled active_doubled ordinary_chart
  active_chart ordinary_budget active_budget activeRaw activeFamily old_section_active
  clip_bounds baseClip)
open Low48BentLattice (Chamber)
open Low48BentCycle (rawFamily capFamily mixedDegree)
open Low6961SharedTally (Data)
open scoped BigOperators Polynomial

open Low6961GeometryCut (le_ceil chargedPrice price_formula_old price_formula_tilted price_formula_active)

variable {Γ : Finset K} {s : K→(Polynomial K)} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}

def orderCost (D : Data Γ s f Q l S) (weight : Ideal GeoJets → ℕ) : ℕ :=
  ∑ b∈D.branches, weight b.surface * (b.weight*(D.points b).card)

private theorem eq_surface :
    surfaceNumerator32 (shape f).chamber primaryBox =
      min (budget4 (shape f).chamber) (budget5 (shape f).chamber) := rfl

private theorem four_budget (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime) :
    32*orderCost D weight ≤ budget4 (shape f).chamber := by
  have h := Low6961SharedCycleFour.bound_with_cut K1_13_6_2_3_1.proof
    (K1_13_6_2_3_2.of_children
      K1_13_6_2_3_2_1.proof K1_13_6_2_3_2_2.proof K1_13_6_2_3_2_3.proof
      K1_13_6_2_3_2_4.proof K1_13_6_2_3_2_5.proof K1_13_6_2_3_2_6.proof)
    (K1_13_6_2_3_3.of_children K1_13_6_2_3_3_1.proof
      (K1_13_6_2_3_3_2.of_children K1_13_6_2_3_3_2_1.proof K1_13_6_2_3_3_2_2.proof))
    f Q Q l input.small input.proper primaryBox ⟨by decide,by decide,by decide⟩ input.box weight
    D.branches D.points (D.four input) (fun b hb => ⟨b.base,hcut b hb⟩)
  have hh := (le_div_iff₀ (by norm_num : (0:ℚ)<32)).mp h
  apply (Nat.cast_le (α := ℚ)).mp
  simp only [orderCost,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat,mul_comm (32:ℚ)]
  simpa only [Nat.cast_mul,budget4] using hh

private theorem legacy_budget (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime) :
    32*orderCost D weight ≤ budget5 (shape f).chamber := by
  have h := Low6961SharedCycleLegacy.bound_with_weights f Q l input.small input.proper input.box
    weight D.branches D.points (D.five input) hcut
  apply (Nat.cast_le (α := ℚ)).mp
  simpa only [orderCost,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] using h

private theorem bent_budget (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime)
    (hguard : Low6961Prices.tiltedFits (shape f)) :
    (60*32)*orderCost D weight ≤ tiltedSurface (shape f).chamber primaryBox := by
  let p := (shape f).chamber
  have ht : 1 ≤ p.t := input.small.2.1
  have hC : ∀ i, Chamber (caps p i) :=
    caps_chamber (K1_13_7_1.shape_chamber f).1 ht hguard.1
  have h := Low6961SharedCycleBound.bound_with_cut (R := rawFamily (caps p)) (B := capFamily (caps p)) (ordinary_doubled (p := p)) f Q Q l input.small input.proper weight
    (Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩)
    (Low48BentCycle.old_section input.box)
    D.branches D.points (D.bent input (ordinary_chart ht)) (fun b hb => ⟨b.base,hcut b hb⟩)
  have hh := (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℚ) ≤ 60*32)).trans (ordinary_budget hC)
  apply (Nat.cast_le (α := ℚ)).mp
  simpa only [orderCost,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] using hh

private theorem active_charge (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime)
    (K : ℕ) (hK : Low6961Prices.ActiveFits f K) (hQ : Low6961Prices.ActiveFits Q 5164)
    (hguard : Low6961Prices.tiltedFits (shape f))
    (hactive : Low6961Prices.activeFitsPrice (shape f) K) :
    (60*32)*orderCost D weight ≤ tiltedSurfaceActive (shape f).chamber primaryBox K := by
  let p := (shape f).chamber
  have hfits := caps_active hguard hactive
  have hK' : baseClip p K ≤ p.b+p.j-K := (clip_bounds _ _ _).1
  have hsum : K+baseClip p K ≤ p.b+p.j := by
    have hc : 4 ≤ baseClip p K := hactive.2.1
    omega
  have h := Low6961SharedCycleBound.bound_with_cut (active_doubled hfits)
    f Q Q l input.small input.proper weight
    (old_section_active ⟨le_max_left _ _,le_rfl,le_rfl⟩ hK hsum)
    (old_section_active input.box hQ (by decide : 5164+498≤4012+1650))
    D.branches D.points (D.bent input (active_chart hK hactive))
    (fun b hb => ⟨b.base,hcut b hb⟩)
  have hh := (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℚ)≤60*32)).trans
    (active_budget (show 3≤p.t from hactive.1) hfits)
  apply (Nat.cast_le (α := ℚ)).mp
  simpa only [orderCost,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] using hh

def auxiliaryCap (x : Shape) : ℕ :=
  ceilDiv (82326*auxCurves32 x + 2*46421*auxPoints32 x) (32*46421)
def continuedCap (x : Shape) : ℕ :=
  ceilDiv ((82326+2*46421)*membershipDegree x) 46421
def surfaceCap (x : Shape) : ℕ :=
  2*(133397*x.b*primaryBox.b)

private theorem charge_le {x : Shape} {l a c d n scale budget O : ℕ}
    (hl : 0<l) (hs : 0<scale)
    (ha : a ≤ auxiliaryCap x) (hc : l*c ≤ continuedCap x)
    (hd : d ≤ surfaceCap x) (hn : l*n≤O) (hO : scale*O≤budget) :
    a+c+d+n ≤ chargedPrice x l scale budget := by
  have H : l*n ≤ ceilDiv budget scale :=
    hn.trans (le_ceil hs (by simpa [Nat.mul_comm] using hO))
  have hmain : c+n ≤ ceilDiv (ceilDiv budget scale+continuedCap x) l := by
    apply le_ceil hl
    rw [Nat.add_mul,Nat.mul_comm c l,Nat.mul_comm n l]
    omega
  unfold chargedPrice auxiliaryCap continuedCap surfaceCap at *
  omega

theorem physical_bound (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (K : ℕ) (hK : Low6961Prices.ActiveFits f K) (hQ : Low6961Prices.ActiveFits Q 5164)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime)
    {a c d n : ℕ} (ha : a ≤ auxiliaryCap (shape f))
    (hc : l*c ≤ continuedCap (shape f)) (hd : d ≤ surfaceCap (shape f))
    (hn : l*n≤orderCost D weight) : a+c+d+n ≤ physicalPrice (shape f) l K := by
  have hraw : 32*orderCost D weight ≤ surfaceNumerator32 (shape f).chamber primaryBox := by
    rw [eq_surface]
    exact le_min (four_budget D input weight hcut) (legacy_budget D input weight hcut)
  have hold : a+c+d+n ≤ physicalPriceOld (shape f) l := by
    rw [price_formula_old]
    exact charge_le input.positive (by decide) ha hc hd hn hraw
  by_cases ht : Low6961Prices.tiltedFits (shape f)
  · have hbent : a+c+d+n ≤ physicalPriceTilted (shape f) l := by
      rw [price_formula_tilted]
      exact charge_le input.positive (by decide) ha hc hd hn (bent_budget D input weight hcut ht)
    rw [physicalPrice,ite_eq_left ht]
    split_ifs with haa
    · refine le_min (le_min hold hbent) ?_
      rw [price_formula_active]
      exact charge_le input.positive (by decide) ha hc hd hn (active_charge D input weight hcut K hK hQ ht haa)
    · exact le_min hold hbent
  · simpa only [physicalPrice,ite_eq_right ht] using hold

theorem additive_le {x : Shape} {l a c d : ℕ} (hl : 0<l)
    (ha : a≤auxiliaryCap x) (hc : l*c≤continuedCap x) (hd : d≤surfaceCap x) :
    a+c+d ≤ Low6961SharedPrice.additiveBase x l := by
  have hc' : c≤ceilDiv (continuedCap x) l :=
    le_ceil hl (by simpa only [Nat.mul_comm] using hc)
  calc
    a+c+d ≤ auxiliaryCap x+ceilDiv (continuedCap x) l+surfaceCap x :=
      Nat.add_le_add (Nat.add_le_add ha hc') hd
    _ = _ := by
      unfold Low6961SharedPrice.additiveBase auxiliaryCap continuedCap surfaceCap
        auxCurves32 auxPoints32 membershipDegree
      simp only [show Low6961Prices.errors = 82326 by decide, show Low6961Prices.incidenceGap = 46421 by decide, show Low6961Prices.physicalDegree = 133397 by decide,
        Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      omega

#print axioms physical_bound
#print axioms additive_le
end
end Low6961SharedTallyOld
