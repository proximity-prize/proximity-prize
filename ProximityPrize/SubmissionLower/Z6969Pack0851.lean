import ProximityPrize.SubmissionLower.R6960Low6960SharedTallyNew
import ProximityPrize.SubmissionLower.Fast063
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import ProximityPrize.SubmissionLower.Z6969Pack0850
import ProximityPrize.SubmissionLower.Shared50OrderDivision
import ProximityPrize.SubmissionLower.Z6969Pack0838
import ProximityPrize.SubmissionLower.Z6969Pack0837
import ProximityPrize.SubmissionLower.Z6969Pack0836
import ProximityPrize.SubmissionLower.Z6969Pack0840
import ProximityPrize.SubmissionLower.RingHomShortcuts
import ProximityPrize.SubmissionLower.Z6969Pack0832
import ProximityPrize.SubmissionLower.FrontBranch3

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969SharedTallyNew
section Z6969Source2405
set_option autoImplicit true
set_option Elab.async false





-- merged module R6960Low6969SharedChooseCut
section Merged_R6960Low6969SharedChooseCut
set_option Elab.async false
set_option linter.style.haveILetI false
set_option maxRecDepth 12000

namespace Low6969SharedChooseCut
noncomputable section

open K1_13 (Geom Row Shape shape InBox indexDegree)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo pair_height cycleLength_ge_order)
open MvPolynomial
open Low6969SharedPrice (slope coord)

theorem weighted_pow (w : Fin 4 → ℕ) {P : Row 4} (h : P ≠ 0) (a : ℕ) :
    (P^a).weightedTotalDegree w = a * P.weightedTotalDegree w := by
  induction a with
  | zero => rw [pow_zero,zero_mul,← MvPolynomial.C_1,weightedTotalDegree_C]
  | succ a ih =>
    rw [pow_succ,weightedTotalDegree_mul _ _ _ (pow_ne_zero _ h) h,ih,Nat.succ_mul]

theorem valuation_factorization {f P : Row 4} (hf : f ≠ 0)
    (hpos : 0 < f.totalDegree) (hP : P ≠ 0) :
    ∃ a : ℕ, ∃ G : Row 4, P=f^a*G ∧ G≠0 ∧ ¬ f ∣ G := by
  have hm : FiniteMultiplicity f P := by
    refine ⟨P.totalDegree, ?_⟩
    intro hd
    have hle := weightedTotalDegree_le_of_dvd (1 : Fin 4→ℕ) hd hP
    rw [weighted_pow _ hf,weightedTotalDegree_one,weightedTotalDegree_one] at hle
    have ht := Nat.mul_le_mul_left (P.totalDegree+1) hpos
    simp only [Nat.mul_one] at ht
    omega
  obtain ⟨G,hG,hd⟩ := hm.exists_eq_pow_mul_and_not_dvd
  exact ⟨_,G,hG,fun h0 => hP (by rw [hG,h0,mul_zero]),hd⟩

theorem weight_coord (i : Fin 3) (P : Row 4) :
    coord (shape P) i =
      P.weightedTotalDegree (![fun _ : Fin 4 => 1,Fin.val,Pi.single 3 1] i) := by
  fin_cases i
  · exact (weightedTotalDegree_one P).symm
  · exact K1_13_1.indexDegree_eq P
  · exact (weightedTotalDegree_piSingle (3 : Fin 4) P).symm

theorem shape_product {f Q G : Row 4} (hf : f ≠ 0) (hG : G ≠ 0)
    {a : ℕ} (he : Q=f^a*G) (i : Fin 3) :
    coord (shape Q) i = a*coord (shape f) i+coord (shape G) i := by
  simp only [weight_coord,he,weightedTotalDegree_mul _ _ _ (pow_ne_zero _ hf) hG,weighted_pow _ hf]

private theorem cap_coords {Q : Row 4} {r : ℕ}
    (hQ : ∀ m ∈ Q.support, Low6969ShapeGate.fits r m) (i : Fin 3) :
    coord (shape Q) i ≤ r*coord slope i := by
  rw [weight_coord]
  apply Finset.sup_le
  intro m hm
  have hs := hQ m hm
  fin_cases i
  · exact hs.1
  · exact hs.2.1
  · simpa [Finsupp.weight_eq_sum, Finsupp.sum_fintype, Low6969SharedPrice.coord,
      Low6969SharedPrice.slope, Pi.single_apply] using hs.2.2

theorem minimal_pair {f G : Row 4} {P : Ideal GeoJets} [P.IsPrime]
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
  have hht : P'.height=2 := pair_height hzero hrel hmin
  letI : P'.IsPrime := hmin.isPrime
  have heq : P'=P := by
    by_contra hne
    have hs := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
    rw [hht,hP] at hs
    exact (by decide : ¬(2:ℕ∞)+1≤2) hs
  exact heq ▸ hmin

theorem mem_of_order {P : Ideal GeoJets} [P.IsPrime] {Q : GeoJets} {n : ℕ}
    (hn : 0<n) (hQ : VanishesTo P Q n) : Q∈P := by
  let L := Localization.AtPrime P
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L P _).mp
    ((Ideal.pow_le_self (Nat.ne_of_gt hn)) hQ)

structure SuitableSurface (f : Row 4) (s : ℕ) (P : Ideal GeoJets) : Prop where
  prime : P.IsPrime
  height : P.height = 2
  contains : toGeneric f ∈ P
  low : ¬ @VanishesTo _ _ P prime (toGeneric f) (s+1)

/-- The same independent cut has positive residual order at every selected surface. -/
theorem exists_cut {w Γ s} (hm : Low6969Prices.Messages w Γ s)
    (f : Row 4) (hf : Irreducible f) (hpos : 0<f.totalDegree)
    (multiplicityCap : ℕ) (pivot : Fin 3)
    (hguard : multiplicityCap*coord slope pivot < coord (shape f) pivot)
    (surfaces : Finset (Ideal GeoJets))
    (hp : ∀ P ∈ surfaces, Low6969SharedPersistent.Persistent Γ s P)
    (hh : ∀ P ∈ surfaces, SuitableSurface f multiplicityCap P) :
    ∃ r a : ℕ, 0<r ∧ 0<r-multiplicityCap*a ∧ ∃ G : Row 4, G≠0 ∧ ¬f∣G ∧
      (∀ i, a*coord (shape f) i + coord (shape G) i ≤ r*coord slope i) ∧
      ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f G).IsMinimalPrime P,
        @VanishesTo _ _ P h.isPrime (toGeneric G) (r-multiplicityCap*a) ∧
        ((r-multiplicityCap*a : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f G) P h.isPrime := by
  obtain ⟨r,hr,Q,hQ,hs,ho⟩ := Low6969SharedShapeRank.exists_polynomial hm surfaces hp
  obtain ⟨a,G,hfac,hG,hind⟩ := valuation_factorization hf.ne_zero hpos hQ
  have hbound (i : Fin 3) : a*coord (shape f) i+coord (shape G) i ≤ r*coord slope i := by
    rw [← shape_product hf.ne_zero hG hfac i]
    exact cap_coords hs i
  have hres : 0<r-multiplicityCap*a := Shared50ShapeRankBase.residual_order_pos hr hguard
    ((Nat.le_add_right _ _).trans (hbound pivot))
  refine ⟨r,a,hr,hres,G,hG,hind,hbound,?_⟩
  intro P hP
  have hdata := hh P hP
  letI := hdata.prime
  have hmap : toGeneric Q = (toGeneric f)^a*toGeneric G := by
    simp [hfac,toGeneric,map_mul,map_pow]
  have hGo : VanishesTo P (toGeneric G) (r-multiplicityCap*a) := by
    apply Shared50OrderDivision.vanishesTo_of_pow_mul_hasse P hdata.low
    rw [← hmap]
    exact ho P hP
  have hmin := minimal_pair hf hind hdata.height hdata.contains (mem_of_order hres hGo)
  exact ⟨hmin,hGo,cycleLength_ge_order hdata.height hdata.contains hGo⟩

end
end Low6969SharedChooseCut

end Merged_R6960Low6969SharedChooseCut

-- merged module R6960Low6969SharedTallyNew
section Merged_R6960Low6969SharedTallyNew

set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
namespace Low6969SharedTallyNew
noncomputable section
open P3 (K)
open K1_13 (Row Shape shape InBox chart)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_2_4 (oldEmbedding)
open K1_13_6_1_2 (VanishesTo cycleLength_ge_order pair_height)
open Low6969GeometryCut (CutInput)
open Low6969GeometryCut_2 (Branch)
open Low6969Prices (taylorLength)
open Low6969SharedPrice (Rate RateFits coord slope deficit weights surface surfaceScale)
open Low6969SharedTally (Data)
open MvPolynomial Finset
open scoped Polynomial BigOperators
open Low6969SharedChooseCut (minimal_pair mem_of_order)

variable {Γ : Finset K} {s : K→(Polynomial K)} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}

def tally (D : Data Γ s f Q l S) (F : Finset (Branch f Q l)) : ℕ :=
  ∑ b∈F,b.weight*(D.points b).card

private theorem scale_limit {x y e : ℕ} (h : ∀ N>0, N*x ≤ N*y+e) : x≤y := by
  by_contra! hh
  have hb := h (e+1) (by omega)
  have hc := Nat.mul_le_mul_left (e+1) (show y+1≤x by omega)
  rw [Nat.mul_add,Nat.mul_one] at hc
  omega

private theorem power_box (G : Row 4) (N : ℕ) :
    InBox (shape (G^N)) ⟨N*(shape G).chamber.b+3,N*(shape G).j+3,N*(shape G).t+1⟩ := by
  refine ⟨?_,?_,?_⟩
  · have h := weightedTotalDegree_pow_le (1 : Fin 4→ℕ) G N
    rw [weightedTotalDegree_one,weightedTotalDegree_one] at h
    exact (h.trans (Nat.mul_le_mul_left _ (le_max_left _ _))).trans (Nat.le_add_right _ _)
  · have h := weightedTotalDegree_pow_le (Fin.val : Fin 4→ℕ) G N
    rw [← K1_13_1.indexDegree_eq,← K1_13_1.indexDegree_eq] at h
    exact h.trans (Nat.le_add_right _ _)
  · have h := weightedTotalDegree_pow_le (Pi.single (3 : Fin 4) 1) G N
    simp only [weightedTotalDegree_piSingle] at h
    exact h.trans (Nat.le_add_right _ _)

private theorem power_order {P : Ideal GeoJets} [P.IsPrime] {G : Row 4} {n : ℕ}
    (h : VanishesTo P (toGeneric G) n) (N : ℕ) : VanishesTo P (toGeneric (G^N)) (N*n) := by
  let L := Localization.AtPrime P
  change algebraMap GeoJets L (toGeneric (G^N)) ∈ IsLocalRing.maximalIdeal L^(N*n)
  unfold toGeneric
  rw [map_pow,map_pow,Nat.mul_comm N n,pow_mul]
  exact Ideal.pow_mem_pow h _

private theorem four_count (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F⊆D.branches) (G : Row 4) (hproper : ¬ f∣G)
    (n amount : ℕ) (hn : 0<n) (hv : K1_13_8.Valid (shape f))
    (hcut : ∀ b∈F, ∃ h : (intersectionIdeal f G).IsMinimalPrime b.surface,
      @VanishesTo _ _ b.surface h.isPrime (toGeneric G) n)
    (hrate : surface .ordinary (shape f) (shape G).chamber ≤ 32*amount*n) :
    tally D F ≤ amount := by
  let W := weights .ordinary (shape f)
  have hbase : W.b*(shape G).chamber.b+W.j*(shape G).j+W.t*(shape G).t ≤ 32*amount*n := by
    rw [Low6969SharedPrice.surface_ordinary_eq_weights hv] at hrate
    change _ ≤ _ at hrate
    exact hrate
  have hall (N : ℕ) (hN : 0<N) :
      N*(32*n*tally D F) ≤ N*(32*n*amount)+(W.b*3+W.j*3+W.t) := by
    let q : Shape := ⟨N*(shape G).chamber.b+3,N*(shape G).j+3,N*(shape G).t+1⟩
    have hCh : K1_13_6_2_3.ChamberBox q := by
      have ht := (K1_13_7_1.shape_chamber G).2
      have hj := Nat.mul_le_mul_left N ht
      have hb := Nat.mul_le_mul_left N (le_max_right (shape G).b (shape G).j)
      refine ⟨?_,?_,?_⟩
      · change N*(shape G).j+3 ≤ N*max (shape G).b (shape G).j+3
        exact Nat.add_le_add_right hb _
      · change 3*(N*(shape G).t+1) ≤ N*(shape G).j+3
        rw [show 3*(N*(shape G).t+1)=N*(3*(shape G).t)+3 by ring]
        exact Nat.add_le_add_right hj _
      · dsimp [q]; omega
    have hp' : ¬ f∣G^N := fun h => hproper (input.small.1.prime.dvd_of_dvd_pow h)
    have hdata (b : Branch f Q l) (hb : b∈F) :
        ∃ h : (intersectionIdeal f (G^N)).IsMinimalPrime b.surface,
          ((N*n : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f (G^N)) b.surface h.isPrime := by
      obtain ⟨hP,horder⟩ := hcut b hb
      letI := hP.isPrime
      have hheight := pair_height (K1_13_6_3_6.toGeneric_ne_zero input.small.1.ne_zero)
        (K1_13_7_1.proper_generic f G input.small.1 hproper) hP
      have hmem : toGeneric f∈b.surface := hP.le (Ideal.subset_span (by simp))
      have ho := power_order horder N
      have hmin := minimal_pair input.small.1 hp' hheight hmem
        (mem_of_order (Nat.mul_pos hN hn) ho)
      exact ⟨hmin,cycleLength_ge_order hheight hmem ho⟩
    have hbound := Low6969SharedCycleFour.bound_with_cut K1_13_6_2_3_1.proof
      (K1_13_6_2_3_2.of_children
        K1_13_6_2_3_2_1.proof K1_13_6_2_3_2_2.proof K1_13_6_2_3_2_3.proof
        K1_13_6_2_3_2_4.proof K1_13_6_2_3_2_5.proof K1_13_6_2_3_2_6.proof)
      (K1_13_6_2_3_3.of_children K1_13_6_2_3_3_1.proof
        (K1_13_6_2_3_3_2.of_children K1_13_6_2_3_3_2_1.proof K1_13_6_2_3_3_2_2.proof))
      f Q (G^N) l input.small hp' q hCh (power_box G N) (fun _ => N*n) F D.points
      (fun b hb => D.four input b (hF hb)) hdata
    have hnum : N*(32*n*tally D F) ≤ surface .ordinary (shape f) q := by
      have h := (le_div_iff₀ (by norm_num : (0:ℚ)<32)).mp hbound
      apply (Nat.cast_le (α := ℚ)).mp
      simpa only [tally,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat,← Finset.mul_sum,
        mul_comm,mul_left_comm,mul_assoc, surface] using h
    have hlin : surface .ordinary (shape f) q =
        N*(W.b*(shape G).chamber.b+W.j*(shape G).j+W.t*(shape G).t)+(W.b*3+W.j*3+W.t) := by
      rw [Low6969SharedPrice.surface_ordinary_eq_weights hv]
      unfold q W
      ring
    rw [hlin] at hnum
    exact hnum.trans (by simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.add_le_add_right (Nat.mul_le_mul_left N hbase) (W.b*3+W.j*3+W.t))
  have hh := scale_limit hall
  apply Nat.le_of_mul_le_mul_left _ (Nat.mul_pos (by decide : 0<32) hn)
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh

theorem tilted_count (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F⊆D.branches) (G : Row 4) (hproper : ¬ f∣G)
    (n amount : ℕ) (hn : 0<n) (htilt : Low6969Prices.tiltedFits (shape f))
    (hcut : ∀ b∈F, ∃ h : (intersectionIdeal f G).IsMinimalPrime b.surface,
      (n : ℕ∞) ≤ cycleLength (intersectionIdeal f G) b.surface h.isPrime)
    (hrate : surface .tilted (shape f) (shape G).chamber ≤ 1920*amount*n) :
    tally D F ≤ amount := by
  let p := (shape f).chamber
  let q := (shape G).chamber
  have ht : 1≤p.t := input.small.2.1
  have hq : Low48BentLattice.Chamber (q,0) :=
    ⟨(K1_13_7_1.shape_chamber G).1,(K1_13_7_1.shape_chamber G).2,Nat.zero_le _⟩
  have hfamily := Low6969SharedBentCaps.caps_chamber (K1_13_7_1.shape_chamber f).1 ht htilt.1 hq
  let R := Low48BentCycle.rawFamily (Low6969SharedBentCaps.caps p q)
  let B := Low48BentCycle.capFamily (Low6969SharedBentCaps.caps p q)
  have h := Low6969SharedCycleBound.bound_with_cut (R := R) (B := B)
    Low6969SharedBentCaps.ordinary_doubled f Q G l input.small hproper (fun _ => n)
    (Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩)
    (Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩)
    F D.points (fun b hb => D.bent input (Low6969SharedBentCaps.chart q ht) b (hF hb)) hcut
  have hh := (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℚ)≤60*32)).trans
    (Low6969SharedBentCaps.ordinary_budget hfamily)
  have hnum : 1920*n*tally D F ≤ surface .tilted (shape f) (shape G).chamber := by
    norm_num only [show (60 : ℚ) * 32 = 1920 by norm_num] at hh
    apply (Nat.cast_le (α := ℚ)).mp
    simpa only [tally,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat,← Finset.mul_sum, mul_comm,mul_left_comm,mul_assoc, surface] using hh
  apply Nat.le_of_mul_le_mul_left _ (Nat.mul_pos (by decide : 0<1920) hn)
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hnum.trans hrate

theorem count (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F⊆D.branches) (G : Row 4) (hproper : ¬ f∣G)
    (u : Rate) (hu : RateFits (shape f) u) (r a : ℕ) (hn : 0<r-u.split*a)
    (hv : K1_13_8.Valid (shape f))
    (hbound : ∀ i, a*coord (shape f) i+coord (shape G) i≤r*coord slope i)
    (hcut : ∀ b∈F, ∃ h : (intersectionIdeal f G).IsMinimalPrime b.surface,
      @VanishesTo _ _ b.surface h.isPrime (toGeneric G) (r-u.split*a) ∧
      ((r-u.split*a : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f G) b.surface h.isPrime) :
    tally D F ≤ u.amount := by
  have hfit i := (Nat.le_add_right _ _).trans (hbound i)
  have hb (i : Fin 3) : coord (shape G) i≤r*coord slope i-a*coord (shape f) i :=
    Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using hbound i)
  have hbox : InBox (shape G) (deficit r a (shape f)) := ⟨hb 0,hb 1,hb 2⟩
  have hc := Low6969SharedPrice.chamber_bound hu r a hfit (shape G) hbox (K1_13_7_1.shape_chamber G).2
  have hcap : (weights u.kind (shape f)).b*(shape G).chamber.b +
      (weights u.kind (shape f)).j*(shape G).j + (weights u.kind (shape f)).t*(shape G).t ≤
      surfaceScale u.kind*u.amount*(r-u.split*a) :=
    Nat.le_of_mul_le_mul_left (by simpa only [Nat.mul_assoc] using hc) (by decide : 0<3)
  cases hkind : u.kind
  · apply four_count D input F hF G hproper _ _ hn hv
    · intro b hb
      obtain ⟨h,ho,_⟩ := hcut b hb
      exact ⟨h,ho⟩
    · rw [Low6969SharedPrice.surface_ordinary_eq_weights hv]
      rw [hkind] at hcap
      exact hcap
  · have ht := hu.1 hkind
    apply tilted_count D input F hF G hproper _ _ hn ht
    · intro b hb
      obtain ⟨h,_,hl⟩ := hcut b hb
      exact ⟨h,hl⟩
    · rw [Low6969SharedPrice.surface_tilted_eq_weights hv ht]
      rw [hkind] at hcap
      exact hcap

end
end Low6969SharedTallyNew

end Merged_R6960Low6969SharedTallyNew
end Z6969Source2405

-- Source: ProximityPrize.SubmissionLower.Low6969WeightedTally
section Z6969Source2406
set_option autoImplicit true
set_option Elab.async false

-- merged module R6960Low6969SharedThirdCut
section Merged_R6960Low6969SharedThirdCut

set_option Elab.async false
set_option autoImplicit false

namespace Low6969SharedThirdCut
noncomputable section

open Finset Polynomial MvPolynomial
open P3 (I K)

local instance (p : Prop) : Decidable p := Classical.propDecidable p
open scoped BigOperators ENat Polynomial
open K1_13 (Row Geom Shape shape InBox chart atJet extend embed)
open K1_13_6 (GeoJets GeoField HighChart markIdeal evalGeneric toGeneric intersectionIdeal
  cycleLength divisorIdeal separant CurveSections Pieces)
open K1_13_6_1 (mem_markIdeal mark_curve)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective)
open K1_13_6_3 (dimension cycleWeight)
open K1_13_7_1 (derivative_in_box shape_chamber)
open P0_9_6_1_2 (exists_value_cut)
open Low6969Prices (taylorLength primaryBox Messages)
open Low6969GeometryCut (CutInput)
open Low6969GeometryCut_3 (cutCycle)
open P0_9_6_3 (canonical_unique cycleWeight_ge)
open K1_14_6 (curve_degree_nat)

abbrev chartWidth (f : Row 4) : ℕ := (chart (taylorLength+2) (shape f).chamber).b

def Marked (f Q : Row 4) (l : ℕ) (surfaces : Finset (Ideal GeoJets)) (S : (Polynomial Geom)) : Prop :=
  ∃ P ∈ surfaces, ∃ r, HighChart f Q l S P r

private theorem points_of_value {Γ : Finset K} {s : K → (Polynomial K)} {C : Ideal GeoJets}
    (prime : C.IsPrime) (hdim : dimension C = 1)
    (hinj : Set.InjOn s (Γ : Set K))
    (hC : ∀ γ ∈ Γ, C ≤ markIdeal (extend (s γ)))
    (d : ℕ) (cuts : ∀ x a : K, ∃ D : GeoJets, D.totalDegree ≤ d ∧
      ∀ γ ∈ Γ, (evalGeneric (extend (s γ)) D = 0 ↔ (s γ).eval x = a)) :
    CurveSections Γ s ⌊(d : ℚ) * affineDegree C⌋₊ := by
  classical
  let := prime
  intro x a hmiss
  obtain ⟨D, hD, hvalue⟩ := cuts x a
  have hproper : D ∉ C := by
    obtain ⟨γ, hγ, hne⟩ := hmiss
    exact fun hm => hne ((hvalue γ hγ).mp (hC γ hγ hm))
  let J := C ⊔ Ideal.span {D}
  obtain ⟨hJdim, hJdeg⟩ :=
    principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime prime hproper hD
  have hJzero : (affineHilbertPolynomial J).natDegree = 0 := by
    change (affineHilbertPolynomial J).natDegree ≤ dimension C - 1 at hJdim
    omega
  have hdeg : affineDegree J ≤ (d : ℚ) * affineDegree C := by
    have hd : (affineHilbertPolynomial C).natDegree = 1 := hdim
    simpa [J, affineDegree, hd, hJzero, Polynomial.leadingCoeff] using hJdeg
  let T := Γ.filter fun γ => (s γ).eval x = a
  let point (γ : K) := actualPoint (extend (s γ))
  have hpoint : Set.InjOn point (Γ : Set K) := fun _ hγ _ hη he =>
    hinj hγ hη (Polynomial.map_injective embed embed.injective (actualPoint_injective he))
  have hinto : (T.image point : Set JetPoint) ⊆ zeroLocus GeoField J := by
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hy
    obtain ⟨hΓ, hv⟩ := mem_filter.mp hγ
    exact mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hC γ hΓ, (hvalue γ hΓ).mpr hv⟩
  obtain ⟨hfinite, hcount⟩ := finite_zeroLocus_and_ncard_le_affineDegree (K := GeoField) J hJzero
  have hcard := Set.ncard_le_ncard hinto hfinite
  rw [Set.ncard_coe_finset, card_image_of_injOn (hpoint.mono (filter_subset _ _))] at hcard
  exact Nat.le_floor ((Nat.cast_le.mpr hcard).trans (hcount.trans hdeg))

private theorem curve_family {Γ : Finset K} {s : K → (Polynomial K)} {f Q R : Row 4} {l : ℕ}
    (input : CutInput Γ s f Q l) {P C : Ideal GeoJets}
    (hP : (intersectionIdeal f Q).IsMinimalPrime P) (hR : toGeneric R ∉ P)
    (hC : (divisorIdeal P R).IsMinimalPrime C) :
    let part := Γ.filter fun γ => C ≤ markIdeal (extend (s γ)) ∧
      ∃ r, HighChart f Q l (extend (s γ)) P r
    CurveSections part s ⌊(chartWidth f : ℚ) * affineDegree C⌋₊ ∧
      0 < ⌊(chartWidth f : ℚ) * affineDegree C⌋₊ := by
  classical
  let := hP.isPrime
  have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hR hC
  change dimension C + 1 = dimension P at hd
  rw [(cutCycle input.small input.proper input.box).local_bound P hP |>.1] at hd
  have hdim : dimension C = 1 := by omega
  let part := Γ.filter fun γ => C ≤ markIdeal (extend (s γ)) ∧
    ∃ r, HighChart f Q l (extend (s γ)) P r
  have hsub : part ⊆ Γ := filter_subset _ _
  have hposW : 1 ≤ chartWidth f := le_max_of_le_left (Nat.le_add_right 1 _)
  obtain ⟨δ, hδ, hδeq⟩ := K1_14_6.curve_degree_nat C hC.isPrime hdim
  have hdpos : 0 < ⌊(chartWidth f : ℚ) * affineDegree C⌋₊ := by
    change 1 ≤ _
    apply Nat.le_floor
    rw [hδeq]
    exact_mod_cast (Nat.mul_le_mul hposW (Nat.succ_le_of_lt hδ))
  refine ⟨?_, hdpos⟩
  change CurveSections part s _
  by_cases hempty : part = ∅
  · rw [hempty]
    intro x a h
    simpa using h
  obtain ⟨γ₀, hγ₀⟩ := nonempty_iff_ne_empty.mpr hempty
  obtain ⟨r, hγchart⟩ := (mem_filter.mp hγ₀).2.2
  let p := (shape f).chamber
  let g := (separant^[r]) f
  have hgbox : InBox (shape g) p :=
    let hb := derivative_in_box f r
    ⟨hb.1.trans (le_max_left _ _), hb.2.1, hb.2.2⟩
  apply points_of_value hC.isPrime hdim (input.distinct.mono hsub)
    (fun γ hγ => (mem_filter.mp hγ).2.1)
  intro x a
  obtain ⟨D, hD, hv⟩ := exists_value_cut (by decide : taylorLength+2 ≤ K1.p) hgbox
    (shape_chamber f) input.small.2.1 x a
  refine ⟨D, hD.1, fun γ hγ => ?_⟩
  obtain ⟨r', hh⟩ := (mem_filter.mp hγ).2.2
  have heq := P0_9_6_3.canonical_unique hh.chart hγchart.chart
  subst r'
  have hvan := mem_markIdeal.mp (hh.point (hh.chart.2.1 r le_rfl))
  exact hv (s γ) ((input.degree γ (hsub hγ)).trans_lt (by decide)) hvan hh.regular

private theorem cut_degree {f Q R : Row 4} {l : ℕ} {Γ : Finset K} {s : K → (Polynomial K)}
    (input : CutInput Γ s f Q l) (surfaces : Finset (Ideal GeoJets))
    (origin : ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P h.isPrime)
    (hR : ∀ P ∈ surfaces, toGeneric R ∉ P) (hwidth : (shape R).b ≤ primaryBox.b) :
    (l : ℚ) * (∑ P ∈ surfaces, ∑ C ∈ (divisorIdeal P R).minimalPrimesFinset, affineDegree C) ≤
      ((shape f).b * primaryBox.b * primaryBox.b : ℕ) := by
  let pair := intersectionIdeal f Q
  let w := cycleWeight pair
  let B := primaryBox.b
  have hc := cutCycle input.small input.proper input.box
  have sub : surfaces ⊆ pair.minimalPrimesFinset := fun P hP =>
    Ideal.mem_minimalPrimesFinset.mpr (origin P hP).choose
  have hwidth' : (toGeneric R).totalDegree ≤ B :=
    (K1_13_6_3_6.totalDegree_toGeneric R).le.trans hwidth
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ P ∈ surfaces, (B : ℚ) * ((w P : ℚ) * affineDegree P) := by
      apply sum_le_sum
      intro P hP
      obtain ⟨hp, hl⟩ := origin P hP
      let := hp.isPrime
      have hl' : (l : ℚ) ≤ w P := by exact_mod_cast P0_9_6_3.cycleWeight_ge hc hp hl
      have hdeg := principalCut_sum_affineDegree_minimalPrimes_le (hR P hP) hwidth'
      exact (mul_le_mul_of_nonneg_left hdeg (by positivity)).trans (by
        rw [mul_left_comm]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hl' (affineDegree_nonneg P))
    _ = (B : ℚ) * ∑ P ∈ surfaces, (w P : ℚ) * affineDegree P := (Finset.mul_sum ..).symm
    _ ≤ (B : ℚ) * (((shape f).b * B : ℕ) : ℚ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sum_le_sum_of_subset_of_nonneg sub
        (fun P _ _ => mul_nonneg (by positivity) (affineDegree_nonneg P))).trans hc.weighted_degree
    _ = _ := by push_cast; ring

/-- Assign third-cut curves using the old surface and one regular value section. -/
theorem cover {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}
    (input : CutInput Γ s f Q l) (surfaces : Finset (Ideal GeoJets)) (R : Row 4)
    (origin : ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P h.isPrime)
    (hwidth : (shape R).b ≤ primaryBox.b)
    (hproper : ∀ P ∈ surfaces, toGeneric R ∉ P)
    (hzero : ∀ γ ∈ Γ, atJet R (extend (s γ)) = 0) :
    ∃ C : Pieces Γ, C.curves s ∧ (∀ i, 0 < C.degree i) ∧
      (∀ γ ∈ Γ, Marked f Q l surfaces (extend (s γ)) → γ ∈ C.union) ∧
      l * C.total ≤ (shape f).b * primaryBox.b * primaryBox.b * chartWidth f := by
  classical
  let T := surfaces.sigma fun P => (divisorIdeal P R).minimalPrimesFinset
  let e := T.equivFin.symm
  let marks (P C : Ideal GeoJets) := Γ.filter fun γ => C ≤ markIdeal (extend (s γ)) ∧
    ∃ r, HighChart f Q l (extend (s γ)) P r
  let d (C : Ideal GeoJets) := ⌊(chartWidth f : ℚ) * affineDegree C⌋₊
  let blocks : Pieces Γ := ⟨T.card, fun i => marks (e i).val.1 (e i).val.2,
    fun _ => filter_subset _ _, fun i => d (e i).val.2⟩
  have square (i : Fin T.card) : CurveSections (blocks.piece i) s (blocks.degree i) ∧
      0 < blocks.degree i := by
    let a := e i
    obtain ⟨hP,hC⟩ := mem_sigma.mp a.property
    exact curve_family input (origin a.val.1 hP).choose (hproper a.val.1 hP)
      (Ideal.mem_minimalPrimesFinset.mp hC)
  refine ⟨blocks, fun i => (square i).1, fun i => (square i).2, ?_, ?_⟩
  · intro γ hγ hm
    obtain ⟨P, hP, r, hh⟩ := hm
    obtain ⟨C, hC, hγC⟩ := mark_curve hh.point (hzero γ hγ)
    let a : T := ⟨⟨P,C⟩, mem_sigma.mpr ⟨hP, Ideal.mem_minimalPrimesFinset.mpr hC⟩⟩
    apply mem_biUnion.mpr
    refine ⟨T.equivFin a, mem_univ _, ?_⟩
    change γ ∈ marks (e (T.equivFin a)).val.1 (e (T.equivFin a)).val.2
    rw [show e (T.equivFin a) = a from T.equivFin.symm_apply_apply a]
    exact mem_filter.mpr ⟨hγ,hγC,⟨r,hh⟩⟩
  · have htotal : ((blocks.total : ℕ) : ℚ) ≤
        (chartWidth f : ℚ) * ∑ P ∈ surfaces, ∑ C ∈ (divisorIdeal P R).minimalPrimesFinset,
          affineDegree C := by
      unfold Pieces.total
      rw [Nat.cast_sum]
      change (∑ i : Fin T.card, ((d (e i).val.2 : ℕ) : ℚ)) ≤ _
      let value (a : Σ _ : Ideal GeoJets, Ideal GeoJets) : ℚ := (d a.2 : ℚ)
      have eq : (∑ i : Fin T.card, ((d (e i).val.2 : ℕ) : ℚ)) = ∑ a ∈ T, value a := by
        calc
          _ = ∑ a : T, value a.val := Fintype.sum_equiv e _ _ (fun _ => rfl)
          _ = _ := Finset.sum_attach T value
      rw [eq, show T = surfaces.sigma (fun P => (divisorIdeal P R).minimalPrimesFinset) from rfl,
        Finset.sum_sigma, Finset.mul_sum]
      refine sum_le_sum fun P _ => ?_
      rw [Finset.mul_sum]
      exact sum_le_sum fun C _ => Nat.floor_le (mul_nonneg (by positivity) (affineDegree_nonneg C))
    apply (Nat.cast_le (α := ℚ)).mp
    push_cast
    calc
      _ ≤ (l : ℚ) * ((chartWidth f : ℚ) * ∑ P ∈ surfaces,
          ∑ C ∈ (divisorIdeal P R).minimalPrimesFinset, affineDegree C) :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
      _ ≤ _ := by
        rw [mul_left_comm]
        have hc := mul_le_mul_of_nonneg_left
          (cut_degree input surfaces origin hproper hwidth) (by positivity : 0 ≤ (chartWidth f : ℚ))
        push_cast at hc
        exact hc.trans_eq (by ring)

/-- The charged nonpersistent labels use the third-cut fee alone. -/
theorem count {Γ : Finset K} {s : K → (Polynomial K)} {w : I → K} {f Q : Row 4} {l : ℕ}
    (hmsg : Messages w Γ s) (input : CutInput Γ s f Q l)
    (surfaces : Finset (Ideal GeoJets)) (R : Row 4)
    (origin : ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P h.isPrime)
    (hwidth : (shape R).b ≤ primaryBox.b)
    (hproper : ∀ P ∈ surfaces, toGeneric R ∉ P)
    (hzero : ∀ γ ∈ Γ, atJet R (extend (s γ)) = 0) :
    let assigned := Γ.filter fun γ => Marked f Q l surfaces (extend (s γ))
    assigned.card ≤ Low6969SharedPrice.nonsharedFee (shape f) l := by
  classical
  obtain ⟨C,hC,hpos,hcover,hdegree⟩ := cover input surfaces R origin hwidth hproper hzero
  have hsub : (Γ.filter fun γ => Marked f Q l surfaces (extend (s γ))) ⊆ C.union :=
    fun γ hγ => hcover _ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2
  apply (card_le_card hsub).trans ((Low6969FatPad.pieces_curve_capacity_integral C hmsg hC hpos).trans ?_)
  unfold Low6969SharedPrice.nonsharedFee K1_13.ceilDiv
  apply (Nat.le_div_iff_mul_le input.positive).mpr
  let numerator := 2 * (shape f).b * primaryBox.b^2 * chartWidth f
  change (2*C.total)*l ≤ numerator+l-1
  have hc : (2*C.total)*l ≤ numerator := by
    simpa only [numerator, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using Nat.mul_le_mul_left 2 hdegree
  have hl := input.positive
  omega

end
end Low6969SharedThirdCut

end Merged_R6960Low6969SharedThirdCut

-- merged module R6960Low6969SharedCount
section Merged_R6960Low6969SharedCount

set_option Elab.async false
set_option maxHeartbeats 1700000
set_option maxRecDepth 20000
namespace Low6969SharedCount
noncomputable section

open P3 (K)
open K1_13 (Row Shape shape chart extend ceilDiv)
open K1_13_6 (GeoJets HighChart HighMark toGeneric intersectionIdeal cycleLength separant)
open K1_13_6_1_2 (VanishesTo pair_height)
open K1_13_6_2 (actualPoint)
open Low6969Prices (Messages SmallFactor ActiveFits physicalDegree primaryBox ProperCut)
open Low6969GeometryCut (CutInput MixedMark highMark_cases)
open Low6969GeometryCut_2 (Branch)
open Low6969SharedPrice (Rate RateFits slope coord)
open Low6969SharedTally (Data hasBranch)
open Low6969SharedTallyNew (tally)
open Low6969SharedTallyNew (tilted_count)
open Low6969SharedTallyOld (orderCost auxiliaryCap continuedCap surfaceCap)
open Low6969SharedPersistent (Persistent)
open Finset
open scoped Polynomial BigOperators
attribute [local instance] Classical.propDecidable
open Low6969GeometryCut (continued_bound le_ceil)
open Low6969GeometryCut_2 (eval_actualPoint genericCoeffs_injective)

theorem shape_valid {f : Row 4} (hf : SmallFactor f) : K1_13_8.Valid (shape f) := by
  refine ⟨hf.2.1,(K1_13_7_1.shape_chamber f).2,?_⟩
  change K1_13.indexDegree f ≤ 3*f.totalDegree
  rw [K1_13_1.indexDegree_eq]
  apply Finset.sup_le
  intro m hm
  have hdeg : (∑ i ∈ m.support,m i)≤f.totalDegree := MvPolynomial.le_totalDegree hm
  have hw : ∀ i : Fin 4, m i*i.val≤3*m i := fun i => by
    rw [Nat.mul_comm (m i)]
    exact Nat.mul_le_mul_right _ (by omega)
  change (∑ i ∈ m.support,m i*i.val) ≤ _
  exact (Finset.sum_le_sum (fun i _ => hw i)).trans
    (by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ hdeg)

private def HighOrder (f : Row 4) (k : ℕ) (P : Ideal GeoJets) : Prop :=
  ∃ h : P.IsPrime, @VanishesTo _ _ P h (toGeneric f) (k+1)

private theorem hasBranch_of_mixed {f Q l g S} (h : MixedMark f Q l g)
    (hs : ∀ P, (∃ r, HighChart f Q l g P r) → P∈S) : hasBranch f Q l S g := by
  obtain ⟨surf,r,hz,hE,C,hC,hP,hterminal⟩ := h
  have hr : MvPolynomial.eval (actualPoint g) (toGeneric (separant ((separant^[r]) f))) ≠ 0 := by
    rw [eval_actualPoint]
    exact fun hzero => hz.regular (genericCoeffs_injective (by simpa using hzero))
  have hc : toGeneric (separant ((separant^[r]) f)) ∉ C := fun hmem => hr (hP hmem)
  let b : Branch f Q l := ⟨surf,r,hz.base,hz.high,hz.chart,hz.invariant,hE,C,hC,hc,hterminal⟩
  exact ⟨b,hs surf ⟨r,hz⟩,hP,hr⟩

private theorem high_weight {Γ s f Q l}
    (data : Data Γ s f Q l {P | Persistent Γ s P}) (input : CutInput Γ s f Q l)
    (k : ℕ) :
    ∀ b ∈ data.branches,
      ((if HighOrder f k b.surface then (k+1)*l else l : ℕ) : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime := by
  classical
  intro b hb
  split_ifs with hh
  · obtain ⟨hP,hf⟩ := hh
    letI := b.base.isPrime
    have hQ := Low6969SharedPersistent.local_order (data.allowed b hb) input.box input.order
    exact Shared50Multiplicity.cycleLength_ge_product_of_minimal b.base
      (K1_13_6_3_6.toGeneric_ne_zero input.small.1.ne_zero)
      (K1_13_7_1.proper_generic f Q input.small.1 input.proper) hf hQ
  · exact b.high

private theorem sum_weights {Γ s f Q l S} (data : Data Γ s f Q l S) (k : ℕ) :
    let high := data.branches.filter (fun b => HighOrder f k b.surface)
    let low := data.branches.filter (fun b => ¬HighOrder f k b.surface)
    orderCost data (fun P => if HighOrder f k P then (k+1)*l else l) =
      l*(tally data low+(k+1)*tally data high) := by
  classical
  let p (b : Branch f Q l) := HighOrder f k b.surface
  let w (b : Branch f Q l) := (if p b then (k+1)*l else l)*(b.weight*(data.points b).card)
  change ∑ b∈data.branches,w b = _
  rw [← Finset.sum_filter_add_sum_filter_not data.branches p w]
  rw [Nat.mul_add,← Nat.mul_assoc]
  unfold tally
  rw [Finset.mul_sum,Finset.mul_sum]
  have hh : ∑ b ∈ data.branches.filter p,w b =
      ∑ b ∈ data.branches.filter p,(l*(k+1))*(b.weight*(data.points b).card) := by
    apply Finset.sum_congr rfl
    intro b hb
    simp only [w,if_pos (Finset.mem_filter.mp hb).2,Nat.mul_comm l (k+1)]
  have hl : ∑ b ∈ data.branches.filter (fun b=>¬p b),w b =
      ∑ b ∈ data.branches.filter (fun b=>¬p b),l*(b.weight*(data.points b).card) := by
    apply Finset.sum_congr rfl
    intro b hb
    simp only [w,if_neg (Finset.mem_filter.mp hb).2]
  rw [hh,hl,Nat.add_comm]

private theorem count_low {w Γ s f Q l}
    (hm : Messages w Γ s) (data : Data Γ s f Q l {P | Persistent Γ s P})
    (input : CutInput Γ s f Q l) (u : Rate) (hu : RateFits (shape f) u) :
    tally data (data.branches.filter (fun b => ¬HighOrder f u.split b.surface)) ≤ u.amount := by
  classical
  let F := data.branches.filter (fun b => ¬HighOrder f u.split b.surface)
  let P := F.image Branch.surface
  have memP (b : Branch f Q l) (hb : b∈F) : b.surface∈P := Finset.mem_image.mpr ⟨b,hb,rfl⟩
  have hp : ∀ p∈P, Persistent Γ s p := by
    intro p hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hp
    exact data.allowed b (Finset.mem_filter.mp hb).1
  have hs : ∀ p∈P, Low6969SharedChooseCut.SuitableSurface f u.split p := by
    intro p hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨b.base.isPrime, ?_, b.base.le (Ideal.subset_span (by simp)), ?_⟩
    · exact pair_height (K1_13_6_3_6.toGeneric_ne_zero input.small.1.ne_zero)
        (K1_13_7_1.proper_generic f Q input.small.1 input.proper) b.base
    · exact fun hh => (Finset.mem_filter.mp hb).2 ⟨b.base.isPrime,hh⟩
  have hfpos : 0<f.totalDegree := lt_of_lt_of_le input.small.2.1
    (MvPolynomial.degreeOf_le_totalDegree _ _)
  obtain ⟨r,a,hr,hn,G,hG,hproper,hbox,hcut⟩ :=
    Low6969SharedChooseCut.exists_cut hm f input.small.1 hfpos u.split u.pivot hu.2.2.1 P hp hs
  exact Low6969SharedTallyNew.count data input F (Finset.filter_subset _ _) G hproper u hu r a hn
    (shape_valid input.small) hbox (fun b hb=>hcut _ (memP b hb))

/-- A proper cut of all persistent surfaces of the indicated anchor order. -/
def TiltedCut {Γ : Finset K} {s : K → (Polynomial K)} (f : Row 4) (u : Rate) : Prop :=
  ∀ (P : Finset (Ideal GeoJets)), (∀ p ∈ P, Persistent Γ s p) →
    (∀ p ∈ P, Low6969SharedChooseCut.SuitableSurface f u.split p) →
    ∃ (n : ℕ) (G : Row 4), 0 < n ∧ (¬ f ∣ G) ∧
      (∀ p ∈ P, ∃ h : (intersectionIdeal f G).IsMinimalPrime p,
        (n : ℕ∞) ≤ cycleLength (intersectionIdeal f G) p h.isPrime) ∧
      Low6969SharedPrice.surface .tilted (shape f) (shape G).chamber ≤ 1920 * u.amount * n

private theorem count_low_tilted {Γ s f Q l}
    (data : Data Γ s f Q l {P | Persistent Γ s P}) (input : CutInput Γ s f Q l)
    (u : Rate) (ht : Low6969Prices.tiltedFits (shape f)) (cut : TiltedCut (Γ := Γ) (s := s) f u) :
    tally data (data.branches.filter (fun b => ¬ HighOrder f u.split b.surface)) ≤ u.amount := by
  classical
  let F := data.branches.filter (fun b => ¬ HighOrder f u.split b.surface)
  let P := F.image Branch.surface
  have hp : ∀ p ∈ P, Persistent Γ s p := by
    intro p hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hp
    exact data.allowed b (Finset.mem_filter.mp hb).1
  have hs : ∀ p ∈ P, Low6969SharedChooseCut.SuitableSurface f u.split p := by
    intro p hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨b.base.isPrime, ?_, b.base.le (Ideal.subset_span (by simp)), ?_⟩
    · exact pair_height (K1_13_6_3_6.toGeneric_ne_zero input.small.1.ne_zero)
        (K1_13_7_1.proper_generic f Q input.small.1 input.proper) b.base
    · exact fun hh => (Finset.mem_filter.mp hb).2 ⟨b.base.isPrime,hh⟩
  obtain ⟨n,G,hn,hproper,horder,hrate⟩ := cut P hp hs
  exact tilted_count data input F (Finset.filter_subset _ _) G hproper n u.amount hn ht
    (fun b hb => horder b.surface (Finset.mem_image.mpr ⟨b,hb,rfl⟩)) hrate

private theorem cover_split {w Γ s f Q l}
    (hm : Messages w Γ s) (input : CutInput Γ s f Q l) :
    ∃ U : Finset K, U.card ≤ Low6969SharedPrice.nonsharedFee (shape f) l ∧
      ∀ γ∈Γ, MixedMark f Q l (extend (s γ)) → γ∈U ∨
        hasBranch f Q l {P | Persistent Γ s P} (extend (s γ)) := by
  classical
  let mins := (intersectionIdeal f Q).finite_minimalPrimes_of_isNoetherianRing
  let S := mins.toFinset.filter (fun P => ¬Persistent Γ s P ∧
    ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l : ℕ∞)≤cycleLength (intersectionIdeal f Q) P h.isPrime)
  obtain ⟨R,hR,hAvoid⟩ := Low6969SharedPersistent.common_avoider Γ s S
    (fun P hP => (Finset.mem_filter.mp hP).2.1)
  let U := Γ.filter (fun γ => Low6969SharedThirdCut.Marked f Q l S (extend (s γ)))
  have hU : U.card≤Low6969SharedPrice.nonsharedFee (shape f) l :=
    Low6969SharedThirdCut.count hm input S R (fun P hP=>(Finset.mem_filter.mp hP).2.2)
      hR.1 hAvoid hR.2
  refine ⟨U,hU,?_⟩
  intro γ hγ hMixed
  by_cases h : γ∈U
  · exact Or.inl h
  · refine Or.inr (hasBranch_of_mixed hMixed ?_)
    intro P hP
    obtain ⟨r,hchart⟩ := hP
    by_contra hn
    have hP' : P∈S := Finset.mem_filter.mpr
      ⟨mins.mem_toFinset.mpr hchart.base,hn,hchart.base,hchart.high⟩
    exact h (Finset.mem_filter.mpr ⟨hγ,P,hP',r,hchart⟩)

private theorem final_fee {x : Shape} {l K aux curves surfaces L H : ℕ}
    (u : Rate)
    (hold : aux+curves+surfaces+(L+(u.split+1)*H)≤Low6969Prices.physicalPrice x l K)
    (hbase : aux+curves+surfaces≤Low6969SharedPrice.additiveBase x l)
    (hlow : L≤u.amount) :
    aux+curves+surfaces+(L+H)+Low6969SharedPrice.nonsharedFee x l ≤
      Low6969SharedPrice.price x l K u := by
  unfold Low6969SharedPrice.price
  apply Nat.add_le_add_right
  apply le_ceil (by omega)
  calc
    _ = (aux+curves+surfaces+(L+(u.split+1)*H)) +
        u.split*(aux+curves+surfaces)+u.split*L := by ring
    _ ≤ Low6969Prices.physicalPrice x l K + u.split*Low6969SharedPrice.additiveBase x l +
        u.split*u.amount := Nat.add_le_add
          (Nat.add_le_add hold (Nat.mul_le_mul_left _ hbase)) (Nat.mul_le_mul_left _ hlow)
    _ ≤ _ := Nat.le_add_right _ _

theorem cover_counts {w Γ s f Q l} (hm : Messages w Γ s)
    (input : CutInput Γ s f Q l) (data : Data Γ s f Q l {P | Persistent Γ s P}) :
    ∃ a c d : ℕ,
      Γ.card ≤ a+c+d+tally data data.branches+Low6969SharedPrice.nonsharedFee (shape f) l ∧
      a ≤ auxiliaryCap (shape f) ∧ l*c ≤ continuedCap (shape f) ∧ d ≤ surfaceCap (shape f) := by
  classical
  obtain ⟨U,hU,hUC⟩ := cover_split hm input
  obtain ⟨A,B,hA,hAC,hAB,hAB'⟩ := Low6969GeometryCut_1.proof Γ s f Q l input
  obtain ⟨C,E,hC,hEC,hCP,hCB⟩ := data.pieces input
  obtain ⟨D,F,hD,hF,hDP,hFP,hDF,hDB,hFB⟩ := continued_bound Γ s f Q l input
  let a := A.union.card+B.card
  let c := D.union.card
  let d := F.union.card
  have hCover : Γ ⊆ ((A.union ∪ B) ∪ (C.union ∪ E)) ∪ (D.union ∪ F.union) ∪ U := by
    intro γ hγ
    by_cases hh : HighMark f Q l (extend (s γ))
    · have hdeg : (extend (s γ)).natDegree ≤ physicalDegree := by
        rw [Polynomial.natDegree_map]
        exact hm.degree γ hγ
      rcases highMark_cases hdeg hh with h | h
      · rcases hUC γ hγ h with hU | hP
        · exact Finset.mem_union_right _ hU
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
            (hCP γ hγ hP)))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hDF γ hγ h))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (hAC γ hγ hh)))
  have hM : C.union.card+E.card ≤ tally data data.branches := by
    have hCC := Low6969GeometryCut.pieces_curve_capacity_integral C hm hC hEC
    change 2*C.total+E.card≤tally data data.branches at hCB
    omega
  have hCard : Γ.card ≤ a+c+d+tally data data.branches+Low6969SharedPrice.nonsharedFee (shape f) l := by
    have h0 := Finset.card_le_card hCover
    have h1 := Finset.card_union_le (((A.union∪B)∪(C.union∪E))∪(D.union∪F.union)) U
    have h2 := Finset.card_union_le ((A.union∪B)∪(C.union∪E)) (D.union∪F.union)
    have h3 := Finset.card_union_le (A.union∪B) (C.union∪E)
    have h4 := Finset.card_union_le A.union B
    have h5 := Finset.card_union_le C.union E
    have h6 := Finset.card_union_le D.union F.union
    dsimp only [a,c,d]
    omega
  have hAux : a≤auxiliaryCap (shape f) := by
    unfold auxiliaryCap
    apply le_ceil (by decide)
    have hA' := Low6969GeometryCut.pieces_curve_capacity A hm hA
    dsimp only [a]
    omega
  have hCurve : l*c≤continuedCap (shape f) := by
    unfold continuedCap
    apply le_ceil (by decide)
    have hD' := Nat.mul_le_mul_left l (Low6969GeometryCut.pieces_curve_capacity_integral D hm hD hDP)
    change l*D.total ≤ Low6969GeometryCut.membershipDegree (shape f) at hDB
    have hD'' : l*c ≤ 2*Low6969GeometryCut.membershipDegree (shape f) := by
      rw [Nat.mul_left_comm] at hD'
      dsimp only [c]
      omega
    omega
  have hSurface : d≤surfaceCap (shape f) := by
    change F.union.card≤2*(133363*(shape f).b*primaryBox.b)
    have hF' := Low6969GeometryCut.pieces_surface_capacity F hm hF hFP
    change 2*F.total ≤ 133363*(shape f).b*primaryBox.b at hFB
    exact hF'.trans ((show 4*F.total=2*(2*F.total) by ring).le.trans
      (Nat.mul_le_mul_left 2 hFB))
  exact ⟨a,c,d,hCard,hAux,hCurve,hSurface⟩

private theorem count_of_low {w Γ s} (hm : Messages w Γ s) (f : Row 4)
    (hf : SmallFactor f) (cap : ℕ) (hcap : ActiveFits f cap)
    (hOn : ∀ γ ∈ Γ, K1_13.OnFactor f (extend (s γ)))
    (l : ℕ) (hl : 0 < l) (hCut : ProperCut f Γ s l) (u : Rate)
    (bound : ∀ Q, CutInput Γ s f Q l → ∀ data : Data Γ s f Q l {P | Persistent Γ s P},
      tally data (data.branches.filter (fun b => ¬ HighOrder f u.split b.surface)) ≤ u.amount) :
    Γ.card ≤ Low6969SharedPrice.price (shape f) l cap u := by
  classical
  obtain ⟨Q,hproper,hbox,hweight,hQ,horder⟩ := hCut
  have input : CutInput Γ s f Q l :=
    ⟨hm.distinct,hm.degree,hf,hOn,hl,hproper,hbox,hweight,horder⟩
  let data : Data Γ s f Q l {P | Persistent Γ s P} := Low6969SharedTally.build _
  let low := data.branches.filter (fun b => ¬HighOrder f u.split b.surface)
  let high := data.branches.filter (fun b => HighOrder f u.split b.surface)
  let L := tally data low
  let H := tally data high
  have hLow : L≤u.amount := bound Q input data
  have hSum : tally data data.branches = L+H := by
    unfold L H low high tally
    rw [Nat.add_comm]
    exact (Finset.sum_filter_add_sum_filter_not data.branches
      (fun b => HighOrder f u.split b.surface) _).symm
  obtain ⟨a,c,d,hCard,hAux,hCurve,hSurface⟩ := cover_counts hm input data
  rw [hSum] at hCard
  let weight (P : Ideal GeoJets) := if HighOrder f u.split P then (u.split+1)*l else l
  have hW : l*(L+(u.split+1)*H) ≤ orderCost data weight := (sum_weights data u.split).ge
  have hold := Low6969SharedTallyOld.physical_bound data input cap hcap hQ weight
    (high_weight data input u.split) hAux hCurve hSurface hW
  have hbase := Low6969SharedTallyOld.additive_le hl hAux hCurve hSurface
  exact hCard.trans (final_fee u hold hbase hLow)

/-- Count marks using a separate construction for the common tilted surface cut. -/
theorem tilted_proof {w Γ s} (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f)
    (cap : ℕ) (hcap : ActiveFits f cap) (hOn : ∀ γ ∈ Γ, K1_13.OnFactor f (extend (s γ)))
    (l : ℕ) (hl : 0 < l) (hCut : ProperCut f Γ s l) (u : Rate)
    (ht : Low6969Prices.tiltedFits (shape f)) (cut : TiltedCut (Γ := Γ) (s := s) f u) :
    Γ.card ≤ Low6969SharedPrice.price (shape f) l cap u :=
  count_of_low hm f hf cap hcap hOn l hl hCut u (fun _ input data => count_low_tilted data input u ht cut)

theorem proof : Low6969SharedPrice.cShared := by
  intro w Γ s hm f hf cap hcap hOn l hl hCut u hu
  exact count_of_low hm f hf cap hcap hOn l hl hCut u (fun _ input data => count_low hm data input u hu)

end
end Low6969SharedCount

end Merged_R6960Low6969SharedCount

-- merged module R6960Low6969WeightedTally
section Merged_R6960Low6969WeightedTally

set_option Elab.async false
set_option maxHeartbeats 1500000

namespace Low6969WeightedTally
noncomputable section

open P3 (K)
open K1_13 (Row shape ceilDiv)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength)
open K1_13_6_1_2 (VanishesTo pair_height)
open Low6969Prices (Messages SmallFactor ActiveFits ProperCut)
open Low6969GeometryCut (CutInput)
open Low6969GeometryCut_2 (Branch)
open Low6969SharedPrice (Rate surface surfaceScale)
open Low6969SharedTally (Data)
open Low6969SharedTallyNew (tally)
open Low6969SharedTallyOld (orderCost auxiliaryCap continuedCap surfaceCap)
open Low6969SharedPersistent (Persistent)
open Low6969GeometryCut (le_ceil)
open scoped Polynomial BigOperators ENat

variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}
  {S : Set (Ideal GeoJets)}

def weighted (D : Data Γ s f Q l S) (F : Finset (Branch f Q l))
    (w : Ideal GeoJets → ℕ) : ℕ :=
  ∑ b ∈ F, w b.surface * (b.weight * (D.points b).card)

theorem tilted (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F ⊆ D.branches) (G : Row 4) (hproper : ¬ f ∣ G)
    (w : Ideal GeoJets → ℕ) (n limit : ℕ) (hn : 0 < n) (htilt : Low6969Prices.tiltedFits (shape f))
    (hcut : ∀ b ∈ F, ∃ h : (intersectionIdeal f G).IsMinimalPrime b.surface,
      ((n * w b.surface : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f G) b.surface h.isPrime)
    (hsize : surface .tilted (shape f) (shape G).chamber ≤ 1920 * limit * n) :
    weighted D F w ≤ limit := by
  let p := (shape f).chamber
  let q := (shape G).chamber
  have ht : 1 ≤ p.t := input.small.2.1
  have hq : Low48BentLattice.Chamber (q,0) :=
    ⟨(K1_13_7_1.shape_chamber G).1, (K1_13_7_1.shape_chamber G).2, Nat.zero_le _⟩
  have hfamily := Low6969SharedBentCaps.caps_chamber (K1_13_7_1.shape_chamber f).1 ht htilt.1 hq
  let R := Low48BentCycle.rawFamily (Low6969SharedBentCaps.caps p q)
  let B := Low48BentCycle.capFamily (Low6969SharedBentCaps.caps p q)
  have h := Low6969SharedCycleBound.bound_with_cut (R := R) (B := B)
    Low6969SharedBentCaps.ordinary_doubled f Q G l input.small hproper (fun P => n * w P)
    (Low48BentCycle.old_section ⟨le_max_left _ _, le_rfl, le_rfl⟩)
    (Low48BentCycle.old_section ⟨le_max_left _ _, le_rfl, le_rfl⟩)
    F D.points (fun b hb => D.bent input (Low6969SharedBentCaps.chart q ht) b (hF hb)) hcut
  have hh := (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℚ) ≤ 60 * 32)).trans
    (Low6969SharedBentCaps.ordinary_budget hfamily)
  have hnum : 1920 * n * weighted D F w ≤ surface .tilted (shape f) (shape G).chamber := by
    norm_num only [show (60 : ℚ) * 32 = 1920 by norm_num] at hh
    apply (Nat.cast_le (α := ℚ)).mp
    simpa only [weighted, Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, ← Finset.mul_sum,
      mul_comm, mul_left_comm, mul_assoc, surface] using hh
  apply Nat.le_of_mul_le_mul_left _ (Nat.mul_pos (by decide : 0 < 1920) hn)
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnum.trans hsize

def Relevant (f : Row 4) (u : Rate) (order : Ideal GeoJets → ℕ) (P : Ideal GeoJets) : Prop :=
  P.IsPrime ∧ P.height = 2 ∧ toGeneric f ∈ P ∧ order P ≤ u.split

def Cut {Γ : Finset K} {s : K → (Polynomial K)} (f : Row 4) (u : Rate)
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
    (hk : u.kind = .tilted) (ht : Low6969Prices.tiltedFits (shape f))
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
    (hk : u.kind = .tilted) (ht : Low6969Prices.tiltedFits (shape f)) (order : Ideal GeoJets → ℕ)
    (horder : ∀ p (hp : p.IsPrime), toGeneric f ∈ p → order p ≤ u.split + 1 ∧
      @VanishesTo _ _ p hp (toGeneric f) (order p))
    (cut : Cut (Γ := Γ) (s := s) f u order) :
    Γ.card ≤ Low6969SharedPrice.price (shape f) l cap u := by
  classical
  obtain ⟨Q, hQprop, hbox, hweight, hQ, hcontact⟩ := hproper
  have input : CutInput Γ s f Q l := ⟨hm.distinct, hm.degree, hf, hon, hl, hQprop, hbox, hweight, hcontact⟩
  let data : Data Γ s f Q l {P | Persistent Γ s P} := Low6969SharedTally.build _
  obtain ⟨a, c, d, hCard, ha, hc, hd⟩ := Low6969SharedCount.cover_counts hm input data
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
      (Low6969SharedPersistent.local_order (data.allowed b hb) input.box input.order)
  have hphys := Low6969SharedTallyOld.physical_bound data input cap hcap hQ weight
    hlength ha hc hd hweightCharge
  have hbase := Low6969SharedTallyOld.additive_le hl ha hc hd
  have hgap : E ≤ u.split * u.amount := deficit_bound data input u hk ht order cut
  refine hCard.trans (Nat.add_le_add_right ?_ _)
  apply le_ceil (by omega)
  calc
    (a + c + d + G) * (u.split + 1) =
        (a + c + d + W) + u.split * (a + c + d) + E := by
      calc
        _ = (a + c + d) + u.split * (a + c + d) + (u.split + 1) * G := by ring
        _ = _ := by rw [hsum]; ring
    _ ≤ Low6969Prices.physicalPrice (shape f) l cap + u.split * Low6969SharedPrice.additiveBase (shape f) l
        + u.split * u.amount := Nat.add_le_add (Nat.add_le_add hphys (Nat.mul_le_mul_left _ hbase)) hgap
    _ ≤ _ := Nat.le_add_right _ _

end
end Low6969WeightedTally

end Merged_R6960Low6969WeightedTally
end Z6969Source2406

-- Source: ProximityPrize.SubmissionLower.Low6969RetainedPrimary
section Z6969Source2407
set_option autoImplicit true
set_option Elab.async false

-- merged module R6960Low6969RetainedPhysicalBank
section Merged_R6960Low6969RetainedPhysicalBank

set_option autoImplicit false
set_option Elab.async false
namespace Low6969RetainedCut
noncomputable section
open P3 (I K node)
open K1_13 (Geom Row shape InBox extend embed Contact OrderAt)
open Low6969Prices (Messages physicalDegree TrueWeightLE ActiveFits primaryBox primaryCutoff
  agreement layerWidth layerNeed)
open K1_13_3 (symbolAt)
open Polynomial
open scoped Polynomial BigOperators

/-- The accepted Low6969OrderProof.BankRow, abstracting only the published taper predicate. -/
def physicalRow (jets : Row 4 → Prop) (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) primaryBox ∧ TrueWeightLE P T ∧ jets P ∧ Contact w P

def AllContact (jets : Row 4 → Prop) : Prop :=
  ∀ (w : I → K) (T : ℕ) (P : Row 4), T ≤ primaryCutoff → physicalRow jets w T P →
    ∀ S : (Polynomial Geom), S.natDegree ≤ physicalDegree →
    (∃ H : Finset I, agreement ≤ H.card ∧ ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) →
    OrderAt P S (levelOrder T)

def physicalBank {w Γ s} (hm : Messages w Γ s) (jets : Row 4 → Prop)
    (active : ∀ P, jets P → ActiveFits P 5164) (contact : AllContact jets) : Bank Γ s where
  row := physicalRow jets w
  bounds T hT P hP := ⟨hP.1,fun m hm => (hP.2.1 m hm).trans hT,active P hP.2.2.1⟩
  order T hT P hP γ hγ := by
    apply contact w T P hT hP
    · simpa only [extend,natDegree_map_eq_of_injective (RingHom.injective embed)] using hm.degree γ hγ
    · obtain ⟨H,hH,hh⟩ := hm.hits γ hγ
      refine ⟨H,hH,fun i hi => ?_⟩
      rw [extend,eval_map,eval₂_at_apply,hh i hi]

theorem physicalBank_ranked {w Γ s} (hm : Messages w Γ s) (jets : Row 4 → Prop)
    (active : ∀ P, jets P → ActiveFits P 5164) (contact : AllContact jets)
    {rank : ℕ} (enough : layerWidth*(layerNeed-1) < rank)
    (families : ∀ x : Geom, (∀ i : I, x ≠ embed (node i)) →
      ∃ r : ℕ → ℕ, rank ≤ ∑ T ∈ Finset.range (primaryCutoff+1), r T ∧
        ∀ T ≤ primaryCutoff, ∃ e : Fin (r T) → Row 4, (∀ i, physicalRow jets w T (e i)) ∧
          LinearIndependent Geom (fun i => symbolAt x (e i)))
    (symbols : ∀ {n} (x : Geom) (e : Fin n → Row 4), (∀ i, jets (e i)) →
      LinearIndependent Geom (fun i => symbolAt x (e i)) → n ≤ Low6969Prices.symbolCount) :
    (physicalBank hm jets active contact).Ranked := by
  intro x hx
  obtain ⟨r,hr,he⟩ := families x hx
  refine ⟨r,enough.trans_le hr,?_⟩
  intro T hT
  obtain ⟨e,hes,hei⟩ := he T hT
  exact ⟨symbols x e (fun i => (hes i).2.2.1) hei,e,hes,hei⟩

/-- The published floor-plus-one layer identity, with the nonzero remainder required for strict rank. -/
theorem sufficient_rank {rank width need : ℕ} (h : rank/width+1=need)
    (positive_remainder : 0 < rank%width) : width*(need-1)<rank := by
  rw [← h,Nat.add_sub_cancel]
  have total := Nat.mod_add_div rank width
  omega

end
end Low6969RetainedCut

end Merged_R6960Low6969RetainedPhysicalBank

-- merged module R6960Low6969RetainedPrimary
section Merged_R6960Low6969RetainedPrimary

set_option autoImplicit false
set_option Elab.async false
namespace Low6969RetainedCut
noncomputable section
open Low6969Prices (Messages ActiveFits layerWidth layerNeed)
open K1_13 (Row)
open P3 (I K)
open scoped Polynomial

private theorem tapered_active (P : Row 4) (h : PrimaryTaper.JetsBounded P) : ActiveFits P 5164 :=
  fun m hm => (PrimaryTaperActive.of_jets h m hm).trans (by decide)

private theorem bank_contact : AllContact PrimaryTaper.JetsBounded := by
  intro w T P hT hp S hs hits
  obtain ⟨H,hH,hh⟩ := hits
  exact Low6969OrderProof_1.order_of_contact w P hT hp.2.1 hp.2.2.2 hs hH hh

def Bank.of_messages {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} (hm : Messages w Γ s) :
    Bank Γ s := physicalBank hm PrimaryTaper.JetsBounded tapered_active bank_contact

theorem Bank.of_messages_row {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} (hm : Messages w Γ s) :
    (Bank.of_messages hm).row = Low6969OrderProof.BankRow w := rfl

theorem Bank.of_messages_ranked_of_rank {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)}
    (hm : Messages w Γ s) (hr : Low6969Order.PrimaryRank w) :
    (Bank.of_messages hm).Ranked := by
  apply physicalBank_ranked hm PrimaryTaper.JetsBounded tapered_active bank_contact
    (rank := Low6969Order.sourceRank)
  · apply sufficient_rank (show Low6969Order.sourceRank / layerWidth + 1 = layerNeed from
      Low6969Order.certified_layers)
    decide +kernel
  · exact fun x hx => Low6969Order.symbol_families w x hr hx
  · exact fun x e he hi => PrimaryTaper.symbol_rank x e he hi

theorem Bank.of_messages_ranked {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} (hm : Messages w Γ s) :
    (Bank.of_messages hm).Ranked :=
  Bank.of_messages_ranked_of_rank hm (Low6969Order.primary_rank w)

end
end Low6969RetainedCut

end Merged_R6960Low6969RetainedPrimary
end Z6969Source2407

-- Source: ProximityPrize.SubmissionLower.Low6969LeadingBase
section Z6969Source2408
set_option autoImplicit true
set_option Elab.async false
set_option autoImplicit true
section
namespace Low6969Leading
noncomputable section
variable {top : Fin 16}
open P3 (K I)
open Low6969Prices (TrueWeightLE anchorCutoff taylorLength lowerWidth lowerIndex lowerTop)
open K1_13 (Row indexDegree)
open K1_13_5 (NodeFamily)
open K1_13 (Shape)
open scoped BigOperators Polynomial
abbrev lowBox : Shape := ⟨142, 58, 29⟩
abbrev graphBox (top : Fin 16) : Shape :=
  ⟨lowerWidth top, lowerIndex top + 1, (lowerIndex top + 1) / 2⟩
def liftedBox (top : Fin 16) (L : ℕ) : Shape :=
  let j := 2 + (L - 4) * (lowerIndex top + 2)
  ⟨1 + (L - 4) * lowerWidth top, j, min (1 + (L - 4) * (lowerTop top + 2)) (j / 2)⟩
def firstWidth (top : Fin 16) : ℕ :=
  max (lowerWidth top) ((2 * lowerTop top - 1) * lowerWidth top - lowerTop top ^ 2)
def firstIndex (top : Fin 16) : ℕ :=
  max (lowerIndex top) ((2 * lowerTop top - 1) * lowerIndex top - 2 * lowerTop top ^ 2)

structure FirstRow (top : Fin 16) (q : Row 2) : Prop where
  ne_zero : q ≠ 0
  total : q.totalDegree ≤ firstWidth top
  index : indexDegree q ≤ firstIndex top

structure FirstFactors (top : Fin 16) {n : ℕ} (f : Fin n → Row 2) : Prop where
  irreducible : ∀ i, Irreducible (f i)
  positive : ∀ i, 0 < (f i).degreeOf 1
  total : (∑ i, (f i).totalDegree) ≤ firstWidth top
  index : (∑ i, indexDegree (f i)) ≤ firstIndex top

structure SecondFactors (top : Fin 16) {n : ℕ} (f : Fin n → Row 3) : Prop where
  irreducible : ∀ i, Irreducible (f i)
  positive : ∀ i, 0 < (f i).degreeOf 2
  weight : ∀ i, TrueWeightLE (f i) anchorCutoff
  total : (∑ i, (f i).totalDegree) ≤ lowerWidth top
  index : (∑ i, indexDegree (f i)) ≤ lowerIndex top
  coordinate : (∑ i, (f i).degreeOf 2) ≤ lowerTop top
def Whole (f : Row 3) : Prop :=
  f ∣ K1_13_5.compatibilityNumerator f (taylorLength - 3)

-- Mixed volume coefficients in the support bounds of the contracted row.
def mixedCoefficients (top : Fin 16) : ℕ × ℕ × ℕ :=
  ![(94974422841575, 307617475262646, 3983964634720),
    (85663729273094, 297822124715193, 30073357),
    (76833243327041, 283624881031282, 4019535747530),
    (68482965003416, 273046969869491, 30340083),
    (60612894302219, 258031594725158, 4055106860340),
    (53223031223450, 246671122949029, 30606809),
    (46313375767109, 230837616344274, 4090677973150),
    (39883927933196, 218694583953807, 30873535),
    (33934687721711, 202042945888630, 4126249085960),
    (28465655132654, 189117352883825, 31140261),
    (23476830166025, 171647583358226, 4161820198770),
    (18968212821824, 157939429739083, 31406987),
    (14939803100051, 139651528753062, 4197391311580),
    (11391601000706, 125160814519581, 31673713),
    (8323606523789, 106054782073138, 4232962424390),
    (5735819669300, 90781507225319, 31940439)] top

def mixedBudget (top : Fin 16) : ℕ :=
  let (b, j, r) := mixedCoefficients top
  b * lowerWidth top + j * lowerIndex top + r * lowerTop top
def invariantBudget (top : Fin 16) : ℕ :=
  lowerWidth top * (1 + (2 * (taylorLength + 1) - 7) * (lowerWidth top - 1))
abbrev firstExponent : ℕ := 2 * taylorLength - 5
abbrev firstChartTotal (top : Fin 16) : ℕ := 1 + firstExponent * (firstWidth top - 1)
abbrev firstChartTop (top : Fin 16) : ℕ :=
  min (firstChartTotal top) (firstExponent * (firstIndex top - 1) + taylorLength - 1)
def firstMixedBudget (top : Fin 16) : ℕ :=
  firstWidth top * firstChartTop top + firstIndex top * (firstChartTotal top - firstChartTop top)
structure ProperCover (top : Fin 16) (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) where
  isolated : Finset K
  multiple : NodeFamily w Γ s
  invariant : NodeFamily w Γ s
  cover : Γ ⊆ isolated ∪ multiple.labels ∪ invariant.labels
  mixed : isolated.card + 2 * multiple.totalCap ≤ mixedBudget top
  fresh : invariant.totalCap ≤ (invariantBudget top)
  components : multiple.n + invariant.n ≤ 2 * (invariantBudget top)
end
end Low6969Leading
end
section
namespace Low6969Leading_1
noncomputable section
variable {top : Fin 16}
open K1_13 (Geom Row Shape atJet)
open K1_13_5 (RegularAt compatibilityNumerator separant)
open Low6969Leading (graphBox liftedBox)
open K1_13_5_4 (GeometricX GeoRow genericCoeff genericRow graph graphPoint
  InLiftedBox RepresentsOnGraph jetPoint regularLocus extendedAtJet)
open Low6969Prices (taylorLength physicalDegree)
open Low6969Leading (Whole mixedBudget)
open Polynomial
open scoped BigOperators
abbrev Coefficients := Fin taylorLength → GeometricX
abbrev CoefficientIdeal := Ideal (GeoRow taylorLength)
abbrev CurveIndex (n : ℕ) := Fin n × Ideal (GeoRow 3)
def coefficientPoint (S : (Polynomial Geom)) : Coefficients :=
  fun j => algebraMap Geom GeometricX (S.coeff j)
def coefficientPolynomial (a : Coefficients) : (Polynomial GeometricX) :=
  ∑ j : Fin taylorLength, Polynomial.monomial j.val (a j)
def oldCut (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 3)
def oldNext (f : Row 3) : Row 3 := compatibilityNumerator f (taylorLength - 2)
open K1_13_5_4_1 (compatibility_degree)
theorem ordinary_bound (f : Row 3) :
    (oldCut f).totalDegree ≤ 1 + (2 * (taylorLength + 1) - 7) * (f.totalDegree - 1) :=
  compatibility_degree f (taylorLength - 3)
def oldCutIdeal (f : Row 3) : Ideal (GeoRow 3) :=
  Ideal.span {genericRow f, genericRow (oldCut f)}
def properComponents {n : ℕ} (f : Fin n → Row 3) : Finset (CurveIndex n) := by
  classical
  exact Finset.univ.biUnion fun i =>
    if Whole (f i) then ∅ else
      ((oldCutIdeal (f i)).retainedMinimalPrimes (genericRow (separant (f i)))).image
        (fun P => (i, P))
theorem mem_properComponents {n : ℕ} {f : Fin n → Row 3} {i : Fin n}
    {P : Ideal (GeoRow 3)} : (i, P) ∈ properComponents f ↔
    ¬ Whole (f i) ∧ P ∈ (oldCutIdeal (f i)).retainedMinimalPrimes (genericRow (separant (f i))) := by
  classical
  simp only [properComponents, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    by_cases hw : Whole (f k)
    · simp [hw] at hk
    · simp only [hw, ite_false] at hk
      obtain ⟨P', hP', he⟩ := Finset.mem_image.mp hk
      cases he
      exact ⟨hw, hP'⟩
  · rintro ⟨hw, hP⟩
    exact ⟨i, by simpa only [hw, ite_false] using Finset.mem_image.mpr ⟨P, hP, rfl⟩⟩
def componentLength (f : Row 3) (P : Ideal (GeoRow 3)) : ℕ∞ := by
  classical
  exact if hp : P.IsPrime then
    letI := hp
    let A := Localization.AtPrime P
    Module.length A (A ⧸ (oldCutIdeal f).map (algebraMap (GeoRow 3) A))
  else 0
def SimpleInvariant (f : Row 3) (P : Ideal (GeoRow 3)) : Prop :=
  componentLength f P = 1 ∧ genericRow (oldNext f) ∈ P
def nextCutLocus (f : Row 3) (P : Ideal (GeoRow 3)) : Set (Fin 3 → GeometricX) :=
  {y | y ∈ regularLocus f P ∧ MvPolynomial.eval y (genericRow (oldNext f)) = 0}
def reconstruct (f : Row 3) (numerator : Fin taylorLength → GeoRow 4)
    (y : Fin 3 → GeometricX) : Coefficients :=
  fun i => MvPolynomial.eval (graphPoint f y) (numerator i) /
    MvPolynomial.eval y (genericRow (separant f)) ^ (taylorLength - 4)
structure LiftedChart (top : Fin 16) (f : Row 3) where
  cut : GeoRow 4
  next : GeoRow 4
  numerator : Fin taylorLength → GeoRow 4
  graph_box : InLiftedBox (graph f) (graphBox top) 1
  cut_box : InLiftedBox cut (liftedBox top (taylorLength + 1)) (taylorLength - 1)
  next_box : InLiftedBox next (liftedBox top (taylorLength + 2)) taylorLength
  coefficient_box : ∀ i, InLiftedBox (numerator i) (liftedBox top taylorLength) (taylorLength - 2)
  cut_represents : RepresentsOnGraph f (oldCut f) cut
  next_represents : RepresentsOnGraph f (oldNext f) next
  actual : ∀ S : (Polynomial Geom), S.natDegree ≤ physicalDegree → RegularAt 2 f S →
    atJet (oldCut f) S = 0 ∧ atJet (oldNext f) S = 0 ∧
      reconstruct f numerator (jetPoint S) = coefficientPoint S
structure MixedSections (top : Fin 16) {n : ℕ} (f : Fin n → Row 3) (T : ∀ i, LiftedChart top (f i)) where
  length : CurveIndex n → ℕ
  degree : CurveIndex n → ℕ
  length_eq : ∀ a ∈ properComponents f, (length a : ℕ∞) = componentLength (f a.1) a.2
  length_pos : ∀ a ∈ properComponents f, 0 < length a
  total : (∑ a ∈ properComponents f, length a * degree a) ≤ mixedBudget top
  points : ∀ a ∈ properComponents f, genericRow (oldNext (f a.1)) ∉ a.2 →
    (nextCutLocus (f a.1) a.2).Finite ∧ (nextCutLocus (f a.1) a.2).ncard ≤ degree a
  curves : ∀ a ∈ properComponents f, 2 ≤ length a →
    ∃ Q : CoefficientIdeal, Q.IsPrime ∧ (MvPolynomial.affineHilbertPolynomial Q).natDegree ≤ 1 ∧
      0 < degree a ∧ MvPolynomial.affineDegree Q ≤ (degree a : ℚ) ∧
      ∀ y ∈ regularLocus (f a.1) a.2,
        reconstruct (f a.1) (T a.1).numerator y ∈ MvPolynomial.zeroLocus GeometricX Q
structure ActualSolutionCurve (f : Row 3) (Q : CoefficientIdeal) : Prop where
  prime : Q.IsPrime
  dimension : (MvPolynomial.affineHilbertPolynomial Q).natDegree = 1
  solves : ∀ a ∈ MvPolynomial.zeroLocus GeometricX Q,
    extendedAtJet f (coefficientPolynomial a) = 0
  regular : ∃ a ∈ MvPolynomial.zeroLocus GeometricX Q,
    extendedAtJet (separant f) (coefficientPolynomial a) ≠ 0
end
end Low6969Leading_1
end
section
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
namespace Low6969Leading
noncomputable section
variable {top : Fin 16}
open P3 (I K node)
open Low6969Prices (Messages)
open K1_13_5 (NodeCapacity NodeFamily)
open Polynomial ProximityPrize.Benchmark
open scoped BigOperators
theorem agree_pair_le {w Γ s} (h : Messages w Γ s)
    {γ η : K} (hγ : γ ∈ Γ) (hη : η ∈ Γ) (hne : γ ≠ η)
    (sites : Finset I)
    (hγval : ∀ i ∈ sites, (s γ).eval (node i) = w i)
    (hηval : ∀ i ∈ sites, (s η).eval (node i) = w i) :
    sites.card ≤ 133363 := by
  classical
  let diff := s γ - s η
  have hdiff : diff ≠ 0 := sub_ne_zero.mpr (fun heq => hne (h.distinct hγ hη heq))
  have hdeg : diff.natDegree ≤ 133363 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (h.degree γ hγ) (h.degree η hη))
  have hroots : (sites.image node).card ≤ diff.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro a ha
    change a ∈ sites.image node at ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact (Polynomial.mem_roots hdiff).mpr (by simp [diff, hγval i hi, hηval i hi])
  rw [Finset.card_image_of_injective _ IRSProfile.domain.injective] at hroots
  exact hroots.trans hdeg
private theorem count_by_nodes {α ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset α)
    (S : α → Finset ι) {a d : ℕ}
    (hsize : ∀ γ ∈ T, a ≤ (S γ).card)
    (hcap : ∀ i : ι, (T.filter fun γ => i ∈ S γ).card ≤ d) :
    T.card * a ≤ Fintype.card ι * d := by
  classical
  calc
    T.card * a = ∑ _ ∈ T, a := by simp
    _ ≤ ∑ γ ∈ T, (S γ).card := Finset.sum_le_sum hsize
    _ = ∑ γ ∈ T, ∑ i : ι, if i ∈ S γ then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [Finset.sum_boole]
      congr 1
      ext i
      simp
    _ = ∑ i : ι, ∑ γ ∈ T, if i ∈ S γ then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ i : ι, (T.filter fun γ => i ∈ S γ).card := by simp
    _ ≤ ∑ _ : ι, d := Finset.sum_le_sum fun i _ => hcap i
    _ = Fintype.card ι * d := by simp
theorem nodeCapacity_count {w Γ s d} (h : Messages w Γ s)
    (hc : NodeCapacity w Γ s d) : 46377 * Γ.card ≤ 82404 * d + 46377 := by
  classical
  by_cases hsmall : Γ.card ≤ 1
  · omega
  obtain ⟨persistent, hp, hd⟩ := hc
  obtain ⟨γ, hγ, η, hη, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < Γ.card)
  have hpN := agree_pair_le h hγ hη hne persistent
    (fun i hi => hp i hi γ hγ) (fun i hi => hp i hi η hη)
  let U : Finset I := Finset.univ \ persistent
  let hits (γ : K) : Finset I := Finset.univ.filter fun i => (s γ).eval (node i) = w i
  let supports (γ : K) : Finset U := (hits γ \ persistent).subtype (· ∈ U)
  let a : ℕ := 179740 - persistent.card
  let b : ℕ := 133363 - persistent.card
  have hU : Fintype.card U = 262144 - persistent.card := by
    rw [Fintype.card_coe]
    change (Finset.univ \ persistent).card = _
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ persistent), Finset.card_univ]
    change Fintype.card (Fin (2 ^ 18)) - persistent.card = _
    rw [Fintype.card_fin]
    rfl
  have hsubcard (T : Finset I) : ((T \ persistent).subtype (· ∈ U)).card =
      (T \ persistent).card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem]
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hpSub : ∀ γ ∈ Γ, persistent ⊆ hits γ := by
    intro γ hγ i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp i hi γ hγ⟩
  have hsize : ∀ γ ∈ Γ, a ≤ (supports γ).card := by
    intro γ hγ
    obtain ⟨T, hT, hval⟩ := h.hits γ hγ
    have hTsub : T ⊆ hits γ := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hval i hi⟩
    calc
      a ≤ (hits γ).card - persistent.card := Nat.sub_le_sub_right
        (hT.trans (Finset.card_le_card hTsub)) _
      _ = (supports γ).card := by
        dsimp only [supports]
        rw [hsubcard, Finset.card_sdiff_of_subset (hpSub γ hγ)]
  have hpair : ∀ γ ∈ Γ, ∀ η ∈ Γ, γ ≠ η →
      (supports γ ∩ supports η).card ≤ b := by
    intro γ hγ η hη hne
    have heq : supports γ ∩ supports η =
        ((hits γ ∩ hits η) \ persistent).subtype (· ∈ U) := by
      ext i
      simp only [supports, Finset.mem_inter, Finset.mem_subtype, Finset.mem_sdiff]
      exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩,
        fun h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩⟩
    have hsub : persistent ⊆ hits γ ∩ hits η :=
      fun _ hi => Finset.mem_inter.mpr ⟨hpSub γ hγ hi, hpSub η hη hi⟩
    rw [heq, hsubcard, Finset.card_sdiff_of_subset hsub]
    apply Nat.sub_le_sub_right
    exact agree_pair_le h hγ hη hne _
      (fun i hi => (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2)
      (fun i hi => (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2)
  have hcap : ∀ i : U, (Γ.filter fun γ => i ∈ supports γ).card ≤ d := by
    intro i
    have hi := (Finset.mem_sdiff.mp i.property).2
    apply (Finset.card_le_card ?_).trans (hd i.val hi)
    intro γ hγ
    obtain ⟨hγΓ, hγi⟩ := Finset.mem_filter.mp hγ
    exact Finset.mem_filter.mpr
      ⟨hγΓ, (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_subtype.mp hγi)).1).2⟩
  have hincNat := count_by_nodes Γ supports hsize hcap
  let l : ℤ := Γ.card
  let x : ℤ := a
  have hb : (b : ℤ) = x - 46377 := by
    dsimp [b, x, a]
    push_cast [Nat.cast_sub hpN, Nat.cast_sub (hpN.trans (by decide : 133363 ≤ 179740))]
    ring
  have hu : (Fintype.card U : ℤ) = x + 82404 := by
    rw [hU]
    dsimp [x, a]
    push_cast [Nat.cast_sub (hpN.trans (by decide : 133363 ≤ 262144)),
      Nat.cast_sub (hpN.trans (by decide : 133363 ≤ 179740))]
    ring
  have hinc' : l * x ≤ (x + 82404) * (d : ℤ) := by
    rw [← hu]
    dsimp only [l, x]
    exact_mod_cast hincNat
  have hinc : (l - (d : ℤ)) * x ≤ 82404 * d := by nlinarith only [hinc']
  by_contra! hbadNat
  have hbad : 82404 * (d : ℤ) < (l - 1) * 46377 := by
    have hc : 82404 * (d : ℤ) + 46377 < 46377 * l := by
      dsimp only [l]
      exact_mod_cast hbadNat
    linarith only [hc]
  have hd0 : (0 : ℤ) ≤ d := Int.natCast_nonneg _
  have hl0 : (0 : ℤ) < l := by
    dsimp [l]
    exact_mod_cast (show 0 < Γ.card by omega)
  have hk : 0 < l - (d : ℤ) := by linarith only [hbad, hd0]
  have hcoef : 36027 * (d : ℤ) < (l - (d : ℤ)) * 46377 := by linarith only [hbad]
  have hden : 0 < 82404 * 46377 - 36027 * x := by
    have hle := mul_le_mul_of_nonneg_left hinc (by decide : (0 : ℤ) ≤ 36027)
    have hlt := mul_lt_mul_of_pos_right hcoef (by decide : (0 : ℤ) < 82404)
    have hpos : 0 < (l - (d : ℤ)) * (82404 * 46377 - 36027 * x) := by
      nlinarith only [hle, hlt]
    exact pos_of_mul_pos_right hpos hk.le
  have hdenNat : Fintype.card U * b < a * a := by
    have hi : (Fintype.card U : ℤ) * (b : ℤ) < x * x := by
      rw [hu, hb]
      nlinarith only [hden]
    dsimp only [x] at hi
    exact_mod_cast hi
  have hba : b ≤ a := Nat.sub_le_sub_right (by decide : 133363 ≤ 179740) _
  have hj := Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le
    Γ supports a b hsize hpair
  have hjInt : l * ((a * a - Fintype.card U * b : ℕ) : ℤ) ≤
      (Fintype.card U : ℤ) * ((a - b : ℕ) : ℤ) := by
    dsimp only [l]
    exact_mod_cast hj
  push_cast [Nat.cast_sub hba, Nat.cast_sub hdenNat.le] at hjInt
  rw [hu, hb] at hjInt
  have hj' : (l - 1) * 82404 * 46377 ≤ (36027 * l + 46377) * x := by
    nlinarith only [hjInt]
  have hle := mul_le_mul_of_nonneg_left hj' hk.le
  have hle' := mul_le_mul_of_nonneg_left hinc
    (show 0 ≤ 36027 * l + 46377 by linarith only [hl0])
  have hpos := mul_lt_mul_of_pos_left hbad
    (show 0 < 82404 * l by linarith only [hl0])
  nlinarith only [hle, hle', hpos]
theorem nodeFamily_count {w Γ s} (C : NodeFamily w Γ s) (h : Messages w Γ s) :
    46377 * C.labels.card ≤ 82404 * C.totalCap + 46377 * C.n := by
  classical
  calc
    46377 * C.labels.card ≤ 46377 * ∑ i, (C.part i).card :=
      Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ i, 46377 * (C.part i).card := by rw [Finset.mul_sum]
    _ ≤ ∑ i, (82404 * C.cap i + 46377) := by
      exact Finset.sum_le_sum fun i _ => nodeCapacity_count (h.mono (C.sub i)) (C.localCapacity i)
    _ = 82404 * C.totalCap + 46377 * C.n := by
      simp [NodeFamily.totalCap, Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm]
end
end Low6969Leading
end
section
namespace Low6969Leading_1
noncomputable section
variable {top : Fin 16}
open P3 (I K node)
open Low6969Prices (Messages taylorLength physicalDegree)
open Low6969Leading (nodeCapacity_count)
open K1_13 (Geom embed extend)
open K1_13_5 (NodeCapacity)
open K1_13_5_4 (GeometricX GeoRow)
open Polynomial
open scoped BigOperators
private theorem recover_coefficients (S : (Polynomial Geom)) (hS : S.natDegree ≤ physicalDegree) :
    coefficientPolynomial (coefficientPoint S) = S.map (algebraMap Geom GeometricX) := by
  unfold coefficientPolynomial coefficientPoint
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    Polynomial.monomial j (algebraMap Geom GeometricX (S.coeff j)))]
  conv_rhs => rw [Polynomial.as_sum_range' S taylorLength (Nat.lt_succ_of_le hS)]
  simp only [Polynomial.map_sum, Polynomial.map_monomial]
private theorem coefficientPoint_injOn {w Γ s} (h : Messages w Γ s) :
    Set.InjOn (fun γ => coefficientPoint (extend (s γ))) (Γ : Set K) := by
  intro γ hγ δ hδ heq
  apply h.distinct hγ hδ
  apply Polynomial.map_injective embed embed.injective
  apply Polynomial.map_injective (algebraMap Geom GeometricX) (algebraMap Geom GeometricX).injective
  have hdeg : ∀ η ∈ Γ, (extend (s η)).natDegree ≤ physicalDegree := by
    intro η hη
    simpa only [Polynomial.natDegree_map] using h.degree η hη
  rw [← recover_coefficients _ (hdeg _ hγ), ← recover_coefficients _ (hdeg _ hδ)]
  exact congrArg coefficientPolynomial heq
private def valueCut (x y : GeometricX) : GeoRow taylorLength :=
  (∑ j : Fin taylorLength, MvPolynomial.C (x ^ j.val) * MvPolynomial.X j) - MvPolynomial.C y
private theorem totalDegree_valueCut (x y : GeometricX) : (valueCut x y).totalDegree ≤ 1 := by
  unfold valueCut
  apply (MvPolynomial.totalDegree_sub_C_le _ _).trans
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  simpa only [MvPolynomial.totalDegree_C, zero_add, MvPolynomial.totalDegree_X] using
    MvPolynomial.totalDegree_mul (MvPolynomial.C (x ^ j.val)) (MvPolynomial.X j)
private theorem eval_valueCut (a : Coefficients) (x y : GeometricX) :
    MvPolynomial.eval a (valueCut x y) = (coefficientPolynomial a).eval x - y := by
  simp only [valueCut, coefficientPolynomial, map_sub, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  exact congrArg (fun z : GeometricX => z - y) (Finset.sum_congr rfl fun _ _ => mul_comm _ _)
private def constantEmbed : K →+* GeometricX := (algebraMap Geom GeometricX).comp embed
private def nodeCut (w : I → K) (i : I) : GeoRow taylorLength :=
  valueCut (constantEmbed (node i)) (constantEmbed (w i))
private theorem eval_nodeCut_iff {w Γ s} (h : Messages w Γ s) {γ : K} (hγ : γ ∈ Γ) (i : I) :
    MvPolynomial.eval (coefficientPoint (extend (s γ))) (nodeCut w i) = 0 ↔
      (s γ).eval (node i) = w i := by
  have hdeg : (extend (s γ)).natDegree ≤ physicalDegree := by
    simpa only [Polynomial.natDegree_map] using h.degree γ hγ
  rw [nodeCut, eval_valueCut, recover_coefficients _ hdeg, sub_eq_zero]
  unfold constantEmbed
  simp only [RingHom.comp_apply, Polynomial.eval_map_apply]
  exact (algebraMap Geom GeometricX).injective.eq_iff.trans embed.injective.eq_iff
theorem nodeCapacity_of_coefficient_curve {w Γ s} {d : ℕ} (h : Messages w Γ s)
    (Q : CoefficientIdeal) (hp : Q.IsPrime)
    (hdim : (MvPolynomial.affineHilbertPolynomial Q).natDegree ≤ 1)
    (hdegree : MvPolynomial.affineDegree Q ≤ (d : ℚ))
    (hcurve : ∀ γ ∈ Γ, coefficientPoint (extend (s γ)) ∈ MvPolynomial.zeroLocus GeometricX Q) :
    NodeCapacity w Γ s d := by
  classical
  let A := fun γ => coefficientPoint (extend (s γ))
  have hinj : Set.InjOn A (Γ : Set K) := coefficientPoint_injOn h
  by_cases hzero : (MvPolynomial.affineHilbertPolynomial Q).natDegree = 0
  · have bound := MvPolynomial.finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) Q hzero
    have hsub : (↑(Γ.image A) : Set Coefficients) ⊆ MvPolynomial.zeroLocus GeometricX Q := by
      intro a ha
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp ha
      exact hcurve γ hγ
    have hcard := Set.ncard_le_ncard hsub bound.1
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj] at hcard
    have hcard' : (Γ.card : ℚ) ≤ d := (Nat.cast_le.mpr hcard).trans (bound.2.trans hdegree)
    refine ⟨∅, by simp, fun i _ => (Finset.card_filter_le _ _).trans ?_⟩
    exact_mod_cast hcard'
  have hone : (MvPolynomial.affineHilbertPolynomial Q).natDegree = 1 := by omega
  let persistent := Finset.univ.filter fun i => nodeCut w i ∈ Q
  refine ⟨persistent, ?_, ?_⟩
  · intro i hi γ hγ
    have he := hcurve γ hγ (nodeCut w i) (Finset.mem_filter.mp hi).2
    exact (eval_nodeCut_iff h hγ i).mp he
  · intro i hi
    let cut := nodeCut w i
    have hcut : cut ∉ Q := fun hc => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    let J := Q ⊔ Ideal.span {cut}
    have hJ := MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hp hcut (totalDegree_valueCut (constantEmbed (node i)) (constantEmbed (w i)))
    have hjdim : (MvPolynomial.affineHilbertPolynomial J).natDegree = 0 := by
      rw [hone] at hJ
      exact Nat.eq_zero_of_le_zero hJ.1
    have hjdeg : MvPolynomial.affineDegree J ≤ MvPolynomial.affineDegree Q := by
      rw [MvPolynomial.affineDegree_of_natDegree_eq_zero hjdim, MvPolynomial.affineDegree, hone]
      simpa [hone] using hJ.2
    have bound := MvPolynomial.finite_zeroLocus_and_ncard_le_affineDegree (K := GeometricX) J hjdim
    let selected := Γ.filter (fun γ => (s γ).eval (node i) = w i)
    have hsub : (↑(selected.image A) : Set Coefficients) ⊆ MvPolynomial.zeroLocus GeometricX J := by
      intro a ha
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hγ, he⟩ := Finset.mem_filter.mp hγ
      exact MvPolynomial.mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hcurve γ hγ, (eval_nodeCut_iff h hγ i).mpr he⟩
    have hcard := Set.ncard_le_ncard hsub bound.1
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))] at hcard
    have hcard' : (selected.card : ℚ) ≤ d :=
      (Nat.cast_le.mpr hcard).trans (bound.2.trans (hjdeg.trans hdegree))
    exact_mod_cast hcard'
theorem curveCount_le_twice_degree {w Γ s} {d : ℕ} (h : Messages w Γ s) (hd : 0 < d)
    (hc : NodeCapacity w Γ s d) : Γ.card ≤ 2*d := by
  have hcount := nodeCapacity_count h hc
  omega
end
end Low6969Leading_1
end
section
namespace Low6969Leading_1
noncomputable section
variable {top : Fin 16}
open Low6969Prices (physicalDegree taylorLength)
open Low6969Leading (SecondFactors)
open K1_13 (Geom Row atJet indexDegree)
open K1_13_5 (RegularAt separant)
open Low6969Leading (graphBox liftedBox)
open K1_13_5_4 (GeometricX GeoRow InLiftedBox RepresentsOnGraph graph genericCoeff genericRow jetPoint)
open K1_13_5_4_1 (liftRaw liftSep graphRaw thirdVelocityNumerator thirdNumerator
  padJet jetNumerator centre partialFlow_lift generic_graph eval_genericRow graphPoint_of_actual)
open K1_13_7_1 (weight_const_mul_le weight_X_le)
open MvPolynomial
open Polynomial (hasseDeriv)
open scoped BigOperators Polynomial
open K1_13_5_4_1_1 (mul_bound partialFlow_bound liftSep_eq liftedStep_bound generic_bound totalWeight indexWeight topWeight heightWeight lift_weight fits)
open K1_13_5_4_1_2 (represents)
open K1_13_5_4_1 (atJet_padJet taylor_coefficients_aux genericCoeff_ne_zero third_atJet_zero actual_zero_of_represents)
local notation "W" => weightedTotalDegree
private def coefficientNumerator (m : ℕ) (f : Row 3) (i : Fin m) : GeoRow 4 :=
  ∑ j : Fin m, MvPolynomial.C (((Polynomial.X - Polynomial.C centre) ^ j.val).coeff i.val) *
    genericRow (padJet f (m - 4) j.val)
private def cut (m : ℕ) (f : Row 3) : GeoRow 4 := genericRow (thirdNumerator f (m - 3))
private def next (m : ℕ) (f : Row 3) : GeoRow 4 := genericRow (thirdNumerator f (m - 2))
private theorem padded_bound (w : Fin 4 → ℕ) {initial step m : ℕ} {f : Row 3}
    (hinit : ∀ i, w i ≤ initial) (hs : W w (liftSep f) ≤ step)
    (hthird : ∀ k, W w (thirdNumerator f k) ≤ w 3 + k * step) (j : Fin m) :
    W w (padJet f (m - 4) j.val) ≤ initial + (m - 4) * step := by
  unfold padJet jetNumerator
  have hpow := (weightedTotalDegree_pow_le w (liftSep f) (m - 4 - (j.val - 3))).trans
    (Nat.mul_le_mul_left _ hs)
  split_ifs with hj
  · have hz : j.val - 3 = 0 := by omega
    rw [hz, Nat.sub_zero] at hpow ⊢
    exact (mul_bound hpow ((weight_X_le w _).trans (hinit _))).trans_eq (Nat.add_comm _ _)
  · have hsum : (m - 4 - (j.val - 3)) + (j.val - 3) = m - 4 := by
      have hj' := j.isLt
      omega
    calc
      _ ≤ (m - 4 - (j.val - 3)) * step + (w 3 + (j.val - 3) * step) :=
        mul_bound hpow ((weight_const_mul_le w _ _).trans (hthird _))
      _ = w 3 + ((m - 4 - (j.val - 3)) + (j.val - 3)) * step := by ring
      _ ≤ _ := by rw [hsum]; exact Nat.add_le_add_right (hinit 3) _
private theorem weight_bounds (w : Fin 4 → ℕ) (base delta step initial m : ℕ) {f : Row 3}
    (hf : W w (liftRaw f) ≤ base)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + delta)
    (hsep : base - w 2 + delta ≤ step) (hvelocity : base + 2 * delta ≤ w 3 + step)
    (hinit : ∀ i, w i ≤ initial) :
    W w (graph f) ≤ base + delta ∧
    (∀ k, W w (genericRow (thirdNumerator f k)) ≤ w 3 + k * step) ∧
    (∀ i, W w (coefficientNumerator m f i) ≤ initial + (m - 4) * step) := by
  have hg : W w (graphRaw f) ≤ base + delta := by
    rw [← partialFlow_lift]
    exact K1_13_5_4_1_1.partialFlow_bound w hshift hf
  have hs : W w (liftSep f) ≤ base - w 2 := by
    rw [liftSep_eq]
    exact (weightedTotalDegree_pderiv_le_sub w 2 _).trans (Nat.sub_le_sub_right hf _)
  have hu : W w (thirdVelocityNumerator f) ≤ w 3 + step := by
    unfold thirdVelocityNumerator
    exact ((weight_const_mul_le w _ _).trans (K1_13_5_4_1_1.partialFlow_bound w hshift hg)).trans (by omega)
  have hthird (k : ℕ) : W w (thirdNumerator f k) ≤ w 3 + k * step := by
    induction k with
    | zero =>
      simpa only [thirdNumerator, Nat.zero_mul, Nat.add_zero] using weight_X_le (R := (Polynomial Geom)) w 3
    | succ k ih =>
      rw [thirdNumerator, Nat.succ_mul, ← Nat.add_assoc]
      exact liftedStep_bound w hshift ih hs hsep hu k
  refine ⟨?_, fun k => (generic_bound w _).trans (hthird k), ?_⟩
  · rw [← generic_graph]
    exact (generic_bound w _).trans hg
  · intro i
    unfold coefficientNumerator
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.sum_mem
    intro j _
    exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((weight_const_mul_le w _ _).trans ((generic_bound w _).trans
        (padded_bound w hinit (hs.trans ((Nat.le_add_right _ _).trans hsep)) hthird j)))
private theorem fits_lifted {p : GeoRow 4} (L : ℕ)
    (hb : W totalWeight p ≤ 1 + (L - 4) * (Low6969Prices.lowerWidth top))
    (hj : W indexWeight p ≤ 2 + (L - 4) * (Low6969Prices.lowerIndex top + 2))
    (ht : W topWeight p ≤ 1 + (L - 4) * (Low6969Prices.lowerTop top + 2))
    (hh : W heightWeight p ≤ L - 2) :
    InLiftedBox p (liftedBox top L) (L - 2) :=
  fits hb hj ht hh
private theorem support (f : Row 3)
    (hb : f.totalDegree ≤ (Low6969Prices.lowerWidth top)) (hj : indexDegree f ≤ (Low6969Prices.lowerIndex top)) (ht : f.degreeOf 2 ≤ (Low6969Prices.lowerTop top)) :
    InLiftedBox (graph f) (graphBox top) 1 ∧
    InLiftedBox (cut taylorLength f) (liftedBox top (taylorLength + 1)) (taylorLength - 1) ∧
    InLiftedBox (next taylorLength f) (liftedBox top (taylorLength + 2)) taylorLength ∧
    ∀ i, InLiftedBox (coefficientNumerator taylorLength f i) (liftedBox top taylorLength) (taylorLength - 2) := by
  have htotal : W totalWeight (liftRaw f) ≤ (Low6969Prices.lowerWidth top) := by
    rw [lift_weight, show totalWeight ∘ Fin.castSucc = (1 : Fin 3 → ℕ) from by
      funext i; fin_cases i <;> decide, weightedTotalDegree_one]
    exact hb
  have hindex : W indexWeight (liftRaw f) ≤ (Low6969Prices.lowerIndex top) := by
    rw [lift_weight, show indexWeight ∘ Fin.castSucc = (Fin.val : Fin 3 → ℕ) from by
      funext i; fin_cases i <;> decide, ← K1_13_1.indexDegree_eq]
    exact hj
  have htop : W topWeight (liftRaw f) ≤ (Low6969Prices.lowerTop top) := by
    rw [lift_weight, show topWeight ∘ Fin.castSucc = Pi.single (2 : Fin 3) 1 from by
      funext i; fin_cases i <;> decide, weightedTotalDegree_piSingle]
    exact ht
  have hheight : W heightWeight (liftRaw f) ≤ 0 := by
    rw [lift_weight, show heightWeight ∘ Fin.castSucc = (0 : Fin 3 → ℕ) from by
      funext i; fin_cases i <;> decide, weightedTotalDegree, Finset.sup_le_iff]
    intro a _
    simp [Finsupp.weight_eq_sum]
  obtain ⟨bg, bn, bc⟩ := weight_bounds totalWeight (Low6969Prices.lowerWidth top) 0 (Low6969Prices.lowerWidth top) 1 taylorLength htotal
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  obtain ⟨jg, jn, jc⟩ := weight_bounds indexWeight (Low6969Prices.lowerIndex top) 1 (Low6969Prices.lowerIndex top + 2) 2 taylorLength hindex
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  obtain ⟨tg, tn, tc⟩ := weight_bounds topWeight (Low6969Prices.lowerTop top) 1 (Low6969Prices.lowerTop top + 2) 1 taylorLength htop
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  obtain ⟨hg, hn, hc⟩ := weight_bounds heightWeight 0 1 1 1 taylorLength hheight
    (by intro i; fin_cases i <;> decide) (by fin_cases top <;> decide) (by fin_cases top <;> decide)
    (by intro i; fin_cases i <;> decide)
  have hrepl : min (Low6969Prices.lowerTop top + 1) ((Low6969Prices.lowerIndex top + 1) / 2) =
      (Low6969Prices.lowerIndex top + 1) / 2 := by fin_cases top <;> decide
  have hGraphB : W totalWeight (graph f) ≤ Low6969Prices.lowerWidth top := bg
  have hGraphH : W heightWeight (graph f) ≤ 1 := hg
  refine ⟨by simpa only [graphBox, hrepl] using fits hGraphB jg tg hGraphH, ?_, ?_, ?_⟩
  · rw [show taylorLength - 1 = taylorLength + 1 - 2 by decide]
    exact fits_lifted _ ((bn (taylorLength - 3)).trans (by fin_cases top <;> decide))
      ((jn (taylorLength - 3)).trans (by fin_cases top <;> decide))
      ((tn (taylorLength - 3)).trans (by fin_cases top <;> decide))
      ((hn (taylorLength - 3)).trans (by decide))
  · have hh : taylorLength + 2 - 2 = taylorLength := by decide
    simpa only [hh, next] using fits_lifted (taylorLength + 2) ((bn (taylorLength - 2)).trans (by fin_cases top <;> decide))
      ((jn (taylorLength - 2)).trans (by fin_cases top <;> decide))
      ((tn (taylorLength - 2)).trans (by fin_cases top <;> decide))
      ((hn (taylorLength - 2)).trans (by decide))
  · intro i
    exact fits_lifted _ (bc i) (jc i) (tc i) ((hc i).trans (by decide))
private theorem atJet_padded (f : Row 3) (S : (Polynomial Geom)) (hf : atJet f S = 0)
    {m : ℕ} (hm : m < K1.p) (j : Fin m) :
    atJet (padJet f (m - 4) j.val) S =
      atJet (separant f) S ^ (m - 4) * hasseDeriv j.val S := by
  have hj := j.isLt
  exact atJet_padJet f S hf (m - 4) j.val (by omega) (hj.trans hm)
private theorem reconstruct_actual {f : Row 3} {S : (Polynomial Geom)} (hdeg : S.natDegree < taylorLength)
    (hS : RegularAt 2 f S) :
    reconstruct f (coefficientNumerator taylorLength f) (jetPoint S) = coefficientPoint S := by
  funext i
  rw [reconstruct, graphPoint_of_actual hS, eval_genericRow]
  let s := genericCoeff (atJet (separant f) S)
  have hs : s ≠ 0 := genericCoeff_ne_zero hS.2
  have hp : taylorLength < K1.p := by decide
  unfold coefficientNumerator
  rw [map_sum]
  change (∑ j : Fin taylorLength, MvPolynomial.eval (jetPoint S) _) /
    s ^ (taylorLength - 4) = _
  simp only [map_mul, MvPolynomial.eval_C, eval_genericRow, atJet_padded f S hS.1 hp, map_pow]
  change _ = algebraMap Geom GeometricX (S.coeff i)
  rw [div_eq_iff (pow_ne_zero _ hs), ← taylor_coefficients_aux S taylorLength hdeg i.val,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  change _ * (s ^ (taylorLength - 4) * _) = _ * s ^ (taylorLength - 4)
  rw [mul_comm (s ^ (taylorLength - 4)), ← mul_assoc]
private theorem actual {f : Row 3}
    (hcut : RepresentsOnGraph f (oldCut f) (cut taylorLength f))
    (hnext : RepresentsOnGraph f (oldNext f) (next taylorLength f))
    (S : (Polynomial Geom)) (hdeg : S.natDegree ≤ physicalDegree) (hS : RegularAt 2 f S) :
    atJet (oldCut f) S = 0 ∧ atJet (oldNext f) S = 0 ∧
      reconstruct f (coefficientNumerator taylorLength f) (jetPoint S) = coefficientPoint S := by
  have hlength (d m : ℕ) (hd : d < m) (hm : 4 ≤ m) : d - 3 < m - 3 := by omega
  have hdeg' : S.natDegree < taylorLength := Nat.lt_succ_of_le hdeg
  have hfirst := hlength S.natDegree taylorLength hdeg' (by decide)
  have hsecond : S.natDegree - 3 < taylorLength - 2 :=
    hfirst.trans_le (Nat.sub_le_sub_left (by decide : 2 ≤ 3) _)
  refine ⟨actual_zero_of_represents hS hcut ?_, actual_zero_of_represents hS hnext ?_,
    reconstruct_actual hdeg' hS⟩
  · rw [cut, eval_genericRow, third_atJet_zero hS.1 _ hfirst, map_zero]
  · rw [next, eval_genericRow, third_atJet_zero hS.1 _ hsecond, map_zero]
theorem lifted_chart (n : ℕ) (f : Fin n → Row 3) (hf : SecondFactors top f) (i : Fin n) :
    Nonempty (LiftedChart top (f i)) := by
  have hb := (Finset.single_le_sum (f := fun k => (f k).totalDegree)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.total
  have hj := (Finset.single_le_sum (f := fun k => indexDegree (f k))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.index
  have ht := (Finset.single_le_sum (f := fun k => (f k).degreeOf 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hf.coordinate
  obtain ⟨hg, he, hn, hc⟩ := support (f i) hb hj ht
  have hrep : RepresentsOnGraph (f i) (oldCut (f i)) (cut taylorLength (f i)) :=
    represents (f i) (taylorLength - 3)
  have hrep' : RepresentsOnGraph (f i) (oldNext (f i)) (next taylorLength (f i)) :=
    represents (f i) (taylorLength - 2)
  exact ⟨{
    cut := cut taylorLength (f i)
    next := next taylorLength (f i)
    numerator := coefficientNumerator taylorLength (f i)
    graph_box := hg
    cut_box := he
    next_box := hn
    coefficient_box := hc
    cut_represents := hrep
    next_represents := hrep'
    actual := actual hrep hrep'
  }⟩
end
end Low6969Leading_1
end
section
namespace Low6969Leading
noncomputable section
variable {top : Fin 16}
open K1_13 (Geom Row atJet jet indexDegree)
open K1_13_5 (RegularAt)
open Low6969Leading (FirstRow)
open K1_13_5_1
open Low6969Prices (LowerRow TrueWeightLE physicalDegree anchorCutoff lowerWidth lowerIndex lowerTop)
open MvPolynomial UniqueFactorizationMonoid
open scoped Polynomial BigOperators
open K1_13_1 (coeff_flatten)
private theorem trueWeight_iff {n D : ℕ} (P : Row n) :
    TrueWeightLE P D ↔
      ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).weightedTotalDegree
        (fun v => v.elim 1 (fun i => physicalDegree - i.val)) ≤ D := by
  classical
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  constructor
  · intro h u hu
    have hc : (P.coeff u.some).coeff (u none) ≠ 0 := by
      rw [← coeff_flatten, Finsupp.optionElim_some]
      exact MvPolynomial.mem_support_iff.mp hu
    have hm : u.some ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr (fun hz => hc (by simp [hz]))
    have hi := Polynomial.le_natDegree_of_ne_zero hc
    rw [← Finsupp.optionElim_some u, Finsupp.weight_optionElim, one_mul]
    apply (Nat.add_le_add_right hi _).trans
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using h _ hm
  · intro h m hm
    let d := (P.coeff m).natDegree
    have hc : (P.coeff m).coeff d ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    have hu : m.optionElim d ∈ ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).support :=
      MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten])
    have hb := h _ hu
    rw [Finsupp.weight_optionElim, one_mul] at hb
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hb
private theorem increase_budget {a b c C t d : ℕ} (hc : 0 < c) (hC : c ≤ C)
    (ht : a * t ≤ 2 * b) (hd : d + a * c ^ 2 ≤ (2 * c - 1) * b) :
    d + a * c ^ 2 + a * ((C - c) * t) ≤ (2 * C - 1) * b := by
  have hincr := Nat.mul_le_mul_left (C - c) ht
  have he : 2 * C - 1 = (2 * c - 1) + 2 * (C - c) := by omega
  rw [he, Nat.add_mul]
  rw [show a * ((C - c) * t) = (C - c) * (a * t) by ring,
    show 2 * (C - c) * b = (C - c) * (2 * b) by ring]
  exact Nat.add_le_add hd hincr
private theorem aggregate_contracted {ι : Type*} (T : Finset ι) (b c d : ι → ℕ) (B a r : ℕ)
    (hb : ∑ i ∈ T, b i ≤ B) (hc : ∑ i ∈ T, c i ≤ r) (hB : a * r ≤ B)
    (hbase : ∀ i ∈ T, a * c i ≤ b i)
    (hzero : ∀ i ∈ T, c i = 0 → d i ≤ b i)
    (hpos : ∀ i ∈ T, 0 < c i → d i + a * (c i)^2 ≤ (2 * c i - 1) * b i) :
    ∑ i ∈ T, d i ≤ max B ((2 * r - 1) * B - a * r^2) := by
  let C := ∑ i ∈ T, c i
  have hci (i : ι) (hi : i ∈ T) : c i ≤ C := Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) hi
  by_cases hC : C = 0
  · have h := (Finset.sum_le_sum fun i hi => hzero i hi (by have := hci i hi; omega)).trans hb
    exact h.trans (le_max_left _ _)
  have hCpos := Nat.pos_of_ne_zero hC
  have hterm (i : ι) (hi : i ∈ T) : d i + a * (C * c i) ≤ (2 * C - 1) * b i := by
    by_cases hi₀ : c i = 0
    · rw [hi₀, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
      exact (hzero i hi hi₀).trans (by
        simpa using Nat.mul_le_mul_right (b i) (show 1 ≤ 2 * C - 1 by omega))
    · have h := increase_budget (Nat.pos_of_ne_zero hi₀) (hci i hi)
        ((hbase i hi).trans (by omega : b i ≤ 2 * b i)) (hpos i hi (Nat.pos_of_ne_zero hi₀))
      have he : C = c i + (C - c i) := by have := hci i hi; omega
      have hweight : a * (C * c i) = a * (c i)^2 + a * ((C - c i) * c i) := by
        calc
          _ = a * ((c i + (C - c i)) * c i) := congrArg (fun n => a * (n * c i)) he
          _ = _ := by ring
      rw [hweight, ← Nat.add_assoc]
      exact h
  have hs : (∑ i ∈ T, (d i + a * (C * c i))) ≤ (2 * C - 1) * B :=
    (Finset.sum_le_sum hterm).trans (by
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ hb)
  have hjoint : (∑ i ∈ T, d i) + a * C ^ 2 ≤ (2 * C - 1) * B := by
    simp only [Finset.sum_add_distrib, ← Nat.mul_assoc, ← Finset.mul_sum] at hs
    change (∑ i ∈ T, d i) + (a * C) * C ≤ _ at hs
    rwa [Nat.mul_assoc, ← pow_two] at hs
  have ha : a * (r + C) ≤ 2 * B := by
    calc
      _ ≤ a * (r + r) := Nat.mul_le_mul_left _ (Nat.add_le_add_left hc r)
      _ = 2 * (a * r) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 2 hB
  have hfinal := increase_budget hCpos hc ha hjoint
  have he : r = C + (r - C) := by omega
  have hsq : a * C ^ 2 + a * ((r - C) * (r + C)) = a * r ^ 2 := by
    calc
      _ = a * C ^ 2 + a * ((r - C) * ((C + (r - C)) + C)) := by
        exact congrArg (fun n => a * C ^ 2 + a * ((r - C) * (n + C))) he
      _ = a * (C + (r - C)) ^ 2 := by ring
      _ = _ := by rw [← he]
  exact (Nat.le_sub_of_add_le (by simpa only [Nat.add_assoc, hsq] using hfinal)).trans (le_max_right _ _)
theorem factor_cover (g : Row 3) (hg : LowerRow top g) :
    ∃ (n : ℕ) (f : Fin n → Row 3) (q : Row 2), SecondFactors top f ∧ FirstRow top q ∧
      ∀ S : (Polynomial Geom), atJet g S = 0 →
        atJet q S = 0 ∨ ∃ i, RegularAt 2 (f i) S := by
  classical
  obtain ⟨hg₀, hgt₀, hgi₀, hgw⟩ := hg
  let _ : StrongNormalizationMonoid (Row 3) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := normalizedFactors g
  let T := A.toFinset
  let c (f : Row 3) := (view f).natDegree
  let P := T.filter fun f => 0 < c f
  let n := Fintype.card ↥P
  let e : Fin n ≃ ↥P := (Fintype.equivFin ↥P).symm
  let f : Fin n → Row 3 := fun i => (e i).val
  let q : Row 2 := ∏ a ∈ T, elimination a
  have hmem (a : Row 3) (ha : a ∈ T) : a ∈ A := Multiset.mem_toFinset.mp ha
  have hirr (a : Row 3) (ha : a ∈ T) : Irreducible a :=
    irreducible_of_normalized_factor a (hmem a ha)
  have hf (i : Fin n) : f i ∈ T ∧ 0 < c (f i) := Finset.mem_filter.mp (e i).property
  have hdvd : (∏ a ∈ T, a) ∣ g :=
    (Multiset.toFinset_prod_dvd_prod A).trans (prod_normalizedFactors hg₀).dvd
  have hsum (w : Fin 3 → ℕ) :
      (∑ a ∈ T, a.weightedTotalDegree w) ≤ g.weightedTotalDegree w :=
    sum_weightedTotalDegree_le_of_prod_dvd w T id hg₀ hdvd
  have htop (a : Row 3) : c a = a.degreeOf 2 := view_degree a
  have hc : ∑ a ∈ T, c a ≤ lowerTop top := by
    have hbound : g.weightedTotalDegree (fun i => i.val) ≤ lowerIndex top :=
      (K1_13_1.indexDegree_eq g) ▸ hgi₀
    have h : 2 * (∑ a ∈ T, c a) ≤ lowerIndex top := calc
      _ = ∑ a ∈ T, (2 * c a) := Finset.mul_sum T c 2
      _ ≤ ∑ a ∈ T, a.weightedTotalDegree (fun i => i.val) := by
        apply Finset.sum_le_sum
        intro a _
        exact (Nat.le_add_left _ _).trans (view_coeff_weight (fun i => i.val) a (c a) le_rfl)
      _ ≤ _ := (hsum _).trans hbound
    unfold lowerTop
    omega
  have hr : lowerTop top < K1.p := by fin_cases top <;> decide
  have he₀ (a : Row 3) (ha : a ∈ T) : elimination a ≠ 0 := by
    have hca := (Finset.single_le_sum (fun i _ => Nat.zero_le (c i)) ha).trans hc
    exact elimination_ne_zero (hirr a ha) (hca.trans_lt hr)
  have hq (w : Fin 3 → ℕ) (B : ℕ) (hb : g.weightedTotalDegree w ≤ B)
      (hB : w 2 * lowerTop top ≤ B) :
      q.weightedTotalDegree (fun i => w i.castSucc) ≤
        max B ((2 * lowerTop top - 1) * B - w 2 * lowerTop top ^ 2) := by
    let v : Fin 2 → ℕ := fun i => w i.castSucc
    rw [show q = ∏ a ∈ T, elimination a from rfl, weightedTotalDegree_prod v T _ he₀]
    apply aggregate_contracted T (fun a => a.weightedTotalDegree w) c
      (fun a => (elimination a).weightedTotalDegree v) B (w 2) (lowerTop top)
      ((hsum w).trans hb) hc hB
    · intro a _
      exact (Nat.le_add_left _ _).trans (view_coeff_weight w a (c a) le_rfl)
    · intro a _ ha
      exact elimination_weight_zero w a ha
    · intro a _ ha
      exact elimination_weight_positive w a ha
  have hqtotal : q.totalDegree ≤ firstWidth top := by
    have hb : g.totalDegree ≤ lowerWidth top := hgt₀
    have h := hq (1 : Fin 3 → ℕ) (lowerWidth top)
      (by simpa only [weightedTotalDegree_one] using hb)
      (by fin_cases top <;> decide)
    have hv : (fun i : Fin 2 => (1 : Fin 3 → ℕ) i.castSucc) = (1 : Fin 2 → ℕ) := by
      funext i
      simp
    rw [hv, weightedTotalDegree_one, Pi.one_apply, one_mul] at h
    exact h
  have hqindex : indexDegree q ≤ firstIndex top := by
    rw [K1_13_1.indexDegree_eq] at hgi₀ ⊢
    have hbudget : (2 : ℕ) * lowerTop top ≤ lowerIndex top := by
      unfold lowerTop
      omega
    exact hq (fun i => i.val) (lowerIndex top) hgi₀ hbudget
  have hsub (d : Row 3 → ℕ) : (∑ i, d (f i)) ≤ ∑ a ∈ T, d a := by
    calc
      _ = ∑ a : ↥P, d a.val := e.sum_comp _
      _ = ∑ a ∈ P, d a := Finset.sum_coe_sort P d
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  refine ⟨n, f, q, ⟨fun i => hirr _ (hf i).1, fun i => htop _ ▸ (hf i).2, ?_, ?_, ?_, ?_⟩,
    ⟨Finset.prod_ne_zero_iff.mpr he₀, hqtotal, hqindex⟩, ?_⟩
  · intro i
    let E := MvPolynomial.optionEquivRight Geom (Fin 3)
    have hdi := map_dvd E.symm (dvd_of_mem_normalizedFactors (hmem _ (hf i).1))
    have hgn : E.symm g ≠ 0 := fun hz => hg₀ (E.symm.injective (hz.trans (map_zero _).symm))
    exact (trueWeight_iff _).mpr
      ((weightedTotalDegree_le_of_dvd _ hdi hgn).trans ((trueWeight_iff _).mp hgw))
  · exact (hsub _).trans ((by simpa only [weightedTotalDegree_one] using hsum (1 : Fin 3 → ℕ) :
      (∑ a ∈ T, a.totalDegree) ≤ g.totalDegree).trans hgt₀)
  · exact (hsub _).trans ((by simpa only [← K1_13_1.indexDegree_eq] using hsum (fun i => i.val) :
      (∑ a ∈ T, indexDegree a) ≤ indexDegree g).trans hgi₀)
  · simpa only [htop] using (hsub c).trans hc
  · intro S hS
    have hz := map_dvd (eval (jet S)) (prod_normalizedFactors hg₀).symm.dvd
    change atJet g S ∣ eval (jet S) A.prod at hz
    rw [hS, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hz
    obtain ⟨a, ha, hzero⟩ := hz
    have haT : a ∈ T := Multiset.mem_toFinset.mpr ha
    rcases elimination_eval a S hzero with h | ⟨hp, hr⟩
    · left
      change eval (jet S) (∏ a ∈ T, elimination a) = 0
      rw [map_prod]
      exact Finset.prod_eq_zero haT h
    · right
      let j : ↥P := ⟨a, Finset.mem_filter.mpr ⟨haT, hp⟩⟩
      refine ⟨e.symm j, ?_⟩
      change RegularAt 2 ((e (e.symm j)).val) S
      rw [Equiv.apply_symm_apply]
      exact hr
end
end Low6969Leading
end
namespace Low6969LeadingFirst
noncomputable section
variable {top : Fin 16}
open K1_13 MvPolynomial UniqueFactorizationMonoid
open K1_13_5 (RegularAt)
open Low6969Leading (FirstRow FirstFactors firstWidth firstIndex)
open scoped BigOperators Polynomial
private def firstView : Row 2 ≃ₐ[(Polynomial Geom)] (Polynomial (Row 1)) :=
  (renameEquiv (Polynomial Geom) finSuccEquivLast).trans (optionEquivLeft (Polynomial Geom) (Fin 1))
private abbrev valueView : Row 1 ≃ₐ[(Polynomial Geom)] (Polynomial (Polynomial Geom)) :=
  uniqueAlgEquiv (Polynomial Geom) (Fin 1)
private theorem firstView_degree (f : Row 2) : (firstView f).natDegree = f.degreeOf 1 := by
  change (optionEquivLeft _ _ (rename finSuccEquivLast f)).natDegree = f.degreeOf 1
  rw [natDegree_optionEquivLeft]
  exact degreeOf_rename_of_injective finSuccEquivLast.injective (Fin.last 1)
private theorem firstView_pderiv (f : Row 2) :
    firstView (pderiv 1 f) = (firstView f).derivative := by
  change optionEquivLeft _ _ (rename finSuccEquivLast (pderiv 1 f)) =
    (optionEquivLeft _ _ (rename finSuccEquivLast f)).derivative
  rw [← pderiv_rename finSuccEquivLast.injective,
    show finSuccEquivLast (1 : Fin 2) = none from finSuccEquivLast_last,
    optionEquivLeft_pderiv_none]
private theorem valueView_eval (g : Row 1) (S : (Polynomial Geom)) :
    (valueView g).eval S = MvPolynomial.eval (jet S) g := by
  have h := eval₂_uniqueAlgEquiv (f := g) (φ := RingHom.id (Polynomial Geom)) (a := jet S)
  have hzero : jet S (default : Fin 1) = S := by
    change Polynomial.hasseDeriv 0 S = S
    simp
  simpa only [Polynomial.eval₂_id, MvPolynomial.eval₂_id, hzero] using h
private theorem firstView_eval (f : Row 2) (S : (Polynomial Geom)) :
    ((firstView f).map (MvPolynomial.eval (jet S))).eval (jet S (1 : Fin 2)) =
      atJet f S := by
  rw [firstView, AlgEquiv.trans_apply, renameEquiv_apply, ← optionEquivLeft_elim_eval,
    eval_rename, atJet]
  apply congrArg (fun x : Fin 2 → (Polynomial Geom) => MvPolynomial.eval x f)
  funext i
  fin_cases i <;> rfl
private theorem valueView_degree_le (g : Row 1) : (valueView g).natDegree ≤ g.totalDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [valueView, coeff_uniqueAlgEquiv]
  by_contra hn
  have h := le_totalDegree (mem_support_iff.mpr hn)
  change (Finsupp.single (default : Fin 1) k).degree ≤ g.totalDegree at h
  rw [Finsupp.degree_single] at h
  exact (not_le_of_gt hk) h
private theorem firstView_coeff_bound (f : Row 2) (k : ℕ) (hk : k ≤ f.totalDegree) :
    k + (valueView ((firstView f).coeff k)).natDegree ≤ f.totalDegree := by
  change k + (valueView ((optionEquivLeft _ _ (rename finSuccEquivLast f)).coeff k)).natDegree ≤ _
  have hdeg : (rename finSuccEquivLast f).totalDegree = f.totalDegree :=
    totalDegree_renameEquiv finSuccEquivLast f
  have hh := totalDegree_coeff_optionEquivLeft_add_le (Polynomial Geom) (Fin 1)
    (rename finSuccEquivLast f) k
    (by rw [hdeg]; exact hk)
  rw [hdeg] at hh
  exact (Nat.add_le_add_left (valueView_degree_le _) _).trans (by simpa [add_comm] using hh)
private def eliminant (f : Row 2) : (Polynomial (Polynomial Geom)) :=
  let A := firstView f
  if 0 < A.natDegree then
    valueView (A.resultant A.derivative A.natDegree (A.natDegree - 1))
  else valueView (A.coeff 0)
set_option maxHeartbeats 600000 in
private theorem eliminant_spec (f : Row 2) (hf : Irreducible f) (hb : f.totalDegree ≤ (firstWidth top)) :
    eliminant f ≠ 0 ∧ (eliminant f).natDegree ≤ f.totalDegree * ((firstWidth top) - 1) ∧
      ∀ S : (Polynomial Geom), atJet f S = 0 → (eliminant f).eval S = 0 ∨
        (0 < f.degreeOf 1 ∧ RegularAt 1 f S) := by
  let A := firstView f
  let c := A.natDegree
  let b := f.totalDegree
  have hcb : c ≤ b := by
    change (firstView f).natDegree ≤ f.totalDegree
    exact (firstView_degree f).le.trans (f.degreeOf_le_totalDegree 1)
  have hAb : A ≠ 0 := (map_ne_zero_iff _ firstView.injective).mpr hf.ne_zero
  by_cases hc : 0 < c
  · let R := A.resultant A.derivative c (c - 1)
    have hform : eliminant f = valueView R := ite_eq_left hc
    have hcast : (c : Row 1) ≠ 0 := by
      have : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
      have : CharP (Polynomial Geom) K1.p :=
        charP_of_injective_ringHom (Polynomial.C_injective (R := Geom)) K1.p
      have : CharP (Row 1) K1.p :=
        charP_of_injective_ringHom (MvPolynomial.C_injective (σ := Fin 1) (R := (Polynomial Geom))) K1.p
      intro h
      have hp : K1.p ∣ c := (CharP.cast_eq_zero_iff (Row 1) K1.p c).mp h
      exact (not_le_of_gt (hcb.trans_lt (hb.trans_lt (by fin_cases top <;> decide : (firstWidth top) < K1.p))))
        (Nat.le_of_dvd hc hp)
    have hder : A.derivative ≠ 0 := by
      intro h
      have hz := congrArg (fun P : (Polynomial (Row 1)) => P.coeff (c - 1)) h
      rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hc, Polynomial.coeff_zero] at hz
      have hnat : (((c - 1 : ℕ) : Row 1) + 1) = (c : Row 1) := calc
        _ = ((c - 1 + 1 : ℕ) : Row 1) := by rw [Nat.cast_add, Nat.cast_one]
        _ = _ := congrArg (fun k : ℕ => (k : Row 1)) (Nat.sub_add_cancel hc)
      rw [hnat] at hz
      change A.leadingCoeff * (c : Row 1) = 0 at hz
      exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hAb) hcast) hz
    have hR : R ≠ 0 :=
      Polynomial.resultant_derivative_ne_zero_of_irreducible A (hf.map firstView) hder
    have hdeg : (valueView R).natDegree + c ^ 2 ≤ (2 * c - 1) * b := by
      let B := A.map valueView.toRingHom
      have h := Polynomial.natDegree_resultant_derivative_padded_add_sq_le B c b (by
        intro k hk
        rw [Polynomial.coeff_map]
        exact firstView_coeff_bound f k (hk.trans hcb))
      dsimp only [B] at h
      rw [Polynomial.derivative_map, Polynomial.resultant_map_map] at h
      exact h
    have hbudget : (valueView R).natDegree ≤ b * (b - 1) := by
      have hbpos : 1 ≤ b := hc.trans_le hcb
      have hcpos : 1 ≤ 2 * c := by omega
      zify [hbpos, hcpos] at hdeg ⊢
      nlinarith [sq_nonneg ((b : ℤ) - (c : ℤ))]
    refine ⟨by rw [hform]; exact (map_ne_zero_iff _ valueView.injective).mpr hR, ?_, ?_⟩
    · rw [hform]
      exact hbudget.trans (Nat.mul_le_mul_left b (Nat.sub_le_sub_right hb 1))
    · intro S hS
      by_cases hS' : atJet (pderiv 1 f) S = 0
      · left
        rw [hform, valueView_eval]
        exact Polynomial.map_resultant_eq_zero_of_common_root (MvPolynomial.eval (jet S))
          A A.derivative le_rfl (Polynomial.natDegree_derivative_le A) (Or.inl hc.ne')
          (jet S (1 : Fin 2)) ((firstView_eval f S).trans hS) (by
            rw [show A.derivative = firstView (pderiv 1 f) from (firstView_pderiv f).symm]
            exact (firstView_eval _ S).trans hS')
      · exact Or.inr ⟨(firstView_degree f) ▸ hc, hS, hS'⟩
  · have hform : eliminant f = valueView (A.coeff 0) := ite_eq_right hc
    have hAc : A = Polynomial.C (A.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero (Nat.eq_zero_of_not_pos hc).le
    have hA0 : A.coeff 0 ≠ 0 := fun h => hAb (by simpa [h] using hAc)
    refine ⟨by rw [hform]; exact (map_ne_zero_iff _ valueView.injective).mpr hA0, ?_, ?_⟩
    · rw [hform]
      have h := firstView_coeff_bound f 0 (Nat.zero_le _)
      exact (by simpa using h : (valueView (A.coeff 0)).natDegree ≤ b).trans
        (by simpa using Nat.mul_le_mul_left b (by fin_cases top <;> decide : 1 ≤ (firstWidth top) - 1))
    · intro S hS
      left
      have h := (firstView_eval f S).trans hS
      change (A.map _).eval _ = 0 at h
      conv at h => lhs; rw [hAc]
      rw [hform, valueView_eval]
      simpa only [Polynomial.map_C, Polynomial.eval_C] using h
theorem proof (q : Row 2) (hq : FirstRow top q) :
    ∃ (n : ℕ) (f : Fin n → Row 2) (u : (Polynomial (Polynomial Geom))), FirstFactors top f ∧ u ≠ 0 ∧
      u.natDegree ≤ (firstWidth top) * ((firstWidth top) - 1) ∧
      ∀ S : (Polynomial Geom), atJet q S = 0 →
        u.eval S = 0 ∨ ∃ i, RegularAt 1 (f i) S := by
  classical
  let _ : StrongNormalizationMonoid (Row 2) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let M := normalizedFactors q
  let A := M.toFinset
  let T := A.filter fun g => 0 < g.degreeOf 1
  let n := Fintype.card ↥T
  let e : Fin n ≃ ↥T := (Fintype.equivFin ↥T).symm
  let f : Fin n → Row 2 := fun i => (e i).val
  have hA : ∀ g ∈ A, Irreducible g := fun g hg =>
    irreducible_of_normalized_factor g (Multiset.mem_toFinset.mp hg)
  have hdiv : (∏ g ∈ A, g) ∣ q :=
    (Multiset.toFinset_prod_dvd_prod M).trans (prod_normalizedFactors hq.ne_zero).dvd
  have hcap : (∑ g ∈ A, g.totalDegree) ≤ (firstWidth top) := by
    have h := sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 2 → ℕ) A id hq.ne_zero hdiv
    simp only [id_eq, weightedTotalDegree_one] at h
    exact h.trans hq.total
  have hfactor : ∀ i, f i ∈ A ∧ 0 < (f i).degreeOf 1 := fun i =>
    Finset.mem_filter.mp (e i).property
  have hfdiv : (∏ i, f i) ∣ q := by
    rw [show (∏ i, f i) = ∏ g : ↥T, id g.val from e.prod_comp Subtype.val,
      Finset.prod_coe_sort T id]
    exact (Finset.prod_dvd_prod_of_subset T A id (Finset.filter_subset _ _)).trans hdiv
  have hf : FirstFactors top f := by
    refine ⟨fun i => hA _ (hfactor i).1, fun i => (hfactor i).2, ?_, ?_⟩
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 2 → ℕ) Finset.univ f hq.ne_zero hfdiv
      simp only [weightedTotalDegree_one] at h
      exact h.trans hq.total
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (fun i : Fin 2 => i.val)
        Finset.univ f hq.ne_zero hfdiv
      simp only [← K1_13_1.indexDegree_eq] at h
      exact h.trans hq.index
  have hspec (g : Row 2) (hg : g ∈ A) :=
    eliminant_spec g (hA g hg) ((Finset.single_le_sum (fun x _ => Nat.zero_le x.totalDegree) hg).trans hcap)
  let u := ∏ g ∈ A, eliminant g
  refine ⟨n, f, u, hf, Finset.prod_ne_zero_iff.mpr (fun g hg => (hspec g hg).1), ?_, ?_⟩
  · calc
      u.natDegree ≤ ∑ g ∈ A, (eliminant g).natDegree := Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ g ∈ A, g.totalDegree * ((firstWidth top) - 1) := Finset.sum_le_sum fun g hg => (hspec g hg).2.1
      _ ≤ (firstWidth top) * ((firstWidth top) - 1) := by rw [← Finset.sum_mul]; exact Nat.mul_le_mul_right _ hcap
  · intro S hS
    have hroot : MvPolynomial.eval (jet S) M.prod = 0 := by
      have hd := map_dvd (MvPolynomial.eval (jet S)) (prod_normalizedFactors hq.ne_zero).symm.dvd
      change atJet q S ∣ _ at hd
      rwa [hS, zero_dvd_iff] at hd
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hroot
    obtain ⟨g, hgM, hgS⟩ := hroot
    have hgA : g ∈ A := Multiset.mem_toFinset.mpr hgM
    rcases (hspec g hgA).2.2 S hgS with hzero | ⟨hpos, hreg⟩
    · left
      change Polynomial.evalRingHom S u = 0
      rw [show u = ∏ g ∈ A, eliminant g from rfl, map_prod]
      exact Finset.prod_eq_zero_iff.mpr ⟨g, hgA, hzero⟩
    · right
      let j := e.symm ⟨g, Finset.mem_filter.mpr ⟨hgA, hpos⟩⟩
      have hj : f j = g := congrArg Subtype.val (e.apply_symm_apply _)
      exact ⟨j, hj ▸ hreg⟩
end
end Low6969LeadingFirst

section
namespace Low6969Leading
noncomputable section
variable {top : Fin 16}
open P3 (I K node p)
open Low6969Prices (Messages taylorLength)
open K1_13 (Row Geom embed extend indexDegree atJet)
open K1_13_5 (RegularAt NodeCapacity NodeFamily)
open Low6969Leading (FirstFactors)
open K1_13_5_3 (CenterField toCenter constants center chart plane marked toCenter_inj
  marked_injective aeval_plane plane_ne_zero plane_prime chart_degree chart_top
  degreeOf_le_index mem_capped capped_cut_card)
open Polynomial PolynomialDifferential
open scoped BigOperators
open K1_13_5_3 (eval_at_center specialization_flatten)
open K1_13_5_3 (flatten)
private theorem exponent_sufficient : TaylorExponentSufficient 1 taylorLength firstExponent := by
  exact taylorExponentSufficient_firstOrder_tight 133363
private theorem chart_cut_agreement {f : Row 2} {S : (Polynomial Geom)} (hS : RegularAt 1 f S)
    (hD : S.natDegree ≤ 133363) (x y : Geom) :
    MvPolynomial.aeval (marked S)
      (taylorAgreementEquation center (chart f) taylorLength firstExponent (constants x) (constants y))
      = 0 ↔ S.eval x = y := by
  have hsol : differentialSpecialization (chart f) (S.map constants) = 0 := by
    rw [chart, ← map_differentialSpecialization, specialization_flatten, hS.1, Polynomial.map_zero]
  have hsf : differentialSpecialization (PolynomialDifferential.separant (flatten f) 1) S ≠ 0 := by
    change differentialSpecialization
      (MvPolynomial.pderiv (some 1) ((MvPolynomial.optionEquivRight Geom (Fin 2)).symm f)) S ≠ 0
    rw [← MvPolynomial.optionEquivRight_symm_pderiv]
    exact (specialization_flatten (MvPolynomial.pderiv 1 f) S).substr hS.2
  have hsep : jetEvaluation (PolynomialDifferential.separant (chart f) (Fin.last 1))
      center (marked S) ≠ 0 := by
    change jetEvaluation (PolynomialDifferential.separant (chart f) 1) center (marked S) ≠ 0
    rw [marked, ← eval_differentialSpecialization, chart, ← map_separant,
      ← map_differentialSpecialization, eval_at_center]
    exact fun he => hsf (toCenter_inj (he.trans (map_zero _).symm))
  have hdeg : (S.map constants).degree < (taylorLength : WithBot ℕ) := by
    have hb : (S.map constants).natDegree ≤ 133363 := Polynomial.natDegree_map_le.trans hD
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hb)
  have hcharG : CharP Geom P3.p := charP_of_injective_ringHom embed.injective P3.p
  have : CharP CenterField P3.p := charP_of_injective_ringHom constants.injective P3.p
  have hpiv : ∀ i : ℕ, 1 < i → i < taylorLength → (i.choose 1 : CenterField) ≠ 0 := by
    intro i hi ht
    rw [Nat.choose_one_right]
    intro hz
    have hp := Nat.le_of_dvd (by omega : 0 < i)
      ((CharP.cast_eq_zero_iff CenterField P3.p i).mp hz)
    change 0x7f000001 ≤ i at hp
    change i < 133364 at ht
    omega
  rw [taylorAgreementEquation_eq_zero_iff center (chart f) exponent_sufficient (marked S)
      (by rwa [aeval_initialJetSeparant]) (constants x) (constants y)]
  rw [marked, rationalTaylorPolynomial_polynomialJet center (chart f) (S.map constants)
    hsol hsep hdeg hpiv, Polynomial.eval_map_apply, constants.injective.eq_iff]
private theorem plane_capped (f : Row 2) :
    plane f ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      f.totalDegree (indexDegree f) := by
  intro m hm
  have hf := MvPolynomial.support_map_subset toCenter f hm
  exact ⟨MvPolynomial.le_totalDegree hf,
    (MvPolynomial.monomial_le_degreeOf 1 hf).trans (degreeOf_le_index f)⟩
private def nodeCut (w : I → K) (f : Row 2) (i : I) : MvPolynomial (Fin 2) CenterField :=
  taylorAgreementEquation center (chart f) taylorLength firstExponent
    (constants (embed (node i))) (constants (embed (w i)))
private theorem nodeCut_capped (w : I → K) (f : Row 2)
    (hB : f.totalDegree ≤ (firstWidth top)) (hJ : indexDegree f ≤ (firstIndex top)) (i : I) :
    nodeCut w f i ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      (firstChartTotal top) (firstChartTop top) := by
  have ht : (nodeCut w f i).totalDegree ≤ (firstChartTotal top) := by
    refine (totalDegree_taylorAgreementEquation_le center (chart f)
      exponent_sufficient _ _).trans ?_
    exact Nat.add_le_add_left (Nat.mul_le_mul_left firstExponent
      (Nat.sub_le_sub_right ((chart_degree f).trans hB) 1)) 1
  refine mem_capped _ ht (le_min ((MvPolynomial.degreeOf_le_totalDegree _ _).trans ht) ?_)
  exact degreeOf_taylorAgreementEquation_firstOrder_le center (chart f) (firstIndex top)
    taylorLength firstExponent exponent_sufficient
    ((chart_top f).trans ((degreeOf_le_index f).trans hJ)) _ _
private theorem nodeCut_vanishes {w : I → K} {f : Row 2} {S : (Polynomial K)}
    (hreg : RegularAt 1 f (extend S)) (hD : S.natDegree ≤ 133363) (i : I) :
    MvPolynomial.aeval (marked (extend S)) (nodeCut w f i) = 0 ↔
      S.eval (node i) = w i := by
  rw [nodeCut, chart_cut_agreement hreg (Polynomial.natDegree_map_le.trans hD),
    Polynomial.eval_map_apply, embed.injective.eq_iff]
private theorem factor_capacity {w Γ s} (h : Messages w Γ s) (f : Row 2)
    (hf : Irreducible f) (hp : 0 < f.degreeOf 1)
    (hB : f.totalDegree ≤ (firstWidth top)) (hJ : indexDegree f ≤ (firstIndex top))
    (hreg : ∀ γ ∈ Γ, RegularAt 1 f (extend (s γ))) :
    NodeCapacity w Γ s
      (MvPolynomial.cappedDegreeMixedVolume f.totalDegree (indexDegree f) (firstChartTotal top) (firstChartTop top)) := by
  classical
  let P := Ideal.span {plane f}
  let x (γ : K) := marked (extend (s γ))
  have hx : Set.InjOn x (Γ : Set K) := by
    intro γ hγ η hη heq
    exact h.distinct hγ hη (Polynomial.map_injective embed embed.injective (marked_injective heq))
  have hxg : ∀ γ ∈ Γ, MvPolynomial.aeval (x γ) (plane f) = 0 := by
    intro γ hγ
    change MvPolynomial.aeval (marked (extend (s γ))) (plane f) = 0
    rw [aeval_plane, (hreg γ hγ).1, map_zero]
  have hxe (γ : K) (hγ : γ ∈ Γ) (i : I) :
      MvPolynomial.aeval (x γ) (nodeCut w f i) = 0 ↔ (s γ).eval (node i) = w i :=
    nodeCut_vanishes (hreg γ hγ) (h.degree γ hγ) i
  refine ⟨Finset.univ.filter (fun i => nodeCut w f i ∈ P), ?_, ?_⟩
  · intro i hi γ hγ
    apply (hxe γ hγ i).mp
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp (Finset.mem_filter.mp hi).2
    rw [hq, map_mul, hxg γ hγ, zero_mul]
  · intro i hi
    have hi' : nodeCut w f i ∉ P := by
      intro hh
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    let hits := Γ.filter fun γ => (s γ).eval (node i) = w i
    have hh : (hits.image x).card ≤ _ := capped_cut_card (by fin_cases top <;> decide : 0 < (firstChartTotal top))
      (by fin_cases top <;> decide : 0 < (firstChartTop top)) (plane_ne_zero hf.ne_zero) (plane_prime hf hp)
      (plane_capped f) (nodeCut_capped w f hB hJ i) hi' (hits.image x) (by
        intro z hz
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨hm, hh⟩ := Finset.mem_filter.mp hγ
        exact ⟨hxg γ hm, (hxe γ hm i).mpr hh⟩)
    rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hh
theorem first_order_cover {w Γ s} (h : Messages w Γ s)
    {n : ℕ} (f : Fin n → Row 2) (hf : FirstFactors top f)
    (hregular : ∀ γ ∈ Γ, ∃ i, RegularAt 1 (f i) (extend (s γ))) :
    ∃ C : NodeFamily w Γ s, Γ ⊆ C.labels ∧ C.n ≤ (firstWidth top) ∧
      C.totalCap ≤ (firstMixedBudget top) := by
  classical
  let part (i : Fin n) := Γ.filter fun γ => RegularAt 1 (f i) (extend (s γ))
  let cap (i : Fin n) :=
    MvPolynomial.cappedDegreeMixedVolume (f i).totalDegree (indexDegree (f i)) (firstChartTotal top) (firstChartTop top)
  have hsub : ∀ i, part i ⊆ Γ := fun _ => Finset.filter_subset _ _
  have hlocal : ∀ i, NodeCapacity w (part i) s (cap i) := by
    intro i
    apply factor_capacity (h.mono (hsub i)) (f i) (hf.irreducible i) (hf.positive i)
    · exact (Finset.single_le_sum (fun j _ => Nat.zero_le (f j).totalDegree)
        (Finset.mem_univ i)).trans hf.total
    · exact (Finset.single_le_sum (fun j _ => Nat.zero_le (indexDegree (f j)))
        (Finset.mem_univ i)).trans hf.index
    · exact fun γ hγ => (Finset.mem_filter.mp hγ).2
  let C : NodeFamily w Γ s := ⟨n, part, cap, hsub, hlocal⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨i, hi⟩ := hregular γ hγ
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, hi⟩⟩
  · change n ≤ (firstWidth top)
    calc
      n = ∑ _ : Fin n, 1 := by simp
      _ ≤ ∑ i, (f i).totalDegree := Finset.sum_le_sum fun i _ =>
        (Nat.succ_le_of_lt (hf.positive i)).trans (MvPolynomial.degreeOf_le_totalDegree _ _)
      _ ≤ (firstWidth top) := hf.total
  · change (∑ i, cap i) ≤ (firstMixedBudget top)
    simp only [cap, MvPolynomial.cappedDegreeMixedVolume, Finset.sum_add_distrib,
      ← Finset.sum_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right (firstChartTop top) hf.total)
      (Nat.mul_le_mul_right ((firstChartTotal top) - (firstChartTop top)) hf.index)
end
end Low6969Leading
end
section
namespace Low6969Leading
noncomputable section
variable {top : Fin 16}
open P3 (K)
open Low6969Prices (Messages taylorLength lowerCap)
open K1_13 (Row Geom embed extend atJet)
open K1_13_5 (RegularAt NodeFamily mixed3)
open Low6969Leading (lowBox graphBox liftedBox FirstRow)
open Polynomial
open scoped BigOperators
def c1 (top : Fin 16) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ n (f : Fin n → Row 3), SecondFactors top f →
    (∀ γ ∈ Γ, ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ ¬ Whole (f i)) →
    Nonempty (ProperCover top w Γ s)
def c2 (top : Fin 16) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ n (f : Fin n → Row 3), SecondFactors top f →
    (∀ γ ∈ Γ, ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ Whole (f i)) →
    ∃ C : NodeFamily w Γ s, Γ ⊆ C.labels ∧ C.n ≤ Low6969Prices.lowerWidth top ∧ C.totalCap ≤ 133363 * Low6969Prices.lowerWidth top
private theorem roots_card_le {w Γ s} (h : Messages w Γ s) (u : (Polynomial (Polynomial Geom))) (hu : u ≠ 0)
    (hr : ∀ γ ∈ Γ, u.eval (extend (s γ)) = 0) :
    Γ.card ≤ u.natDegree := by
  classical
  let a : K → (Polynomial Geom) := fun γ => extend (s γ)
  have hinj : Set.InjOn a (Γ : Set K) :=
    fun _ hx _ hy heq => h.distinct hx hy (Polynomial.map_injective embed embed.injective heq)
  have hb : (Γ.image a).card ≤ u.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro b hb
    change b ∈ Γ.image a at hb
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hb
    exact (Polynomial.mem_roots hu).mpr (hr γ hγ)
  rw [Finset.card_image_of_injOn hinj] at hb
  exact hb
private theorem first_count {w Γ s} (h : Messages w Γ s)
    (q : Row 2) (hq : FirstRow top q) (hr : ∀ γ ∈ Γ, atJet q (extend (s γ)) = 0) :
    46377 * Γ.card ≤ 82404 * (firstMixedBudget top) + 46377 * ((firstWidth top) * (firstWidth top)) := by
  classical
  obtain ⟨n, f, u, hf, hu, hd, hc⟩ := Low6969LeadingFirst.proof q hq
  let ordinary := Γ.filter fun γ => u.eval (extend (s γ)) = 0
  let regular := Γ.filter fun γ => ∃ i, RegularAt 1 (f i) (extend (s γ))
  have hr₀ : ordinary.card ≤ (firstWidth top) * ((firstWidth top) - 1) :=
    (roots_card_le (h.mono (Finset.filter_subset _ _)) u hu
      (fun _ hγ => (Finset.mem_filter.mp hγ).2)).trans hd
  obtain ⟨C, hC, hn, hcap⟩ := first_order_cover (h.mono (Δ := regular) (Finset.filter_subset _ _)) f hf
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hr₁ := nodeFamily_count C (h.mono (Finset.filter_subset _ _))
  have hr₁' : 46377 * regular.card ≤ 82404 * C.totalCap + 46377 * C.n :=
    (Nat.mul_le_mul_left _ (Finset.card_le_card hC)).trans hr₁
  have covers : Γ ⊆ ordinary ∪ regular := by
    intro γ hγ
    rcases hc _ (hr γ hγ) with ho | hreg
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hreg⟩)
  have htotal := (Finset.card_le_card covers).trans (Finset.card_union_le _ _)
  have hw : 1 ≤ firstWidth top := by fin_cases top <;> decide
  have hs : firstWidth top * (firstWidth top - 1) + firstWidth top =
      firstWidth top * firstWidth top := by
    calc
      _ = firstWidth top * (firstWidth top - 1) + firstWidth top * 1 := by rw [Nat.mul_one]
      _ = _ := by rw [← Nat.mul_add, Nat.sub_add_cancel hw]
  omega
private theorem proper_count {w Γ s} (C : ProperCover top w Γ s) (h : Messages w Γ s) :
    46377 * Γ.card ≤ 46377 * mixedBudget top + (82404 + 2 * 46377) * (invariantBudget top) := by
  classical
  have hm := nodeFamily_count C.multiple h
  have hi := nodeFamily_count C.invariant h
  have hc := (Finset.card_le_card C.cover).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hmix := C.mixed
  have hf := C.fresh
  have hn := C.components
  omega
theorem of_children (h1 : c1 top) (h2 : c2 top) : Low6969Prices.c5 top := by
  classical
  intro w Γ s h g hg hr
  obtain ⟨n, f, q, hf, hq, hc⟩ := factor_cover g hg
  let first := Γ.filter fun γ => atJet q (extend (s γ)) = 0
  let proper := Γ.filter fun γ => ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ ¬ Whole (f i)
  let whole := Γ.filter fun γ => ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ Whole (f i)
  have hfirst := first_count (h.mono (Δ := first) (Finset.filter_subset _ _)) q hq
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hpmsg := h.mono (Δ := proper) (Finset.filter_subset _ _)
  obtain ⟨P⟩ := h1 w proper s hpmsg n f hf (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hproper := proper_count P hpmsg
  have hwmsg := h.mono (Δ := whole) (Finset.filter_subset _ _)
  obtain ⟨W, hW, hn, hcap⟩ := h2 w whole s hwmsg n f hf (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hwhole : 46377 * whole.card ≤ 82404 * W.totalCap + 46377 * W.n :=
    (Nat.mul_le_mul_left _ (Finset.card_le_card hW)).trans (nodeFamily_count W hwmsg)
  have covers : Γ ⊆ first ∪ proper ∪ whole := by
    intro γ hγ
    rcases hc _ (hr γ hγ) with hlow | ⟨i, hreg⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hlow⟩))
    by_cases hw : Whole (f i)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, i, hreg, hw⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hγ, i, hreg, hw⟩))
  have htotal := (Finset.card_le_card covers).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hnumeric : 82404 * (firstMixedBudget top) + 46377 * ((firstWidth top) * (firstWidth top)) +
      (46377 * mixedBudget top + (82404 + 2 * 46377) * (invariantBudget top)) +
      (82404 * (133363 * Low6969Prices.lowerWidth top) + 46377 * Low6969Prices.lowerWidth top) ≤ 46377 * lowerCap top := by
    fin_cases top <;> decide
  omega
end
end Low6969Leading
end
end Z6969Source2408
