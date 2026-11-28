import ProximityPrize.SubmissionLower.R6960Low6960SharedTallyNew
import ProximityPrize.SubmissionLower.Fast063
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import ProximityPrize.SubmissionLower.Z6969Pack0850
import ProximityPrize.SubmissionLower.Shared50OrderDivision
import ProximityPrize.SubmissionLower.Z6969Pack0838
import ProximityPrize.SubmissionLower.Z6969Pack0837
import ProximityPrize.SubmissionLower.Z6969Pack0836
import ProximityPrize.SubmissionLower.Z6970H2307SharedSurface
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


def Selector : Prop :=
  ∀ {w Γ s}, Low6969Prices.Messages w Γ s →
  ∀ surfaces : Finset (Ideal GeoJets),
  (∀ P ∈ surfaces, Low6969SharedPersistent.Persistent Γ s P) →
  ∃ r : ℕ, 0<r ∧ ∃ Q : Row 4, Q ≠ 0 ∧
    (∀ m ∈ Q.support, Low6969ShapeGate.fits r m) ∧
    ∀ P ∈ surfaces, ∀ a : Fin 4 →₀ ℕ,
      K1_13_6_1_2.multiOrder a < r →
      K1_13_6_1_2.hassePartial a (toGeneric Q) ∈ P

/-- The same independent cut has positive residual order at every selected surface. -/
theorem exists_cut (select : Selector) {w Γ s} (hm : Low6969Prices.Messages w Γ s)
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
  obtain ⟨r,hr,Q,hQ,hs,ho⟩ := select hm surfaces hp
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
      have hl' : (l : ℚ) ≤ w P := by exact_mod_cast Height2307CutEnvelope.cycleWeight_ge hc hp hl
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
theorem cover_precise {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}
    (input : CutInput Γ s f Q l) (surfaces : Finset (Ideal GeoJets)) (R : Row 4)
    (origin : ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P h.isPrime)
    (hwidth : (shape R).b ≤ primaryBox.b)
    (hproper : ∀ P ∈ surfaces, toGeneric R ∉ P)
    (hzero : ∀ γ ∈ Γ, atJet R (extend (s γ)) = 0) :
    ∃ C : Pieces Γ, C.curves s ∧ (∀ i, 0 < C.degree i) ∧
      (∀ γ ∈ Γ, Marked f Q l surfaces (extend (s γ)) → γ ∈ C.union) ∧
      l * C.total ≤ (shape f).b * primaryBox.b * primaryBox.b * chartWidth f ∧
      l * C.n ≤ (shape f).b * primaryBox.b * primaryBox.b := by
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
  refine ⟨blocks, fun i => (square i).1, fun i => (square i).2, ?_, ?_, ?_⟩
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

  · have degOne (a : Σ _ : Ideal GeoJets, Ideal GeoJets) (ha : a ∈ T) :
        (1 : ℚ) ≤ affineDegree a.2 := by
      obtain ⟨hP,hC⟩ := mem_sigma.mp ha
      have hp := (origin a.1 hP).choose
      let := hp.isPrime
      have hc := Ideal.mem_minimalPrimesFinset.mp hC
      have hd := principalCut_natDegree_affineHilbertPolynomial_add_one (hproper a.1 hP) hc
      change dimension a.2 + 1 = dimension a.1 at hd
      rw [(cutCycle input.small input.proper input.box).local_bound a.1 hp |>.1] at hd
      have hdim : dimension a.2 = 1 := by omega
      obtain ⟨d, positive, defEq⟩ := curve_degree_nat a.2 hc.isPrime hdim
      rw [defEq]
      exact_mod_cast Nat.succ_le_of_lt positive
    have hnum : (T.card : ℚ) ≤ ∑ a ∈ T, affineDegree a.2 := by
      calc
        _ = ∑ _a ∈ T, (1 : ℚ) := by simp
        _ ≤ _ := Finset.sum_le_sum degOne
    rw [show T = surfaces.sigma (fun P => (divisorIdeal P R).minimalPrimesFinset) from rfl,
      Finset.sum_sigma] at hnum
    apply (Nat.cast_le (α := ℚ)).mp
    push_cast
    have hdeg := cut_degree input surfaces origin hproper hwidth
    push_cast at hdeg
    exact (mul_le_mul_of_nonneg_left hnum (by positivity)).trans hdeg

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
  obtain ⟨C,hc,hp,hcover,hcost,_⟩ :=
    cover_precise input surfaces R origin hwidth hproper hzero
  exact ⟨C,hc,hp,hcover,hcost⟩

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

theorem count_precise {Γ : Finset K} {s : K → (Polynomial K)} {w : I → K} {f Q : Row 4} {l : ℕ}
    (hmsg : Messages w Γ s) (input : CutInput Γ s f Q l)
    (surfaces : Finset (Ideal GeoJets)) (R : Row 4)
    (origin : ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P h.isPrime)
    (hwidth : (shape R).b ≤ primaryBox.b)
    (hproper : ∀ P ∈ surfaces, toGeneric R ∉ P)
    (hzero : ∀ γ ∈ Γ, atJet R (extend (s γ)) = 0) :
    let assigned := Γ.filter fun γ => Marked f Q l surfaces (extend (s γ))
    assigned.card ≤ preciseFee (shape f) l := by
  classical
  obtain ⟨C,hC,hpos,hcover,hdegree,hnum⟩ := cover_precise input surfaces R origin hwidth hproper hzero
  have hsub : (Γ.filter fun γ => Marked f Q l surfaces (extend (s γ))) ⊆ C.union :=
    fun γ hγ => hcover _ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2
  have hraw : Low6969Prices.incidenceGap * C.union.card ≤
      Low6969Prices.errors * C.total + Low6969Prices.incidenceGap * C.n :=
    Low6969GeometryCut.pieces_curve_capacity C hmsg hC
  have hgap : 0 < Low6969Prices.incidenceGap := by decide
  have hden : 0 < Low6969Prices.incidenceGap * l := Nat.mul_pos hgap input.positive
  have hc := Nat.mul_le_mul_left l hraw
  have htotal := Nat.mul_le_mul_left Low6969Prices.errors hdegree
  have hparts := Nat.mul_le_mul_left Low6969Prices.incidenceGap hnum
  have hbound : (Low6969Prices.incidenceGap * l) * C.union.card ≤
      (Low6969Prices.errors * chartWidth f + Low6969Prices.incidenceGap) *
        ((shape f).b * primaryBox.b * primaryBox.b) := by
    have step := Nat.add_le_add htotal hparts
    calc
      _ = l * (Low6969Prices.incidenceGap * C.union.card) := by ring
      _ ≤ l * (Low6969Prices.errors * C.total + Low6969Prices.incidenceGap * C.n) := hc
      _ = Low6969Prices.errors * (l * C.total) + Low6969Prices.incidenceGap * (l * C.n) := by ring
      _ ≤ _ := step.trans_eq (by ring)
  have quick := count hmsg input surfaces R origin hwidth hproper hzero
  dsimp only at quick ⊢
  unfold preciseFee
  refine le_min quick ((card_le_card hsub).trans ?_)
  unfold K1_13.ceilDiv
  apply (Nat.le_div_iff_mul_le hden).mpr
  rw [Nat.mul_comm C.union.card]
  change (Low6969Prices.incidenceGap * l) * C.union.card ≤
    (Low6969Prices.errors * chartWidth f + Low6969Prices.incidenceGap) *
      ((shape f).b * primaryBox.b * primaryBox.b) + Low6969Prices.incidenceGap * l - 1
  exact hbound.trans (by omega)

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

private theorem count_low (select : Low6969SharedChooseCut.Selector) {w Γ s f Q l}
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
    Low6969SharedChooseCut.exists_cut select hm f input.small.1 hfpos u.split u.pivot hu.2.2.1 P hp hs
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

private theorem cover_split_precise {w Γ s f Q l}
    (hm : Messages w Γ s) (input : CutInput Γ s f Q l) :
    ∃ U : Finset K, U.card ≤ Low6969SharedThirdCut.preciseFee (shape f) l ∧
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
  have hU : U.card≤Low6969SharedThirdCut.preciseFee (shape f) l :=
    Low6969SharedThirdCut.count_precise hm input S R (fun P hP=>(Finset.mem_filter.mp hP).2.2)
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

theorem cover_counts_precise {w Γ s f Q l} (hm : Messages w Γ s)
    (input : CutInput Γ s f Q l) (data : Data Γ s f Q l {P | Persistent Γ s P}) :
    ∃ a c d : ℕ,
      Γ.card ≤ a+c+d+tally data data.branches+Low6969SharedThirdCut.preciseFee (shape f) l ∧
      a ≤ auxiliaryCap (shape f) ∧ l*c ≤ continuedCap (shape f) ∧ d ≤ surfaceCap (shape f) := by
  classical
  obtain ⟨U,hU,hUC⟩ := cover_split_precise hm input
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
  have hCard : Γ.card ≤ a+c+d+tally data data.branches+Low6969SharedThirdCut.preciseFee (shape f) l := by
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
    change F.union.card≤2*(133378*(shape f).b*primaryBox.b)
    have hF' := Low6969GeometryCut.pieces_surface_capacity F hm hF hFP
    change 2*F.total ≤ 133378*(shape f).b*primaryBox.b at hFB
    exact hF'.trans ((show 4*F.total=2*(2*F.total) by ring).le.trans
      (Nat.mul_le_mul_left 2 hFB))
  exact ⟨a,c,d,hCard,hAux,hCurve,hSurface⟩

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
    change F.union.card≤2*(133378*(shape f).b*primaryBox.b)
    have hF' := Low6969GeometryCut.pieces_surface_capacity F hm hF hFP
    change 2*F.total ≤ 133378*(shape f).b*primaryBox.b at hFB
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

theorem proof_of_selector (select : Low6969SharedChooseCut.Selector) : Low6969SharedPrice.cShared := by
  intro w Γ s hm f hf cap hcap hOn l hl hCut u hu
  exact count_of_low hm f hf cap hcap hOn l hl hCut u (fun _ input data => count_low select hm data input u hu)

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




/-- The published floor-plus-one layer identity, with the nonzero remainder required for strict rank. -/
theorem sufficient_rank {rank width need : ℕ} (h : rank/width+1=need)
    (positive_remainder : 0 < rank%width) : width*(need-1)<rank := by
  rw [← h,Nat.add_sub_cancel]
  have total := Nat.mod_add_div rank width
  omega

end
end Low6969RetainedCut

end Merged_R6960Low6969RetainedPhysicalBank

end Z6969Source2407
