import ProximityPrize.SubmissionLower.R6960Low6960SharedTallyNew
import ProximityPrize.SubmissionLower.Fast063
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import ProximityPrize.SubmissionLower.Low6966VariableSelect
import ProximityPrize.SubmissionLower.Shared50OrderDivision
import ProximityPrize.SubmissionLower.Low6966RetainedAssembly
import ProximityPrize.SubmissionLower.Low6966ActiveCycleMixed
import ProximityPrize.SubmissionLower.Low6966SurfaceLinearFour
import ProximityPrize.SubmissionLower.Low6966FastPrice

set_option Elab.async false





-- merged module R6960Low6966SharedChooseCut
section Merged_R6960Low6966SharedChooseCut
set_option Elab.async false
set_option linter.style.haveILetI false
set_option maxRecDepth 12000

namespace Low6966SharedChooseCut
noncomputable section

open K1_13 (Geom Row Shape shape InBox indexDegree)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo pair_height cycleLength_ge_order)
open MvPolynomial
open Low6966SharedPrice (slope coord)

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
    (hQ : ∀ m ∈ Q.support, Low6966ShapeGate.fits r m) (i : Fin 3) :
    coord (shape Q) i ≤ r*coord slope i := by
  rw [weight_coord]
  apply Finset.sup_le
  intro m hm
  have hs := hQ m hm
  fin_cases i
  · exact hs.1
  · exact hs.2.1
  · simpa [Finsupp.weight_eq_sum, Finsupp.sum_fintype, Low6966SharedPrice.coord,
      Low6966SharedPrice.slope, Pi.single_apply] using hs.2.2

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
theorem exists_cut {w Γ s} (hm : Low6966Prices.Messages w Γ s)
    (f : Row 4) (hf : Irreducible f) (hpos : 0<f.totalDegree)
    (multiplicityCap : ℕ) (pivot : Fin 3)
    (hguard : multiplicityCap*coord slope pivot < coord (shape f) pivot)
    (surfaces : Finset (Ideal GeoJets))
    (hp : ∀ P ∈ surfaces, Low6966SharedPersistent.Persistent Γ s P)
    (hh : ∀ P ∈ surfaces, SuitableSurface f multiplicityCap P) :
    ∃ r a : ℕ, 0<r ∧ 0<r-multiplicityCap*a ∧ ∃ G : Row 4, G≠0 ∧ ¬f∣G ∧
      (∀ i, a*coord (shape f) i + coord (shape G) i ≤ r*coord slope i) ∧
      ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f G).IsMinimalPrime P,
        @VanishesTo _ _ P h.isPrime (toGeneric G) (r-multiplicityCap*a) ∧
        ((r-multiplicityCap*a : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f G) P h.isPrime := by
  obtain ⟨r,hr,Q,hQ,hs,ho⟩ := Low6966SharedShapeRank.exists_polynomial hm surfaces hp
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
end Low6966SharedChooseCut

end Merged_R6960Low6966SharedChooseCut

-- merged module R6960Low6966SharedTallyNew
section Merged_R6960Low6966SharedTallyNew

set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
namespace Low6966SharedTallyNew
noncomputable section
open P3 (K)
open K1_13 (Row Shape shape InBox chart)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_2_4 (oldEmbedding)
open K1_13_6_1_2 (VanishesTo cycleLength_ge_order pair_height)
open Low6966GeometryCut (CutInput)
open Low6966GeometryCut_2 (Branch)
open Low6966Prices (taylorLength)
open Low6966SharedPrice (Rate RateFits coord slope deficit weights surface surfaceScale)
open Low6966SharedTally (Data)
open MvPolynomial Finset
open scoped Polynomial BigOperators
open Low6966SharedChooseCut (minimal_pair mem_of_order)

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
    rw [Low6966SharedPrice.surface_ordinary_eq_weights hv] at hrate
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
    have hbound := Low6966SharedCycleFour.bound_with_cut K1_13_6_2_3_1.proof
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
      rw [Low6966SharedPrice.surface_ordinary_eq_weights hv]
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
    (n amount : ℕ) (hn : 0<n) (htilt : Low6966Prices.tiltedFits (shape f))
    (hcut : ∀ b∈F, ∃ h : (intersectionIdeal f G).IsMinimalPrime b.surface,
      (n : ℕ∞) ≤ cycleLength (intersectionIdeal f G) b.surface h.isPrime)
    (hrate : surface .tilted (shape f) (shape G).chamber ≤ 1920*amount*n) :
    tally D F ≤ amount := by
  let p := (shape f).chamber
  let q := (shape G).chamber
  have ht : 1≤p.t := input.small.2.1
  have hq : Low48BentLattice.Chamber (q,0) :=
    ⟨(K1_13_7_1.shape_chamber G).1,(K1_13_7_1.shape_chamber G).2,Nat.zero_le _⟩
  have hfamily := Low6966SharedBentCaps.caps_chamber (K1_13_7_1.shape_chamber f).1 ht htilt.1 hq
  let R := Low48BentCycle.rawFamily (Low6966SharedBentCaps.caps p q)
  let B := Low48BentCycle.capFamily (Low6966SharedBentCaps.caps p q)
  have h := Low6966SharedCycleBound.bound_with_cut (R := R) (B := B)
    Low6966SharedBentCaps.ordinary_doubled f Q G l input.small hproper (fun _ => n)
    (Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩)
    (Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩)
    F D.points (fun b hb => D.bent input (Low6966SharedBentCaps.chart q ht) b (hF hb)) hcut
  have hh := (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℚ)≤60*32)).trans
    (Low6966SharedBentCaps.ordinary_budget hfamily)
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
  have hc := Low6966SharedPrice.chamber_bound hu r a hfit (shape G) hbox (K1_13_7_1.shape_chamber G).2
  have hcap : (weights u.kind (shape f)).b*(shape G).chamber.b +
      (weights u.kind (shape f)).j*(shape G).j + (weights u.kind (shape f)).t*(shape G).t ≤
      surfaceScale u.kind*u.amount*(r-u.split*a) :=
    Nat.le_of_mul_le_mul_left (by simpa only [Nat.mul_assoc] using hc) (by decide : 0<3)
  cases hkind : u.kind
  · apply four_count D input F hF G hproper _ _ hn hv
    · intro b hb
      obtain ⟨h,ho,_⟩ := hcut b hb
      exact ⟨h,ho⟩
    · rw [Low6966SharedPrice.surface_ordinary_eq_weights hv]
      rw [hkind] at hcap
      exact hcap
  · have ht := hu.1 hkind
    apply tilted_count D input F hF G hproper _ _ hn ht
    · intro b hb
      obtain ⟨h,_,hl⟩ := hcut b hb
      exact ⟨h,hl⟩
    · rw [Low6966SharedPrice.surface_tilted_eq_weights hv ht]
      rw [hkind] at hcap
      exact hcap

end
end Low6966SharedTallyNew

end Merged_R6960Low6966SharedTallyNew
