import ProximityPrize.SubmissionLower.GoldBranch6N8
import ProximityPrize.SubmissionLower.Final50Price
import ProximityPrize.SubmissionLower.KoalaRetainedCut
import ProximityPrize.SubmissionLower.R6960Low6960Anchor
import ProximityPrize.SubmissionLower.R6960Low6960Fat
import ProximityPrize.SubmissionLower.R6960Low6960Retained

-- merged module Euler50Price
section Merged_Euler50Price

set_option Elab.async false
namespace Euler50Price
noncomputable section
open P3 (I K node)
open K1_13 (Geom extend Row Shape shape Fits InBox Contact chart liftedChart mixed32 ceilDiv atJet
  OnFactor FatEligible OrderAt indexDegree)
open scoped BigOperators Polynomial

abbrev agreement : ℕ := 179925
abbrev physicalDegree : ℕ := 133438
abbrev taylorLength : ℕ := physicalDegree + 1

def ActiveFits (f : Row 4) (K : ℕ) : Prop :=
  ∀ m ∈ f.support, m 0 + 2*m 1 + 2*m 2 + 2*m 3 ≤ K




structure Messages (w : I → K) (Γ : Finset K) (s : K → (Polynomial K)) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  hits : ∀ γ ∈ Γ, ∃ T : Finset I, agreement ≤ T.card ∧ ∀ i ∈ T, (s γ).eval (node i) = w i

theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ ⊆ Γ) : Messages w Δ s :=
  ⟨h.distinct.mono hΔ, fun γ hγ => h.degree γ (hΔ hγ), fun γ hγ => h.hits γ (hΔ hγ)⟩

abbrev BentCap := Shape × ℕ


def bentLift (k : ℕ) (p : Shape) : BentCap :=
  let top := 2 + k * p.t
  (⟨1 + k * (p.b - 1), 4 + k * (p.j - 2), top⟩, min (1 + k) (top / 2))





def evenClip (p : Shape) (h amount : ℕ) : ℕ :=
  let c := min (min amount (p.b - p.j)) (min (p.j / 2) (2 * (p.t - h)))
  c - c % 2

def activeClips (p : Shape) (K : ℕ) : List (ℕ × ℕ) :=
  let c := evenClip p 0 (p.b + p.j - K)
  let g : Shape := ⟨p.b, p.j + 1, p.t + 1⟩
  let lift (k : ℕ) :=
    (k + 1, evenClip (bentLift k p).1 (k + 1) (2 + k * (c - 2)))
  [(0, c), (0, 498), (1, evenClip g 1 c), lift (taylorLength - 4), lift (taylorLength - 3)]



def tiltedFits (x : Shape) : Prop := 3*x.t + 3 ≤ x.j ∧ x.j + 1 ≤ x.b

instance (x : Shape) : Decidable (tiltedFits x) := inferInstanceAs (Decidable (_ ∧ _))

def activeFitsPrice (x : Shape) (K : ℕ) : Prop :=
  3 ≤ x.t ∧ 4 ≤ evenClip x.chamber 0 (x.chamber.b + x.chamber.j - K) ∧
    (activeClips x.chamber K).all (fun c => decide (2*c.1 ≤ c.2)) = true

instance (x : Shape) (K : ℕ) : Decidable (activeFitsPrice x K) :=
  inferInstanceAs (Decidable (_ ∧ _))







end
end Euler50Price

end Merged_Euler50Price

-- merged module Euler50GeoCover
section Merged_Euler50GeoCover
set_option Elab.async false
namespace Euler50GeoLead
open K1_13 (Geom Row shape indexDegree)
open K1_13_1 (topView topView_degree anchorLead anchorLead_ne indexDegree_eq)
open MvPolynomial
open scoped Polynomial
theorem term_weight (P : Row 4) (m : Fin 3 →₀ ℕ) (hm : m ∈ (anchorLead P).support) :
    ∃ u ∈ P.support, ∀ w : Fin 4 → ℕ,
      m.weight (fun i => w i.castSucc) + (shape P).t * w 3 = u.weight w := by
  classical
  let k := (topView P).natDegree
  let c := rename finSuccEquivLast P
  have hc : c.coeff (m.optionElim k) = (anchorLead P).coeff m :=
    (optionEquivLeft_coeff_coeff _ _ _ _).symm
  have hs : m.optionElim k ∈ c.support :=
    mem_support_iff.mpr (by rw [hc]; exact mem_support_iff.mp hm)
  rw [show c = rename finSuccEquivLast P from rfl,
    support_rename_of_injective finSuccEquivLast.injective] at hs
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hs
  refine ⟨u, hu, fun w => ?_⟩
  let w' : Option (Fin 3) → ℕ := fun v => v.elim (w 3) (fun i => w i.castSucc)
  have hlast : finSuccEquivLast (3 : Fin 4) = none := finSuccEquivLast_last
  have hw : ∀ i : Fin 4, w' (finSuccEquivLast i) = w i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [w', hlast, show Fin.last 3 = (3 : Fin 4) by rfl]
    · simp [w']
  have hweight : (m.optionElim k).weight w' = u.weight w := by
    rw [← he]
    simp only [Finsupp.weight_apply, smul_eq_mul]
    rw [Finsupp.sum_mapDomain_index (by simp) (by intros; rw [Nat.add_mul])]
    simp only [hw]
  rw [Finsupp.weight_optionElim] at hweight
  simpa only [w', Option.elim, k, topView_degree, smul_eq_mul, Nat.add_comm, Nat.mul_comm] using hweight
theorem lead_degree (P : Row 4) (hP : P ≠ 0) :
    (anchorLead P).totalDegree + (shape P).t ≤ P.totalDegree := by
  classical
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup _ ((support_nonempty.mpr (anchorLead_ne hP))) (fun m => m.weight (1 : Fin 3 → ℕ))
  obtain ⟨u, hu, hw⟩ := term_weight P m hm
  have h := (hw (1 : Fin 4 → ℕ)).le.trans (le_weightedTotalDegree _ hu)
  rw [← weightedTotalDegree_one, weightedTotalDegree, he, ← weightedTotalDegree_one]
  have hconst : (fun i : Fin 3 => (1 : Fin 4 → ℕ) i.castSucc) = (1 : Fin 3 → ℕ) := rfl
  rw [hconst] at h
  simpa only [Pi.one_apply, Nat.mul_one] using h
theorem lead_index (P : Row 4) (hP : P ≠ 0) :
    indexDegree (anchorLead P) + 3 * (shape P).t ≤ indexDegree P := by
  classical
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.mpr (anchorLead_ne hP)) (fun m => m.weight (fun i : Fin 3 => i.val))
  obtain ⟨u, hu, hw⟩ := term_weight P m hm
  rw [indexDegree_eq, weightedTotalDegree, he, indexDegree_eq]
  simpa [Nat.mul_comm] using (hw (fun i => i.val)).le.trans (le_weightedTotalDegree _ hu)
end Euler50GeoLead
namespace Euler50GeoCover
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K I node)
open Euler50Price (  physicalDegree    ActiveFits)
open K1_13 (Geom embed extend Row shape InBox atJet indexDegree jet OnFactor)
open K1_13_1 (anchorLead anchorLead_ne anchorLead_mul indexDegree_eq eval_anchorLead
  atJet_eq_anchorLead_of_top_zero)
open scoped BigOperators Polynomial
open K1_13_1 (coeff_flatten anchorLead_term index_bounds)
def activeDegree (f : Row 4) : ℕ :=
  MvPolynomial.weightedTotalDegree (![1, 2, 2, 2] : Fin 4 → ℕ) f
private theorem activeWeight_at (m : Fin 4 →₀ ℕ) :
    m.weight (![1, 2, 2, 2] : Fin 4 → ℕ) = m 0 + 2*m 1 + 2*m 2 + 2*m 3 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, smul_eq_mul, Nat.mul_comm]
theorem activeFits_iff (f : Row 4) (K : ℕ) : ActiveFits f K ↔ activeDegree f ≤ K := by
  unfold ActiveFits activeDegree MvPolynomial.weightedTotalDegree
  rw [Finset.sup_le_iff]
  simp only [activeWeight_at]
section FactorCover
open MvPolynomial UniqueFactorizationMonoid
end FactorCover
end
end Euler50GeoCover

end Merged_Euler50GeoCover

-- merged module Final50GeoCover
section Merged_Final50GeoCover

set_option Elab.async false
namespace Final50GeoCover
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K I node)
open Final50Price (TrueWeightLE anchorCutoff physicalDegree Fits  SmallFactor ActiveFits)
open K1_13 (Geom embed extend Row shape InBox atJet indexDegree jet OnFactor)
open K1_13_1 (anchorLead anchorLead_ne anchorLead_mul indexDegree_eq eval_anchorLead
  atJet_eq_anchorLead_of_top_zero)
open scoped BigOperators Polynomial
open K1_13_1 (coeff_flatten anchorLead_term index_bounds)

abbrev activeDegree := Euler50GeoCover.activeDegree

theorem activeFits_iff (f : Row 4) (K : ℕ) : ActiveFits f K ↔ activeDegree f ≤ K :=
  Euler50GeoCover.activeFits_iff f K

theorem trueWeight_iff {n D : ℕ} (P : Row n) :
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
section FactorCover
open MvPolynomial UniqueFactorizationMonoid
end FactorCover

end
end Final50GeoCover

end Merged_Final50GeoCover

-- merged module KoalaRetainedWitness
section Merged_KoalaRetainedWitness
set_option autoImplicit false
set_option Elab.async false
namespace KoalaRetainedCut
noncomputable section
open MvPolynomial
open K1_13 (Row Geom Shape shape InBox OrderAt atJet extend embed indexDegree)
open Final50Price (primaryBox primaryCutoff TrueWeightLE ActiveFits physicalDegree)
open P0_9_3_2 (translateTop topHasse topHasse_zero topHasse_coeff source_support sum_add_top total_add_top apply_add_top erase_top_add topHasse_order exact_hasse_not_dvd)
open scoped Polynomial BigOperators
def residualBox (h : Shape) (l : ℕ) : Shape :=
  ⟨primaryBox.b-l*h.b, primaryBox.j-l*h.j, primaryBox.t-l*h.t⟩
private theorem wdegree_pow (w : Fin 4 → ℕ) {H : Row 4} (hn : H ≠ 0) (k : ℕ) :
    (H^k).weightedTotalDegree w = k*H.weightedTotalDegree w := by
  induction k with
  | zero => rw [pow_zero,zero_mul,← MvPolynomial.C_1,weightedTotalDegree_C]
  | succ k ih => rw [pow_succ,weightedTotalDegree_mul _ _ _ (pow_ne_zero k hn) hn,ih,Nat.succ_mul]
theorem residual_box {H G : Row 4} {v l : ℕ} (hv : l ≤ v)
    (hH : H ≠ 0) (hG : G ≠ 0) (hb : InBox (shape (H^v*G)) primaryBox) :
    InBox (shape G) (residualBox (shape H) l) := by
  have bound (w : Fin 4 → ℕ) {cap : ℕ} (hc : (H^v*G).weightedTotalDegree w ≤ cap) :
      G.weightedTotalDegree w ≤ cap - l*H.weightedTotalDegree w := by
    rw [weightedTotalDegree_mul _ _ _ (pow_ne_zero v hH) hG,wdegree_pow _ hH] at hc
    have hs := Nat.mul_le_mul_right (H.weightedTotalDegree w) hv
    omega
  have hb₁ : (H^v*G).totalDegree ≤ primaryBox.b := hb.1
  have hb₂ : indexDegree (H^v*G) ≤ primaryBox.j := hb.2.1
  have hb₃ : (H^v*G).degreeOf 3 ≤ primaryBox.t := hb.2.2
  rw [← weightedTotalDegree_one] at hb₁
  rw [K1_13_1.indexDegree_eq] at hb₂
  rw [← weightedTotalDegree_piSingle] at hb₃
  refine ⟨?_, ?_, ?_⟩
  · change G.totalDegree ≤ primaryBox.b-l*H.totalDegree
    simpa only [weightedTotalDegree_one] using bound (1 : Fin 4 → ℕ) hb₁
  · change indexDegree G ≤ primaryBox.j-l*indexDegree H
    simpa only [← K1_13_1.indexDegree_eq] using bound Fin.val hb₂
  · change G.degreeOf 3 ≤ primaryBox.t-l*H.degreeOf 3
    simpa only [weightedTotalDegree_piSingle] using bound (Pi.single (3 : Fin 4) 1) hb₃
private theorem weight_of_factor {P G : Row 4} {D : ℕ} (hP : P ≠ 0) (hG : G ∣ P)
    (hw : TrueWeightLE P D) : TrueWeightLE G D := by
  let e := MvPolynomial.optionEquivRight Geom (Fin 4)
  have hd := map_dvd e.symm.toRingHom hG
  have hn : e.symm P ≠ 0 := fun h => hP (e.symm.injective (h.trans (map_zero _).symm))
  exact (Final50GeoCover.trueWeight_iff G).mpr <|
    (weightedTotalDegree_le_of_dvd _ hd hn).trans ((Final50GeoCover.trueWeight_iff P).mp hw)
private theorem topHasse_bounds (box : Shape) (T a : ℕ) (P : Row 4)
    (hb : InBox (shape P) box) (hw : TrueWeightLE P T) :
    InBox (shape (topHasse a P)) box ∧ TrueWeightLE (topHasse a P) T := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change (topHasse a P).totalDegree ≤ box.b
    apply Finset.sup_le
    intro m hm
    have hp := (MvPolynomial.le_totalDegree (source_support hm)).trans hb.1
    rw [total_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change indexDegree (topHasse a P) ≤ box.j
    apply Finset.sup_le
    intro m hm
    have hp := (Finset.le_sup (f := fun u : Fin 4 →₀ ℕ => u.sum (fun i k => i.val * k))
      (source_support hm)).trans hb.2.1
    rw [sum_add_top Fin.val] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change (topHasse a P).degreeOf 3 ≤ box.t
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have hp := (MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)).trans hb.2.2
    rw [apply_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · intro m hm
    have hp := hw _ (source_support hm)
    rw [sum_add_top (fun i => physicalDegree - i.val)] at hp
    rw [topHasse_coeff]
    have hc := Polynomial.natDegree_mul_le
      (p := (↑((m 3 + a).choose a) : (Polynomial Geom))) (q := P.coeff (m + Finsupp.single 3 a))
    rw [Polynomial.natDegree_natCast, zero_add] at hc
    exact (Nat.add_le_add_right hc _).trans ((Nat.add_le_add_left (Nat.le_add_right _ _) _).trans hp)
private theorem topHasse_one_not_dvd (f : Row 4) (hf : Irreducible f)
    (hpos : 0 < f.degreeOf 3) (hsmall : f.degreeOf 3 < K1.p) : ¬ f ∣ topHasse 1 f := by
  classical
  have hdeg : (topHasse 1 f).degreeOf 3 ≤ f.degreeOf 3 - 1 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have h := MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)
    rw [apply_add_top] at h
    omega
  have hnz : topHasse 1 f ≠ 0 := by
    have hsup : 0 < f.support.sup (fun m => m (3 : Fin 4)) := by
      rwa [← MvPolynomial.degreeOf_eq_sup]
    obtain ⟨u, hu, htop⟩ := (Finset.le_sup_iff hsup).mp (le_refl _)
    rw [← MvPolynomial.degreeOf_eq_sup] at htop
    have hupos : 0 < u 3 := hpos.trans_le htop
    have hult : u 3 < K1.p := (MvPolynomial.le_degreeOf_of_mem_support 3 hu).trans_lt hsmall
    let m := u.erase 3 + Finsupp.single 3 (u 3 - 1)
    have hsum : m + Finsupp.single 3 1 = u := by
      dsimp [m]
      rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel hupos, erase_top_add]
    have hm : m 3 + 1 = u 3 := by
      rw [← apply_add_top, hsum]
    have hc : (↑(u 3) : (Polynomial Geom)) ≠ 0 := by
      have : CharP Geom K1.p :=
        charP_of_injective_ringHom (RingHom.injective embed) K1.p
      intro hz
      have hz' : (↑(u 3) : Geom) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg (Polynomial.evalRingHom (0 : Geom)) hz
      exact (not_le_of_gt hult)
        (Nat.le_of_dvd hupos ((CharP.cast_eq_zero_iff Geom K1.p _).mp hz'))
    have hcoeff : (topHasse 1 f).coeff m ≠ 0 := by
      rw [topHasse_coeff, hm, hsum, Nat.choose_one_right]
      exact mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hu)
    intro hz
    exact hcoeff (by rw [hz]; rfl)
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro h
    exact hnz (by rw [hg, h, mul_zero])
  have h := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.ne_zero hg0
  rw [hg, h] at hdeg
  omega
theorem exists_divided_cut {P H f : Row 4} {k a l A : ℕ} (hP : P ≠ 0) (hH : H ≠ 0)
    (hf : Irreducible f) (htop : 0 < f.degreeOf 3) (hchar : f.degreeOf 3 < K1.p)
    (hc : IsRelPrime f H) (hl : l ≤ k-a)
    (hb : InBox (shape P) primaryBox) (hw : TrueWeightLE P primaryCutoff)
    (hactive : ActiveFits P A) (divH : H^k ∣ P) (divF : f^a ∣ P) (exactF : ¬ f^(a+1) ∣ P) :
    ∃ Q : Row 4, (¬ f ∣ Q) ∧ InBox (shape Q) (residualBox (shape H) l) ∧
      TrueWeightLE Q primaryCutoff ∧ ActiveFits Q A ∧
      ∀ S : (Polynomial Geom), atJet H S ≠ 0 → OrderAt P S k → OrderAt Q S l := by
  obtain ⟨G,rfl⟩ := divH
  have hn : G ≠ 0 := right_ne_zero_of_mul hP
  have hGb := residual_box (hl.trans (Nat.sub_le k a)) hH hn hb
  have hGw := weight_of_factor hP (dvd_mul_left G (H^k)) hw
  have hdiv : f^a ∣ G := hc.pow.dvd_of_dvd_mul_left divF
  have hnext : ¬ f^(a+1) ∣ G := fun hd => exactF (hd.trans (dvd_mul_left G _))
  have hnd := exact_hasse_not_dvd translateTop topHasse_zero f G a
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf)
    (topHasse_one_not_dvd f hf htop hchar) hdiv hnext
  obtain ⟨boxQ,weightQ⟩ := topHasse_bounds _ _ a G hGb hGw
  have hactiveG : ActiveFits G A := (Final50GeoCover.activeFits_iff G A).mpr
    ((weightedTotalDegree_le_of_dvd _ (dvd_mul_left G (H^k)) hP).trans
      ((Final50GeoCover.activeFits_iff _ A).mp hactive))
  have hactiveQ : ActiveFits (topHasse a G) A := by
    intro m hm
    have hh := hactiveG _ (source_support hm)
    simp [Finsupp.add_apply] at hh
    omega
  refine ⟨topHasse a G,hnd,boxQ,weightQ,hactiveQ,?_⟩
  intro S hS hPS m hm
  have hor := orderAt_off_quotient hS hPS
  exact hl.trans (topHasse_order a k G S hor m hm)
theorem retained_power_dvd {ι : Type*} [Fintype ι] [DecidableEq ι] (z : Finset ι)
    (f : ι → Row 4) (hfi : ∀ i, Irreducible (f i))
    (hdis : ∀ i j, i ≠ j → ¬ Associated (f i) (f j))
    {P : Row 4} {k : ℕ} (hdiv : ∀ i ∈ z, f i ^ k ∣ P) : (∏ i ∈ z, f i)^k ∣ P := by
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_isRelPrime
  · intro i _ j _ hij
    exact ((hfi i).isRelPrime_iff_not_dvd.mpr
      (fun hd => hdis i j hij ((hfi i).associated_of_dvd (hfi j) hd))).pow
  · exact hdiv
theorem prime_off_product {ι : Type*} [DecidableEq ι] (z : Finset ι)
    (f : ι → Row 4) (hfi : ∀ i, Irreducible (f i))
    (hdis : ∀ i j, i ≠ j → ¬ Associated (f i) (f j))
    {i : ι} (hi : i ∉ z) : IsRelPrime (f i) (∏ j ∈ z, f j) := by
  apply IsRelPrime.prod_right
  intro j hj
  exact (hfi i).isRelPrime_iff_not_dvd.mpr
    (fun hd => hdis i j (fun eq => hi (eq ▸ hj)) ((hfi i).associated_of_dvd (hfi j) hd))
#print axioms residual_box
#print axioms exists_divided_cut
#print axioms retained_power_dvd
end
end KoalaRetainedCut

end Merged_KoalaRetainedWitness

-- merged module KoalaRetainedCover
section Merged_KoalaRetainedCover
set_option autoImplicit false
set_option Elab.async false
namespace KoalaRetainedCut
noncomputable section
open P3 (K)
open K1_13 (Geom Row shape topLead atJet jet extend OnFactor)
open K1_13_1 (anchorLead anchorLead_mul eval_anchorLead atJet_eq_anchorLead_of_top_zero)
open UniqueFactorizationMonoid MvPolynomial
open scoped Polynomial BigOperators
theorem anchor_factors {P : Row 4} (hP : P ≠ 0) :
    ∃ (n : ℕ) (f : Fin n → Row 4),
      (∀ i, Irreducible (f i) ∧ 0 < (shape (f i)).t ∧ f i ∣ P) ∧
      (∀ i j, i ≠ j → ¬ Associated (f i) (f j)) ∧ (∏ i, f i) ∣ P ∧
      ∀ S : (Polynomial Geom), atJet P S = 0 → atJet (anchorLead P) S = 0 ∨ ∃ i, OnFactor (f i) S := by
  classical
  let _ : StrongNormalizationMonoid (Row 4) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := normalizedFactors P
  let T := A.toFinset.filter fun q => 0 < (shape q).t
  let n := Fintype.card ↥T
  let e : Fin n ≃ ↥T := (Fintype.equivFin ↥T).symm
  let f : Fin n → Row 4 := fun i => (e i).val
  have hT (q) (hq : q ∈ T) : q ∈ A ∧ 0 < (shape q).t := by simpa [T] using hq
  have hfi (i : Fin n) : f i ∈ A ∧ 0 < (shape (f i)).t := hT _ (e i).property
  refine ⟨n,f,fun i => ⟨irreducible_of_normalized_factor _ (hfi i).1,(hfi i).2,
    dvd_of_mem_normalizedFactors (hfi i).1⟩,?_,?_,?_⟩
  · intro i j hij hassoc
    apply hij
    apply e.injective
    exact Subtype.ext (mem_normalizedFactors_eq_of_associated (hfi i).1 (hfi j).1 hassoc)
  · have heq : (∏ i, f i) = ∏ q ∈ T, q := by
      rw [show (∏ i, f i) = ∏ q : ↥T, q.val from e.prod_comp Subtype.val]
      exact Finset.prod_coe_sort T id
    rw [heq]
    exact ((Finset.prod_dvd_prod_of_subset T A.toFinset id (Finset.filter_subset _ _)).trans
      (Multiset.toFinset_prod_dvd_prod A)).trans (prod_normalizedFactors hP).dvd
  · intro S hz
    by_cases hg : atJet (anchorLead P) S = 0
    · exact Or.inl hg
    right
    have hSA : MvPolynomial.eval (jet S) A.prod = 0 := by
      have hdiv := _root_.map_dvd (MvPolynomial.eval (jet S)) (prod_normalizedFactors hP).symm.dvd
      change atJet P S ∣ MvPolynomial.eval (jet S) A.prod at hdiv
      rw [hz,zero_dvd_iff] at hdiv
      exact hdiv
    rw [map_multiset_prod,Multiset.prod_eq_zero_iff,Multiset.mem_map] at hSA
    obtain ⟨q,hq,hqS⟩ := hSA
    have hqlead : atJet (anchorLead q) S ≠ 0 := by
      intro hzero
      obtain ⟨R,hR⟩ := dvd_of_mem_normalizedFactors hq
      apply hg
      rw [hR,anchorLead_mul,atJet,map_mul]
      exact mul_eq_zero_of_left hzero _
    have hqt : 0 < (shape q).t := by
      by_contra! h
      apply hqlead
      rw [← atJet_eq_anchorLead_of_top_zero q S (Nat.eq_zero_of_le_zero h)]
      exact hqS
    have hqT : q ∈ T := Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hq,hqt⟩
    let j := e.symm ⟨q,hqT⟩
    have hj : f j = q := congrArg Subtype.val (e.apply_symm_apply ⟨q,hqT⟩)
    exact ⟨j,by rw [hj,OnFactor,← eval_anchorLead]; exact ⟨hqS,hqlead⟩⟩
theorem topLead_off_lower {P f : Row 4} {S : (Polynomial Geom)} (h : f ∣ P)
    (hoff : atJet (anchorLead P) S ≠ 0) : topLead f S ≠ 0 := by
  obtain ⟨G,rfl⟩ := h
  rw [anchorLead_mul,atJet,map_mul] at hoff
  rw [← eval_anchorLead]
  exact left_ne_zero_of_mul hoff
theorem priority_pieces {n : ℕ} {P : Row 4} {f : Fin n → Row 4} (hdiv : ∀ i, f i ∣ P)
    {Γ : Finset K} (s : K → (Polynomial K)) (book : Finset K) (z : Finset (Fin n))
    (hbase : ∀ γ ∈ Γ, atJet (anchorLead P) (extend (s γ)) = 0 ∨ ∃ i, OnFactor (f i) (extend (s γ))) :
    ∃ (low : Finset K) (piece : Fin n → Finset K),
      low ⊆ Γ ∧ (∀ γ ∈ low, atJet (anchorLead P) (extend (s γ)) = 0) ∧
      (∀ i, piece i ⊆ Γ) ∧ (∀ i γ, γ ∈ piece i → γ ∉ book ∧ OnFactor (f i) (extend (s γ))) ∧
      (∀ i ∉ z, ∀ γ ∈ piece i, atJet (∏ j ∈ z, f j) (extend (s γ)) ≠ 0) ∧
      Γ.card ≤ book.card + low.card + ∑ i, (piece i).card := by
  classical
  let S (γ : K) := extend (s γ)
  let H := ∏ j ∈ z, f j
  let low := Γ.filter (fun γ => atJet (anchorLead P) (S γ)=0)
  let piece (i : Fin n) := Γ.filter (fun γ => γ∉book ∧ OnFactor (f i) (S γ) ∧
    (i∈z ∨ atJet H (S γ) ≠ 0))
  refine ⟨low,piece,Finset.filter_subset _ _,fun γ h => (Finset.mem_filter.mp h).2,
    fun i => Finset.filter_subset _ _,fun i _ h => ⟨(Finset.mem_filter.mp h).2.1,
      (Finset.mem_filter.mp h).2.2.1⟩,fun i hi _ h => (Finset.mem_filter.mp h).2.2.2.resolve_left hi,?_⟩
  have full : Γ ⊆ book ∪ low ∪ Finset.univ.biUnion piece := by
    intro γ hγ
    by_cases hb : γ∈book
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
    by_cases hg : atJet (anchorLead P) (S γ)=0
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ,hg⟩))
    apply Finset.mem_union_right
    by_cases hH : atJet H (S γ)=0
    · have hp : ∏ j∈z, atJet (f j) (S γ) = 0 := by
        simpa only [H,atJet,map_prod] using hH
      obtain ⟨i,hi,hzero⟩ := Finset.prod_eq_zero_iff.mp hp
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr
        ⟨hγ,hb,⟨hzero,topLead_off_lower (hdiv i) hg⟩,Or.inl hi⟩⟩
    · obtain ⟨i,hon⟩ := (hbase γ hγ).resolve_left hg
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr
        ⟨hγ,hb,hon,Or.inr hH⟩⟩
  exact (Finset.card_le_card full).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le))
#print axioms anchor_factors
#print axioms priority_pieces
end
end KoalaRetainedCut

end Merged_KoalaRetainedCover

-- merged module R6960Low6960Inventory
section Merged_R6960Low6960Inventory
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
namespace Lower6960.Low
noncomputable section
open Finset Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K I node)
open K1_13 (Geom extend Row Shape shape InBox atJet indexDegree OnFactor)
open K1_13_1 (anchorLead anchorLead_ne indexDegree_eq)
open Final50Price (ActiveFits)
open Final50GeoCover (activeDegree activeFits_iff)
open K1_13_1 (coeff_flatten anchorLead_term index_bounds)
open scoped BigOperators Polynomial Classical
abbrev anchorCutoff : ℕ := 105*agreement-1+59
def fullCap (top : ℕ) : Shape := ⟨141, 59, top⟩
def Fits (top : ℕ) {n : ℕ} (a : Fin n → Shape) : Prop :=
  (∀ i, K1_13_8.Valid (a i)) ∧ (∑ i, (a i).b) ≤ 141 ∧ (∑ i, (a i).j) ≤ 59 ∧
    (∑ i, (a i).t) ≤ top
def LowerRow (top : ℕ) (g : Row 3) : Prop :=
  g≠0 ∧ g.totalDegree≤141-top ∧ indexDegree g≤59-3*top ∧ TrueWeightLE g anchorCutoff
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0<(shape f).t ∧ InBox (shape f) (fullCap 14) ∧ TrueWeightLE f anchorCutoff
theorem trueWeight_iff {n D : ℕ} (P : Row n) :
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
theorem differentialWeight_eq : differentialWeight (d := 3) physicalDegree =
    fun v => v.elim 1 (fun i => physicalDegree - i.val) := by
  funext v
  cases v <;> rfl
section FactorCover
open MvPolynomial UniqueFactorizationMonoid
theorem lower_of_anchor (P : Row 4) (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨141, 59, 14⟩) (hw : TrueWeightLE P anchorCutoff) :
    LowerRow (shape P).t (anchorLead P) := by
  refine ⟨anchorLead_ne hP, ?_, ?_, ?_⟩
  · have hb := (Euler50GeoLead.lead_degree P hP).trans hbox.1
    change (anchorLead P).totalDegree + (shape P).t ≤ 141 at hb
    change (anchorLead P).totalDegree ≤ 141 - (shape P).t
    omega
  · have hj := (Euler50GeoLead.lead_index P hP).trans hbox.2.1
    change indexDegree (anchorLead P) + 3 * (shape P).t ≤ 59 at hj
    change indexDegree (anchorLead P) ≤ 59 - 3 * (shape P).t
    omega
  · intro m hm
    obtain ⟨u, hu, hc, h⟩ := anchorLead_term P m hm
    have hle := h (fun i => physicalDegree - i.val)
    rw [← hc]
    apply (Nat.add_le_add_left _ _).trans (hw u hu)
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm, Fin.val_castSucc] using hle
theorem factor_small {P f : Row 4} (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨141, 59, 14⟩) (hw : TrueWeightLE P anchorCutoff)
    (hf : Irreducible f) (ht : 0 < (shape f).t) (hd : f ∣ P) : SmallFactor f := by
  refine ⟨hf, ht, ⟨?_, ?_, ?_⟩, ?_⟩
  · have h := weightedTotalDegree_le_of_dvd (1 : Fin 4 → ℕ) hd hP
    rw [weightedTotalDegree_one, weightedTotalDegree_one] at h
    exact h.trans hbox.1
  · have h := weightedTotalDegree_le_of_dvd (fun i => i.val) hd hP
    rw [← indexDegree_eq, ← indexDegree_eq] at h
    exact h.trans hbox.2.1
  · have h := weightedTotalDegree_le_of_dvd (Pi.single (3 : Fin 4) 1) hd hP
    simp only [weightedTotalDegree_piSingle] at h
    exact h.trans hbox.2.2
  · let e := MvPolynomial.optionEquivRight Geom (Fin 4)
    have hd' : e.symm f ∣ e.symm P := _root_.map_dvd e.symm hd
    have hP' : e.symm P ≠ 0 := fun h => hP (e.symm.injective (h.trans (map_zero _).symm))
    exact (trueWeight_iff f).mpr
      ((weightedTotalDegree_le_of_dvd _ hd' hP').trans ((trueWeight_iff P).mp hw))
end FactorCover
structure Inventory (Γ : Finset K) (s : K→(Polynomial K)) where
  top : ℕ
  top_le : top≤14
  g : Row 3
  lower : LowerRow top g
  low : Finset K
  low_sub : low⊆Γ
  low_vanish : ∀ γ∈low,atJet g (extend (s γ))=0
  n : ℕ
  factor : Fin n→Row 4
  small : ∀ i,SmallFactor (factor i)
  different : ∀ i j,i≠j → ¬Associated (factor i) (factor j)
  fits : Fits top (fun i=>shape (factor i))
  active : (∑ i,activeDegree (factor i))≤177
  order : Fin n→ℕ
  layers : LayerBudget (fun i=>shape (factor i)) order
  proper : ∀ i,0<order i → ProperCut (factor i) Γ s (order i)
  zeros : Finset (Fin n)
  zero_iff : ∀ i,i∈zeros ↔ order i=0
  retained : zeros=∅ ∨ (Low6960Retained.Box (Low6960Retained.combined (fun i=>shape (factor i)) zeros) ∧
    1≤(Low6960Retained.combined (fun i=>shape (factor i)) zeros).t ∧
    (Low6960Retained.combined (fun i=>shape (factor i)) zeros).t≤2)
  pieces : Fin n→Finset K
  piece_sub : ∀ i,pieces i⊆Γ
  on_factor : ∀ i γ,γ∈pieces i → OnFactor (factor i) (extend (s γ))
  off_retained : ∀ i∉zeros,∀ γ∈pieces i,atJet (∏ j∈zeros,factor j) (extend (s γ))≠0
  book : Finset K
  book_cap : book.card≤140000
  fat : Low6960Fat.FatEquations
  fat_at : ∀ i γ,γ∈pieces i → Low6960Fat.Holds fat (extend (s γ))
  cover_count : Γ.card ≤ book.card+low.card+∑ i,(pieces i).card
theorem inventory_of_family {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179808 M Γ) (lo : 1≤M.overhead) (hi : M.overhead≤2378) :
    Nonempty (Inventory Γ F.scalar) := by
  obtain ⟨P,hP,hbox,hact,weight,vanish⟩ := Low6960Anchor.anchor_of_family M F hi
  have hw : TrueWeightLE P anchorCutoff := by
    apply (trueWeight_iff P).mpr
    rw [← differentialWeight_eq,←differentialWeightedDegree]
    exact weight
  obtain ⟨n,f,factors,different,prodDvd,covers⟩ := KoalaRetainedCut.anchor_factors hP
  let top := (shape P).t
  have htop : top≤14 := hbox.2.2
  have small (i : Fin n) : SmallFactor (f i) := factor_small hP hbox hw
    (factors i).1 (factors i).2.1 (factors i).2.2
  have fits : Fits top (fun i => shape (f i)) := by
    refine ⟨fun i => ⟨(factors i).2.1,index_bounds (f i)⟩,?_,?_,?_⟩
    · have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 4 → ℕ) Finset.univ f hP prodDvd
      simp only [MvPolynomial.weightedTotalDegree_one] at h
      exact h.trans hbox.1
    · have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd Fin.val Finset.univ f hP prodDvd
      simp only [← indexDegree_eq] at h
      exact h.trans hbox.2.1
    · have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd (Pi.single (3 : Fin 4) 1) Finset.univ f hP prodDvd
      change (∑ i, (f i).degreeOf 3) ≤ P.degreeOf 3
      simpa only [MvPolynomial.weightedTotalDegree_piSingle] using h
  have active : (∑ i, activeDegree (f i)) ≤ 177 :=
    (MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd (![1,2,2,2] : Fin 4 → ℕ)
      Finset.univ f hP prodDvd).trans ((activeFits_iff P 177).mp hact)
  have hchar (i : Fin n) : (shape (f i)).t<K1.p := (small i).2.2.1.2.2.trans_lt (by decide)
  have hm := Low6960Order.messages_of_family M F hi
  obtain ⟨ord,layers,proper⟩ := Low6960Order.proper_layers hm (fun i=>(small i).1)
    (fun i=>(small i).2.1) hchar different
  let zeros := (univ : Finset (Fin n)).filter fun i=>ord i=0
  have zero_iff (i : Fin n) : i∈zeros ↔ ord i=0 := by simp [zeros]
  have retained := Low6960Retained.no_cut_shape _ _ fits.1 layers zeros
    (fun i hi=>(zero_iff i).mp hi)
  obtain ⟨book,E,booked,fat⟩ := fat_of_family M F lo hi
  obtain ⟨low,piece,lowSub,lowOn,sub,on,off,total⟩ := KoalaRetainedCut.priority_pieces
    (fun i => (factors i).2.2) F.scalar book zeros (fun γ hγ => covers _ (vanish γ hγ))
  exact ⟨⟨top,htop,K1_13_1.anchorLead P,lower_of_anchor P hP hbox hw,low,lowSub,lowOn,
    n,f,small,different,fits,active,ord,layers,proper,zeros,zero_iff,retained,piece,sub,
    (fun i γ hγ=>(on i γ hγ).2),off,book,booked,E,(fun i γ hγ=>fat γ (sub i hγ) (on i γ hγ).1),total⟩⟩
#print axioms inventory_of_family
end
end Lower6960.Low

end Merged_R6960Low6960Inventory
