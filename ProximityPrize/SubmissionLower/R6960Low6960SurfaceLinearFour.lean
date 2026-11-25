import ProximityPrize.SubmissionLower.GoldBranch6N8
import ProximityPrize.SubmissionLower.Final50Price
import ProximityPrize.SubmissionLower.KoalaRetainedCut
import ProximityPrize.SubmissionLower.R6960Low6960Anchor
import ProximityPrize.SubmissionLower.R6960Low6960Retained
import ProximityPrize.SubmissionLower.R6960Low6960FatBanks

set_option Elab.async false

-- merged module R6960Low6960Inventory
section Merged_R6960Low6960Inventory

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
abbrev anchorCutoff : ℕ := 101*agreement-1+57
def fullCap (top : ℕ) : Shape := ⟨136, 57, top⟩
def Fits (top : ℕ) {n : ℕ} (a : Fin n → Shape) : Prop :=
  (∀ i, K1_13_8.Valid (a i)) ∧ (∑ i, (a i).b) ≤ 136 ∧ (∑ i, (a i).j) ≤ 57 ∧
    (∑ i, (a i).t) ≤ top
def LowerRow (top : ℕ) (g : Row 3) : Prop :=
  g≠0 ∧ g.totalDegree≤136-top ∧ indexDegree g≤57-3*top ∧ TrueWeightLE g anchorCutoff
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
    (hbox : InBox (shape P) ⟨136, 57, 14⟩) (hw : TrueWeightLE P anchorCutoff) :
    LowerRow (shape P).t (anchorLead P) := by
  refine ⟨anchorLead_ne hP, ?_, ?_, ?_⟩
  · have hb := (Euler50GeoLead.lead_degree P hP).trans hbox.1
    change (anchorLead P).totalDegree + (shape P).t ≤ 136 at hb
    change (anchorLead P).totalDegree ≤ 136 - (shape P).t
    omega
  · have hj := (Euler50GeoLead.lead_index P hP).trans hbox.2.1
    change indexDegree (anchorLead P) + 3 * (shape P).t ≤ 57 at hj
    change indexDegree (anchorLead P) ≤ 57 - 3 * (shape P).t
    omega
  · intro m hm
    obtain ⟨u, hu, hc, h⟩ := anchorLead_term P m hm
    have hle := h (fun i => physicalDegree - i.val)
    rw [← hc]
    apply (Nat.add_le_add_left _ _).trans (hw u hu)
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm, Fin.val_castSucc] using hle
theorem factor_small {P f : Row 4} (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨136, 57, 14⟩) (hw : TrueWeightLE P anchorCutoff)
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
  active : (∑ i,activeDegree (factor i))≤169
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
    (F : P1.FamilyAt 179818 M Γ) (lo : 1≤M.overhead) (hi : M.overhead≤2358) :
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
  have active : (∑ i, activeDegree (f i)) ≤ 169 :=
    (MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd (![1,2,2,2] : Fin 4 → ℕ)
      Finset.univ f hP prodDvd).trans ((activeFits_iff P 169).mp hact)
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

end Merged_R6960Low6960Inventory

-- merged module R6960Low6960Monotone
section Merged_R6960Low6960Monotone

-- merged module Final50FatReserve
section Merged_Final50FatReserve
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
namespace Final50FatReserve
open K1_13 (Shape chart ceilDiv mixed32)
open K1_13_8 (Valid)
open K1_13_8_4 (TotalLE IndexFits mixed_mono_total)
open Final50Price (fatPrice linearChart taylorLength physicalDegree incidenceGap
  resultantBox commonBox fatOrder divisorOrder isolatedOrder)
private def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
private abbrev divisorBox : Shape :=
  ⟨commonBox.b + resultantBox.b / divisorOrder, commonBox.j + resultantBox.j / divisorOrder, 0⟩
private def divisorCut (h : Shape) : Shape :=
  ⟨max (max h.b divisorBox.b) (max h.j (divisorBox.j + 1)),
    max h.j (divisorBox.j + 1), max 1 h.t⟩
private def divisorFee (p h : Shape) (md mp : ℕ) : ℕ :=
  ceilDiv (Final50Price.errors * md) (32 * incidenceGap) + ceilDiv mp 32 +
    20 * p.b * h.b ^ 2 + 5 * physicalDegree * p.b * h.b + 1
private def singularFee (x : Shape) (ms : ℕ) : ℕ :=
  if 1 < x.t then ceilDiv (4 * x.t * ms) 32 + x.t * x.b ^ 2 + 1 else 0
private def curveFee (mc mq : ℕ) : ℕ :=
  let length := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  ceilDiv (Final50Price.errors * mc + incidenceGap * mq) (32 * incidenceGap * length)
private def isolatedFee : ℕ :=
  ceilDiv (3 * resultantBox.j ^ 2 * (2 * resultantBox.b - resultantBox.j))
    (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
private theorem fatPrice_expand (x : Shape) :
    fatPrice x =
      divisorFee x.chamber (fatChart x)
        (mixed32 x.chamber divisorBox (divisorCut (fatChart x)) (fatChart x))
        (mixed32 x.chamber divisorBox (divisorCut (fatChart x)) x.chamber) +
      singularFee x (mixed32 x.chamber x.chamber (fatChart x) (fatChart x)) +
      curveFee (mixed32 x.chamber resultantBox resultantBox (fatChart x))
        (mixed32 x.chamber resultantBox resultantBox x.chamber) + isolatedFee := rfl
private theorem chamber_widen {x y : Shape} (h : TotalLE x y) :
    TotalLE x.chamber y.chamber :=
  ⟨max_le_max h.1 h.2.1.le, h.2⟩
private theorem chart_widen (L : ℕ) {x y : Shape} (h : TotalLE x y) :
    TotalLE (chart L x) (chart L y) := by
  refine ⟨?_, by simp only [chart, h.2.1], by simp only [chart, h.2.1, h.2.2]⟩
  dsimp only [chart]
  rw [h.2.1]
  exact max_le_max
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right h.1 _)) _) le_rfl
private theorem fatChart_widen {x y : Shape} (h : TotalLE x y) :
    TotalLE (fatChart x) (fatChart y) := by
  have hp := chamber_widen h
  unfold fatChart
  rw [← h.2.2]
  split
  · refine ⟨?_, by simp only [linearChart, hp.2.1], by simp only [linearChart, hp.2.1]⟩
    dsimp only [linearChart]
    rw [hp.2.1]
    exact max_le_max
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hp.1 _)) _) le_rfl
  · exact chart_widen _ hp
private theorem cut_widen {h H : Shape} (hh : TotalLE h H) :
    TotalLE (divisorCut h) (divisorCut H) := by
  refine ⟨?_, by simp only [divisorCut, hh.2.1], by simp only [divisorCut, hh.2.2]⟩
  dsimp only [divisorCut]
  rw [hh.2.1]
  exact max_le_max (max_le_max hh.1 le_rfl) le_rfl
private theorem capped_index (b j t : ℕ) : IndexFits ⟨b, j, min t (j / 3)⟩ := by
  change 3 * min t (j / 3) ≤ j
  exact (Nat.mul_le_mul_left 3 (min_le_right _ _)).trans (by omega)
private theorem fatChart_index (x : Shape) : IndexFits (fatChart x) := by
  unfold fatChart
  split <;> exact capped_index _ _ _
private theorem cut_index {h : Shape} (hh : IndexFits h) : IndexFits (divisorCut h) := by
  change 3 * h.t ≤ h.j at hh
  change 3 * max 1 h.t ≤ max h.j (divisorBox.j + 1)
  rcases le_total 1 h.t with ht | ht
  · rw [max_eq_right ht]
    exact hh.trans (le_max_left _ _)
  · rw [max_eq_left ht]
    exact (show 3 * 1 ≤ divisorBox.j + 1 from by decide).trans (le_max_right _ _)
private theorem ceil_mono {a b l : ℕ} (h : a ≤ b) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h _) _)
theorem fatPrice_widen {x y : Shape} (h : TotalLE x y) (hv : IndexFits x) :
    fatPrice x ≤ fatPrice y := by
  have hp := chamber_widen h
  have hh := fatChart_widen h
  have hc := cut_widen hh
  have hp' : IndexFits x.chamber := hv
  have hh' := fatChart_index x
  have hc' := cut_index hh'
  have hbig : IndexFits divisorBox := Nat.zero_le _
  have hq : IndexFits resultantBox := Nat.zero_le _
  rw [fatPrice_expand x, fatPrice_expand y]
  refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_) le_rfl
  · have hd := mixed_mono_total hp (TotalLE.refl divisorBox) hc hh hp' hbig hc' hh'
    have hm := mixed_mono_total hp (TotalLE.refl divisorBox) hc hp hp' hbig hc' hp'
    dsimp only [divisorFee]
    refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_) ?_) le_rfl
    · exact ceil_mono (Nat.mul_le_mul_left _ hd)
    · exact ceil_mono hm
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp.1)
        (by simpa only [pow_two] using Nat.mul_le_mul hh.1 hh.1)
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp.1) hh.1
  · have hs := mixed_mono_total hp hp hh hh hp' hp' hh' hh'
    dsimp only [singularFee]
    rw [← h.2.2]
    split
    · exact Nat.add_le_add (Nat.add_le_add (ceil_mono (Nat.mul_le_mul_left _ hs))
        (Nat.mul_le_mul_left _ (by simpa only [pow_two] using Nat.mul_le_mul h.1 h.1))) le_rfl
    · exact le_rfl
  · have hc := mixed_mono_total hp (TotalLE.refl resultantBox) (TotalLE.refl resultantBox)
      hh hp' hq hq hh'
    have hm := mixed_mono_total hp (TotalLE.refl resultantBox) (TotalLE.refl resultantBox)
      hp hp' hq hq hp'
    exact ceil_mono (Nat.add_le_add (Nat.mul_le_mul_left _ hc) (Nat.mul_le_mul_left _ hm))
def degreeCap : ℕ → ℕ
  | 3 => 25
  | 4 => 23
  | 5 => 20
  | 6 => 16
  | 7 => 10
  | _ => 0
def charge (b j t : ℕ) : ℕ :=
  match t, j with
  | 1, 3 =>
    if b ≤ 1 then 2343347415003976
    else 16815154701363143
  | 1, 4 => 30532279541963794
  | 1, 5 => 46409127523914633
  | 1, 6 => 54064306903674190
  | 1, 7 => 48720018058055370
  | 2, 6 =>
    if b ≤ 3 then 78811583990757641
    else if b ≤ 11 then 135278860228783795
    else if b ≤ 13 then 158427079143371143
    else 193964641150607994
  | 2, 7 =>
    if b ≤ 6 then 143089016514969561
    else 194164445885822982
  | _, _ => 0
private theorem price_3_1_1 : fatPrice ⟨1,3,1⟩ ≤ charge 1 3 1 := by
  decide +kernel
private theorem price_3_1_25 : fatPrice ⟨25,3,1⟩ ≤ charge 25 3 1 := by
  decide +kernel
private theorem price_4_1_23 : fatPrice ⟨23,4,1⟩ ≤ charge 23 4 1 := by
  decide +kernel
private theorem price_5_1_20 : fatPrice ⟨20,5,1⟩ ≤ charge 20 5 1 := by
  decide +kernel
private theorem price_6_1_16 : fatPrice ⟨16,6,1⟩ ≤ charge 16 6 1 := by
  decide +kernel
private theorem price_7_1_10 : fatPrice ⟨10,7,1⟩ ≤ charge 10 7 1 := by
  decide +kernel
private theorem price_6_2_3 : fatPrice ⟨3,6,2⟩ ≤ charge 3 6 2 := by
  decide +kernel
private theorem price_6_2_11 : fatPrice ⟨11,6,2⟩ ≤ charge 11 6 2 := by
  decide +kernel
private theorem price_6_2_13 : fatPrice ⟨13,6,2⟩ ≤ charge 13 6 2 := by
  decide +kernel
private theorem price_6_2_16 : fatPrice ⟨16,6,2⟩ ≤ charge 16 6 2 := by
  decide +kernel
private theorem price_7_2_6 : fatPrice ⟨6,7,2⟩ ≤ charge 6 7 2 := by
  decide +kernel
private theorem price_7_2_10 : fatPrice ⟨10,7,2⟩ ≤ charge 10 7 2 := by
  decide +kernel
theorem single (x : Shape) (hv : Valid x) (hj : x.j ≤ 7) (hb : x.b ≤ degreeCap x.j) :
    fatPrice x ≤ charge x.b x.j x.t := by
  obtain ⟨b, j, t⟩ := x
  have hpos : 1 ≤ t := hv.1
  have hindex : 3 * t ≤ j := hv.2.1
  change j ≤ 7 at hj
  have htop : t = 1 ∨ t = 2 := by omega
  rcases htop with rfl | rfl
  · have hcases : j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · by_cases hs1 : b ≤ 1
      · simpa [charge, hs1] using
          (fatPrice_widen (x := ⟨b,3,1⟩) (y := ⟨1,3,1⟩) ⟨hs1, rfl, rfl⟩ hindex).trans price_3_1_1
      · simpa [charge, hs1] using
          (fatPrice_widen (x := ⟨b,3,1⟩) (y := ⟨25,3,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_3_1_25
    · exact (fatPrice_widen (x := ⟨b,4,1⟩) (y := ⟨23,4,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_4_1_23
    · exact (fatPrice_widen (x := ⟨b,5,1⟩) (y := ⟨20,5,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_5_1_20
    · exact (fatPrice_widen (x := ⟨b,6,1⟩) (y := ⟨16,6,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_6_1_16
    · exact (fatPrice_widen (x := ⟨b,7,1⟩) (y := ⟨10,7,1⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_7_1_10
  · have hcases : j = 6 ∨ j = 7 := by omega
    rcases hcases with rfl | rfl
    · by_cases hs3 : b ≤ 3
      · simpa [charge, hs3] using
          (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨3,6,2⟩) ⟨hs3, rfl, rfl⟩ hindex).trans price_6_2_3
      · by_cases hs11 : b ≤ 11
        · simpa [charge, hs3, hs11] using
            (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨11,6,2⟩) ⟨hs11, rfl, rfl⟩ hindex).trans price_6_2_11
        · by_cases hs13 : b ≤ 13
          · simpa [charge, hs3, hs11, hs13] using
              (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨13,6,2⟩) ⟨hs13, rfl, rfl⟩ hindex).trans price_6_2_13
          · simpa [charge, hs3, hs11, hs13] using
              (fatPrice_widen (x := ⟨b,6,2⟩) (y := ⟨16,6,2⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_6_2_16
    · by_cases hs6 : b ≤ 6
      · simpa [charge, hs6] using
          (fatPrice_widen (x := ⟨b,7,2⟩) (y := ⟨6,7,2⟩) ⟨hs6, rfl, rfl⟩ hindex).trans price_7_2_6
      · simpa [charge, hs6] using
          (fatPrice_widen (x := ⟨b,7,2⟩) (y := ⟨10,7,2⟩) ⟨hb, rfl, rfl⟩ hindex).trans price_7_2_10
private def PairCap (j k cap : ℕ) : Prop :=
  (j + k = 6 ∧ (cap = 3 ∨ cap = 11 ∨ cap = 13 ∨ cap = 16)) ∨
  (j + k = 7 ∧ (cap = 6 ∨ cap = 10))
private theorem pair_endpoints (j k cap : ℕ) (hjk : 3 ≤ j ∧ 3 ≤ k ∧ j + k ≤ 7)
    (hcap : PairCap j k cap) :
    ∀ b : Fin (cap+1), j ≤ 3 * b.val → k ≤ 3 * (cap-b.val) →
      fatPrice ⟨b.val,j,1⟩ + fatPrice ⟨cap-b.val,k,1⟩ ≤ charge cap (j + k) 2 := by
  unfold PairCap at hcap
  have indices : (j = 3 ∧ k = 3) ∨ (j = 3 ∧ k = 4) ∨ (j = 4 ∧ k = 3) := by omega
  rcases indices with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have caps : cap = 3 ∨ cap = 11 ∨ cap = 13 ∨ cap = 16 := by omega
    rcases caps with rfl | rfl | rfl | rfl <;> decide +kernel
  · have caps : cap = 6 ∨ cap = 10 := by omega
    rcases caps with rfl | rfl <;> decide +kernel
  · have caps : cap = 6 ∨ cap = 10 := by omega
    rcases caps with rfl | rfl <;> decide +kernel
private theorem pair_width (j k cap : ℕ) (hjk : 3 ≤ j ∧ 3 ≤ k ∧ j + k ≤ 7)
    (hcap : PairCap j k cap)
    (b c : ℕ) (hb : j ≤ 3 * b) (hc : k ≤ 3 * c) (hbc : b + c ≤ cap) :
    fatPrice ⟨b,j,1⟩ + fatPrice ⟨c,k,1⟩ ≤ charge cap (j + k) 2 := by
  have hc' : c ≤ cap-b := by omega
  have hck : k ≤ 3 * (cap-b) := hc.trans (Nat.mul_le_mul_left 3 hc')
  have hfee := fatPrice_widen (x := ⟨c,k,1⟩) (y := ⟨cap-b,k,1⟩) ⟨hc', rfl, rfl⟩ hjk.2.1
  exact (Nat.add_le_add_left hfee _).trans
    (pair_endpoints j k cap hjk hcap ⟨b, by omega⟩ hb hck)
theorem pair (b c j k : ℕ) (hj : 3 ≤ j) (hk : 3 ≤ k) (hjk : j + k ≤ 7)
    (hb : j ≤ 3 * b) (hc : k ≤ 3 * c) (hbc : b + c ≤ degreeCap (j+k)) :
    fatPrice ⟨b,j,1⟩ + fatPrice ⟨c,k,1⟩ ≤ charge (b+c) (j+k) 2 := by
  have indices : j + k = 6 ∨ j + k = 7 := by omega
  rcases indices with h | h
  · by_cases hs3 : b + c ≤ 3
    · have paid := pair_width j k 3 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc hs3
      simpa [charge, hs3, h] using paid
    · by_cases hs11 : b + c ≤ 11
      · have paid := pair_width j k 11 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc hs11
        simpa [charge, hs3, hs11, h] using paid
      · by_cases hs13 : b + c ≤ 13
        · have paid := pair_width j k 13 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc hs13
          simpa [charge, hs3, hs11, hs13, h] using paid
        · have paid := pair_width j k 16 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc (by simpa only [h, degreeCap] using hbc)
          simpa [charge, hs3, hs11, hs13, h] using paid
  · by_cases hs6 : b + c ≤ 6
    · have paid := pair_width j k 6 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc hs6
      simpa [charge, hs6, h] using paid
    · have paid := pair_width j k 10 ⟨hj,hk,hjk⟩ (by simp [PairCap, h]) b c hb hc (by simpa only [h, degreeCap] using hbc)
      simpa [charge, hs6, h] using paid
theorem family (n : ℕ) (a : Fin n → Shape) (hv : ∀ i, Valid (a i))
    (hj : (∑ i, (a i).j) ≤ 7)
    (hb : (∑ i, (a i).b) ≤ degreeCap (∑ i, (a i).j)) :
    (∑ i, fatPrice (a i)) ≤ charge (∑ i, (a i).b) (∑ i, (a i).j) (∑ i, (a i).t) := by
  have hsum : 3 * (∑ i, (a i).t) ≤ ∑ i, (a i).j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hv i).2.1
  have hn' : n ≤ ∑ i, (a i).t := calc
    n = ∑ _ : Fin n, 1 := by simp
    _ ≤ ∑ i, (a i).t := Finset.sum_le_sum fun i _ => (hv i).1
  have hn : n ≤ 2 := by omega
  interval_cases n
  · simp [charge]
  · simp only [Fin.sum_univ_one] at hj hb ⊢
    exact single _ (hv 0) hj hb
  · simp only [Fin.sum_univ_two] at hsum hj hb ⊢
    have ht0 := (hv 0).1
    have ht1 := (hv 1).1
    have h0 : (a 0).t = 1 := by omega
    have h1 : (a 1).t = 1 := by omega
    have he (i : Fin 2) : a i = ⟨(a i).b, (a i).j, (a i).t⟩ := by cases a i; rfl
    have hh := pair (a 0).b (a 1).b (a 0).j (a 1).j
      (by simpa only [h0] using (hv 0).2.1) (by simpa only [h1] using (hv 1).2.1)
      hj (hv 0).2.2 (hv 1).2.2 hb
    have ha0 : a 0 = ⟨(a 0).b, (a 0).j, 1⟩ :=
      (he 0).trans (congrArg (fun t => (⟨(a 0).b, (a 0).j, t⟩ : Shape)) h0)
    have ha1 : a 1 = ⟨(a 1).b, (a 1).j, 1⟩ :=
      (he 1).trans (congrArg (fun t => (⟨(a 1).b, (a 1).j, t⟩ : Shape)) h1)
    rw [h0, h1]
    simpa only [← ha0, ← ha1] using hh
#print axioms fatPrice_widen
#print axioms single
#print axioms pair
#print axioms family
end Final50FatReserve

end Merged_Final50FatReserve

-- merged module R6960Low6960RetainedFees
section Merged_R6960Low6960RetainedFees
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Lower6960.Low
open Finset
open K1_13 (Shape chart ceilDiv mixed32 shape)
open K1_13_8 (Valid)
open Low6960Fat (commonBox resultantBox)
open K1_13_8_4 (TotalLE)
open scoped BigOperators Classical
abbrev errors : ℕ := 262144-agreement
abbrev incidenceGap : ℕ := agreement-physicalDegree
abbrev taylorLength : ℕ := physicalDegree+1
abbrev fatOrder : ℕ := 23893
abbrev divisorOrder : ℕ := 22155
abbrev isolatedOrder : ℕ := 174
def lowDegreeCap : ℕ → ℕ
  | 3 => 26
  | 4 => 24
  | 5 => 21
  | 6 => 17
  | 7 => 12
  | 8 => 4
  | _ => 0
def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩
def fatPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := if x.t = 1 then linearChart p else chart (taylorLength + 4) p
  let q : Shape := resultantBox
  let big : Shape := ⟨commonBox.b + q.b / divisorOrder, commonBox.j + q.j / divisorOrder, 0⟩
  let cut : Shape := ⟨max (max h.b big.b) (max h.j (big.j + 1)),
    max h.j (big.j + 1), max 1 h.t⟩
  let divisors := ceilDiv (errors * mixed32 p big cut h) (32 * incidenceGap) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b^2 + 5 * physicalDegree * p.b * h.b + 1
  let singular := if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b^2 + 1 else 0
  let curveLength := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  let curves := ceilDiv (errors * mixed32 p q q h + incidenceGap * mixed32 p q q p)
    (32 * incidenceGap * curveLength)
  let isolated := ceilDiv (3 * q.j^2 * (2 * q.b - q.j)) (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
  divisors + singular + curves + isolated
def retainedTariffs : ℕ→ℕ→List ℕ
  | 3,1 => [0, 1952879554821531, 1952879554821531, 1952879554821531, 2264030333312493, 2582480582752554, 2910366730929716, 3249825205631977, 3602992434647339, 3972004845763800, 4358998866769362, 4766110925452023, 5195477449599785, 5649234867000646, 6129519605442608, 6638468092713669, 7178216756601831, 7750902024895092, 8358660325381453, 9003628085848914, 9687941734085476, 10413737697879137, 11183152405017899, 11998322283289760, 12861383760482722, 13774473264384783, 14739727222783944]
  | 4,1 => [0, 0, 4595623903046235, 4595623903046235, 4595623903046235, 5369691775899144, 6153195547489152, 6948271645604260, 7757056498032469, 8581686532561778, 9424298176980187, 10287027859075695, 11172012006636304, 12081387047450012, 13017289409304820, 13981855519988729, 14977221807289737, 16005524698995846, 17068900622895054, 18169486006775363, 19309417278424772, 20490830865631280, 21715863196182889, 22986650697867597, 24305329798473406]
  | 5,1 => [0, 0, 9797261559566592, 9797261559566592, 9797261559566592, 9797261559566592, 11239103013607327, 12692516794173162, 14159639329052097, 15642607046032133, 17143556372901268, 18664623737447503, 20207945567458838, 21775658290723275, 23369898335028810, 24992802128163445, 26646506097915180, 28333146672072016, 30054860278421951, 31813783344752986, 33612052298853121, 35451803568510358]
  | 6,1 => [0, 0, 17004859032909927, 17004859032909927, 17004859032909927, 17004859032909927, 17004859032909927, 19066433846681251, 21141717414765676, 23232846164951201, 25341956525025827, 27471184922777552, 29622667785994377, 31798541542464301, 34000942619975327, 36232007446315452, 38493872449272677, 40788674056635002]
  | 7,1 => [0, 0, 0, 26337331550252863, 26337331550252863, 26337331550252863, 26337331550252863, 26337331550252863, 29020776151542777, 31720065934933792, 34437337328213907, 37174726759171121, 39934370655593437]
  | 8,1 => [0, 0, 0, 37796815539383397, 37796815539383397]
  | 6,2 => [0, 0, 55462371369774712, 55462371369774722, 55462371369774736, 55462371369774754, 55462371369774776, 63291232093810052, 71174575000860732, 79120946314457695, 87138892258131824, 95236959055413996, 103423692929835092, 111707640104925991, 120097346804217575, 128601359251240723, 137228223669526315, 145986486282605231]
  | 7,2 => [0, 0, 0, 100206150776982578, 100206150776982592, 100206150776982610, 100206150776982632, 100206150776982658, 112072656565082685, 124002190759728996, 136003299584452471, 148084529262783989, 160254426018254432]
  | 8,2 => [0, 0, 0, 159588895902744113, 159588895902744127]
  | _,_ => []
def retainedTariff (b j t : ℕ) : ℕ := (retainedTariffs j t).getD b 0
def singleTariffs : ℕ→ℕ→List ℕ
  | 3,1 => [0, 1952879554821531, 1952879554821531, 1952879554821531, 2264030333312493, 2582480582752554, 2910366730929716, 3249825205631977, 3602992434647339, 3972004845763800, 4358998866769362, 4766110925452023, 5195477449599785, 5649234867000646, 6129519605442608, 6638468092713669, 7178216756601831, 7750902024895092, 8358660325381453, 9003628085848914, 9687941734085476, 10413737697879137, 11183152405017899, 11998322283289760, 12861383760482722, 13774473264384783, 14739727222783944]
  | 4,1 => [0, 0, 4595623903046235, 4595623903046235, 4595623903046235, 5369691775899144, 6153195547489152, 6948271645604260, 7757056498032469, 8581686532561778, 9424298176980187, 10287027859075695, 11172012006636304, 12081387047450012, 13017289409304820, 13981855519988729, 14977221807289737, 16005524698995846, 17068900622895054, 18169486006775363, 19309417278424772, 20490830865631280, 21715863196182889, 22986650697867597, 24305329798473406]
  | 5,1 => [0, 0, 9797261559566592, 9797261559566592, 9797261559566592, 9797261559566592, 11239103013607327, 12692516794173162, 14159639329052097, 15642607046032133, 17143556372901268, 18664623737447503, 20207945567458838, 21775658290723275, 23369898335028810, 24992802128163445, 26646506097915180, 28333146672072016, 30054860278421951, 31813783344752986, 33612052298853121, 35451803568510358]
  | 6,1 => [0, 0, 17004859032909927, 17004859032909927, 17004859032909927, 17004859032909927, 17004859032909927, 19066433846681251, 21141717414765676, 23232846164951201, 25341956525025827, 27471184922777552, 29622667785994377, 31798541542464301, 34000942619975327, 36232007446315452, 38493872449272677, 40788674056635002]
  | 7,1 => [0, 0, 0, 26337331550252863, 26337331550252863, 26337331550252863, 26337331550252863, 26337331550252863, 29020776151542777, 31720065934933792, 34437337328213907, 37174726759171121, 39934370655593437]
  | 8,1 => [0, 0, 0, 37796815539383397, 37796815539383397]
  | 6,2 => [0, 0, 55462371369774712, 55462371369774722, 55462371369774736, 55462371369774754, 55462371369774776, 63291232093810052, 71174575000860732, 79120946314457695, 87138892258131824, 95236959055413996, 103423692929835092, 111707640104925991, 120097346804217575, 128601359251240723, 137228223669526315, 145986486282605231]
  | 7,2 => [0, 0, 0, 100206150776982578, 100206150776982592, 100206150776982610, 100206150776982632, 100206150776982658, 112072656565082685, 124002190759728996, 136003299584452471, 148084529262783989, 160254426018254432]
  | 8,2 => [0, 0, 0, 159588895902744113, 159588895902744127]
  | _,_ => []
def singleTariff (b j t : ℕ) : ℕ := (singleTariffs j t).getD b 0
private theorem cell_1_3_1 : fatPrice ⟨1,3,1⟩ ≤ singleTariff 1 3 1 := by decide +kernel
private theorem cell_2_3_1 : fatPrice ⟨2,3,1⟩ ≤ singleTariff 2 3 1 := by decide +kernel
private theorem cell_3_3_1 : fatPrice ⟨3,3,1⟩ ≤ singleTariff 3 3 1 := by decide +kernel
private theorem cell_4_3_1 : fatPrice ⟨4,3,1⟩ ≤ singleTariff 4 3 1 := by decide +kernel
private theorem cell_5_3_1 : fatPrice ⟨5,3,1⟩ ≤ singleTariff 5 3 1 := by decide +kernel
private theorem cell_6_3_1 : fatPrice ⟨6,3,1⟩ ≤ singleTariff 6 3 1 := by decide +kernel
private theorem cell_7_3_1 : fatPrice ⟨7,3,1⟩ ≤ singleTariff 7 3 1 := by decide +kernel
private theorem cell_8_3_1 : fatPrice ⟨8,3,1⟩ ≤ singleTariff 8 3 1 := by decide +kernel
private theorem cell_9_3_1 : fatPrice ⟨9,3,1⟩ ≤ singleTariff 9 3 1 := by decide +kernel
private theorem cell_10_3_1 : fatPrice ⟨10,3,1⟩ ≤ singleTariff 10 3 1 := by decide +kernel
private theorem cell_11_3_1 : fatPrice ⟨11,3,1⟩ ≤ singleTariff 11 3 1 := by decide +kernel
private theorem cell_12_3_1 : fatPrice ⟨12,3,1⟩ ≤ singleTariff 12 3 1 := by decide +kernel
private theorem cell_13_3_1 : fatPrice ⟨13,3,1⟩ ≤ singleTariff 13 3 1 := by decide +kernel
private theorem cell_14_3_1 : fatPrice ⟨14,3,1⟩ ≤ singleTariff 14 3 1 := by decide +kernel
private theorem cell_15_3_1 : fatPrice ⟨15,3,1⟩ ≤ singleTariff 15 3 1 := by decide +kernel
private theorem cell_16_3_1 : fatPrice ⟨16,3,1⟩ ≤ singleTariff 16 3 1 := by decide +kernel
private theorem cell_17_3_1 : fatPrice ⟨17,3,1⟩ ≤ singleTariff 17 3 1 := by decide +kernel
private theorem cell_18_3_1 : fatPrice ⟨18,3,1⟩ ≤ singleTariff 18 3 1 := by decide +kernel
private theorem cell_19_3_1 : fatPrice ⟨19,3,1⟩ ≤ singleTariff 19 3 1 := by decide +kernel
private theorem cell_20_3_1 : fatPrice ⟨20,3,1⟩ ≤ singleTariff 20 3 1 := by decide +kernel
private theorem cell_21_3_1 : fatPrice ⟨21,3,1⟩ ≤ singleTariff 21 3 1 := by decide +kernel
private theorem cell_22_3_1 : fatPrice ⟨22,3,1⟩ ≤ singleTariff 22 3 1 := by decide +kernel
private theorem cell_23_3_1 : fatPrice ⟨23,3,1⟩ ≤ singleTariff 23 3 1 := by decide +kernel
private theorem cell_24_3_1 : fatPrice ⟨24,3,1⟩ ≤ singleTariff 24 3 1 := by decide +kernel
private theorem cell_25_3_1 : fatPrice ⟨25,3,1⟩ ≤ singleTariff 25 3 1 := by decide +kernel
private theorem cell_26_3_1 : fatPrice ⟨26,3,1⟩ ≤ singleTariff 26 3 1 := by decide +kernel
private theorem cell_2_4_1 : fatPrice ⟨2,4,1⟩ ≤ singleTariff 2 4 1 := by decide +kernel
private theorem cell_3_4_1 : fatPrice ⟨3,4,1⟩ ≤ singleTariff 3 4 1 := by decide +kernel
private theorem cell_4_4_1 : fatPrice ⟨4,4,1⟩ ≤ singleTariff 4 4 1 := by decide +kernel
private theorem cell_5_4_1 : fatPrice ⟨5,4,1⟩ ≤ singleTariff 5 4 1 := by decide +kernel
private theorem cell_6_4_1 : fatPrice ⟨6,4,1⟩ ≤ singleTariff 6 4 1 := by decide +kernel
private theorem cell_7_4_1 : fatPrice ⟨7,4,1⟩ ≤ singleTariff 7 4 1 := by decide +kernel
private theorem cell_8_4_1 : fatPrice ⟨8,4,1⟩ ≤ singleTariff 8 4 1 := by decide +kernel
private theorem cell_9_4_1 : fatPrice ⟨9,4,1⟩ ≤ singleTariff 9 4 1 := by decide +kernel
private theorem cell_10_4_1 : fatPrice ⟨10,4,1⟩ ≤ singleTariff 10 4 1 := by decide +kernel
private theorem cell_11_4_1 : fatPrice ⟨11,4,1⟩ ≤ singleTariff 11 4 1 := by decide +kernel
private theorem cell_12_4_1 : fatPrice ⟨12,4,1⟩ ≤ singleTariff 12 4 1 := by decide +kernel
private theorem cell_13_4_1 : fatPrice ⟨13,4,1⟩ ≤ singleTariff 13 4 1 := by decide +kernel
private theorem cell_14_4_1 : fatPrice ⟨14,4,1⟩ ≤ singleTariff 14 4 1 := by decide +kernel
private theorem cell_15_4_1 : fatPrice ⟨15,4,1⟩ ≤ singleTariff 15 4 1 := by decide +kernel
private theorem cell_16_4_1 : fatPrice ⟨16,4,1⟩ ≤ singleTariff 16 4 1 := by decide +kernel
private theorem cell_17_4_1 : fatPrice ⟨17,4,1⟩ ≤ singleTariff 17 4 1 := by decide +kernel
private theorem cell_18_4_1 : fatPrice ⟨18,4,1⟩ ≤ singleTariff 18 4 1 := by decide +kernel
private theorem cell_19_4_1 : fatPrice ⟨19,4,1⟩ ≤ singleTariff 19 4 1 := by decide +kernel
private theorem cell_20_4_1 : fatPrice ⟨20,4,1⟩ ≤ singleTariff 20 4 1 := by decide +kernel
private theorem cell_21_4_1 : fatPrice ⟨21,4,1⟩ ≤ singleTariff 21 4 1 := by decide +kernel
private theorem cell_22_4_1 : fatPrice ⟨22,4,1⟩ ≤ singleTariff 22 4 1 := by decide +kernel
private theorem cell_23_4_1 : fatPrice ⟨23,4,1⟩ ≤ singleTariff 23 4 1 := by decide +kernel
private theorem cell_24_4_1 : fatPrice ⟨24,4,1⟩ ≤ singleTariff 24 4 1 := by decide +kernel
private theorem cell_2_5_1 : fatPrice ⟨2,5,1⟩ ≤ singleTariff 2 5 1 := by decide +kernel
private theorem cell_3_5_1 : fatPrice ⟨3,5,1⟩ ≤ singleTariff 3 5 1 := by decide +kernel
private theorem cell_4_5_1 : fatPrice ⟨4,5,1⟩ ≤ singleTariff 4 5 1 := by decide +kernel
private theorem cell_5_5_1 : fatPrice ⟨5,5,1⟩ ≤ singleTariff 5 5 1 := by decide +kernel
private theorem cell_6_5_1 : fatPrice ⟨6,5,1⟩ ≤ singleTariff 6 5 1 := by decide +kernel
private theorem cell_7_5_1 : fatPrice ⟨7,5,1⟩ ≤ singleTariff 7 5 1 := by decide +kernel
private theorem cell_8_5_1 : fatPrice ⟨8,5,1⟩ ≤ singleTariff 8 5 1 := by decide +kernel
private theorem cell_9_5_1 : fatPrice ⟨9,5,1⟩ ≤ singleTariff 9 5 1 := by decide +kernel
private theorem cell_10_5_1 : fatPrice ⟨10,5,1⟩ ≤ singleTariff 10 5 1 := by decide +kernel
private theorem cell_11_5_1 : fatPrice ⟨11,5,1⟩ ≤ singleTariff 11 5 1 := by decide +kernel
private theorem cell_12_5_1 : fatPrice ⟨12,5,1⟩ ≤ singleTariff 12 5 1 := by decide +kernel
private theorem cell_13_5_1 : fatPrice ⟨13,5,1⟩ ≤ singleTariff 13 5 1 := by decide +kernel
private theorem cell_14_5_1 : fatPrice ⟨14,5,1⟩ ≤ singleTariff 14 5 1 := by decide +kernel
private theorem cell_15_5_1 : fatPrice ⟨15,5,1⟩ ≤ singleTariff 15 5 1 := by decide +kernel
private theorem cell_16_5_1 : fatPrice ⟨16,5,1⟩ ≤ singleTariff 16 5 1 := by decide +kernel
private theorem cell_17_5_1 : fatPrice ⟨17,5,1⟩ ≤ singleTariff 17 5 1 := by decide +kernel
private theorem cell_18_5_1 : fatPrice ⟨18,5,1⟩ ≤ singleTariff 18 5 1 := by decide +kernel
private theorem cell_19_5_1 : fatPrice ⟨19,5,1⟩ ≤ singleTariff 19 5 1 := by decide +kernel
private theorem cell_20_5_1 : fatPrice ⟨20,5,1⟩ ≤ singleTariff 20 5 1 := by decide +kernel
private theorem cell_21_5_1 : fatPrice ⟨21,5,1⟩ ≤ singleTariff 21 5 1 := by decide +kernel
private theorem cell_2_6_1 : fatPrice ⟨2,6,1⟩ ≤ singleTariff 2 6 1 := by decide +kernel
private theorem cell_3_6_1 : fatPrice ⟨3,6,1⟩ ≤ singleTariff 3 6 1 := by decide +kernel
private theorem cell_4_6_1 : fatPrice ⟨4,6,1⟩ ≤ singleTariff 4 6 1 := by decide +kernel
private theorem cell_5_6_1 : fatPrice ⟨5,6,1⟩ ≤ singleTariff 5 6 1 := by decide +kernel
private theorem cell_6_6_1 : fatPrice ⟨6,6,1⟩ ≤ singleTariff 6 6 1 := by decide +kernel
private theorem cell_7_6_1 : fatPrice ⟨7,6,1⟩ ≤ singleTariff 7 6 1 := by decide +kernel
private theorem cell_8_6_1 : fatPrice ⟨8,6,1⟩ ≤ singleTariff 8 6 1 := by decide +kernel
private theorem cell_9_6_1 : fatPrice ⟨9,6,1⟩ ≤ singleTariff 9 6 1 := by decide +kernel
private theorem cell_10_6_1 : fatPrice ⟨10,6,1⟩ ≤ singleTariff 10 6 1 := by decide +kernel
private theorem cell_11_6_1 : fatPrice ⟨11,6,1⟩ ≤ singleTariff 11 6 1 := by decide +kernel
private theorem cell_12_6_1 : fatPrice ⟨12,6,1⟩ ≤ singleTariff 12 6 1 := by decide +kernel
private theorem cell_13_6_1 : fatPrice ⟨13,6,1⟩ ≤ singleTariff 13 6 1 := by decide +kernel
private theorem cell_14_6_1 : fatPrice ⟨14,6,1⟩ ≤ singleTariff 14 6 1 := by decide +kernel
private theorem cell_15_6_1 : fatPrice ⟨15,6,1⟩ ≤ singleTariff 15 6 1 := by decide +kernel
private theorem cell_16_6_1 : fatPrice ⟨16,6,1⟩ ≤ singleTariff 16 6 1 := by decide +kernel
private theorem cell_17_6_1 : fatPrice ⟨17,6,1⟩ ≤ singleTariff 17 6 1 := by decide +kernel
private theorem cell_3_7_1 : fatPrice ⟨3,7,1⟩ ≤ singleTariff 3 7 1 := by decide +kernel
private theorem cell_4_7_1 : fatPrice ⟨4,7,1⟩ ≤ singleTariff 4 7 1 := by decide +kernel
private theorem cell_5_7_1 : fatPrice ⟨5,7,1⟩ ≤ singleTariff 5 7 1 := by decide +kernel
private theorem cell_6_7_1 : fatPrice ⟨6,7,1⟩ ≤ singleTariff 6 7 1 := by decide +kernel
private theorem cell_7_7_1 : fatPrice ⟨7,7,1⟩ ≤ singleTariff 7 7 1 := by decide +kernel
private theorem cell_8_7_1 : fatPrice ⟨8,7,1⟩ ≤ singleTariff 8 7 1 := by decide +kernel
private theorem cell_9_7_1 : fatPrice ⟨9,7,1⟩ ≤ singleTariff 9 7 1 := by decide +kernel
private theorem cell_10_7_1 : fatPrice ⟨10,7,1⟩ ≤ singleTariff 10 7 1 := by decide +kernel
private theorem cell_11_7_1 : fatPrice ⟨11,7,1⟩ ≤ singleTariff 11 7 1 := by decide +kernel
private theorem cell_12_7_1 : fatPrice ⟨12,7,1⟩ ≤ singleTariff 12 7 1 := by decide +kernel
private theorem cell_3_8_1 : fatPrice ⟨3,8,1⟩ ≤ singleTariff 3 8 1 := by decide +kernel
private theorem cell_4_8_1 : fatPrice ⟨4,8,1⟩ ≤ singleTariff 4 8 1 := by decide +kernel
private theorem cell_2_6_2 : fatPrice ⟨2,6,2⟩ ≤ singleTariff 2 6 2 := by decide +kernel
private theorem cell_3_6_2 : fatPrice ⟨3,6,2⟩ ≤ singleTariff 3 6 2 := by decide +kernel
private theorem cell_4_6_2 : fatPrice ⟨4,6,2⟩ ≤ singleTariff 4 6 2 := by decide +kernel
private theorem cell_5_6_2 : fatPrice ⟨5,6,2⟩ ≤ singleTariff 5 6 2 := by decide +kernel
private theorem cell_6_6_2 : fatPrice ⟨6,6,2⟩ ≤ singleTariff 6 6 2 := by decide +kernel
private theorem cell_7_6_2 : fatPrice ⟨7,6,2⟩ ≤ singleTariff 7 6 2 := by decide +kernel
private theorem cell_8_6_2 : fatPrice ⟨8,6,2⟩ ≤ singleTariff 8 6 2 := by decide +kernel
private theorem cell_9_6_2 : fatPrice ⟨9,6,2⟩ ≤ singleTariff 9 6 2 := by decide +kernel
private theorem cell_10_6_2 : fatPrice ⟨10,6,2⟩ ≤ singleTariff 10 6 2 := by decide +kernel
private theorem cell_11_6_2 : fatPrice ⟨11,6,2⟩ ≤ singleTariff 11 6 2 := by decide +kernel
private theorem cell_12_6_2 : fatPrice ⟨12,6,2⟩ ≤ singleTariff 12 6 2 := by decide +kernel
private theorem cell_13_6_2 : fatPrice ⟨13,6,2⟩ ≤ singleTariff 13 6 2 := by decide +kernel
private theorem cell_14_6_2 : fatPrice ⟨14,6,2⟩ ≤ singleTariff 14 6 2 := by decide +kernel
private theorem cell_15_6_2 : fatPrice ⟨15,6,2⟩ ≤ singleTariff 15 6 2 := by decide +kernel
private theorem cell_16_6_2 : fatPrice ⟨16,6,2⟩ ≤ singleTariff 16 6 2 := by decide +kernel
private theorem cell_17_6_2 : fatPrice ⟨17,6,2⟩ ≤ singleTariff 17 6 2 := by decide +kernel
private theorem cell_3_7_2 : fatPrice ⟨3,7,2⟩ ≤ singleTariff 3 7 2 := by decide +kernel
private theorem cell_4_7_2 : fatPrice ⟨4,7,2⟩ ≤ singleTariff 4 7 2 := by decide +kernel
private theorem cell_5_7_2 : fatPrice ⟨5,7,2⟩ ≤ singleTariff 5 7 2 := by decide +kernel
private theorem cell_6_7_2 : fatPrice ⟨6,7,2⟩ ≤ singleTariff 6 7 2 := by decide +kernel
private theorem cell_7_7_2 : fatPrice ⟨7,7,2⟩ ≤ singleTariff 7 7 2 := by decide +kernel
private theorem cell_8_7_2 : fatPrice ⟨8,7,2⟩ ≤ singleTariff 8 7 2 := by decide +kernel
private theorem cell_9_7_2 : fatPrice ⟨9,7,2⟩ ≤ singleTariff 9 7 2 := by decide +kernel
private theorem cell_10_7_2 : fatPrice ⟨10,7,2⟩ ≤ singleTariff 10 7 2 := by decide +kernel
private theorem cell_11_7_2 : fatPrice ⟨11,7,2⟩ ≤ singleTariff 11 7 2 := by decide +kernel
private theorem cell_12_7_2 : fatPrice ⟨12,7,2⟩ ≤ singleTariff 12 7 2 := by decide +kernel
private theorem cell_3_8_2 : fatPrice ⟨3,8,2⟩ ≤ singleTariff 3 8 2 := by decide +kernel
private theorem cell_4_8_2 : fatPrice ⟨4,8,2⟩ ≤ singleTariff 4 8 2 := by decide +kernel
private theorem price_3_1 (b : ℕ) (lo : 1≤b) (hi : b≤26) :
    fatPrice ⟨b,3,1⟩ ≤ singleTariff b 3 1 := by
  interval_cases b
  · exact cell_1_3_1
  · exact cell_2_3_1
  · exact cell_3_3_1
  · exact cell_4_3_1
  · exact cell_5_3_1
  · exact cell_6_3_1
  · exact cell_7_3_1
  · exact cell_8_3_1
  · exact cell_9_3_1
  · exact cell_10_3_1
  · exact cell_11_3_1
  · exact cell_12_3_1
  · exact cell_13_3_1
  · exact cell_14_3_1
  · exact cell_15_3_1
  · exact cell_16_3_1
  · exact cell_17_3_1
  · exact cell_18_3_1
  · exact cell_19_3_1
  · exact cell_20_3_1
  · exact cell_21_3_1
  · exact cell_22_3_1
  · exact cell_23_3_1
  · exact cell_24_3_1
  · exact cell_25_3_1
  · exact cell_26_3_1
private theorem price_4_1 (b : ℕ) (lo : 2≤b) (hi : b≤24) :
    fatPrice ⟨b,4,1⟩ ≤ singleTariff b 4 1 := by
  interval_cases b
  · exact cell_2_4_1
  · exact cell_3_4_1
  · exact cell_4_4_1
  · exact cell_5_4_1
  · exact cell_6_4_1
  · exact cell_7_4_1
  · exact cell_8_4_1
  · exact cell_9_4_1
  · exact cell_10_4_1
  · exact cell_11_4_1
  · exact cell_12_4_1
  · exact cell_13_4_1
  · exact cell_14_4_1
  · exact cell_15_4_1
  · exact cell_16_4_1
  · exact cell_17_4_1
  · exact cell_18_4_1
  · exact cell_19_4_1
  · exact cell_20_4_1
  · exact cell_21_4_1
  · exact cell_22_4_1
  · exact cell_23_4_1
  · exact cell_24_4_1
private theorem price_5_1 (b : ℕ) (lo : 2≤b) (hi : b≤21) :
    fatPrice ⟨b,5,1⟩ ≤ singleTariff b 5 1 := by
  interval_cases b
  · exact cell_2_5_1
  · exact cell_3_5_1
  · exact cell_4_5_1
  · exact cell_5_5_1
  · exact cell_6_5_1
  · exact cell_7_5_1
  · exact cell_8_5_1
  · exact cell_9_5_1
  · exact cell_10_5_1
  · exact cell_11_5_1
  · exact cell_12_5_1
  · exact cell_13_5_1
  · exact cell_14_5_1
  · exact cell_15_5_1
  · exact cell_16_5_1
  · exact cell_17_5_1
  · exact cell_18_5_1
  · exact cell_19_5_1
  · exact cell_20_5_1
  · exact cell_21_5_1
private theorem price_6_1 (b : ℕ) (lo : 2≤b) (hi : b≤17) :
    fatPrice ⟨b,6,1⟩ ≤ singleTariff b 6 1 := by
  interval_cases b
  · exact cell_2_6_1
  · exact cell_3_6_1
  · exact cell_4_6_1
  · exact cell_5_6_1
  · exact cell_6_6_1
  · exact cell_7_6_1
  · exact cell_8_6_1
  · exact cell_9_6_1
  · exact cell_10_6_1
  · exact cell_11_6_1
  · exact cell_12_6_1
  · exact cell_13_6_1
  · exact cell_14_6_1
  · exact cell_15_6_1
  · exact cell_16_6_1
  · exact cell_17_6_1
private theorem price_7_1 (b : ℕ) (lo : 3≤b) (hi : b≤12) :
    fatPrice ⟨b,7,1⟩ ≤ singleTariff b 7 1 := by
  interval_cases b
  · exact cell_3_7_1
  · exact cell_4_7_1
  · exact cell_5_7_1
  · exact cell_6_7_1
  · exact cell_7_7_1
  · exact cell_8_7_1
  · exact cell_9_7_1
  · exact cell_10_7_1
  · exact cell_11_7_1
  · exact cell_12_7_1
private theorem price_8_1 (b : ℕ) (lo : 3≤b) (hi : b≤4) :
    fatPrice ⟨b,8,1⟩ ≤ singleTariff b 8 1 := by
  interval_cases b
  · exact cell_3_8_1
  · exact cell_4_8_1
private theorem price_6_2 (b : ℕ) (lo : 2≤b) (hi : b≤17) :
    fatPrice ⟨b,6,2⟩ ≤ singleTariff b 6 2 := by
  interval_cases b
  · exact cell_2_6_2
  · exact cell_3_6_2
  · exact cell_4_6_2
  · exact cell_5_6_2
  · exact cell_6_6_2
  · exact cell_7_6_2
  · exact cell_8_6_2
  · exact cell_9_6_2
  · exact cell_10_6_2
  · exact cell_11_6_2
  · exact cell_12_6_2
  · exact cell_13_6_2
  · exact cell_14_6_2
  · exact cell_15_6_2
  · exact cell_16_6_2
  · exact cell_17_6_2
private theorem price_7_2 (b : ℕ) (lo : 3≤b) (hi : b≤12) :
    fatPrice ⟨b,7,2⟩ ≤ singleTariff b 7 2 := by
  interval_cases b
  · exact cell_3_7_2
  · exact cell_4_7_2
  · exact cell_5_7_2
  · exact cell_6_7_2
  · exact cell_7_7_2
  · exact cell_8_7_2
  · exact cell_9_7_2
  · exact cell_10_7_2
  · exact cell_11_7_2
  · exact cell_12_7_2
private theorem price_8_2 (b : ℕ) (lo : 3≤b) (hi : b≤4) :
    fatPrice ⟨b,8,2⟩ ≤ singleTariff b 8 2 := by
  interval_cases b
  · exact cell_3_8_2
  · exact cell_4_8_2
private theorem single_price {b j t : ℕ} (ht : 1≤t) (hj : 3*t≤j)
    (hs : j≤8) (hv : j≤3*b) (hb : b≤lowDegreeCap j) :
    fatPrice ⟨b,j,t⟩≤singleTariff b j t := by
  have ht2 : t≤2 := by omega
  interval_cases t
  · have jl : 3≤j := by omega
    interval_cases j
    · exact price_3_1 b (by omega) hb
    · exact price_4_1 b (by omega) hb
    · exact price_5_1 b (by omega) hb
    · exact price_6_1 b (by omega) hb
    · exact price_7_1 b (by omega) hb
    · exact price_8_1 b (by omega) hb
  · have jl : 6≤j := by omega
    interval_cases j
    · exact price_6_2 b (by omega) hb
    · exact price_7_2 b (by omega) hb
    · exact price_8_2 b (by omega) hb
private def splitPrices (b j : ℕ) : List ℕ :=
  (List.range (b+1)).flatMap (fun c=>(List.range (j+1)).map (fun k=>
    if 3≤k ∧ k≤3*c ∧ 3≤j-k ∧ j-k≤3*(b-c) then
      singleTariff c k 1+singleTariff (b-c) (j-k) 1 else 0))
private def widthCharge (b j t : ℕ) : ℕ :=
  if t=0 then 0 else
    max (singleTariff b j t) (if t=2 then (splitPrices b j).foldr max 0 else 0)
private theorem le_fold_max {v : ℕ} {L : List ℕ} (mem : v∈L) : v≤L.foldr max 0 := by
  induction L with
  | nil => simp at mem
  | cons a tail ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | m
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih m).trans (le_max_right _ _)
private theorem width_single (b j t : ℕ) (hp : 0<t) : singleTariff b j t≤widthCharge b j t := by
  unfold widthCharge
  rw [ite_eq_right (Nat.ne_of_gt hp)]
  exact le_max_left _ _
private theorem width_pair (b c j k : ℕ) (hj : 3≤j) (hk : 3≤k) (hb : j≤3*b) (hc : k≤3*c) :
    singleTariff b j 1+singleTariff c k 1≤widthCharge (b+c) (j+k) 2 := by
  unfold widthCharge
  rw [ite_eq_right (by decide : ¬(2 : ℕ)=0), ite_eq_left rfl]
  apply le_trans _ (le_max_right _ _)
  apply le_fold_max
  unfold splitPrices
  refine List.mem_flatMap.mpr ⟨b,List.mem_range.mpr (by omega),?_⟩
  refine List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),?_⟩
  rw [show b+c-b=c by omega,show j+k-j=k by omega]
  rw [ite_eq_left ⟨hj,hb,hk,hc⟩]
private theorem checked_row (j : Fin 9) (t : Fin 3) :
    (List.range (lowDegreeCap j.val+1)).all (fun b=>decide
      (1≤t.val → 3*t.val≤j.val → j.val≤3*b → widthCharge b j.val t.val≤retainedTariff b j.val t.val)) = true := by
  fin_cases j <;> fin_cases t <;> decide +kernel
private theorem width_checked {b j t : ℕ} (ht : 1≤t) (hj : 3*t≤j)
    (hs : j≤8) (hv : j≤3*b) (hb : b≤lowDegreeCap j) :
    widthCharge b j t≤retainedTariff b j t := by
  have inj : t<3 := by omega
  have h := List.all_eq_true.mp (checked_row ⟨j,by omega⟩ ⟨t,inj⟩)
    b (List.mem_range.mpr (Nat.lt_succ_of_le hb))
  exact of_decide_eq_true h ht hj hv
theorem retained_family_fee (n : ℕ) (a : Fin n→Shape) (hv : ∀ i,Valid (a i))
    (hj : (∑ i,(a i).j)≤8) (hb : (∑ i,(a i).b) ≤ lowDegreeCap (∑ i,(a i).j)) :
    (∑ i,fatPrice (a i)) ≤ retainedTariff (∑ i,(a i).b) (∑ i,(a i).j) (∑ i,(a i).t) := by
  have hsum : 3*(∑ i,(a i).t)≤∑ i,(a i).j := by
    rw [Finset.mul_sum]
    exact sum_le_sum fun i _=>(hv i).2.1
  have hn' : n≤∑ i,(a i).t := calc
    n = ∑ _ : Fin n,1 := by simp
    _ ≤ ∑ i,(a i).t := sum_le_sum fun i _=>(hv i).1
  have hn : n≤2 := by omega
  interval_cases n
  · simp
  · simp only [Fin.sum_univ_one] at hj hb ⊢
    have one := hv 0
    have eq : a 0=⟨(a 0).b,(a 0).j,(a 0).t⟩ := by cases a 0; rfl
    conv_lhs => rw [eq]
    exact (single_price one.1 one.2.1 hj one.2.2 hb).trans
      ((width_single _ _ _ one.1).trans (width_checked one.1 one.2.1 hj one.2.2 hb))
  · simp only [Fin.sum_univ_two] at hsum hj hb ⊢
    have ht0 : (a 0).t=1 := by have := (hv 0).1; have := (hv 1).1; omega
    have ht1 : (a 1).t=1 := by have := (hv 0).1; have := (hv 1).1; omega
    have he (i : Fin 2) : a i=⟨(a i).b,(a i).j,(a i).t⟩ := by cases a i; rfl
    have shape0 : a 0=⟨(a 0).b,(a 0).j,1⟩ :=
      (he 0).trans (congrArg (fun t=>(⟨(a 0).b,(a 0).j,t⟩ : Shape)) ht0)
    have shape1 : a 1=⟨(a 1).b,(a 1).j,1⟩ :=
      (he 1).trans (congrArg (fun t=>(⟨(a 1).b,(a 1).j,t⟩ : Shape)) ht1)
    have hj0 : 3≤(a 0).j := by simpa only [ht0,Nat.mul_one] using (hv 0).2.1
    have hj1 : 3≤(a 1).j := by simpa only [ht1,Nat.mul_one] using (hv 1).2.1
    have j0hi : (a 0).j≤5 := by omega
    have j1hi : (a 1).j≤5 := by omega
    have totalB : (a 0).b+(a 1).b≤17 := by
      apply hb.trans
      have eq : (a 0).j+(a 1).j=6 ∨ (a 0).j+(a 1).j=7 ∨ (a 0).j+(a 1).j=8 := by omega
      rcases eq with eq | eq | eq <;> rw [eq] <;> decide
    have below (j : ℕ) (lo : 3≤j) (hi : j≤5) : 17≤lowDegreeCap j := by
      interval_cases j <;> decide
    have p0 := single_price (b:=(a 0).b) (t:=1) (by decide) (by simpa using hj0) (by omega)
      (hv 0).2.2 ((by omega : (a 0).b≤17).trans (below _ hj0 j0hi))
    have p1 := single_price (b:=(a 1).b) (t:=1) (by decide) (by simpa using hj1) (by omega)
      (hv 1).2.2 ((by omega : (a 1).b≤17).trans (below _ hj1 j1hi))
    rw [←shape0] at p0
    rw [←shape1] at p1
    have h := width_pair (a 0).b (a 1).b (a 0).j (a 1).j hj0 hj1 (hv 0).2.2 (hv 1).2.2
    rw [ht0,ht1]
    exact (Nat.add_le_add p0 p1).trans (h.trans (width_checked (by decide) (by omega) hj (by
      have := (hv 0).2.2; have := (hv 1).2.2; omega) hb))
#print axioms retained_family_fee
end Lower6960.Low

end
end Merged_R6960Low6960RetainedFees

-- merged module R6960Low6960Width
section Merged_R6960Low6960Width

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6960.Low
open Finset Polynomial
open P3 (K)
open K1_13 (Shape shape)
open K1_13_8 (Valid zeroShape)
open Low6960Retained (Box combined)
open Lower6960.Low (lowDegreeCap)
open P3_6_8 (shapeSum shapeSum_empty shapeSum_valid_or_empty)
open scoped Classical BigOperators

theorem degree_bound {r : Shape} (hr : Valid r) (hx : Box r) :
    r.b ≤ lowDegreeCap r.j := by
  have hjl : 3≤r.j := (Nat.mul_le_mul_left 3 hr.1).trans hr.2.1
  have hju := hx.2.1
  have hj : r.j=3 ∨ r.j=4 ∨ r.j=5 ∨ r.j=6 ∨ r.j=7 ∨ r.j=8 := by omega
  rcases hj with hj | hj | hj | hj | hj | hj <;> rw [hj] <;> simp only [lowDegreeCap]
  · exact hx.1
  · exact hx.2.2.1 (by omega)
  · exact hx.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.2.2 (by omega)

/-- The retained factors selected by the actual primary bank spend the
finite charge for their exact total width, before the positive-order allocation. -/
theorem Inventory.retained_charge {Γ : Finset K} {s : K→(Polynomial K)} (d : Inventory Γ s) :
    let r := combined (fun i=>shape (d.factor i)) d.zeros
    (∑ i∈d.zeros,fatPrice (shape (d.factor i))) ≤ retainedTariff r.b r.j r.t := by
  let q i := shape (d.factor i)
  let r := combined q d.zeros
  change (∑ i∈d.zeros,fatPrice (q i)) ≤ retainedTariff r.b r.j r.t
  by_cases empty : d.zeros=∅
  · simp [empty,r,combined,P3_6_8.shapeSum_empty,zeroShape,retainedTariff,retainedTariffs]
  · have box := (d.retained.resolve_left empty).1
    have hv : Valid r := (P3_6_8.shapeSum_valid_or_empty d.fits.1 d.zeros).resolve_left empty
    let e := d.zeros.equivFin.symm
    let ar : Fin d.zeros.card→Shape := fun i=>q (e i).val
    have sums (g : Shape→ℕ) : (∑ i,g (ar i)) = ∑ i∈d.zeros,g (q i) := by
      rw [←sum_attach d.zeros (fun i=>g (q i))]
      exact Fintype.sum_equiv e _ _ (fun _=>rfl)
    have hj : (∑ i,(ar i).j)≤8 := by rw [sums]; exact box.2.1
    have hb : (∑ i,(ar i).b)≤lowDegreeCap (∑ i,(ar i).j) := by
      rw [sums,sums]
      exact degree_bound hv box
    have h := retained_family_fee d.zeros.card ar (fun i=>d.fits.1 (e i).val) hj hb
    rw [sums,sums,sums,sums] at h
    exact h

#print axioms Inventory.retained_charge
end Lower6960.Low

end
end Merged_R6960Low6960Width

-- merged module R6960Low6960Prices
section Merged_R6960Low6960Prices

set_option Elab.async false
namespace Low6960Prices
noncomputable section
open P3 (I K node)
open K1_13 (Geom extend Row Shape shape Fits InBox Contact chart liftedChart mixed32 ceilDiv atJet
  OnFactor FatEligible OrderAt indexDegree)
open scoped BigOperators Polynomial

abbrev agreement := Lower6960.Low.agreement
abbrev physicalDegree := Lower6960.Low.physicalDegree
abbrev errors := Lower6960.Low.errors
abbrev incidenceGap := Lower6960.Low.incidenceGap
abbrev taylorLength := Lower6960.Low.taylorLength
abbrev anchorCutoff := Lower6960.Low.anchorCutoff
abbrev primaryCutoff := Lower6960.Low.primaryCutoff
def primaryBox : Shape := ⟨4012,1650,550⟩
abbrev layerWidth := Lower6960.Low.layerWidth
abbrev layerNeed := Lower6960.Low.need
abbrev symbolCount := Final50Price.symbolCount
abbrev TrueWeightLE := @Lower6960.Low.TrueWeightLE
abbrev LayerBudget := @Lower6960.Low.LayerBudget
abbrev remaining := Final50Price.remaining
abbrev Messages := Lower6960.Low.Messages
abbrev SmallFactor := Lower6960.Low.SmallFactor
abbrev LowerRow := Lower6960.Low.LowerRow
abbrev ProperCut := Lower6960.Low.ProperCut
abbrev ActiveFits := Final50Price.ActiveFits
abbrev Fits := @Lower6960.Low.Fits
abbrev fullCap := Lower6960.Low.fullCap
def lowerWidth (top : ℕ) : ℕ := 136-top
def lowerIndex (top : ℕ) : ℕ := 57-3*top
def lowerTop (top : ℕ) : ℕ := lowerIndex top/2
abbrev fatPrice := Lower6960.Low.fatPrice
abbrev FatEquations := Low6960Fat.FatEquations
abbrev Holds := Low6960Fat.Holds
abbrev fatOrder := Lower6960.Low.fatOrder
abbrev divisorOrder := Lower6960.Low.divisorOrder
abbrev isolatedOrder := Lower6960.Low.isolatedOrder
abbrev commonBox := Low6960Fat.commonBox
abbrev resultantBox := Low6960Fat.resultantBox
abbrev linearChart := Lower6960.Low.linearChart

theorem Messages.mono {w Γ s Δ} (h : Messages w Γ s) (hΔ : Δ ⊆ Γ) : Messages w Δ s :=
  Lower6960.Low.Messages.mono h hΔ

def lowerCap : ℕ → ℕ
  | 0 => 28939832636599906
  | 1 => 26150061697196931
  | 2 => 23488581035640966
  | 3 => 20958102538135074
  | 4 => 18560287483819229
  | 5 => 16297730917037374
  | 6 => 14172203991418967
  | 7 => 12186197718951818
  | 8 => 10341580113663363
  | 9 => 8640751373865300
  | 10 => 7085662950714511
  | 11 => 5678637856703625
  | 12 => 4421697147673414
  | 13 => 3317100687331508
  | 14 => 2366924894579984
  | _ => 0

def surfaceNumerator32 (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L + 1) p
  let b := liftedChart (L + 2) p
  min (mixed32 p q (chart (L + 1) p) (chart (L + 2) p))
    (mixed32 p q a b + (L + 1) * mixed32 p q g b + (L + 2) * mixed32 p q g a)
def physicalPriceOld (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32 p q) 32 +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
abbrev BentCap := Shape × ℕ

def bentGraph (p : Shape) : BentCap := (⟨max p.b (p.j + 1), p.j + 1, p.t + 1⟩, 1)

def bentLift (k : ℕ) (p : Shape) : BentCap :=
  let top := 2 + k * p.t
  (⟨1 + k * (p.b - 1), 4 + k * (p.j - 2), top⟩, min (1 + k) (top / 2))

def bentIntegral (B J T H : ℤ) : ℤ :=
  -576 * H ^ 5 + 160 * T ^ 2 * H ^ 3 - 480 * T ^ 3 * H ^ 2 + 540 * T ^ 4 * H
  + 960 * J * H ^ 4 - 320 * J * T * H ^ 3 + 960 * J * T ^ 2 * H ^ 2 - 1200 * J * T ^ 3 * H
  - 480 * J ^ 2 * H ^ 3 - 480 * J ^ 2 * T * H ^ 2 + 840 * J ^ 2 * T ^ 2 * H
  + 240 * J ^ 3 * H ^ 2 - 240 * J ^ 3 * T * H - 960 * B * H ^ 4 + 640 * B * T * H ^ 3
  - 1440 * B * T ^ 2 * H ^ 2 + 1440 * B * T ^ 3 * H + 640 * B * J * H ^ 3
  + 960 * B * J * T * H ^ 2 - 1440 * B * J * T ^ 2 * H - 480 * B * J ^ 2 * H ^ 2
  + 480 * B * J ^ 2 * T * H

def addBent (p q : BentCap) : BentCap := (p.1.plus q.1, p.2 + q.2)

def ambientMix (caps : List BentCap) : ℕ :=
  (caps.sublists.foldl (fun acc boxes =>
    let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
    acc + (-1 : ℤ) ^ (5 - boxes.length) *
      bentIntegral s.1.b s.1.j s.1.t s.2) 0).toNat

def tiltedSurface (p q : Shape) : ℕ :=
  ambientMix [(p, 0), (q, 0), bentGraph p,
    bentLift (taylorLength - 4) p, bentLift (taylorLength - 3) p]

def evenClip (p : Shape) (h amount : ℕ) : ℕ :=
  let c := min (min amount (p.b - p.j)) (min (p.j / 2) (2 * (p.t - h)))
  c - c % 2

def activeClips (p : Shape) (K : ℕ) : List (ℕ × ℕ) :=
  let c := evenClip p 0 (p.b + p.j - K)
  let g : Shape := ⟨p.b, p.j + 1, p.t + 1⟩
  let lift (k : ℕ) :=
    (k + 1, evenClip (bentLift k p).1 (k + 1) (2 + k * (c - 2)))
  [(0, c), (0, 498), (1, evenClip g 1 c), lift (taylorLength - 4), lift (taylorLength - 3)]

def activeLoss (cs : List (ℕ × ℕ)) : ℕ :=
  480 * ((cs.map Prod.snd).prod - (cs.map (fun x => x.2 - 2*x.1)).prod)

def tiltedSurfaceActive (p q : Shape) (K : ℕ) : ℕ :=
  tiltedSurface p q - activeLoss (activeClips p K)

def tiltedFits (x : Shape) : Prop := 3*x.t + 3 ≤ x.j ∧ x.j + 1 ≤ x.b

instance (x : Shape) : Decidable (tiltedFits x) := inferInstanceAs (Decidable (_ ∧ _))

def activeFitsPrice (x : Shape) (K : ℕ) : Prop :=
  3 ≤ x.t ∧ 4 ≤ evenClip x.chamber 0 (x.chamber.b + x.chamber.j - K) ∧
    (activeClips x.chamber K).all (fun c => decide (2*c.1 ≤ c.2)) = true

instance (x : Shape) (K : ℕ) : Decidable (activeFitsPrice x K) :=
  inferInstanceAs (Decidable (_ ∧ _))

def physicalPriceWith (x : Shape) (l surface : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv surface (60 * 32) +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixed32 p q auxBox h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q auxBox p + 2 * x.t * mixed32 p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)

def physicalPriceTilted (x : Shape) (l : ℕ) : ℕ :=
  physicalPriceWith x l (tiltedSurface x.chamber primaryBox)

def physicalPriceActive (x : Shape) (l K : ℕ) : ℕ :=
  physicalPriceWith x l (tiltedSurfaceActive x.chamber primaryBox K)

def physicalPrice (x : Shape) (l K : ℕ) : ℕ :=
  if tiltedFits x then
    let base := min (physicalPriceOld x l) (physicalPriceTilted x l)
    if activeFitsPrice x K then min base (physicalPriceActive x l K) else base
  else physicalPriceOld x l

def c5 (top : ℕ) : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ g, LowerRow top g →
    (∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) → Γ.card ≤ lowerCap top
def c6 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → ∀ K, ActiveFits f K →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → Γ.card ≤ physicalPrice (shape f) l K
def c7 : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) → FatEligible (shape f) →
    ∀ E : FatEquations, (∀ γ ∈ Γ, Holds E (extend (s γ))) → Γ.card ≤ fatPrice (shape f)

end
end Low6960Prices

end Merged_R6960Low6960Prices

-- merged module R6960Low6960Monotone
section Merged_R6960Low6960Monotone
set_option Elab.async false
section
namespace Low6960Monotone
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
theorem box_refl (x : Shape) : InBox x x := ⟨le_rfl, le_rfl, le_rfl⟩
theorem normalize_mono {x y : Shape} (h : InBox x y) :
    InBox x.chamber y.chamber := ⟨max_le_max h.1 h.2.1, h.2.1, h.2.2⟩
theorem normalize_chamber (x : Shape) (h : 3 * x.t ≤ x.j) :
    Chamber x.chamber := ⟨le_max_right _ _, h⟩
theorem plus_mono {x y u v : Shape} (h : InBox x y) (h' : InBox u v) :
    InBox (x.plus u) (y.plus v) :=
  ⟨Nat.add_le_add h.1 h'.1, Nat.add_le_add h.2.1 h'.2.1, Nat.add_le_add h.2.2 h'.2.2⟩
theorem plus_chamber {x y : Shape} (hx : Chamber x) (hy : Chamber y) :
    Chamber (x.plus y) := by
  exact ⟨Nat.add_le_add hx.1 hy.1, by simp only [Shape.plus, Nat.mul_add]; exact Nat.add_le_add hx.2 hy.2⟩
theorem scale_mono {x y : Shape} (h : InBox x y) (k : ℕ) :
    InBox (x.scale k) (y.scale k) :=
  ⟨Nat.mul_le_mul_left k h.1, Nat.mul_le_mul_left k h.2.1, Nat.mul_le_mul_left k h.2.2⟩
theorem scale_chamber {x : Shape} (hx : Chamber x) (k : ℕ) :
    Chamber (x.scale k) :=
  ⟨Nat.mul_le_mul_left k hx.1, by simpa [Shape.scale, Nat.mul_left_comm 3 k] using Nat.mul_le_mul_left k hx.2⟩
private theorem min_fits_index (a i : ℕ) : 3 * min a (i / 3) ≤ i := by
  have h := min_le_right a (i / 3)
  omega
theorem chart_chamber (L : ℕ) (x : Shape) : Chamber (chart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
private theorem lifted_chamber (L : ℕ) (x : Shape) : Chamber (liftedChart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
theorem chart_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (chart L x) (chart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [chart] <;> gcongr
private theorem lifted_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (liftedChart L x) (liftedChart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [liftedChart] <;> gcongr
private def graphShape (p : Shape) : Shape :=
  ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
private theorem graph_chamber (x : Shape) : Chamber (graphShape x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
private theorem graph_mono {x y : Shape} (h : InBox x y) :
    InBox (graphShape x) (graphShape y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [graphShape] <;> gcongr
private theorem surface_mono {p p' q : Shape} (hp : InBox p p') (hp' : Chamber p') (hq : Chamber q) :
    Low6960Prices.surfaceNumerator32 p q ≤ Low6960Prices.surfaceNumerator32 p' q := by
  let L := Low6960Prices.taylorLength
  have hchart : mixed32 p q (chart (L+1) p) (chart (L+2) p) ≤
      mixed32 p' q (chart (L+1) p') (chart (L+2) p') :=
    mixed_mono hp (box_refl q) (chart_mono _ hp) (chart_mono _ hp) hp' hq
      (chart_chamber _ _) hq (chart_chamber _ _) (chart_chamber _ _)
  have hlift : mixed32 p q (liftedChart (L+1) p) (liftedChart (L+2) p) ≤
      mixed32 p' q (liftedChart (L+1) p') (liftedChart (L+2) p') :=
    mixed_mono hp (box_refl q) (lifted_mono _ hp) (lifted_mono _ hp) hp' hq
      (lifted_chamber _ _) hq (lifted_chamber _ _) (lifted_chamber _ _)
  have hgraph (M : ℕ) :
      mixed32 p q (graphShape p) (liftedChart M p) ≤ mixed32 p' q (graphShape p') (liftedChart M p') :=
    mixed_mono hp (box_refl q) (graph_mono hp) (lifted_mono _ hp) hp' hq
      (graph_chamber _) hq (graph_chamber _) (lifted_chamber _ _)
  exact min_le_min hchart (Nat.add_le_add (Nat.add_le_add hlift (Nat.mul_le_mul_left _ (hgraph _)))
    (Nat.mul_le_mul_left _ (hgraph _)))
theorem ceil_mono {a b : ℕ} (h : a ≤ b) (l : ℕ) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)
theorem physical_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l : ℕ) : Low6960Prices.physicalPriceOld x l ≤ Low6960Prices.physicalPriceOld y l := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := Low6960Prices.primaryBox
  let L := Low6960Prices.taylorLength
  let A := q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp := normalize_mono h
  have hpc : Chamber p := normalize_chamber x hx
  have hp'c : Chamber p' := normalize_chamber y hy
  have hqc : Chamber q := ⟨by decide, le_rfl⟩
  have ha : InBox A A' := plus_mono (box_refl q) (scale_mono hp 4)
  have hac : Chamber A := plus_chamber hqc (scale_chamber hpc 4)
  have ha'c : Chamber A' := plus_chamber hqc (scale_chamber hp'c 4)
  have hs := surface_mono hp hp'c hqc
  have hb := (chart_mono (L+1) hp).1
  have hmain : (Low6960Prices.errors + 2*Low6960Prices.incidenceGap) * x.b * q.b * (chart (L+1) p).b ≤
      (Low6960Prices.errors + 2*Low6960Prices.incidenceGap) * y.b * q.b * (chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left Low6960Prices.errors hc) (Nat.mul_le_mul_left (2*Low6960Prices.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*Low6960Prices.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (ceil_mono (Nat.add_le_add (ceil_mono hs _) (ceil_mono hmain _)) l) hraw)
    (ceil_mono hgeom _)
end Low6960Monotone
end

namespace Low6960Monotone
open K1_13 (Shape)
open Low6960Prices (physicalPrice physicalPriceOld physicalPriceTilted physicalPriceActive physicalPriceWith)

theorem physicalPrice_le_old (x : Shape) (l K : ℕ) : physicalPrice x l K ≤ physicalPriceOld x l := by
  unfold physicalPrice
  split
  · split
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact min_le_left _ _
  · exact le_rfl

private theorem with_anti (a : Shape) (s : ℕ) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    physicalPriceWith a u s ≤ physicalPriceWith a l s := by
  unfold physicalPriceWith
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (K1_13_8.ceilDiv_anti _ hl h) _) _

theorem physicalPrice_anti (a : Shape) (K : ℕ) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    physicalPrice a u K ≤ physicalPrice a l K := by
  have hold : physicalPriceOld a u ≤ physicalPriceOld a l := by
    unfold physicalPriceOld
    exact Nat.add_le_add_right
      (Nat.add_le_add_right (K1_13_8.ceilDiv_anti _ hl h) _) _
  have hnew : physicalPriceTilted a u ≤ physicalPriceTilted a l := with_anti a _ hl h
  have hactive : physicalPriceActive a u K ≤ physicalPriceActive a l K := with_anti a _ hl h
  unfold physicalPrice
  split
  · split
    · exact min_le_min (min_le_min hold hnew) hactive
    · exact min_le_min hold hnew
  · exact hold
end Low6960Monotone

end Merged_R6960Low6960Monotone

end Merged_R6960Low6960Monotone

-- merged module R6960Low6960SurfaceLinearFour
section Merged_R6960Low6960SurfaceLinearFour

-- merged module R6960Low6960SharedPrice
section Merged_R6960Low6960SharedPrice
set_option Elab.async false
set_option autoImplicit false
namespace Low6960SharedPrice
open K1_13 (Shape chart ceilDiv mixed32 shape OnFactor extend)
open Low6960Prices (Messages SmallFactor ActiveFits ProperCut taylorLength primaryBox
  physicalPrice physicalDegree errors incidenceGap tiltedFits tiltedSurface)
open scoped Polynomial
abbrev slope : Shape := ⟨62,26,7⟩
abbrev slopeLoss : ℕ := 20625302605067
inductive Surface where
  | ordinary
  | tilted
  deriving DecidableEq
def surfaceScale : Surface → ℕ
  | .ordinary => 32
  | .tilted => 1920
def surface (kind : Surface) (f q : Shape) : ℕ :=
  match kind with
  | .ordinary =>
    let p := f.chamber
    mixed32 p q (chart (taylorLength + 1) p) (chart (taylorLength + 2) p)
  | .tilted => tiltedSurface f.chamber q
def weights (kind : Surface) (f : Shape) : Shape :=
  let b := surface kind f ⟨1,0,0⟩
  let j := surface kind f ⟨1,1,0⟩ - b
  let t := surface kind f ⟨3,3,1⟩ - 3 * (b+j)
  ⟨b,j,t⟩
def coord (p : Shape) (i : Fin 3) : ℕ := (![p.b,p.j,p.t] : Fin 3 → ℕ) i
def expression (w q : Shape) (useIndex topIndex : Bool) : ℕ :=
  3*w.b*(if useIndex then q.j else q.b) + 3*w.j*q.j +
    w.t*(if topIndex then q.j else 3*q.t)
def deficit (r a : ℕ) (f : Shape) : Shape :=
  ⟨r*slope.b-a*f.b,r*slope.j-a*f.j,r*slope.t-a*f.t⟩
structure Rate where
  kind : Surface
  pivot : Fin 3
  split : ℕ
  topIndex : Bool
  amount : ℕ
def RateFits (f : Shape) (u : Rate) : Prop :=
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let w := weights u.kind f
  let target := 3 * surfaceScale u.kind * u.amount
  (u.kind = .tilted → tiltedFits f) ∧
  0 < u.split ∧ u.split*p < q ∧
  (∀ i, p * coord f i ≤ q * coord slope i) ∧
  (∀ useIndex : Bool, expression w slope useIndex u.topIndex ≤ target) ∧
  (∀ useIndex : Bool, expression w (deficit q p f) useIndex u.topIndex ≤ target*(q-u.split*p))
instance (f : Shape) (u : Rate) : Decidable (RateFits f u) := by
  unfold RateFits
  infer_instance
private theorem expression_line (w f : Shape) (r a : ℕ) (u t : Bool)
    (hb : a*f.b ≤ r*slope.b) (hj : a*f.j ≤ r*slope.j) (ht : a*f.t ≤ r*slope.t) :
    expression w (deficit r a f) u t + a*expression w f u t = r*expression w slope u t := by
  have b := Nat.sub_add_cancel hb
  have j := Nat.sub_add_cancel hj
  have h := Nat.sub_add_cancel ht
  cases u <;> cases t <;> simp only [expression, deficit, Bool.false_eq_true, ↓reduceIte, ite_true]
  all_goals
    rw [mul_add, mul_add]
    simp only [mul_assoc, ← mul_add, ← add_assoc] <;> ring_nf at b j h ⊢
    <;> nlinarith only [congrArg (fun z => w.b*z) b, congrArg (fun z => w.b*z) j,
      congrArg (fun z => w.j*z) j, congrArg (fun z => w.t*z) j, congrArg (fun z => w.t*z) h]
private theorem affine_of_endpoints (p q s x y W r a : ℕ)
    (hp : 0 < p) (hb : a*q ≤ r*p)
    (h₀ : x ≤ W) (h₁ : (q : ℤ)*x-p*y ≤ (q-(s:ℤ)*p)*W) :
    (r : ℤ)*x-a*y ≤ (r-(s:ℤ)*a)*W := by
  have hq : (0 : ℤ) < p := by exact_mod_cast hp
  have hr : (a : ℤ)*q ≤ (r : ℤ)*p := by exact_mod_cast hb
  have hzero : (0 : ℤ) ≤ (W : ℤ)-x := sub_nonneg.mpr (by exact_mod_cast h₀)
  have hA := mul_nonneg (sub_nonneg.mpr hr) hzero
  have hB := mul_nonneg (Int.natCast_nonneg a)
    (show 0 ≤ (p : ℤ)*((y:ℤ)-s*W)-q*((x:ℤ)-W) by linarith)
  apply sub_nonneg.mp
  refine nonneg_of_mul_nonneg_left ?_ hq
  have ident : (p : ℤ)*(((r:ℤ)-s*a)*W-((r:ℤ)*x-a*y)) =
      ((r:ℤ)*p-a*q)*((W:ℤ)-x)+a*(p*((y:ℤ)-s*W)-q*((x:ℤ)-W)) := by ring
  rw [mul_comm, ident]
  exact add_nonneg hA hB
private theorem pivot_pos (i : Fin 3) : 0 < coord slope i := by fin_cases i <;> decide
theorem rate_bound {f : Shape} {u : Rate} (hu : RateFits f u) (r a : ℕ)
    (hfit : ∀ i, a*coord f i ≤ r*coord slope i) (chooseWidth : Bool) :
    expression (weights u.kind f) (deficit r a f) chooseWidth u.topIndex ≤
      (3*surfaceScale u.kind*u.amount)*(r-u.split*a) := by
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let W := 3*surfaceScale u.kind*u.amount
  let w := weights u.kind f
  obtain ⟨_,hs,hpos,hcoord,h₀,h₁⟩ := hu
  have hp : 0 < p := pivot_pos u.pivot
  have hfitPivot : a*q ≤ r*p := hfit u.pivot
  have har : u.split*a ≤ r := by
    by_contra! hbad
    have hleft := Nat.mul_lt_mul_of_pos_right hbad hp
    have hright := Nat.mul_le_mul_left a (Nat.le_of_lt hpos)
    exact (not_lt_of_ge (hfitPivot.trans' (by
      simpa only [mul_left_comm, mul_assoc, mul_comm] using hright : u.split*a*p ≤ a*q))) hleft
  have f0 := expression_line w f q p chooseWidth u.topIndex
    (hcoord 0) (hcoord 1) (hcoord 2)
  have f1 := expression_line w f r a chooseWidth u.topIndex
    (hfit 0) (hfit 1) (hfit 2)
  have hend : ((q : ℤ)*expression w slope chooseWidth u.topIndex -
      p*expression w f chooseWidth u.topIndex) ≤ (q-(u.split:ℤ)*p)*W := by
    have hnum : expression w (deficit q p f) chooseWidth u.topIndex ≤ W*(q-u.split*p) := h₁ chooseWidth
    have hnum' : (expression w (deficit q p f) chooseWidth u.topIndex : ℤ) ≤
        (W:ℤ)*(q-(u.split:ℤ)*p) := by
      have hh : (expression w (deficit q p f) chooseWidth u.topIndex : ℤ) ≤ (W:ℤ) * ((q-u.split*p : ℕ) : ℤ) := by exact_mod_cast hnum
      change u.split*p < q at hpos
      rwa [Int.ofNat_sub (Nat.le_of_lt hpos)] at hh
    have hline : (expression w (deficit q p f) chooseWidth u.topIndex : ℤ) +
        p*expression w f chooseWidth u.topIndex = q*expression w slope chooseWidth u.topIndex := by
      exact_mod_cast f0
    nlinarith
  have haff := affine_of_endpoints p q u.split _ _ W r a hp hfitPivot (h₀ chooseWidth) hend
  have hline : (expression w (deficit r a f) chooseWidth u.topIndex : ℤ) +
      a*expression w f chooseWidth u.topIndex = r*expression w slope chooseWidth u.topIndex := by
    exact_mod_cast f1
  have hgoal : (expression w (deficit r a f) chooseWidth u.topIndex : ℤ) ≤
      (W:ℤ)*(r-(u.split:ℤ)*a) := by nlinarith
  rw [← Nat.cast_mul, ← Nat.cast_sub har, ← Nat.cast_mul] at hgoal
  exact_mod_cast hgoal
theorem remainder_pos {f : Shape} {u : Rate} (hu : RateFits f u) {r a : ℕ}
    (hr : 0 < r) (hfit : ∀ i, a*coord f i ≤ r*coord slope i) : 0 < r-u.split*a := by
  obtain ⟨_,_,hs,_,_,_⟩ := hu
  have hp := pivot_pos u.pivot
  have hmark := hfit u.pivot
  by_cases ha : a = 0
  · simpa [ha] using hr
  have hm := Nat.mul_lt_mul_of_pos_left hs (Nat.pos_of_ne_zero ha)
  have h : u.split*a * coord slope u.pivot < r * coord slope u.pivot := by
    simpa only [mul_left_comm,mul_assoc,mul_comm] using hm.trans_le hmark
  exact Nat.sub_pos_of_lt (Nat.lt_of_mul_lt_mul_right h)
theorem chamber_bound {f : Shape} {u : Rate} (hu : RateFits f u) (r a : ℕ)
    (hfit : ∀ i, a*coord f i ≤ r*coord slope i) (g : Shape)
    (hg : K1_13.InBox g (deficit r a f)) (hgt : 3*g.t ≤ g.j) :
    3*((weights u.kind f).b*g.chamber.b + (weights u.kind f).j*g.j + (weights u.kind f).t*g.t) ≤
      (3*surfaceScale u.kind*u.amount)*(r-u.split*a) := by
  let w := weights u.kind f
  let d := deficit r a f
  have hgB : g.b ≤ d.b := hg.1
  have hgJ : g.j ≤ d.j := hg.2.1
  have hgT : g.t ≤ d.t := hg.2.2
  have hTop : 3*g.t ≤ (if u.topIndex then d.j else 3*d.t) := by
    split
    · exact hgt.trans hgJ
    · exact Nat.mul_le_mul_left _ hgT
  have component (i : Bool)
      (hB : max g.b g.j ≤ (if i then d.j else d.b)) :
      3*(w.b*g.chamber.b + w.j*g.j + w.t*g.t) ≤ expression w d i u.topIndex := by
    change 3*(w.b*max g.b g.j + w.j*g.j + w.t*g.t) ≤ _
    unfold expression
    calc
      _ = 3*w.b*max g.b g.j + 3*w.j*g.j + w.t*(3*g.t) := by ring
      _ ≤ _ := Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul_left _ hB) (Nat.mul_le_mul_left _ hgJ)) (Nat.mul_le_mul_left _ hTop)
  rcases le_total d.b d.j with h | h
  · exact (component true (max_le (hgB.trans h) hgJ)).trans (rate_bound hu r a hfit true)
  · exact (component false (max_le hgB (hgJ.trans h))).trans (rate_bound hu r a hfit false)
def additiveBase (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let h1 := chart (taylorLength+1) p
  let cont := ceilDiv ((errors+2*incidenceGap)*x.b*q.b*h1.b) incidenceGap
  let z := q.plus (p.scale 4)
  let cv := mixed32 p q z h + 2*x.t*mixed32 p p p h
  let pt := mixed32 p q z p + 2*x.t*mixed32 p p p p
  ceilDiv cont l + 2*physicalDegree*x.b*q.b +
    ceilDiv (errors*cv+2*incidenceGap*pt) (32*incidenceGap)
def nonsharedFee (x : Shape) (l : ℕ) : ℕ :=
  ceilDiv (2*x.b*primaryBox.b^2*(chart (taylorLength+2) x.chamber).b) l
def price (x : Shape) (l K : ℕ) (u : Rate) : ℕ :=
  ceilDiv (physicalPrice x l K + u.split*additiveBase x l + u.split*u.amount + 1)
    (u.split+1) + nonsharedFee x l
def cShared : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → ∀ K, ActiveFits f K →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → ∀ u, RateFits (shape f) u →
      Γ.card ≤ price (shape f) l K u
end Low6960SharedPrice

end Merged_R6960Low6960SharedPrice

-- merged module R6960Low6960SurfaceLinearFour
section Merged_R6960Low6960SurfaceLinearFour
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Low6960SharedPrice
open K1_13 (Shape chart difference volume32)
open K1_13_8 (Valid)
open Low6960Prices (taylorLength)
open K1_13_8_2 (signedMixed signed_rotate signed_nonneg)
theorem surface_eq_weights_of_signed (kind : Surface) (f : Shape) (b j t : ℤ)
    (hb : 0 ≤ b) (hj : 0 ≤ j) (ht : 0 ≤ t)
    (h : ∀ q : Shape, (surface kind f q : ℤ) = b*q.b + j*q.j + t*q.t) (q : Shape) :
    surface kind f q = (weights kind f).b*q.b + (weights kind f).j*q.j +
      (weights kind f).t*q.t := by
  have hn (u : Shape) : surface kind f u = b.toNat*u.b + j.toNat*u.j + t.toNat*u.t := by
    apply Int.ofNat.inj
    change (surface kind f u : ℤ) = ((b.toNat*u.b + j.toNat*u.j + t.toNat*u.t : ℕ) : ℤ)
    rw [h u]
    push_cast
    rw [Int.toNat_of_nonneg hb, Int.toNat_of_nonneg hj, Int.toNat_of_nonneg ht]
  have hw : weights kind f = ⟨b.toNat,j.toNat,t.toNat⟩ := by
    unfold weights
    simp only [hn ⟨1,0,0⟩, hn ⟨1,1,0⟩, hn ⟨3,3,1⟩, Nat.mul_one, Nat.mul_zero,
      Nat.add_zero, Nat.add_sub_cancel_left]
    congr 1
    omega
  rw [hw]
  exact hn q
private theorem signed_four_linear (q p r s : Shape) :
    signedMixed q p r s = signedMixed ⟨1,0,0⟩ p r s*q.b +
      signedMixed ⟨0,1,0⟩ p r s*q.j + signedMixed ⟨0,0,1⟩ p r s*q.t := by
  simp only [signedMixed, difference, volume32, Shape.plus, Nat.cast_add, Nat.cast_zero,
    Nat.cast_one]
  ring
theorem surface_ordinary_eq_weights {f : Shape} (hf : Valid f) (q : Shape) :
    surface .ordinary f q = (weights .ordinary f).b*q.b + (weights .ordinary f).j*q.j +
      (weights .ordinary f).t*q.t := by
  let p := f.chamber
  let r := chart (taylorLength+1) p
  let s := chart (taylorLength+2) p
  have hp : K1_13_8_2.Chamber p := ⟨le_max_right _ _,hf.2.1⟩
  have hr : K1_13_8_2.Chamber r := K1_13_7_1.chart_chamber _ _
  have hs : K1_13_8_2.Chamber s := K1_13_7_1.chart_chamber _ _
  have hnonneg (u : Shape) : 0 ≤ signedMixed u r s p := signed_nonneg u r s p hr hs hp
  refine surface_eq_weights_of_signed .ordinary f _ _ _ (hnonneg ⟨1,0,0⟩)
    (hnonneg ⟨0,1,0⟩) (hnonneg ⟨0,0,1⟩) (fun u => ?_) q
  change (↑(signedMixed p u r s).toNat : ℤ) = _
  rw [signed_rotate, Int.toNat_of_nonneg (hnonneg u)]
  exact signed_four_linear u r s p
#print axioms surface_ordinary_eq_weights
end Low6960SharedPrice

end Merged_R6960Low6960SurfaceLinearFour

end Merged_R6960Low6960SurfaceLinearFour
