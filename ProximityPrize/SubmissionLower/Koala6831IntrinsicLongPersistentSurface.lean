import ProximityPrize.SubmissionLower.Koala6831IntrinsicFrobeniusSlice
import ProximityPrize.SubmissionLower.Koala6831IntrinsicChartPersistentIncidence

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open scoped Classical BigOperators
open RCN002 RCN005 RCN044 RCN135 RCN136 RCN137 RCN264 RCN267 RCN341 RCN344
open Koala6831OrdinaryIncidence

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option synthInstance.maxHeartbeats 450000
set_option maxRecDepth 22000
set_option linter.style.haveILetI false

variable {K I : Type} [Field K] [CharP K 2130706433]

theorem long_persistent_surface_selected_count
    (F : Carrier K) (hF : Irreducible F)
    (hweight : RCN234.wt (![1, 131071, 0, 0] : Fin 4 → ℕ) F < 4000000)
    (ht : ∀ d ∈ F.support, d 2 ≤ 200) (hz : ∀ d ∈ F.support, d 3 ≤ 162)
    (G : MvPolynomial (Fin 3) (GenericField K)) (hG : Irreducible G)
    (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F)
    (hfirst : G ∣ surfaceMap (polynomialEmbedding K) (tailNumerator F 131071))
    (hGy : G.degreeOf 0 ≤ 22) (hGz : G.degreeOf 2 ≤ 162)
    (x : I ↪ K) (u₀ u₁ : I → K) (nodes : Finset I)
    (hAn : 181084 ≤ nodes.card) (haverage : nodeAverage nodes.card 131071 181084 ≤ 3)
    (seeds allSeeds : Finset K) (hsub : seeds ⊆ allSeeds)
    (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hgraph : ∀ g ∈ seeds, graphSpecialize (selected g) g (g ^ 2130706433) F = 0)
    (hreg : ∀ g ∈ seeds, graphSpecialize (selected g) g (g ^ 2130706433)
      (implicitRegularity F) ≠ 0)
    (hzero : ∀ g ∈ seeds, MvPolynomial.eval (selectedGraphPoint 2130706433 selected g) G = 0)
    (hagreements : ∀ g ∈ seeds, 181084 ≤
      (nodes.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hpencil : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ 131071 → P₁.natDegree ≤ 131071 →
      (RCN050.pencilSeeds allSeeds selected P₀ P₁).card ≤ 81061) :
    seeds.card ≤ 1050000000000 * G.degreeOf 0 := by
  classical
  let Ω := GenericField K
  let φ := polynomialEmbedding K
  let p := 2130706433
  let H := surfaceMap φ (implicitRegularity F)
  let T := frobeniusSlice Ω p
  let C := RegularComponent Ω G T H
  let onCurve (c : C) := componentSeeds Ω G T H seeds (selectedGraphPoint p selected) c
  letI : CharP Ω p := genericField_charP K p
  have hcover : seeds.card ≤ ∑ c : C, (onCurve c).card :=
    frobeniusSlice_seed_cover p F G seeds selected hzero hreg
  by_cases hC : Nonempty C
  swap
  · letI : IsEmpty C := not_nonempty_iff.mp hC
    have hempty : seeds.card ≤ 0 := by simpa using hcover
    exact hempty.trans (Nat.zero_le _)
  have hregular (c : C) : MvPolynomial.pderiv (0 : Fin 3) G ∉ c.1 := by
    intro hd
    apply regularComponent_H_not_mem Ω G T H c
    obtain ⟨Q, hQ⟩ := hdiv
    have hGmem := regularComponent_G_mem Ω G T H c
    have hH : H = MvPolynomial.pderiv (0 : Fin 3) (surfaceMap φ F) :=
      (surfaceMap_pderiv φ F 0).symm
    let P : Ideal (MvPolynomial (Fin 3) Ω) := c.1
    change H ∈ P
    rw [hH, hQ, MvPolynomial.pderiv_mul]
    exact P.add_mem (P.mul_mem_right _ hd) (P.mul_mem_right _ hGmem)
  have hGpos : 0 < G.degreeOf 0 := by
    apply Nat.pos_of_ne_zero
    intro hY
    obtain ⟨c⟩ := hC
    have hdiff : MvPolynomial.pderiv (0 : Fin 3) G = 0 := by
      apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
      intro hy
      exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hy) hY
    exact hregular c (hdiff.symm ▸ c.1.zero_mem)
  have hFpos : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3 := by
    have hmem := hGpos.trans_le ((coordinate_degree_le_of_dvd 0 G (surfaceMap φ F) hdiv
      (surfaceMap_ne_zero φ (polynomialEmbedding_injective K) F hF.ne_zero)).trans
      (surfaceMap_degreeOf_le φ F 0))
    change 0 < F.degreeOf 1 at hmem
    omega
  let hx (c : C) : Transcendental Ω (coordinate Ω c.1 1) :=
    frobeniusSlice_seed_transcendental p G H c (hregular c)
  letI : ∀ c : C, Algebra (RatFunc Ω) (CoordinateField Ω c.1) :=
    fun c => rationalBaseAlgebra Ω c.1 1 (hx c)
  let d (c : C) := Module.finrank (RatFunc Ω) (CoordinateField Ω c.1)
  obtain ⟨fields, hsum⟩ := frobeniusSlice_projection_budget p G H hG
    (hGy.trans_lt (by decide)) (hGz.trans_lt (by decide)) hregular hGpos
  have hcount (c : C) : (onCurve c).card ≤ 1050000000000 * d c := by
    let base : SeparableLiteralCoordinate c.1 := ⟨1, hx c, (fields c).1, (fields c).2⟩
    letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω c.1) := (fields c).1
    have hpos : 1 ≤ d c := Module.finrank_pos
    have hmem (g : K) (hg : g ∈ onCurve c) :
        g ∈ seeds ∧ c.1 ≤ (RingHom.ker (MvPolynomial.aeval (selectedGraphPoint p selected g)).toRingHom) :=
      Finset.mem_filter.mp hg
    have hGmem : G ∈ c.1 := regularComponent_G_mem Ω G T H c
    have hFmem : surfaceMap φ F ∈ c.1 := c.1.mem_of_dvd hdiv hGmem
    have hS : H ∉ c.1 := regularComponent_H_not_mem Ω G T H c
    have htail (j : ℕ) : surfaceMap φ (tailNumerator F (131071 + j)) ∈ c.1 :=
      c.1.mem_of_dvd (geometric_dvd_tailNumerator_add F hF hFpos 131071 G hG hdiv hfirst j) hGmem
    have hpoles (W : Finset (Place Ω (CoordinateField Ω c.1))) :=
      frobeniusSlice_component_poles p c.1 (regularComponent_T_mem Ω G T H c) (hx c)
        (fields c).1 (fields c).2 W
    have hlocal := persistent_curve_selected_seed_bound F 131071 4000000 p 200 162 c.1 base
      (d c) (p * d c) (fun W => (hpoles W).1) (fun W => by exact_mod_cast (hpoles W).2)
      hFmem hS htail (by decide) (by decide) (by decide) hweight ht hz
      x u₀ u₁ nodes 181084 81060 (by decide) hAn haverage (onCurve c) allSeeds
      (fun g hg => hsub (hmem g hg).1) selected (fun g => g ^ p)
      (fun g hg => hdegree g (hmem g hg).1)
      (fun g hg => hgraph g (hmem g hg).1)
      (fun g hg => by
        rw [eval_polynomialGraphSurfacePoint, ne_eq, polynomialEmbedding_eq_zero_iff]
        exact hreg g (hmem g hg).1)
      (fun g hg => (hmem g hg).2) (fun g hg => hagreements g (hmem g hg).1) hpencil
    refine hlocal.trans ?_
    change 3 * ((200 + 1) * d c + 162 * (2130706433 * d c)) + (81060 + 1) ≤ 1050000000000 * d c
    omega
  calc
    _ ≤ ∑ c : C, (onCurve c).card := hcover
    _ ≤ ∑ c : C, 1050000000000 * d c := Finset.sum_le_sum (fun c _ => hcount c)
    _ = 1050000000000 * ∑ c : C, d c := (Finset.mul_sum _ _ _).symm
    _ ≤ 1050000000000 * G.degreeOf 0 := Nat.mul_le_mul_left _ hsum

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
