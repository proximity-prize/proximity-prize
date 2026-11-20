import ProximityPrize.SubmissionLower.Bridge6925Sections
import ProximityPrize.SubmissionLower.Fast076
set_option Elab.async false
section PackSource_P0_10RBridgeLedger
set_option autoImplicit true
namespace P0_10R.Bridge

noncomputable section

open K1_14_2 (Ambient)
open K1_14_2_2 (Fits mass dot weight dot_mono dot_mass_sdiff mass_mono)
open scoped BigOperators

private def firstWeight (fee : Fin 3) := weight stageFiveShape fee
private def midWeight (fee : Fin 3) := weight stageLateShape fee
private def lastWeight (fee : Fin 3) := weight terminalFullShape fee
private def delta (a b : Fin 4 → ℕ) := fun j => b j - a j

private theorem expand_dot (a b : Fin 4 → ℕ) (h : ∀ j, a j ≤ b j) (v : Fin 4 → ℕ) :
    dot b v = dot a v + dot (delta a b) v := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Nat.add_mul, show a j + delta a b j = b j from Nat.add_sub_of_le (h j)]

def extraFee (fee : Fin 3) : ℕ := if fee = 2 then fixedPrice 319 66 + fixedPrice 837 168 else 0

private theorem schedule_charge (fee : Fin 3)
    (A B D U V lastSet : Finset (Ideal Ambient)) (hBA : B ⊆ A) (hDB : D ⊆ B)
    (hU : U ⊆ A \ B) (hV : V ⊆ B \ D) (hZ : lastSet ⊆ D)
    (hA : Fits A initialCap) (hB : Fits B reserveFiveCap) (hD : Fits D lateCap) :
    dot (firstWeight fee) (mass U) + (dot (midWeight fee) (mass V) + dot (lastWeight fee) (mass lastSet) + extraFee fee) ≤
      dot (firstWeight fee) initialCap + dot (delta (firstWeight fee) (midWeight fee)) reserveFiveCap +
      dot (delta (midWeight fee) (lastWeight fee)) lateCap + extraFee fee := by
  let a := firstWeight fee
  let b := midWeight fee
  let c := lastWeight fee
  have hab : ∀ j, a j ≤ b j := by fin_cases fee <;> intro j <;> fin_cases j <;> decide
  have hbc : ∀ j, b j ≤ c j := by fin_cases fee <;> intro j <;> fin_cases j <;> decide
  have hmid : dot b (mass V) + dot c (mass lastSet) ≤ dot b (mass B) + dot (delta b c) (mass D) := by
    calc
      _ ≤ dot b (mass (B \ D)) + dot c (mass D) :=
        Nat.add_le_add (dot_mono _ _ _ (mass_mono hV)) (dot_mono _ _ _ (mass_mono hZ))
      _ = _ := by rw [expand_dot b c hbc, ← Nat.add_assoc, dot_mass_sdiff hDB]
  have hsum : dot a (mass U) + (dot b (mass V) + dot c (mass lastSet)) ≤
      dot a (mass A) + dot (delta a b) (mass B) + dot (delta b c) (mass D) := by
    calc
      _ ≤ dot a (mass (A \ B)) + (dot b (mass B) + dot (delta b c) (mass D)) :=
        Nat.add_le_add (dot_mono _ _ _ (mass_mono hU)) hmid
      _ = _ := by rw [expand_dot a b hab (mass B), ← Nat.add_assoc, ← Nat.add_assoc, dot_mass_sdiff hBA]
  have hcap := Nat.add_le_add (Nat.add_le_add (dot_mono a _ _ hA) (dot_mono (delta a b) _ _ hB))
    (dot_mono (delta b c) _ _ hD)
  dsimp only [a,b,c] at hsum hcap
  simpa only [Nat.add_assoc] using Nat.add_le_add_right (hsum.trans hcap) (extraFee fee)

theorem loss_bounds (A B D U V lastSet : Finset (Ideal Ambient)) (hBA : B ⊆ A) (hDB : D ⊆ B)
    (hU : U ⊆ A \ B) (hV : V ⊆ B \ D) (hZ : lastSet ⊆ D)
    (hA : Fits A initialCap) (hB : Fits B reserveFiveCap) (hD : Fits D lateCap) :
    dot (weight stageFiveShape 0) (mass U) + (dot (weight stageLateShape 0) (mass V) + dot (weight terminalFullShape 0) (mass lastSet) + extraFee 0) ≤ lossSeedCap ∧
    dot (weight stageFiveShape 1) (mass U) + (dot (weight stageLateShape 1) (mass V) + dot (weight terminalFullShape 1) (mass lastSet) + extraFee 1) ≤ lossYCap ∧
    dot (weight stageFiveShape 2) (mass U) + (dot (weight stageLateShape 2) (mass V) + dot (weight terminalFullShape 2) (mass lastSet) + extraFee 2) ≤ constantFee := by
  have h := fun fee => schedule_charge fee A B D U V lastSet hBA hDB hU hV hZ hA hB hD
  exact ⟨(h 0).trans (by decide +kernel), (h 1).trans (by decide +kernel), (h 2).trans (by decide +kernel)⟩

theorem prefix_ledger (w : ℤ) (hw : w ≤ 3554) :
    initialFee + fixedPrice 76 16 + fixedPrice 222 46 +
      fixedPrice 126 27 + fixedPrice 369 77 + fixedPrice 350344 63777 +
      constantFee + curveFee ≤ P0.highPrefix w := by
  unfold P0.highPrefix K21.highPrefix
  rw [ite_eq_left hw]
  decide +kernel
end
end P0_10R.Bridge
end PackSource_P0_10RBridgeLedger
section PackSource_P0_10RBridgeRootDonors
set_option autoImplicit true
namespace P0_10R.Bridge

/- Assembly of the unchanged geometric lemmas from the 69.15 port. -/
private theorem donor_1_1_1 : K1_14_2_4_1_1.c1 :=
  K1_14_2_4_1_1_1.proof
private theorem donor_1_1_2 : K1_14_2_4_1_1.c2 :=
  K1_14_2_4_1_1_2.proof
private theorem donor_1_1 : K1_14_2_4_1.c1 :=
  K1_14_2_4_1_1.of_children donor_1_1_1 donor_1_1_2
private theorem donor_1_2_1 : K1_14_2_4_1_2.c1 :=
  K1_14_2_4_1_2_1.proof
private theorem donor_1_2_2 : K1_14_2_4_1_2.c2 :=
  K1_14_2_4_1_2_2.proof
private theorem donor_1_2 : K1_14_2_4_1.c2 :=
  K1_14_2_4_1_2.of_children donor_1_2_1 donor_1_2_2
private theorem donor_1_3_1 : K1_14_2_4_1_3.c1 :=
  K1_14_2_4_1_3_1.proof
private theorem donor_1_3_2_1 : K1_14_2_4_1_3_2.c1 :=
  K1_14_2_4_1_3_2_1.proof
private theorem donor_1_3_2_2 : K1_14_2_4_1_3_2.c2 :=
  K1_14_2_4_1_3_2_2.proof
private theorem donor_1_3_2 : K1_14_2_4_1_3.c2 :=
  K1_14_2_4_1_3_2.of_children donor_1_3_2_1 donor_1_3_2_2
private theorem donor_1_3_3_1 : K1_14_2_4_1_3_3.c1 :=
  K1_14_2_4_1_3_3_1.proof
private theorem donor_1_3_3_2 : K1_14_2_4_1_3_3.c2 :=
  K1_14_2_4_1_3_3_2.proof
private theorem donor_1_3_3_3 : K1_14_2_4_1_3_3.c3 :=
  K1_14_2_4_1_3_3_3.proof
private theorem donor_1_3_3 : K1_14_2_4_1_3.c3 :=
  K1_14_2_4_1_3_3.of_children donor_1_3_3_1 donor_1_3_3_2 donor_1_3_3_3
private theorem donor_1_3 : K1_14_2_4_1.c3 :=
  K1_14_2_4_1_3.of_children donor_1_3_1 donor_1_3_2 donor_1_3_3
private theorem donor_1_4_1 : K1_14_2_4_1_4.c1 :=
  K1_14_2_4_1_4_1.proof
private theorem donor_1_4_2 : K1_14_2_4_1_4.c2 :=
  K1_14_2_4_1_4_2.proof
private theorem donor_1_4_3 : K1_14_2_4_1_4.c3 :=
  K1_14_2_4_1_4_3.proof
private theorem donor_1_4 : K1_14_2_4_1.c4 :=
  K1_14_2_4_1_4.of_children donor_1_4_1 donor_1_4_2 donor_1_4_3
private theorem donor_1_5_1 : K1_14_2_4_1_5.c1 :=
  K1_14_2_4_1_5_1.proof
private theorem donor_1_5_2 : K1_14_2_4_1_5.c2 :=
  K1_14_2_4_1_5_2.proof
private theorem donor_1_5 : K1_14_2_4_1.c5 :=
  K1_14_2_4_1_5.of_children donor_1_5_1 donor_1_5_2
theorem root_chart : K1_14_2_4.c1 :=
  K1_14_2_4_1.of_children donor_1_1 donor_1_2 donor_1_3 donor_1_4 donor_1_5
theorem root_taylor : K1_14_2_4.c2 :=
  K1_14_2_4_2.proof
private theorem donor_3_1_1 : K1_14_2_4_3_1.c1 :=
  K1_14_2_4_3_1_1.proof
private theorem donor_3_1_2 : K1_14_2_4_3_1.c2 :=
  K1_14_2_4_3_1_2.proof
private theorem donor_3_1_P0_10RBridgeRootDonors : K1_14_2_4_3.c1 :=
  K1_14_2_4_3_1.of_children donor_3_1_1 donor_3_1_2
private theorem donor_3_2_1 : K1_14_2_4_3_2.c1 :=
  K1_14_2_4_3_2_1.proof
private theorem donor_3_2_2 : K1_14_2_4_3_2.c2 :=
  K1_14_2_4_3_2_2.proof
private theorem donor_3_2_P0_10RBridgeRootDonors : K1_14_2_4_3.c2 :=
  K1_14_2_4_3_2.of_children donor_3_2_1 donor_3_2_2
theorem root_embedding : K1_14_2_4.c3 :=
  K1_14_2_4_3.of_children donor_3_1_P0_10RBridgeRootDonors donor_3_2_P0_10RBridgeRootDonors

end P0_10R.Bridge
end PackSource_P0_10RBridgeRootDonors
section PackSource_P0_10RBridgeRoot
set_option autoImplicit true
namespace P0_10R.Bridge

noncomputable section

open P0 (K I node p)
open K1_14 (FX L seedEmbedding)
open K1_14_2 (endpointDegree)
open K1_14_2_4 hiding specialize
open Polynomial MvPolynomial Finset
open scoped BigOperators
open private proper_section_card from ProximityPrize.SubmissionLower.Fast055

private theorem regular_count_P0_10RBridgeRoot {n U s g H w} (A : RegularChart U s g H n)
    (hw : P0_10.FixedWord w U s endpointDegree)
    (C : TaylorForms n (ordinateBound endpointDegree g) (taylorPower endpointDegree))
    (hrec : ∀ γ ∈ U, C.Recovers (A.parameter γ) (s γ)) (hdegree : c3) :
    (U.card : ℚ) ≤
      beta * ((taylorPower endpointDegree * (g * H) +
        ordinateBound endpointDegree g * H : ℕ) : ℚ) + 1 := by
  classical
  let a := ordinateBound endpointDegree g
  let b := taylorPower endpointDegree
  let D := b * (g * H) + a * H
  have ha : 0 < a := by simp [a, ordinateBound]
  have hb : 0 < b := by decide
  let P := linearIdeal a b A.source
  let M := bidegreeMap (Fin n) FX a b
  let v (γ : K) := markedPoint (A.parameter γ) (s γ)
  let point (γ : K) := monomialPoint (bidegreeExponents (Fin n) a b) (v γ)
  have hP : P.IsPrime := A.source_prime.comap M
  let _ : P.IsPrime := hP
  have hdim_eq : (affineHilbertPolynomial P).natDegree =
      (affineHilbertPolynomial A.source).natDegree :=
    natDegree_affineHilbertPolynomial_comap_bidegreeMap ha hb _
  have hdim := hdim_eq.trans_le A.source_dim
  have hdeg (h : (affineHilbertPolynomial P).natDegree = 1) : affineDegree P ≤ (D : ℚ) :=
    hdegree n a b (g * H) H ha hb A.source A.source_prime (hdim_eq.symm.trans h) A.slices
  have eval_linear (γ : K) (F : LinearRing n a b) :
      MvPolynomial.aeval (point γ) F = MvPolynomial.aeval (v γ) (M F) := by
    rw [show M = monomialMap FX (bidegreeExponents (Fin n) a b) from
      bidegreeMap_eq_monomialMap a b]
    exact aeval_monomialPoint _ _
  have hpoints (γ : K) (hγ : γ ∈ U) : point γ ∈ zeroLocus FX P := by
    intro F hF
    rw [eval_linear]
    exact A.lies_on γ hγ _ hF
  have hinj : Set.InjOn point (U : Set K) := by
    intro γ hγ η hη heq
    have hv := (monomialPoint_injective (fun i =>
      single_mem_bidegreeExponents ha hb i) : Function.Injective
      (monomialPoint (E := FX) (bidegreeExponents (Fin n) a b))) heq
    exact hw.distinct hγ hη (Polynomial.map_injective _ (algebraMap K L).injective
      (IsFractionRing.injective L[X] FX (congrFun hv none)))
  have hsection (i : I) (hmiss : ∃ γ ∈ U, (s γ).eval (node i) ≠ w i) :
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ D := by
    let x := node i
    let y := w i
    let q := C.numerator x - MvPolynomial.C (seedEmbedding y) * C.denominator
    have hq : q ∈ restrictBidegree (Fin n) FX a b := by
      refine Submodule.sub_mem _ (C.numerator_bound x) ?_
      rw [← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ C.denominator_bound
    let Q := bidegreeLift q hq
    have hcut (γ : K) (hγ : γ ∈ U) :
        MvPolynomial.aeval (point γ) Q = 0 ↔ (s γ).eval x = y := by
      have hr := hrec γ hγ
      change MvPolynomial.aeval (v γ) C.denominator ≠ 0 ∧
        (∀ x, MvPolynomial.aeval (v γ) (C.numerator x) =
          MvPolynomial.aeval (v γ) C.denominator * seedEmbedding ((s γ).eval x)) at hr
      rw [eval_linear, show M Q = q from bidegreeMap_bidegreeLift q hq]
      dsimp only [q]
      rw [map_sub, map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, hr.2 x,
        sub_eq_zero, mul_comm (seedEmbedding y), mul_right_inj' hr.1]
      exact seedEmbedding.injective.eq_iff
    have hproper : Q ∉ P := by
      obtain ⟨γ, hγ, hγmiss⟩ := hmiss
      exact fun hQ => hγmiss ((hcut γ hγ).mp (hpoints γ hγ Q hQ))
    refine proper_section_card _ point (hinj.mono (filter_subset _ _)) hproper
      (totalDegree_bidegreeLift_le_one q hq) (fun γ hγ => ?_) hdim hdeg
    obtain ⟨hγU, hγhit⟩ := mem_filter.mp hγ
    exact mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hpoints γ hγU, (hcut γ hγU).mpr hγhit⟩
  have hcount := P0_10.section_capacity hw (by decide) D hsection
  change 45495 * U.card ≤ 82024 * D + 45495 at hcount
  have hcountQ : (45495 : ℚ) * (U.card : ℚ) ≤ 82024 * (D : ℚ) + 45495 := by
    exact_mod_cast hcount
  change (U.card : ℚ) ≤ beta * (D : ℚ) + 1
  unfold beta
  linarith only [hcountQ]

set_option maxHeartbeats 800000 in
theorem root_tariff : RootTariff := by
  intro u del M Γ F hM T hT J g H hg h8 hcurve hmarks
  have hlabel : Set.InjOn M.label (T : Set K) := by
    intro γ _ η _ h
    exact sub_left_inj.mp h
  obtain ⟨U, hU, hexc, n, ⟨A⟩⟩ :=
    root_chart T M.label F.scalar J g H hg h8 hcurve hlabel hmarks
  have hw := bridge_word M F hM U (hU.trans hT)
  obtain ⟨C, hreconstruct⟩ :=
    root_taylor n endpointDegree g (by decide) (by decide) hg A.equation A.equation_degree
  have hregular := regular_count_P0_10RBridgeRoot A hw C
    (fun γ hγ => hreconstruct _ _ (hw.degree γ hγ) (A.root γ hγ) (A.simple γ hγ)) root_embedding
  let b := taylorPower endpointDegree
  have hsum : g + (g - 1) = taylorPower g := by unfold taylorPower; omega
  have hmixed : b * (g * H) + ordinateBound endpointDegree g * H =
      (b * taylorPower g + 1) * H := by
    rw [← hsum]
    dsimp [ordinateBound, b]
    ring
  rw [hmixed] at hregular
  have hcast : (taylorPower g : ℚ) = 2 * (g : ℚ) - 1 := by
    unfold taylorPower
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hgQ : (1 : ℚ) ≤ (g : ℚ) := by exact_mod_cast hg
  calc
    (T.card : ℚ) = ((T \ U).card : ℚ) + (U.card : ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _ ≤ ((taylorPower g * H : ℕ) : ℚ) +
        (beta * (((b * taylorPower g + 1) * H : ℕ) : ℚ) + 1) :=
      add_le_add (Nat.cast_le.mpr hexc) hregular
    _ ≤ ((taylorPower g * H : ℕ) : ℚ) +
        (beta * (((b * taylorPower g + 1) * H : ℕ) : ℚ) + g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _ = rootPrice g H := by
      unfold rootPrice
      push_cast
      rw [hcast]
      dsimp only [b, taylorPower]
      ring


end
end P0_10R.Bridge
end PackSource_P0_10RBridgeRoot
section PackSource_P0_10RBridgeCurves
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace P0_10R.Bridge

noncomputable section

open P0 (AnchorModel AnchoredFamily K p)
open K1_14 (Seeds L graphEval)
open K1_14_2 (Ambient SeedField JetYSection OnJet OnRoot SmallRootCurve endpointDegree)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength
  yLength)
open private on_root on_seed moving_graph_count seed_graph_count equal_image_degree
  union_card_le from ProximityPrize.SubmissionLower.Fast062
open scoped BigOperators Classical

private theorem projected_curve : K1_14_2_3.c2 :=
  K1_14_2_3_2.of_children K1_14_2_3_2_1.proof K1_14_2_3_2_2.proof

private def seedRate : ℚ := ((p + 1 : ℕ) : ℚ) / 9
private def yRate : ℚ := 15 + beta * (((2 * endpointDegree - 1 : ℕ) : ℚ)*15+1)

private theorem root_price_bound (g H : ℕ) (hg : g ≤ 8) :
    rootPrice g H ≤ yRate * (H : ℚ) + (g : ℚ) := by
  have hgq : (g : ℚ) ≤ 8 := by exact_mod_cast hg
  have ht : 2 * (g : ℚ) - 1 ≤ 15 := by linarith
  have hd : 0 ≤ ((2 * endpointDegree - 1 : ℕ) : ℚ) := Nat.cast_nonneg _
  have hb : 0 ≤ beta := by unfold beta; positivity
  exact add_le_add (mul_le_mul_of_nonneg_right
    (add_le_add ht (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left ht hd) (le_refl (1 : ℚ))) hb))
    (Nat.cast_nonneg H)) (le_refl (g : ℚ))

private theorem seedRate_nonneg : 0 ≤ seedRate := by unfold seedRate; positivity
private theorem yRate_nonneg : 0 ≤ yRate := by unfold yRate beta; positivity
private theorem seedCap_lt_p : lossSeedCap < p := by decide

private theorem seedCap_le_rate : (lossSeedCap : ℚ) ≤ seedRate := by
  have h : lossSeedCap * 9 ≤ p + 1 := by decide
  exact (le_div_iff₀ (by norm_num : (0 : ℚ) < 9)).mpr (by exact_mod_cast h)

private theorem linear_rate (r a b c : ℕ) (hb : (b : ℚ) ≠ 0) :
    (r : ℚ) + ((a : ℚ)/b)*((c : ℚ)*15+1) =
      ((r*b+a*(c*15+1) : ℕ) : ℚ)/b := by
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  field_simp

private theorem yRate_eq : yRate = ((331273964089 : ℕ) : ℚ) / 45495 := by
  unfold yRate beta
  have h := linear_rate 15 82024 45495 (2*endpointDegree-1) (by norm_num : (45495 : ℚ) ≠ 0)
  have hn : (15 : ℕ) * 45495 + 82024 * ((2*endpointDegree-1)*15+1) = 331273964089 := by decide
  rw [hn] at h
  exact h

private theorem tariff_fraction (a b d h c m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hc : a*d*n + b*h*m + d*(m*n) ≤ c*(m*n)) :
    ((a : ℚ)/m)*d + ((b : ℚ)/n)*h + d ≤ c := by
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  apply le_of_mul_le_mul_right _ (mul_pos hm' hn')
  have hq : (a : ℚ)*d*n + (b : ℚ)*h*m + (d : ℚ)*((m : ℚ)*n) ≤
      (c : ℚ)*((m : ℚ)*n) := by exact_mod_cast hc
  convert hq using 1
  all_goals field_simp

private theorem tariff_ledger :
    seedRate * (lossSeedCap : ℚ) + yRate * (lossYCap : ℚ) + (lossSeedCap : ℚ) ≤
      (curveFee : ℚ) := by
  rw [yRate_eq]
  exact tariff_fraction (p+1) 331273964089 lossSeedCap lossYCap curveFee 9 45495
    (by decide) (by decide) (by decide)

private theorem group_price {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hhi : M.overhead ≤ 3554) (T : Finset K) (hT : T ⊆ Γ)
    (tariff : RootTariff)
    (P : Ideal Seeds) (s : Finset (Ideal Ambient))
    (hne : s.Nonempty) (himage : ∀ I ∈ s, seedImage I = P)
    (hslice : ∀ I ∈ s, SeedSlice I ∧ Module.Finite SeedField (JetYSection I))
    (hcap : (∑ I ∈ s, seedLength I) ≤ lossSeedCap) :
    let W (I : Ideal Ambient) := T.filter (fun γ => OnJet I (M.label γ) (F.scalar γ))
    ((s.biUnion W).card : ℚ) ≤
      seedRate * (∑ I ∈ s, (seedLength I : ℚ)) +
      yRate * (∑ I ∈ s, (yLength I : ℚ)) + ∑ I ∈ s, (seedLength I : ℚ) := by
  classical
  let W (I : Ideal Ambient) := T.filter (fun γ => OnJet I (M.label γ) (F.scalar γ))
  let U := s.biUnion W
  let D : ℕ := ∑ I ∈ s, seedLength I
  let H : ℕ := ∑ I ∈ s, yLength I
  change (U.card : ℚ) ≤ seedRate * (∑ I ∈ s, (seedLength I : ℚ)) +
    yRate * (∑ I ∈ s, (yLength I : ℚ)) + ∑ I ∈ s, (seedLength I : ℚ)
  rw [← Nat.cast_sum, ← Nat.cast_sum]
  change (U.card : ℚ) ≤ seedRate * (D : ℚ) + yRate * (H : ℚ) + (D : ℚ)
  have extend_seed (h : (U.card : ℚ) ≤ seedRate * (D : ℚ)) :
      (U.card : ℚ) ≤ seedRate * (D : ℚ) + yRate * (H : ℚ) + (D : ℚ) := by
    exact h.trans (le_add_of_nonneg_right (mul_nonneg yRate_nonneg (Nat.cast_nonneg H)) |>.trans
      (le_add_of_nonneg_right (Nat.cast_nonneg D)))
  obtain ⟨J, hJ⟩ := hne
  obtain ⟨C, hC, hJproj, hCpos, hCbound⟩ := K1_14_2_3_1.proof J (hslice J hJ).1
  have hP : P = Ideal.span {C} := (himage J hJ).symm.trans hJproj
  have hCD : C.totalDegree ≤ D :=
    hCbound.trans (Finset.single_le_sum (f := seedLength) (fun _ _ => Nat.zero_le _) hJ)
  have hlabels : ∀ z ∈ U.image M.label, graphEval z C = 0 := by
    intro z hz
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨I, hI, hγI⟩ := Finset.mem_biUnion.mp hγ
    refine on_seed (Finset.mem_filter.mp hγI).2 ?_
    rw [himage I hI, hP]
    exact Ideal.mem_span_singleton_self C
  have hcard : (U.image M.label).card = U.card :=
    Finset.card_image_of_injective _ (fun _ _ hab => sub_left_inj.mp hab)
  by_cases hlarge : 9 * C.totalDegree ≤ D
  · have hc := seed_graph_count C hC.ne_zero ((hCD.trans hcap).trans_lt seedCap_lt_p)
      (U.image M.label) hlabels
    rw [hcard] at hc
    have hcq : (U.card : ℚ) ≤ ((p+1 : ℕ) : ℚ) * (C.totalDegree : ℚ) := by exact_mod_cast hc
    have hdq : (9 : ℚ) * (C.totalDegree : ℚ) ≤ (D : ℚ) := by exact_mod_cast hlarge
    apply extend_seed
    calc
      _ ≤ ((p+1 : ℕ) : ℚ) * (C.totalDegree : ℚ) := hcq
      _ = seedRate * (9 * (C.totalDegree : ℚ)) := by unfold seedRate; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdq seedRate_nonneg
  by_cases hconst : DefinedOverConstants P
  · obtain ⟨Q, hQ, hQproj⟩ := hconst
    have hdeg : C.totalDegree = Q.totalDegree := equal_image_degree C hC.ne_zero Q
      (hP.symm.trans hQproj)
    have hsbound (I : Ideal Ambient) (hI : I ∈ s) :
        ((W I).card : ℚ) ≤ yRate * (yLength I : ℚ) + (seedLength I : ℚ) := by
      obtain ⟨g, hg, hroot, hgD⟩ :=
        projected_curve I Q (hslice I hI).1 (hslice I hI).2 hQ ((himage I hI).trans hQproj)
      have hgi : g ≤ 8 := by
        by_contra! hbad
        have hsuccess := (Nat.mul_le_mul_left Q.totalDegree hbad).trans
          (hgD.trans (Finset.single_le_sum (f := seedLength) (fun _ _ => Nat.zero_le _) hI))
        exact hlarge (by simpa [hdeg, Nat.mul_comm 9] using hsuccess)
      have hgcap : g ≤ seedLength I :=
        (Nat.le_mul_of_pos_left g (hdeg ▸ hCpos)).trans hgD
      have hsub : W I ⊆ Γ := (Finset.filter_subset _ _).trans hT
      have ht := tariff u del M Γ F hhi (W I) hsub (rootImage I) g (yLength I) hg hgi hroot
        (fun _ hz => on_root (Finset.mem_filter.mp hz).2)
      have hgcapq : (g : ℚ) ≤ (seedLength I : ℚ) := by exact_mod_cast hgcap
      exact ht.trans ((root_price_bound g (yLength I) hgi).trans (add_le_add le_rfl hgcapq))
    calc
      (U.card : ℚ) ≤ ∑ I ∈ s, ((W I).card : ℚ) := union_card_le s W
      _ ≤ ∑ I ∈ s, (yRate * (yLength I : ℚ) + (seedLength I : ℚ)) := Finset.sum_le_sum hsbound
      _ = yRate * (H : ℚ) + (D : ℚ) := by
        simp only [H, D, Finset.sum_add_distrib, Finset.mul_sum, Nat.cast_sum]
      _ ≤ _ := by
        rw [add_assoc]
        exact le_add_of_nonneg_left (mul_nonneg seedRate_nonneg (Nat.cast_nonneg D))
  · have hc := moving_graph_count p C hC (hP ▸ hconst) (U.image M.label) hlabels
    rw [hcard] at hc
    have hq : (U.card : ℚ) ≤ (C.totalDegree : ℚ) ^ 2 := by exact_mod_cast hc
    have hCq : (C.totalDegree : ℚ) ≤ (D : ℚ) := by exact_mod_cast hCD
    have hCr : (C.totalDegree : ℚ) ≤ seedRate :=
      (by exact_mod_cast (hCD.trans hcap) : (C.totalDegree : ℚ) ≤ (lossSeedCap : ℚ)).trans
        seedCap_le_rate
    exact extend_seed (hq.trans (by
      rw [pow_two]
      exact mul_le_mul hCr hCq (Nat.cast_nonneg C.totalDegree) seedRate_nonneg))

theorem curve_count (tariff : RootTariff) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) (hhi : M.overhead ≤ 3554) (T : Finset K) (hT : T ⊆ Γ)
    (cs : Finset (Ideal Ambient)) (hs : ∀ I ∈ cs, K1_14_2_2.CurveGeometry I)
    (hD : K1_14_2_2.curveSeedMass cs ≤ lossSeedCap)
    (hH : K1_14_2_2.curveYMass cs ≤ lossYCap)
    (hcover : ∀ γ ∈ T, ∃ I ∈ cs, OnJet I (M.label γ) (F.scalar γ)) :
    T.card ≤ curveFee := by
  classical
  let images := cs.image seedImage
  let group (P : Ideal Seeds) := cs.filter (fun I => seedImage I = P)
  let W (I : Ideal Ambient) := T.filter (fun γ => OnJet I (M.label γ) (F.scalar γ))
  let covered (P : Ideal Seeds) := (group P).biUnion W
  have hsubset : T ⊆ images.biUnion covered := by
    intro γ hγ
    obtain ⟨I, hi, hz⟩ := hcover γ hγ
    refine Finset.mem_biUnion.mpr ⟨seedImage I, Finset.mem_image_of_mem _ hi, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨I, Finset.mem_filter.mpr ⟨hi, rfl⟩,
      Finset.mem_filter.mpr ⟨hγ, hz⟩⟩
  have hgroup (P : Ideal Seeds) (hP : P ∈ images) :
      ((covered P).card : ℚ) ≤
        seedRate * (∑ I ∈ group P, (seedLength I : ℚ)) +
        yRate * (∑ I ∈ group P, (yLength I : ℚ)) + ∑ I ∈ group P, (seedLength I : ℚ) := by
    obtain ⟨I, hi, he⟩ := Finset.mem_image.mp hP
    refine group_price M F hhi T hT tariff P (group P)
      ⟨I, Finset.mem_filter.mpr ⟨hi, he⟩⟩
      (fun _ hJ => (Finset.mem_filter.mp hJ).2) (fun J hJ => ?_) ?_
    · obtain ⟨hp, hdim, hf, hpos, hy⟩ := hs J (Finset.mem_filter.mp hJ).1
      exact ⟨⟨hp, hdim, hf, hpos⟩, hy⟩
    · exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hD
  have hsum (f : Ideal Ambient → ℚ) :
      (∑ P ∈ images, ∑ I ∈ group P, f I) = ∑ I ∈ cs, f I :=
    Finset.sum_fiberwise_of_maps_to (fun _ hI => Finset.mem_image_of_mem seedImage hI) f
  have hDq : (∑ I ∈ cs, (seedLength I : ℚ)) ≤ (lossSeedCap : ℚ) := by
    exact_mod_cast hD
  have hHq : (∑ I ∈ cs, (yLength I : ℚ)) ≤ (lossYCap : ℚ) := by
    exact_mod_cast hH
  have hbound : (T.card : ℚ) ≤ (curveFee : ℚ) := calc
    (T.card : ℚ) ≤ ((images.biUnion covered).card : ℚ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ P ∈ images, ((covered P).card : ℚ) := union_card_le images covered
    _ ≤ ∑ P ∈ images, (seedRate * (∑ I ∈ group P, (seedLength I : ℚ)) +
        yRate * (∑ I ∈ group P, (yLength I : ℚ)) + ∑ I ∈ group P, (seedLength I : ℚ)) :=
      Finset.sum_le_sum hgroup
    _ = seedRate * (∑ I ∈ cs, (seedLength I : ℚ)) +
        yRate * (∑ I ∈ cs, (yLength I : ℚ)) + ∑ I ∈ cs, (seedLength I : ℚ) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
    _ ≤ seedRate * (lossSeedCap : ℚ) + yRate * (lossYCap : ℚ) + (lossSeedCap : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hDq seedRate_nonneg)
        (mul_le_mul_of_nonneg_left hHq yRate_nonneg)) hDq
    _ ≤ _ := tariff_ledger
  exact_mod_cast hbound


end
end P0_10R.Bridge
end PackSource_P0_10RBridgeCurves
