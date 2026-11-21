import ProximityPrize.SubmissionLower.Bridge6925Initial
import ProximityPrize.SubmissionLower.Fast076
import ProximityPrize.SubmissionLower.Fast077
import ProximityPrize.SubmissionLower.Fast072
set_option Elab.async false
section PackSource_P0_10RBridgeAux1
set_option autoImplicit true
namespace P0_10R.Bridge

noncomputable section

open Polynomial
open P0 (K AnchorModel AnchoredFamily p agreement lowCutoff)
open P0_10 (BufferedPair JetSource freeShape movingShape fullShape scheduled reserveCutoff fullCutoff)
open K1_14 (Jet Shape Banks jetAt)
open K1_14_2 (Ambient toJet eval_toJet)
open K1_14_2_2 (RowCaps Active dual orderOn sectionDegree)
open K1_14_2_2_3
open private specialize_shiftedWord shift_word from ProximityPrize.SubmissionLower.Fast052

theorem free_scheduled (w : ℤ) (i : Fin 3) : freeShape w i ∈ scheduled w := by
  fin_cases i <;> simp [scheduled]

theorem moving_scheduled (w : ℤ) (i : Fin 3) : movingShape w i ∈ scheduled w := by
  fin_cases i <;> simp [scheduled]

theorem full_scheduled (w : ℤ) : fullShape w ∈ scheduled w := by simp [scheduled]

theorem full_bridge (w : ℤ) (hw : w ≤ 3554) : fullShape w = terminalFullShape := by
  simp only [fullShape, P0_10.terminalShape, H21.terminalShape, H21.band, ite_eq_left hw]
  rfl

theorem moving_five (w : ℤ) (hw : w ≤ 3554) : movingShape w 1 = stageFiveShape := by
  rw [movingShape, ite_eq_left hw]
  rfl

theorem bridge_five_buffer (w : ℤ) (hw : w ≤ 3554) (s : Shape)
    (hs : s = freeShape w 1 ∨ s = movingShape w 1) :
    reserveCutoff w s 1 + 2*w.toNat*6 ≤ fullCutoff s := by
  have h : w.toNat ≤ 3554 := by omega
  have hcut : 42648 ≤ fullCutoff s := by
    rcases hs with rfl | rfl
    · simp only [freeShape, ite_eq_left hw]
      decide
    · rw [moving_five w hw]
      decide
  have hspend : 2*w.toNat*6 ≤ 42648 := by omega
  change fullCutoff s - 2*w.toNat*6 + 2*w.toNat*6 ≤ fullCutoff s
  omega


theorem moving_late (w : ℤ) (hw : w ≤ 3554) : movingShape w 2 = stageLateShape := by
  rw [movingShape, ite_eq_left hw]
  rfl

theorem late_buffer (w : ℤ) (hw : w ≤ 3554) (s : Shape)
    (hs : s = freeShape w 2 ∨ s = movingShape w 2) :
    reserveCutoff w s 2 + 2*w.toNat*25 ≤ fullCutoff s := by
  have h : w.toNat ≤ 3554 := by omega
  have hcut : 177700 ≤ fullCutoff s := by
    rcases hs with rfl | rfl
    · simp only [freeShape, ite_eq_left hw]
      decide
    · rw [moving_late w hw]
      decide
  have hspend : 2*w.toNat*25 ≤ 177700 := by omega
  change fullCutoff s - 2*w.toNat*25 + 2*w.toNat*25 ≤ fullCutoff s
  omega

/-- Every selected row is a genuine mark equation. -/
theorem bank_zero {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) {s : Shape} (hs : s ∈ scheduled M.overhead)
    (hm : 0 < s.m) {P : Jet} {W : ℕ} (hW : W ≤ fullCutoff s) (hP : P ∈ rows s W) :
    ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 :=
  src.necessary s hs W (by
    have : 0 < s.m * agreement := Nat.mul_pos hm (by decide)
    unfold fullCutoff at hW
    omega) P hP

theorem buffered_zero {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) (hw : M.overhead ≤ 3554)
    (i : Fin 3) (pair : BufferedPair M.overhead rows i) :
    ∀ γ ∈ Γ, jetAt pair.free (M.label γ) (F.scalar γ) = 0 ∧
      jetAt pair.moving (M.label γ) (F.scalar γ) = 0 := by
  have hf : 0 < (freeShape M.overhead i).m := by
    rw [freeShape, ite_eq_left hw]
    fin_cases i <;> decide
  have hq : 0 < (movingShape M.overhead i).m := by
    rw [movingShape, ite_eq_left hw]
    fin_cases i <;> decide
  intro γ hγ
  exact ⟨bank_zero src (free_scheduled _ _) hf (Nat.sub_le _ _) pair.free_mem γ hγ,
    bank_zero src (moving_scheduled _ _) hq (Nat.sub_le _ _) pair.moving_mem γ hγ⟩

theorem failed_bank {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) {s : Shape}
    (hs : s ∈ scheduled M.overhead) (hm : 0 < s.m) {I : Ideal Ambient}
    (hf : ¬ BankPass rows s I) :
    ∃ P : Jet, RowCaps P s ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 := by
  classical
  unfold BankPass at hf
  push Not at hf
  obtain ⟨P, hP, hprop⟩ := hf
  exact ⟨P, src.shape s hs _ P hP, hprop, bank_zero src hs hm le_rfl hP⟩

/-- Select the cutter from a failed full space, or the failed chain-rule equation. -/
theorem failed_pair {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) (hw : M.overhead ≤ 3554)
    (pair : BufferedPair M.overhead rows 1) {I : Ideal Ambient} (hf : ¬ PairPass pair I) :
    ∃ P : Jet, RowCaps P stageFiveShape ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0 := by
  classical
  have hc : freeShape M.overhead 1 = ⟨91, 126, 27, 2072⟩ := by
    rw [freeShape, ite_eq_left hw]
    rfl
  have hm := moving_five M.overhead hw
  have hfreePos : 0 < (freeShape M.overhead 1).m := by rw [hc]; decide
  have hmovePos : 0 < (movingShape M.overhead 1).m := by rw [hm]; decide
  by_cases hP : BankPass rows (freeShape M.overhead 1) I
  · by_cases hQ : BankPass rows (movingShape M.overhead 1) I
    · have htest : ¬ (∀ f : K1_14.Equation, Irreducible f → 0 < f.natDegree →
          C f ∣ pair.free → C f ∣ pair.moving → toJet (C f) ∈ I →
          ∀ g a, K1_14_3.IsClearing f g a → toJet (K1_14_3R.chainCutter g) ∈ I) :=
        fun h => hf ⟨hP, hQ, h⟩
      push Not at htest
      obtain ⟨f, _, _, _, hdiv, hmem, g, a, hclear, hproper⟩ := htest
      have hcaps := src.shape _ (moving_scheduled _ _) _ _ pair.moving_mem
      have hj : 1 ≤ (movingShape M.overhead 1).J := by rw [hm]; decide
      have hG := K1_14_3R.chainCutter_caps_of_dvd pair.moving_ne hcaps hj hdiv hclear
      rw [hm] at hG
      refine ⟨K1_14_3R.chainCutter g, hG, hproper, ?_⟩
      intro γ _ hγ
      apply K1_14_3R.chainCutter_zero hclear
      have hz := RingHom.mem_ker.mp (hγ hmem)
      simpa only [eval_toJet, jetAt, eval₂_C, coe_eval₂RingHom, K1_14.atMark] using hz
    · obtain ⟨P, hcaps, hproper, hzero⟩ := failed_bank src (moving_scheduled _ _) hmovePos hQ
      rw [hm] at hcaps
      exact ⟨P, hcaps, hproper, fun γ hγ _ => hzero γ hγ⟩
  · obtain ⟨P, hcaps, hproper, hzero⟩ := failed_bank src (free_scheduled _ _) hfreePos hP
    rw [hc] at hcaps
    refine ⟨P, ?_, hproper, fun γ hγ _ => hzero γ hγ⟩
    intro j i h
    obtain ⟨hb, hj, hu⟩ := hcaps j i h
    exact ⟨hb.trans (by decide), hj.trans (by decide), hu.trans (by decide)⟩


theorem failed_late_pair {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) (hw : M.overhead ≤ 3554)
    (pair : BufferedPair M.overhead rows 2) {I : Ideal Ambient} (hf : ¬ PairPass pair I) :
    ∃ P : Jet, RowCaps P stageLateShape ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0 := by
  classical
  have hc : freeShape M.overhead 2 = ⟨230, 319, 66, 4045⟩ := by
    rw [freeShape, ite_eq_left hw]
    rfl
  have hm := moving_late M.overhead hw
  have hfreePos : 0 < (freeShape M.overhead 2).m := by rw [hc]; decide
  have hmovePos : 0 < (movingShape M.overhead 2).m := by rw [hm]; decide
  by_cases hP : BankPass rows (freeShape M.overhead 2) I
  · by_cases hQ : BankPass rows (movingShape M.overhead 2) I
    · have htest : ¬ (∀ f : K1_14.Equation, Irreducible f → 0 < f.natDegree →
          C f ∣ pair.free → C f ∣ pair.moving → toJet (C f) ∈ I →
          ∀ g a, K1_14_3.IsClearing f g a → toJet (K1_14_3R.chainCutter g) ∈ I) :=
        fun h => hf ⟨hP, hQ, h⟩
      push Not at htest
      obtain ⟨f, _, _, _, hdiv, hmem, g, a, hclear, hproper⟩ := htest
      have hcaps := src.shape _ (moving_scheduled _ _) _ _ pair.moving_mem
      have hj : 1 ≤ (movingShape M.overhead 2).J := by rw [hm]; decide
      have hG := K1_14_3R.chainCutter_caps_of_dvd pair.moving_ne hcaps hj hdiv hclear
      rw [hm] at hG
      refine ⟨K1_14_3R.chainCutter g, hG, hproper, ?_⟩
      intro γ _ hγ
      apply K1_14_3R.chainCutter_zero hclear
      have hz := RingHom.mem_ker.mp (hγ hmem)
      simpa only [eval_toJet, jetAt, eval₂_C, coe_eval₂RingHom, K1_14.atMark] using hz
    · obtain ⟨P, hcaps, hproper, hzero⟩ := failed_bank src (moving_scheduled _ _) hmovePos hQ
      rw [hm] at hcaps
      exact ⟨P, hcaps, hproper, fun γ hγ _ => hzero γ hγ⟩
  · obtain ⟨P, hcaps, hproper, hzero⟩ := failed_bank src (free_scheduled _ _) hfreePos hP
    rw [hc] at hcaps
    refine ⟨P, ?_, hproper, fun γ hγ _ => hzero γ hγ⟩
    intro j i h
    obtain ⟨hb, hj, hu⟩ := hcaps j i h
    exact ⟨hb.trans (by decide), hj.trans (by decide), hu.trans (by decide)⟩

theorem failed_terminal {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) (hw : M.overhead ≤ 3554)
    {I : Ideal Ambient} (hf : ¬ BankPass rows (fullShape M.overhead) I) :
    ∃ P : Jet, RowCaps P terminalFullShape ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0 := by
  have hm : 0 < (fullShape M.overhead).m := by rw [full_bridge _ hw]; decide
  obtain ⟨P, hc, hp, hz⟩ := failed_bank src (full_scheduled _) hm hf
  rw [full_bridge _ hw] at hc
  exact ⟨P, hc, hp, fun γ hγ _ => hz γ hγ⟩

private theorem shifted_contact {A : Type*} [CommRing A] (a : K1_14.Seeds →+* A)
    {rows : Banks} {s : Shape} {I : Ideal Ambient} {h W r : ℕ} {P : Jet}
    (hn : ∀ W W', W ≤ W' → rows s W ≤ rows s W')
    (hs : K1_14_3.SeedShift h rows s) (hv : BankPass rows s I)
    (hcut : W + 2*h*r ≤ fullCutoff s) (hP : P ∈ rows s W) :
    fibreContact (I.map (specializeJets a)) (specializeJets a (toJet P)) r := by
  intro t ht
  rw [← specialize_shiftedWord]
  apply Ideal.mem_map_of_mem
  exact hv _ (hn _ _ ((Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _).trans hcut)
    (shift_word hs hP t))

/-- Port of the local order lemma, using the new full cutoff. -/
theorem buffered_order {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) (hw : M.overhead ≤ 3554)
    {s : Shape} (hpair : s = freeShape M.overhead 1 ∨ s = movingShape M.overhead 1)
    {I : Ideal Ambient} (hactive : Active I) (hv : BankPass rows s I)
    {P : Jet} (hP : P ∈ rows s (reserveCutoff M.overhead s 1)) :
    orderOn I P 7 := by
  classical
  have hs : s ∈ scheduled M.overhead := by
    rcases hpair with rfl | rfl
    · exact free_scheduled _ _
    · exact moving_scheduled _ _
  have hn := src.nested s hs s hs rfl rfl rfl le_rfl
  have hcut := bridge_five_buffer M.overhead hw s hpair
  have ht : (6 : ℕ) < p := by decide
  by_cases hd : dual I
  · have hc := shifted_contact (algebraMap K1_14.Seeds K1_14_2.SeedField) hn
      (src.shift s hs) hv hcut hP
    rw [← mapGenericJets_eq] at hc
    exact clear_dual hd (K1_14_2_2_3_1.proof I hactive.prime hactive.jet_finite
      hd hactive.jet_lt _ 6 ht hc)
  · obtain ⟨g, hg, hdeg, he⟩ := K1_14_2_2_3_2.proof I hactive hd
    let _ : I.IsPrime := hactive.prime
    let _ : (I.comap jetInclude).IsPrime := Ideal.IsPrime.comap jetInclude
    let _ : CharP K1_14.FX p := charP_of_injective_ringHom K1_14.seedEmbedding.injective p
    let _ : CharP (JetImageField I) p :=
      charP_of_injective_ringHom ((jetImageMap I).comp MvPolynomial.C).injective p
    apply clear_rank_one hactive.prime hd
    have hc := shifted_contact (jetImageMap I) hn (src.shift s hs) hv hcut hP
    change fibreContact (I.map (imageFibreMap I)) (imageFibreMap I (toJet P)) 6 at hc
    rw [he] at hc ⊢
    exact divisor_contact hg hdeg ht hc

theorem late_order {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) (hw : M.overhead ≤ 3554)
    {s : Shape} (hpair : s = freeShape M.overhead 2 ∨ s = movingShape M.overhead 2)
    {I : Ideal Ambient} (hactive : Active I) (hv : BankPass rows s I)
    {P : Jet} (hP : P ∈ rows s (reserveCutoff M.overhead s 2)) :
    orderOn I P 26 := by
  classical
  have hs : s ∈ scheduled M.overhead := by
    rcases hpair with rfl | rfl
    · exact free_scheduled _ _
    · exact moving_scheduled _ _
  have hn := src.nested s hs s hs rfl rfl rfl le_rfl
  have hcut := late_buffer M.overhead hw s hpair
  have ht : (25 : ℕ) < p := by decide
  suffices general : ∀ v : ℕ, v < p → reserveCutoff M.overhead s 2 + 2*M.overhead.toNat*v ≤ fullCutoff s → orderOn I P (v+1) from general 25 ht hcut
  clear hcut ht
  intro v ht hcut
  by_cases hd : dual I
  · have hc := shifted_contact (algebraMap K1_14.Seeds K1_14_2.SeedField) hn
      (src.shift s hs) hv hcut hP
    rw [← mapGenericJets_eq] at hc
    exact clear_dual hd (K1_14_2_2_3_1.proof I hactive.prime hactive.jet_finite
      hd hactive.jet_lt _ v ht hc)
  · obtain ⟨g, hg, hdeg, he⟩ := K1_14_2_2_3_2.proof I hactive hd
    let _ : I.IsPrime := hactive.prime
    let _ : (I.comap jetInclude).IsPrime := Ideal.IsPrime.comap jetInclude
    let _ : CharP K1_14.FX p := charP_of_injective_ringHom K1_14.seedEmbedding.injective p
    let _ : CharP (JetImageField I) p :=
      charP_of_injective_ringHom ((jetImageMap I).comp MvPolynomial.C).injective p
    apply clear_rank_one hactive.prime hd
    have hc := shifted_contact (jetImageMap I) hn (src.shift s hs) hv hcut hP
    change fibreContact (I.map (imageFibreMap I)) (imageFibreMap I (toJet P)) v at hc
    rw [he] at hc ⊢
    exact divisor_contact hg hdeg ht hc

end
end P0_10R.Bridge
end PackSource_P0_10RBridgeAux1
section PackSource_P0_10RBridgeProjection
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 900000

namespace P0_10R.Bridge

noncomputable section

open Polynomial
open P0 (AnchorModel AnchoredFamily agreement p lowCutoff)
open P0_10 (JetSource scheduled terminalShape fullShape fullCutoff)
open K1_14 (Banks Shape Jet Equation Seeds FX seedHasse)
open K1_14_2 (Ambient toJet FibreRing mapGenericSeed mapGenericJets eval_toJet generic)
open K1_14_2_2 (Active dual)
open K1_14_3 (Surface Parent SeedClosure SeedField JetField JetClosure JetPlane seedFibreEval
  seedGeneric jetGeneric fixedEmbedding OrderAt ProjectedProduct)
open K1_14_2_6 (genericSeedPoint genericJetPoint)
open private ambientToJet toJet_equiv from ProximityPrize.SubmissionLower.Fast071
open private fibreHom seedMap jetMap seedPoint jetPoint from ProximityPrize.SubmissionLower.Fast069
open private seed_chart toJet_C toJet_y toJet_v toJet_seed jetCoordinates fractionCoordinates
  generic_C generic_Y generic_V seedGeneric_C from ProximityPrize.SubmissionLower.Fast069

def surfaceOf (I : Ideal Ambient) (hI : I.IsPrime) : Surface :=
  ⟨I.comap toJet, hI.comap _⟩

theorem on_surface {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {I : Ideal Ambient} (hI : I.IsPrime) {γ : P0.K} (hm : OnParent F I γ) :
    P0_10.MarkOn M F (surfaceOf I hI) γ := by
  intro P hP
  apply RingHom.mem_ker.mpr
  change K1_14.jetAt P (M.label γ) (F.scalar γ) = 0
  rw [← eval_toJet]
  exact RingHom.mem_ker.mp (hm hP)

theorem surface_pass {w : ℤ} {rows : Banks} {i : Fin 3}
    {pair : P0_10.BufferedPair w rows i} {I : Ideal Ambient}
    (hI : I.IsPrime) (ht : PairPass pair I) :
    P0_10R.SurfacePass pair (surfaceOf I hI) := by
  refine ⟨ht.1, ht.2.1, ?_⟩
  intro f hirr hdeg hP hQ hmem g a hclear
  exact ht.2.2 f hirr hdeg hP hQ hmem g a hclear

private theorem fixed_chart (a b : SeedClosure) :
    (genericJetPoint a b).comp (toJet.comp fixedEmbedding) =
      seedGeneric.comp jetCoordinates.symm.toRingHom := by
  have hV : ((genericJetPoint a b).comp (toJet.comp fixedEmbedding)) (Polynomial.X (R := FX[X])) =
      (seedGeneric.comp jetCoordinates.symm.toRingHom) Polynomial.X := by
    simp [fixedEmbedding, generic_V, toJet_v, genericJetPoint, seedGeneric, generic]
  apply Polynomial.ringHom_ext' _ hV
  have hY : (((genericJetPoint a b).comp (toJet.comp fixedEmbedding)).comp C)
      (Polynomial.X (R := FX)) =
      ((seedGeneric.comp jetCoordinates.symm.toRingHom).comp C) Polynomial.X := by
    simp [fixedEmbedding, generic_Y, toJet_y, genericJetPoint, seedGeneric, generic]
  apply Polynomial.ringHom_ext' _ hY
  ext x
  simp [fixedEmbedding, generic_C, toJet_C, genericJetPoint, seedGeneric_C]

private theorem surface_height {I : Ideal Ambient} (hI : I.IsPrime) (hh : I.height = 2) :
    (surfaceOf I hI).asIdeal.height = 2 := by
  change (I.comap toJet).height = 2
  rw [toJet_equiv]
  exact (ambientToJet.symm.height_comap I).trans hh

private theorem seed_side_of_active {I : Ideal Ambient} (hI : Active I) :
    ∃ y v, K1_14_3.OnSeedFibre (surfaceOf I hI.prime) y v ∧
      IsSeparable SeedField y ∧ IsSeparable SeedField v := by
  obtain ⟨f, hf, hsep⟩ := @fibreHom mapGenericSeed _ seedMap I hI.prime
    hI.seed_finite hI.seed_size.1 hI.seed_size.2
  refine ⟨f (MvPolynomial.X 0), f (MvPolynomial.X 1), ?_, hsep _, hsep _⟩
  unfold K1_14_3.OnSeedFibre
  rw [← seed_chart, ← RingHom.comap_ker, seedPoint, hf]
  rfl

private theorem jet_side_transport {I : Ideal Ambient} (hI : I.IsPrime)
    (a b : SeedClosure) (hjker : RingHom.ker (genericJetPoint a b) = I)
    (ha : IsSeparable SeedField a) (hb : IsSeparable SeedField b) :
    ∃ g : Jet →+* JetClosure,
      g.comp fixedEmbedding = jetGeneric ∧ RingHom.ker g = (surfaceOf I hI).asIdeal ∧
      ∀ i : Fin 2, IsSeparable JetField (g (C (C (MvPolynomial.X i)))) := by
  let e := fractionCoordinates.symm
  let top : JetField →+* JetClosure := algebraMap JetField JetClosure
  let : Algebra SeedField JetClosure := (top.comp e.toRingHom).toAlgebra
  let l : SeedClosure →ₐ[SeedField] JetClosure :=
    IsAlgClosed.lift (R := SeedField) (S := SeedClosure) (M := JetClosure)
  let F := l.toRingHom.comp ((genericJetPoint a b).comp toJet)
  have hscalar (x : SeedField) :
      l (algebraMap SeedField SeedClosure x) = algebraMap JetField JetClosure (e x) := by
    exact l.commutes x
  refine ⟨F, ?_, ?_, ?_⟩
  · apply RingHom.ext
    intro x
    change l ((genericJetPoint a b).comp (toJet.comp fixedEmbedding) x) = _
    rw [fixed_chart, RingHom.comp_apply]
    change l (algebraMap SeedField SeedClosure (algebraMap Seeds SeedField
      (jetCoordinates.symm x))) = _
    rw [hscalar]
    change top (e (algebraMap Seeds SeedField (jetCoordinates.symm x))) =
      top (algebraMap JetPlane JetField x)
    apply congrArg top
    apply fractionCoordinates.injective
    rw [RingEquiv.apply_symm_apply]
    exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap (A := JetPlane)
      (K := JetField) (B := Seeds) (L := SeedField) jetCoordinates.symm x).symm
  · change RingHom.ker (l.toRingHom.comp ((genericJetPoint a b).comp toJet)) = _
    rw [RingHom.ker_comp_of_injective _ l.injective, ← RingHom.comap_ker, hjker]
    rfl
  · have hs (x : SeedClosure) (hx : IsSeparable SeedField x) : IsSeparable JetField (l x) := by
      have hx' : (minpoly SeedField x).Separable := hx
      apply (hx'.map (f := e.toRingHom)).of_dvd
      apply minpoly.dvd
      rw [aeval_def, Polynomial.eval₂_map]
      change (minpoly SeedField x).eval₂ (algebraMap SeedField JetClosure) (l x) = 0
      rw [← aeval_def, aeval_algHom_apply l, minpoly.aeval, map_zero]
    intro i
    fin_cases i
    · change IsSeparable JetField (l ((genericJetPoint a b) (toJet (C (C (MvPolynomial.X 0))))))
      rw [toJet_seed]
      simpa [genericJetPoint] using hs a ha
    · change IsSeparable JetField (l ((genericJetPoint a b) (toJet (C (C (MvPolynomial.X 1))))))
      rw [toJet_seed]
      simpa [genericJetPoint] using hs b hb

/-- Transport the same two separable generic fibres to the nested polynomial presentation. -/
theorem parent_of_dual {I : Ideal Ambient} (hI : Active I) (hh : I.height = 2) (hj : dual I) :
    Parent (surfaceOf I hI.prime) := by
  obtain ⟨g, hg, hsep⟩ := @fibreHom mapGenericJets _ jetMap I hI.prime hI.jet_finite hj hI.jet_lt
  have hker : RingHom.ker (genericJetPoint (g (MvPolynomial.X 0)) (g (MvPolynomial.X 1))) = I := by
    rw [jetPoint, hg]
  exact ⟨surface_height hI.prime hh, seed_side_of_active hI,
    jet_side_transport hI.prime _ _ hker (hsep _) (hsep _)⟩

private theorem terminal_order {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows)
    (hlo : lowCutoff + 1 ≤ M.overhead) (hhi : M.overhead ≤ 3554)
    {q : Surface} (hq : Parent q) (hv : P0_10.BankVanishes rows (fullShape M.overhead) q)
    {s : Shape} (hs : s ∈ scheduled M.overhead) (hm : s.m = (fullShape M.overhead).m)
    (hb : s.B = (fullShape M.overhead).B) (hj : s.J = (fullShape M.overhead).J)
    (hu : s.U ≤ (fullShape M.overhead).U) {W : ℕ} (hw : W < s.m * agreement)
    {P : Jet} (hp : P ∈ rows s W) : OrderAt q P (contactPower M.overhead s W) := by
  let h := M.overhead.toNat
  apply K1_14_3R_1.proof _ _ _ hq
  · have hchar : s.m * agreement < p := by rw [hm, full_bridge _ hhi]; decide
    have := Nat.div_le_self (fullCutoff s - W) (2*h)
    change 1 + (fullCutoff s - W) / (2*h) < p
    unfold fullCutoff at *
    omega
  intro a b hab
  change a + b < 1 + (fullCutoff s - W) / (2*h) at hab
  have hh : 0 < 2*h := by
    change 2472 ≤ M.overhead at hlo
    dsimp only [h]
    omega
  have hcost := (Nat.le_div_iff_mul_le hh).mp
    (show a+b ≤ (fullCutoff s - W) / (2*h) by omega)
  rw [Nat.mul_comm (a+b), Nat.mul_add] at hcost
  have hle : W + 2*h*a + 2*h*b ≤ fullCutoff (fullShape M.overhead) := by
    unfold fullCutoff at *
    rw [hm] at hcost hw
    omega
  have hA := src.shift s hs W P hp 0 a
  have hB := src.shift s hs _ _ hA 1 b
  exact hv _ (src.nested s hs _ (full_scheduled _) hm hb hj hu _ _ hle hB)

theorem terminal_product {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows)
    (hlo : lowCutoff + 1 ≤ M.overhead) (hhi : M.overhead ≤ 3554)
    (Q : Finset Surface) (hne : Q.Nonempty)
    (hQ : ∀ q ∈ Q, Parent q)
    (hv : ∀ q ∈ Q, P0_10.BankVanishes rows (fullShape M.overhead) q) :
    ∃ f : Equation, ProjectedProduct Q f ∧ FullDivisibility M.overhead rows f ∧
      P0_10.TerminalDivisibility M.overhead rows f := by
  obtain ⟨f, hf⟩ := K1_14_3_7.proof Q hne hQ
  refine ⟨f, hf, ?_, ?_⟩
  · intro W hW P hP hn
    exact hf.divides_leading P _ hn
      (fun q hq => terminal_order src hlo hhi (hQ q hq) (hv q hq) (full_scheduled _)
        rfl rfl rfl le_rfl hW hP)
  · let s := terminalShape M.overhead
    have hs : s ∈ scheduled M.overhead := by simp [s, scheduled]
    have hu : s.U ≤ (fullShape M.overhead).U := by
      simp only [s, terminalShape, H21.terminalShape, H21.band, ite_eq_left hhi, full_bridge _ hhi]
      decide
    intro W hW P hP hn
    suffices horder : ∀ q ∈ Q, OrderAt q P (contactPower M.overhead s W) by
      exact hf.divides_leading P _ hn horder
    intro q hq
    exact terminal_order src hlo hhi (hQ q hq) (hv q hq) hs rfl rfl rfl hu hW hP

end
end P0_10R.Bridge
end PackSource_P0_10RBridgeProjection
section PackSource_P0_10RBridgeCutDonors
set_option autoImplicit true
namespace P0_10R.Bridge

/- Assembly of the unchanged geometric lemmas from the 69.15 port. -/
private theorem donor_2_1 : K1_14_2_2_7_2.c1 :=
  K1_14_2_2_7_2_1.proof
private theorem donor_2_2_1 : K1_14_2_2_7_2_2.c1 :=
  K1_14_2_2_7_2_2_1.proof
private theorem donor_2_2_2 : K1_14_2_2_7_2_2.c2 :=
  K1_14_2_2_7_2_2_2.proof
private theorem donor_2_2_3 : K1_14_2_2_7_2_2.c3 :=
  K1_14_2_2_7_2_2_3.proof
private theorem donor_2_2 : K1_14_2_2_7_2.c2 :=
  K1_14_2_2_7_2_2.of_children donor_2_2_1 donor_2_2_2 donor_2_2_3
private theorem donor_2_3 : K1_14_2_2_7_2.c3 :=
  K1_14_2_2_7_2_3.proof
private theorem donor_2_4 : K1_14_2_2_7_2.c4 :=
  K1_14_2_2_7_2_4.proof
private theorem donor_2_5 : K1_14_2_2_7_2.c5 :=
  K1_14_2_2_7_2_5.proof
theorem cut_seed_mass : K1_14_2_2_7.c2 :=
  K1_14_2_2_7_2.of_children donor_2_1 donor_2_2 donor_2_3 donor_2_4 donor_2_5
private theorem donor_3_1 : K1_14_2_2_7_3.c1 :=
  K1_14_2_2_7_3_1.proof
private theorem donor_3_2 : K1_14_2_2_7_3.c2 :=
  K1_14_2_2_7_3_2.proof
private theorem donor_3_3_1_1 : K1_14_2_2_7_3_3_1.c1 :=
  K1_14_2_2_7_3_3_1_1.proof
private theorem donor_3_3_1_2 : K1_14_2_2_7_3_3_1.c2 :=
  K1_14_2_2_7_3_3_1_2.proof
private theorem donor_3_3_1_3 : K1_14_2_2_7_3_3_1.c3 :=
  K1_14_2_2_7_3_3_1_3.proof
private theorem donor_3_3_1_4 : K1_14_2_2_7_3_3_1.c4 :=
  K1_14_2_2_7_3_3_1_4.proof
private theorem donor_3_3_1 : K1_14_2_2_7_3_3.c1 :=
  K1_14_2_2_7_3_3_1.of_children donor_3_3_1_1 donor_3_3_1_2 donor_3_3_1_3 donor_3_3_1_4
private theorem donor_3_3_2 : K1_14_2_2_7_3_3.c2 :=
  K1_14_2_2_7_3_3_2.proof
private theorem donor_3_3 : K1_14_2_2_7_3.c3 :=
  K1_14_2_2_7_3_3.of_children donor_3_3_1 donor_3_3_2
theorem cut_ordinate_mass : K1_14_2_2_7.c3 :=
  K1_14_2_2_7_3.of_children donor_3_1 donor_3_2 donor_3_3
private theorem donor_4_1 : K1_14_2_2_7_4.c1 :=
  K1_14_2_2_7_4_1.proof
private theorem donor_4_2 : K1_14_2_2_7_4.c2 :=
  K1_14_2_2_7_4_2.proof
private theorem donor_4_3 : K1_14_2_2_7_4.c3 :=
  K1_14_2_2_7_4_3.proof
private theorem donor_4_4_1 : K1_14_2_2_7_4_4.c1 :=
  K1_14_2_2_7_4_4_1.proof
private theorem donor_4_4_2 : K1_14_2_2_7_4_4.c2 :=
  K1_14_2_2_7_4_4_2.proof
private theorem donor_4_4_3 : K1_14_2_2_7_4_4.c3 :=
  K1_14_2_2_7_4_4_3.proof
private theorem donor_4_4_4 : K1_14_2_2_7_4_4.c4 :=
  K1_14_2_2_7_4_4_4.proof
private theorem donor_4_4_5 : K1_14_2_2_7_4_4.c5 :=
  K1_14_2_2_7_4_4_5.proof
private theorem donor_4_4_6 : K1_14_2_2_7_4_4.c6 :=
  K1_14_2_2_7_4_4_6.proof
private theorem donor_4_4_7_1 : K1_14_2_2_7_4_4_7.c1 :=
  K1_14_2_2_7_4_4_7_1.proof
private theorem donor_4_4_7_2 : K1_14_2_2_7_4_4_7.c2 :=
  K1_14_2_2_7_4_4_7_2.proof
private theorem donor_4_4_7 : K1_14_2_2_7_4_4.c7 :=
  K1_14_2_2_7_4_4_7.of_children donor_4_4_7_1 donor_4_4_7_2
private theorem donor_4_4_8 : K1_14_2_2_7_4_4.c8 :=
  K1_14_2_2_7_4_4_8.proof
private theorem donor_4_4 : K1_14_2_2_7_4.c4 :=
  K1_14_2_2_7_4_4.of_children
    donor_4_4_1 donor_4_4_2 donor_4_4_3 donor_4_4_4 donor_4_4_5 donor_4_4_6 donor_4_4_7 donor_4_4_8
theorem cut_constant_count : K1_14_2_2_7.c4 :=
  K1_14_2_2_7_4.of_children donor_4_1 donor_4_2 donor_4_3 donor_4_4

end P0_10R.Bridge
end PackSource_P0_10RBridgeCutDonors
section PackSource_P0_10RBridgeCuts
set_option autoImplicit true
namespace P0_10R.Bridge

noncomputable section

open P0 (AnchorModel AnchoredFamily K)
open K1_14 (Jet Shape jetAt seedEmbedding)
open K1_14_2 (Ambient OnJet jetMarkHom toJet eval_toJet CoordinateRing SeedField JetSeedSection
  JetYSection)
open K1_14_2_2 (Active CutCover RowCaps sectionDegree weight dot joinCuts joinCuts_cost
  sum_dot emptyCut mass)
open K1_14_2_2_7
open private seed_value_eq from ProximityPrize.SubmissionLower.Fast052
open scoped Classical BigOperators

private theorem mark_on_cut {I : Ideal Ambient} {P : Jet} {z : K} {S : Polynomial K}
    (hI : OnJet I z S) (hzero : jetAt P z S = 0) :
    ∃ Q ∈ cutComponents I P, OnJet Q z S := by
  let e := jetMarkHom z S
  have hle : I ⊔ Ideal.span {toJet P} ≤ RingHom.ker e := by
    apply sup_le hI
    exact (Ideal.span_singleton_le_iff_mem _).mpr
      (RingHom.mem_ker.mpr ((eval_toJet _ _ _).trans hzero))
  have : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q, hQ, hmark⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨Q, Ideal.mem_minimalPrimesFinset.mpr hQ, hmark⟩

/-- Assemble the unchanged proper-section bounds for the new marked family. -/
theorem proper_cut {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (s : Shape) {I : Ideal Ambient} {P : Jet} (hs : s.J ≤ s.B) (hI : Active I)
    (hcaps : RowCaps P s) (hprop : toJet P ∉ I) :
    ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight s fee) (sectionDegree I)) ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0 →
        γ ∈ C.direct ∨ ∃ Q ∈ C.curves, OnParent F Q γ := by
  let marked (Q : Ideal Ambient) := Γ.filter (OnParent F Q)
  let direct := (constantComponents I P).biUnion marked
  have hcard : direct.card ≤ (constantComponents I P).card := by
    have hsingle (Q : Ideal Ambient) (hQ : Q ∈ constantComponents I P) :
        (marked Q).card ≤ 1 := by
      obtain ⟨hcomp, hconst⟩ := Finset.mem_filter.mp hQ
      let _ : Q.IsPrime := (cutComponent_curve hI hprop hcomp).1
      apply Finset.card_le_one.mpr
      intro γ hγ δ hδ
      apply sub_left_inj.mp
      apply seedEmbedding.injective
      apply (algebraMap K1_14.FX (CoordinateRing Q)).injective
      exact (seed_value_eq hconst (Finset.mem_filter.mp hγ).2).trans
        (seed_value_eq hconst (Finset.mem_filter.mp hδ).2).symm
    calc
      _ ≤ ∑ Q ∈ constantComponents I P, (marked Q).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ constantComponents I P, 1 := Finset.sum_le_sum hsingle
      _ = _ := by simp
  let C : CutCover :=
    ⟨direct, movingComponents I P, by
      intro Q hQ
      obtain ⟨hcomp, hmov⟩ := Finset.mem_filter.mp hQ
      obtain ⟨hp, hdim⟩ := cutComponent_curve hI hprop hcomp
      exact ⟨hp, hdim, K1_14_2_2_7_1.proof Q hp hdim hmov⟩⟩
  refine ⟨C, ?_, ?_⟩
  · intro fee
    fin_cases fee
    · exact cut_seed_mass s I P hs hI hcaps hprop
    · exact cut_ordinate_mass s I P hs hI hcaps hprop
    · exact hcard.trans (cut_constant_count s I P hs hI hcaps hprop)
  · intro γ hγ hmark hzero
    obtain ⟨Q, hQ, hQmark⟩ := mark_on_cut hmark hzero
    by_cases ht : ConstantSeed Q
    · exact Or.inl (Finset.mem_biUnion.mpr
        ⟨Q, Finset.mem_filter.mpr ⟨hQ, ht⟩, Finset.mem_filter.mpr ⟨hγ, hQmark⟩⟩)
    · exact Or.inr ⟨Q, Finset.mem_filter.mpr ⟨hQ, ht⟩, hQmark⟩

theorem combined_cuts {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    (A : Finset (Ideal Ambient)) (s : Shape) (hs : s.J ≤ s.B)
    (ha : ∀ I ∈ A, Active I)
    (hcut : ∀ I ∈ A, ∃ P : Jet, RowCaps P s ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0) :
    ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight s fee) (mass A)) ∧
      ∀ γ ∈ Γ, (∃ I ∈ A, OnParent F I γ) →
        γ ∈ C.direct ∨ ∃ I ∈ C.curves, OnParent F I γ := by
  have hex (I : Ideal Ambient) (hI : I ∈ A) :
      ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight s fee) (sectionDegree I)) ∧
        ∀ γ ∈ Γ, OnParent F I γ → γ ∈ C.direct ∨ ∃ Q ∈ C.curves, OnParent F Q γ := by
    obtain ⟨P, hp, hprop, hzero⟩ := hcut I hI
    obtain ⟨C, hc, hmarks⟩ := proper_cut F s hs (ha I hI) hp hprop
    exact ⟨C, hc, fun γ hγ hm => hmarks γ hγ hm (hzero γ hγ hm)⟩
  let C (I : Ideal Ambient) : CutCover :=
    if hI : I ∈ A then Classical.choose (hex I hI) else emptyCut
  have hC (I : Ideal Ambient) (hI : I ∈ A) :
      (∀ fee, (C I).cost fee ≤ dot (weight s fee) (sectionDegree I)) ∧
      ∀ γ ∈ Γ, OnParent F I γ → γ ∈ (C I).direct ∨ ∃ Q ∈ (C I).curves, OnParent F Q γ := by
    simpa only [C, dite_eq_left hI] using Classical.choose_spec (hex I hI)
  refine ⟨joinCuts A C, ?_, ?_⟩
  · intro fee
    calc
      _ ≤ ∑ I ∈ A, (C I).cost fee := joinCuts_cost A C fee
      _ ≤ ∑ I ∈ A, dot (weight s fee) (sectionDegree I) :=
        Finset.sum_le_sum (fun I hI => (hC I hI).1 fee)
      _ = _ := sum_dot _ _
  · rintro γ hγ ⟨I, hI, hmark⟩
    rcases (hC I hI).2 γ hγ hmark with hd | ⟨Q, hQ, hmark⟩
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨I, hI, hd⟩)
    · exact Or.inr ⟨Q, Finset.mem_biUnion.mpr ⟨I, hI, hQ⟩, hmark⟩

end
end P0_10R.Bridge
end PackSource_P0_10RBridgeCuts
section PackSource_P0_10RBridgeFixed
set_option autoImplicit true
set_option maxRecDepth 4000

namespace P0_10R.Bridge

noncomputable section

open P0 (AnchorModel AnchoredFamily K I p node)
open K1_13 K1_13_5
open K1_13_5_3 hiding exponent exponent_sufficient chartTotal chartTop
open K1_14_2 (endpointDegree)
open K1_14_2_5
open Polynomial PolynomialDifferential
open scoped BigOperators
open private nodeCut nodeCut_vanishes nodeCut_capped from ProximityPrize.SubmissionLower.Fast070

theorem bridge_word {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hw : M.overhead ≤ 3554) (T : Finset K) (hT : T ⊆ Γ) :
    P0_10.FixedWord M.word T F.scalar endpointDegree := by
  refine ⟨F.distinct.mono hT, ?_, ?_⟩
  · intro γ hγ
    rcases (F.mark γ (hT hγ)).scalar_degree with hz | hd
    · simp [hz]
    · have hc : ((F.scalar γ).natDegree : ℤ) ≤ (endpointDegree : ℤ) := by
        change ((F.scalar γ).natDegree : ℤ) ≤ 134625
        change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at hd
        omega
      exact_mod_cast hc
  · intro γ hγ
    let mark := F.mark γ (hT hγ)
    exact ⟨mark.bad.support, mark.bad.agreement, mark.scalar_hits⟩

/-- The proper value cuts on one regular factor have a uniform capped Bézout bound. -/
private theorem regular_count {w T s} (h : P0_10.FixedWord w T s 134625) (f : Row 2)
    (hf : Irreducible f) (hp : 0 < f.degreeOf 1) {B J : ℕ} (hB : f.totalDegree ≤ B)
    (hJ : f.degreeOf 1 ≤ J) (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) :
    45505 * T.card ≤ 82014 * MvPolynomial.cappedDegreeMixedVolume f.totalDegree
      (f.degreeOf 1) (chartTotal B) (chartTop B J) + 45505 := by
  classical
  let x (γ : K) := marked (extend (s γ))
  have hx : Set.InjOn x (T : Set K) := by
    intro γ hγ η hη heq
    exact h.distinct hγ hη (Polynomial.map_injective embed embed.injective (marked_injective heq))
  have hxg : ∀ γ ∈ T, MvPolynomial.aeval (x γ) (plane f) = 0 := by
    intro γ hγ
    change MvPolynomial.aeval (marked (extend (s γ))) (plane f) = 0
    rw [aeval_plane, (hreg γ hγ).1, map_zero]
  have hxe (γ : K) (hγ : γ ∈ T) (i : I) :
      MvPolynomial.aeval (x γ) (nodeCut w f i) = 0 ↔ (s γ).eval (node i) = w i :=
    nodeCut_vanishes (hreg γ hγ) (h.degree γ hγ) i
  apply P0_10.section_capacity h (by decide)
  rintro i ⟨η, hη, hmiss⟩
  have hproper : nodeCut w f i ∉ Ideal.span {plane f} := by
    intro hcut
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hcut
    exact hmiss ((hxe η hη i).mp (by rw [hq, map_mul, hxg η hη, zero_mul]))
  let hits := T.filter fun γ => (s γ).eval (node i) = w i
  have hplane : plane f ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      f.totalDegree (f.degreeOf 1) := by
    intro m hm
    have hm' := MvPolynomial.support_map_subset toCenter f hm
    exact ⟨MvPolynomial.le_totalDegree hm', MvPolynomial.monomial_le_degreeOf 1 hm'⟩
  have hcap := capped_cut_card (show 0 < chartTotal B by simp [chartTotal])
    (show 0 < chartTop B J by simp [chartTop, chartTotal, K1_14_2.endpointDegree])
    (plane_ne_zero hf.ne_zero) (plane_prime hf hp)
    hplane
    (nodeCut_capped w f hB hJ (hp.trans_le hJ) i) hproper (hits.image x) (by
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hm, hh⟩ := Finset.mem_filter.mp hγ
      exact ⟨hxg γ hm, (hxe γ hm i).mpr hh⟩)
  rw [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hcap
  exact hcap


/-- Fixed first-order tariff at the bridge endpoint for agreement 180217. -/
theorem fixed_count {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hw : M.overhead ≤ 3554) (T : Finset K) (hT : T ⊆ Γ)
    (B J : ℕ) (hB : 2 ≤ B) (hchar : B < p) (hJB : J ≤ B)
    (hG : ∃ G : K1_14_2.ODE, K1_14_2_2.ODECaps G B J ∧
      ∀ γ ∈ T, K1_14_2.fixedAt G (F.scalar γ) = 0) :
    T.card ≤ fixedPrice B J := by
  classical
  obtain ⟨G, ⟨hG0, hGJ, hGB⟩, hg⟩ := hG
  obtain ⟨q, hq, hqb, hqj, hsolve⟩ := clear_equation G hG0 hGJ hGB
  obtain ⟨A, R, hA, hAb, hAj, hR, hRd, hcover⟩ := factor_cover q hq hB hchar hqb hqj
  have word := bridge_word M F hw T hT
  let ordinary := T.filter fun γ => R.eval (extend (F.scalar γ)) = 0
  let reg (g : Row 2) := T.filter fun γ => RegularAt 1 g (extend (F.scalar γ))
  have ordinary_bound : ordinary.card ≤ B * (B - 1) := by
    let s (γ : K) := extend (F.scalar γ)
    have hinj : Set.InjOn s (ordinary : Set K) := fun _ ha _ hb he =>
      word.distinct (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective he)
    have hroot : (ordinary.image s).card ≤ R.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      exact (Polynomial.mem_roots hR).mpr (Finset.mem_filter.mp hγ).2
    rw [Finset.card_image_of_injOn hinj] at hroot
    exact hroot.trans hRd
  have hs : T.card ≤ ordinary.card + ∑ g ∈ A, (reg g).card := by
    have hsub : T ⊆ ordinary ∪ A.biUnion reg := by
      intro γ hγ
      rcases hcover _ (hsolve _ (hg γ hγ)) with hr | ⟨g, ha, hr⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hr⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨g, ha, Finset.mem_filter.mpr ⟨hγ, hr⟩⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))
  let a := chartTotal B
  let v := chartTop B J
  have hn : A.card ≤ B := by
    calc
      A.card = ∑ _ ∈ A, 1 := by simp
      _ ≤ ∑ g ∈ A, g.totalDegree := Finset.sum_le_sum fun g hg =>
        (hA g hg).2.trans_le (g.degreeOf_le_totalDegree 1)
      _ ≤ B := hAb
  have hlocal (g : Row 2) (hg : g ∈ A) :
      45505 * (reg g).card ≤ 82014 * (g.totalDegree * v + g.degreeOf 1 * (a - v)) + 45505 := by
    have hb := (Finset.single_le_sum (fun x _ => Nat.zero_le x.totalDegree) hg).trans hAb
    have hj := (Finset.single_le_sum (fun x _ => Nat.zero_le (x.degreeOf 1)) hg).trans hAj
    exact regular_count (word.mono (Finset.filter_subset _ _)) g (hA g hg).1 (hA g hg).2
      hb hj (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hr : 45505 * (∑ g ∈ A, (reg g).card) ≤
      82014 * (B*v + J*(a-v)) + 45505 * B := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hlocal).trans ?_
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, smul_eq_mul]
    have hn' := Nat.mul_le_mul_left 45505 hn
    rw [Nat.mul_comm 45505 A.card] at hn'
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add
      (Nat.mul_le_mul_right _ hAb) (Nat.mul_le_mul_right _ hAj))) hn'
  have hcost : B*v + J*(a-v) = (B-J)*v + J*a := by
    have hva : v ≤ a := min_le_left _ _
    calc
      B*v + J*(a-v) = ((B-J)+J)*v + J*(a-v) := by rw [Nat.sub_add_cancel hJB]
      _ = (B-J)*v + J*((a-v)+v) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hva]
  have hbox : B * (B - 1) + B = B * B := by
    calc
      _ = B * ((B - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ B)]
  let num := 82014 * ((B-J)*v + J*a)
  have htotal := Nat.mul_le_mul_left 45505 hs
  rw [Nat.mul_add] at htotal
  have ho := Nat.mul_le_mul_left 45505 ordinary_bound
  rw [hcost] at hr
  have hcount : 45505 * T.card ≤ num + 45505 * (B*B) := by
    rw [← hbox, Nat.mul_add]
    dsimp only [num]
    omega
  have hmod := Nat.mod_add_div num 45505
  have hlt := Nat.mod_lt num (by decide : 0 < 45505)
  have hround : T.card ≤ num / 45505 + B*B := by omega
  change T.card ≤ (num + 45505 - 1) / 45505 + B^2
  rw [pow_two]
  exact hround.trans (Nat.add_le_add_right (Nat.div_le_div_right (by omega)) _)


end
end P0_10R.Bridge
end PackSource_P0_10RBridgeFixed
section PackSource_P0_10RBridgeExceptions
set_option autoImplicit true
namespace P0_10R.Bridge

noncomputable section

open P0 (AnchorModel AnchoredFamily K)
open K1_14_2 (Ambient ODE fixedAt)
open K1_14_2_2 (Active ODECaps mass sectionDegree fixedOn eval_fixed)
open K1_14_2_2_5 (product_caps product_fixedOn)
open private parent_caps from ProximityPrize.SubmissionLower.Fast052
open scoped BigOperators Classical

/-- Project the rank-one survivors using the linear section lengths. -/
theorem rank_equation (S : Finset (Ideal Ambient))
    (hS : ∀ I ∈ S, Active I ∧ ¬ K1_14_2_2.dual I)
    (hord : mass S 1 ≤ 65143) (hmix : mass S 2 ≤ 358008) :
    ∃ G : ODE, ODECaps G 358008 65143 ∧ ∀ I ∈ S, fixedOn G I := by
  have hchoose (I : Ideal Ambient) :
      ∃ G : ODE, I ∈ S → ODECaps G (sectionDegree I 2) (sectionDegree I 1) ∧ fixedOn G I := by
    by_cases hI : I ∈ S
    · obtain ⟨G, hg⟩ := parent_caps K1_14_2_2_5_1.proof K1_14_2_2_5_2.proof
        (hS I hI).1 (hS I hI).2
      exact ⟨G, fun _ => hg⟩
    · exact ⟨1, fun h => (hI h).elim⟩
  choose G hG using hchoose
  have hp : ODECaps (∏ I ∈ S, G I) (mass S 2) (mass S 1) :=
    product_caps S G (fun I => sectionDegree I 2) (fun I => sectionDegree I 1)
      (fun I hI => (hG I hI).1)
  exact ⟨∏ I ∈ S, G I, ⟨hp.1, hp.2.1.trans hord, fun j i h => (hp.2.2 j i h).trans hmix⟩,
    fun I hI => product_fixedOn hI G (hG I hI).2⟩

theorem fixed_zero {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {I : Ideal Ambient} {G : ODE} {γ : K} (hm : OnParent F I γ) (hG : fixedOn G I) :
    fixedAt G (F.scalar γ) = 0 := by
  simpa only [eval_fixed] using RingHom.mem_ker.mp (hm hG)

end
end P0_10R.Bridge
end PackSource_P0_10RBridgeExceptions
