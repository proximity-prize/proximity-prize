import ProximityPrize.SubmissionLower.HighFamilyBase82190
import ProximityPrize.SubmissionLower.GoldBranch7N1
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace HighFamily82190_1
noncomputable section
open Polynomial
open K1_14 (L FX Shape liftPoly triangle)
open K1_14_1
open Front82190 (K I HighBand)
open HighFamily82190 (Bank Listed AdjacentChart asP1Model asP1Family)
open P1_7_1 (groupedPoleMoment nodeRows telescope)
open scoped BigOperators Polynomial
open private pole_bound from ProximityPrize.SubmissionLower.UpperBranch1
theorem source
    (hnodes : ∀ (b : HighBand) (t : Bank), Listed b t → nodeRows t.shape = t.nodeRows)
    (hmoment : ∀ (b : HighBand) (t : Bank), Listed b t →
      groupedPoleMoment t.shape.B t.shape.J ≤ t.poleMoment ∧ t.shape.B < K1.p) :
    HighFamily82190.c1 := by
  intro b u del M Γ F hband _ H hH
  have hlocal := P1_7_1_1.of_children P1_7_1_1_1.proof P1_7_1_1_2.proof
  let h := M.overhead.toNat
  have hg := HighFamily82190.terminal_guards b
  have hlo : 0 < h := by
    obtain ⟨hlo, _⟩ := hband
    have := hg.1
    dsimp [h]
    omega
  have hhi : h ≤ 33307 := by
    obtain ⟨_, hhi⟩ := hband
    have := hg.2.1
    dsimp [h]
    omega
  have hraw : h ≤ 131070 := hhi.trans (by decide)
  have hchar : h < K1.p := hhi.trans_lt (by decide)
  obtain ⟨D, hnode, hres⟩ := P1_7_1.chart_poles (asP1Model M) (asP1Family M F) H hH
  obtain ⟨Crt⟩ := P0_10_1.crt_lift D
  let word : I → L := fun i => algebraMap K L (M.word i)
  refine ⟨evaluated Crt word, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro t _ t' _ hm hB hJ hU W W' hW
    exact evaluated_mono Crt word hm hB hJ hU hW
  · intro t _ W hW P hP γ hγ
    let B := F.mark γ hγ
    have hdegree : (liftPoly (F.scalar γ)).natDegree ≤ 131071 + h := by
      rw [liftPoly, Polynomial.natDegree_map]
      rcases B.scalar_degree with hzero | hd
      · simp [hzero]
      · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at hd
        dsimp [h]
        omega
    refine P0_10_1.contact_vanish Crt word hnode (M.label γ) (F.scalar γ) (hres γ hγ) hdegree B.bad.support
      B.bad.agreement ?_ t.shape W hW P hP
    intro i hit
    rw [liftPoly, nodeL, Polynomial.eval_map, Polynomial.eval₂_hom]
    exact congrArg (algebraMap K L) (B.scalar_hits i hit)
  · intro t _ W P hP j i hne
    exact evaluated_shape Crt word hP j i hne
  · intro t _ W P hP hne
    exact P0_10_1.leading_bound hlo hraw Crt word t.shape W P hP hne
  · intro t _ W P hP i r
    exact P0_10_1.evaluated_shift Crt word hP i r
  · intro t ht W _ hW
    obtain ⟨hm, hB⟩ := hmoment b t ht
    have hvol := P0_10_1.ambient_bound (hraw.trans (by decide)) t.shape W hW
    have hcontact := P0_10_1.physical_bound h word t.shape W
    have hpole := pole_bound hlocal hlo hchar Crt word t.shape hB W
    have hsum := telescope hraw Crt word t.shape W
    have hphys : physicalDebit t.shape = triangle t.shape.U * t.nodeRows := by
      rw [← hnodes b t ht]
      unfold physicalDebit nodeRows
      rw [Nat.mul_assoc]
    rw [hphys] at hcontact
    have hextra := Nat.mul_le_mul_left (2*h*(t.shape.U+1)) hm
    change rawVolumeAt h t.shape W ≤
      (triangle t.shape.U * t.nodeRows + 2*h*(t.shape.U+1)*t.poleMoment) +
        ∑ w ∈ Finset.range (W+1), Module.finrank FX (evaluated Crt word t.shape w)
    omega
end
open private listed_ok from ProximityPrize.SubmissionLower.GoldBranch7N1
theorem proof : HighFamily82190.c1 :=
  source (fun b t ht => (listed_ok b t ht).nodes) (fun b t ht => (listed_ok b t ht).moment)
end HighFamily82190_1
end
