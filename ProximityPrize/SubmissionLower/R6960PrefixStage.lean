import ProximityPrize.SubmissionLower.R6960MainPrefixSource

noncomputable section
set_option Elab.async false
namespace Lower6960.PrefixStage
open Polynomial
open K1_14 (Jet Shape jetAt)
open K1_14_2 (Ambient toJet jetMarkHom OnJet)
open K1_14_2_2 (RowCaps Active dual orderOn)
open K1_14_2_2R (chainCompatible)
open DifferentialContact (Native)
open K1_14_2_2_3 (shiftedWord)

private theorem shifted_caps {P : Jet} {s : Shape} (hp : RowCaps P s) (w : List (Fin 2)) :
    RowCaps (shiftedWord P w) s := by
  induction w with
  | nil => exact hp
  | cons j w ih => exact P1_7_4_1_2.proof _ _ ih j 1

theorem failed_contact {J : Ideal Ambient} {P : Jet} {s : Shape} {r : ℕ}
    (cap : RowCaps P s) (fails : ¬Native J (r+1) P) :
    ∃ C : Jet, RowCaps C s ∧ toJet C∉J ∧
      ∀ z S, Native (RingHom.ker (jetMarkHom z S)) (r+1) P → jetAt C z S=0 := by
  classical
  unfold Native at fails
  push Not at fails
  obtain ⟨w,hw,fail⟩ := fails
  refine ⟨shiftedWord P w,shifted_caps cap w,fail,?_⟩
  intro z S marked
  exact K1_14_2.eval_toJet _ _ _ ▸ RingHom.mem_ker.mp (marked w hw)

/-- Either both rows have full local order and compatible ordinary factors,
or a single capped proper cutter vanishes at every marked point on this parent. -/
theorem order_or_cut {J : Ideal Ambient} (active : Active J) (dualJ : dual J)
    {r : ℕ} (small : r<K1.p) {P Q : Jet} {s t : Shape}
    (cp : RowCaps P s) (cq : RowCaps Q t) (nq : Q≠0) (slope : 0<t.J) :
    (orderOn J P (r+1) ∧ orderOn J Q (r+1) ∧ chainCompatible P Q J) ∨
      ∃ C : Jet, (RowCaps C s ∨ RowCaps C t) ∧ toJet C∉J ∧
        ∀ z S, OnJet J z S →
          Native (RingHom.ker (jetMarkHom z S)) (r+1) P →
          Native (RingHom.ker (jetMarkHom z S)) (r+1) Q → jetAt C z S=0 := by
  classical
  by_cases p : Native J (r+1) P
  · by_cases q : Native J (r+1) Q
    · by_cases compat : chainCompatible P Q J
      · exact Or.inl ⟨HelperPrefix.dual_order_of_tests active dualJ P r small
          (fun w hw => p w (Nat.lt_succ_of_le hw)),
          HelperPrefix.dual_order_of_tests active dualJ Q r small
          (fun w hw => q w (Nat.lt_succ_of_le hw)),compat⟩
      · unfold chainCompatible at compat
        push Not at compat
        obtain ⟨f,_,_,_,div,mem,g,a,clear,proper⟩ := compat
        refine Or.inr ⟨K1_14_3R.chainCutter g,Or.inr
          (K1_14_3R.chainCutter_caps_of_dvd nq cq slope div clear),proper,?_⟩
        intro z S on _ _
        apply K1_14_3R.chainCutter_zero clear
        have hz := RingHom.mem_ker.mp (on mem)
        simpa only [K1_14_2.eval_toJet,jetAt,eval₂_C,coe_eval₂RingHom,K1_14.atMark] using hz
    · obtain ⟨C,cap,out,zero⟩ := failed_contact cq q
      exact Or.inr ⟨C,Or.inr cap,out,fun z S _ _ hq=>zero z S hq⟩
  · obtain ⟨C,cap,out,zero⟩ := failed_contact cp p
    exact Or.inr ⟨C,Or.inl cap,out,fun z S _ hp _=>zero z S hp⟩

#print axioms order_or_cut

open FreeSource (bank reserve cutoff)
open HelperSource (helperBank helperCutoff)
open K1_14 (L liftPoly)
open K1_14_1 (PoleData CRTLift evaluated nodeL MarkResidues)
open MainPrefixSource (copies)
open PrefixRows (Prepared rescueDegrees)

/-- The order-or-cut alternative for the actual 17 main pairs. On a failing
parent the cutter is chosen once and works for every main mark on it. -/
theorem all_stages {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I→L)
    (lo : 2339≤h) (hi : h≤33561) (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0) :
    ∃ (P : Fin 17→Jet) (out : Prepared P (fun i=>(bank i).shape) copies
          (evaluated Crt word helperBank.shape (helperCutoff h)) helperBank.shape),
      (out.exception=1 ∨ rescueDegrees out.exception) ∧
      ∀ i (J : Ideal Ambient), Active J → dual J →
      (orderOn J (out.free i) (reserve i+1) ∧ orderOn J (out.helper^copies i) (reserve i+1) ∧
        chainCompatible (out.free i) (out.helper^copies i) J) ∨
      ∃ C : Jet, (RowCaps C (bank i).shape ∨ RowCaps C (HelperPrefix.timesShape (copies i) helperBank.shape)) ∧
        toJet C∉J ∧ ∀ z S, OnJet J z S → MarkResidues D z S →
          (liftPoly S).natDegree≤131071+h →
          ∀ hits : Finset K1.I, 179827≤hits.card →
          (∀ j∈hits,(liftPoly S).eval (nodeL j)=word j) →
          toJet out.exception∉RingHom.ker (jetMarkHom z S) → jetAt C z S=0 := by
  obtain ⟨P,out,kind,_,contact⟩ := MainPrefixSource.rows Crt word lo hi
  refine ⟨P,out,kind,?_⟩
  intro i J active dualJ
  have pos : 0<copies i := by unfold copies; omega
  have slope : 0<(HelperPrefix.timesShape (copies i) helperBank.shape).J :=
    Nat.mul_pos pos (by decide)
  have small : reserve i<K1.p := by fin_cases i <;> decide +kernel
  rcases order_or_cut active dualJ small (out.free_caps i) (out.moving_caps i)
    (pow_ne_zero _ out.helper_ne) slope with good | ⟨C,cap,proper,cut⟩
  · exact Or.inl good
  · refine Or.inr ⟨C,cap,proper,?_⟩
    intro z S on residues degree hits many agree regular
    obtain ⟨free,moving⟩ := contact noPole z S residues degree hits many agree regular i
    exact cut z S on free moving

#print axioms all_stages
end Lower6960.PrefixStage
