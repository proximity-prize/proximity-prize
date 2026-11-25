import ProximityPrize.SubmissionLower.R6960PrefixReceipt
import ProximityPrize.SubmissionLower.Fast069

noncomputable section
set_option Elab.async false
namespace Lower6961.PrefixStage
open Polynomial
open K1_14 (Jet Shape jetAt)
open K1_14_2 (Ambient toJet jetMarkHom OnJet)
open K1_14_2_2 (RowCaps Active dual orderOn)
open K1_14_2_2R (chainCompatible)
open Lower6960.DifferentialContact (Native)
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
      · exact Or.inl ⟨Lower6960.HelperPrefix.dual_order_of_tests active dualJ P r small
          (fun w hw => p w (Nat.lt_succ_of_le hw)),
          Lower6960.HelperPrefix.dual_order_of_tests active dualJ Q r small
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
end Lower6961.PrefixStage
