import ProximityPrize.SubmissionLower.R6960PrefixReceipt
import ProximityPrize.SubmissionLower.R6960FreeSource6960
import ProximityPrize.SubmissionLower.Fast069

-- merged module R6960MainPrefixSource
section Merged_R6960MainPrefixSource
noncomputable section
set_option Elab.async false
namespace Lower6960.MainPrefixSource
open Polynomial
open K1_14 (Jet L liftPoly)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (jetMarkHom toJet)
open HelperSource (helperBank helperCutoff)
open DifferentialContact (Native)
open PrefixRows (Prepared rescueDegrees)
open FreeSource (bank cutoff reserve)
open K1_14_2_6_2 (seedIndex)
open K1_14_2_4_2 (factorial_ne_zero)
open K1_14_2_2_3 (shiftedWord)
open K1_14_2_6_2 (seed_iter coordDeriv)
def copies (i : Fin 17) := (reserve i+11)/11
theorem hasse_at_mark {z : K1.K} {S : (Polynomial K1.K)} {P : Jet} {r : ℕ}
    (contact : Native (RingHom.ker (jetMarkHom z S)) (r+1) P)
    (j : Fin 2) (a : ℕ) (within : a≤r) (small : a<K1.p) :
    K1_14.jetAt (K1_14.seedHasse j a P) z S=0 := by
  have rep (n : ℕ) : toJet (shiftedWord P (List.replicate n j)) =
      (coordDeriv (seedIndex j))^[n] (toJet P) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.replicate_succ,shiftedWord,Function.iterate_succ_apply',←ih]
      simpa using (seed_iter j 1 (shiftedWord P (List.replicate n j))).symm
  have van := RingHom.mem_ker.mp (contact (List.replicate a j) (by simpa using Nat.lt_succ_of_le within))
  rw [rep,seed_iter,map_nsmul,nsmul_eq_mul,K1_14_2.eval_toJet] at van
  exact (mul_eq_zero.mp van).resolve_left (factorial_ne_zero small)
theorem rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I→L)
    (lo : 2402≤h) (hi : h≤33619) :
    ∃ (P : Fin 17→Jet) (out : Prepared P (fun i=>(bank i).shape) copies
          (evaluated Crt word helperBank.shape (helperCutoff h)) helperBank.shape),
      (out.exception=1 ∨ rescueDegrees out.exception) ∧
      (∀ i,P i∈evaluated Crt word (bank i).shape (cutoff h i)) ∧
      ∀ (_noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
        (z : K1.K) (S : (Polynomial K1.K)), MarkResidues D z S →
        (liftPoly S).natDegree ≤ 131071+h →
        ∀ hits : Finset K1.I, 179798≤hits.card →
        (∀ i ∈ hits,(liftPoly S).eval (nodeL i)=word i) →
        toJet out.exception∉RingHom.ker (jetMarkHom z S) →
        ∀ i, Native (RingHom.ker (jetMarkHom z S)) (reserve i+1) (out.free i) ∧
          Native (RingHom.ker (jetMarkHom z S)) (reserve i+1) (out.helper^(copies i)) := by
  choose P inside nz using FreeSource.free_rows Crt word lo hi
  obtain ⟨out,kind⟩ := PrefixRows.prepare_6960 P (fun i=>(bank i).shape) copies nz
    (fun i=>evaluated_shape Crt word (inside i)) Crt word lo hi
  refine ⟨P,out,kind,inside,?_⟩
  intro noPole z S residues degree hits many agree regular i
  apply PrefixRows.native_at_6960 Crt word lo hi out i (cutoff h i) (reserve i) (inside i)
  · exact FreeSource.cutoff_fit lo hi i
  · unfold copies
    omega
  all_goals assumption
#print axioms rows
#print axioms hasse_at_mark
end Lower6960.MainPrefixSource

end
end Merged_R6960MainPrefixSource

-- merged module R6960PrefixStage
section Merged_R6960PrefixStage
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
theorem all_stages {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I→L)
    (lo : 2402≤h) (hi : h≤33619) (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0) :
    ∃ (P : Fin 17→Jet) (out : Prepared P (fun i=>(bank i).shape) copies
          (evaluated Crt word helperBank.shape (helperCutoff h)) helperBank.shape),
      (out.exception=1 ∨ rescueDegrees out.exception) ∧
      ∀ i (J : Ideal Ambient), Active J → dual J →
      (orderOn J (out.free i) (reserve i+1) ∧ orderOn J (out.helper^copies i) (reserve i+1) ∧
        chainCompatible (out.free i) (out.helper^copies i) J) ∨
      ∃ C : Jet, (RowCaps C (bank i).shape ∨ RowCaps C (HelperPrefix.timesShape (copies i) helperBank.shape)) ∧
        toJet C∉J ∧ ∀ z S, OnJet J z S → MarkResidues D z S →
          (liftPoly S).natDegree≤131071+h →
          ∀ hits : Finset K1.I, 179798≤hits.card →
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

end
end Merged_R6960PrefixStage

-- merged module R6960ExceptionalStage
section Merged_R6960ExceptionalStage
noncomputable section
set_option Elab.async false
namespace Lower6960.ExceptionalStage
open Polynomial Finset
open K1_14 (Jet Shape jetAt)
open K1_14_2 (Ambient toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual orderOn mass)
open K1_14_2_2_4 (pairCap)
open DifferentialContact (Native)
open K1_14_2_2_2_3 (jetEquiv jetEquiv_apply)
open Lower6960.PrefixRows (power_caps)
open Lower6960.PrefixStage (failed_contact)
theorem filter {G Q : Jet} (irr : Irreducible G) (avoid : ¬G∣Q) {s t : Shape}
    (gs : RowCaps G s) (qt : RowCaps Q t) (js : s.J≤s.B) (jt : t.J≤t.B)
    (parents : Finset (Ideal Ambient))
    (on : ∀ I∈parents, Active I ∧ dual I ∧ toJet G∈I) (r : ℕ) (small : r<K1.p) :
    ∃ survivors ⊆ parents,
      (∀ I∈survivors, Native I (r+1) Q) ∧
      (∀ c : Fin 4, (r+1)*mass survivors c≤pairCap s t c) ∧
      ∀ I∈parents, I∉survivors →
        ∃ C : Jet, RowCaps C t ∧ toJet C∉I ∧
          ∀ z S, Native (RingHom.ker (jetMarkHom z S)) (r+1) Q → jetAt C z S=0 := by
  classical
  let kept := parents.filter (fun I=>Native I (r+1) Q)
  have spec {I} : I∈kept ↔ I∈parents ∧ Native I (r+1) Q := mem_filter
  have ambientPrime : Irreducible (toJet G) := by
    rw [←jetEquiv_apply]
    exact (MulEquiv.irreducible_iff K1_14_2_2_2_3.jetEquiv).mpr irr
  have proper : IsRelPrime (toJet G) (toJet Q) := by
    apply ambientPrime.isRelPrime_iff_not_dvd.mpr
    rwa [←jetEquiv_apply,←jetEquiv_apply,map_dvd_iff]
  refine ⟨kept,fun _ hin=>(spec.mp hin).1,fun _ hin=>(spec.mp hin).2,?_,?_⟩
  · intro c
    apply HelperPrefix.exceptional_history G Q s t kept (r+1) (Nat.succ_pos _) c irr.ne_zero
      (fun hz=>avoid (hz ▸ dvd_zero G)) proper js jt (power_caps irr.ne_zero gs _) qt
    intro I hi
    obtain ⟨p,d,g⟩ := on I (spec.mp hi).1
    exact ⟨p,d,g,HelperPrefix.dual_order_of_tests p d Q r small
      (fun w hw=>(spec.mp hi).2 w (Nat.lt_succ_of_le hw))⟩
  · intro I inside fails
    exact failed_contact qt (fun pass=>fails (spec.mpr ⟨inside,pass⟩))
#print axioms filter
theorem history {G : Jet} (irr : Irreducible G) {s : Shape} (gs : RowCaps G s) (js : s.J≤s.B)
    (Q : Fin 17→Jet) (t : Fin 17→Shape) (r : Fin 17→ℕ)
    (avoid : ∀ i,¬G∣Q i) (caps : ∀ i,RowCaps (Q i) (t i)) (jt : ∀ i,(t i).J≤(t i).B)
    (small : ∀ i,r i<K1.p) (parents : Finset (Ideal Ambient))
    (on : ∀ I∈parents,Active I ∧ dual I ∧ toJet G∈I) :
    ∃ kept : ℕ → Finset (Ideal Ambient),
      kept 0=parents ∧ Antitone kept ∧
      (∀ i : Fin 17, ∀ n, i.val<n → ∀ c : Fin 4,(r i+1)*mass (kept n) c≤pairCap s (t i) c) ∧
      ∀ (i : Fin 17) I, I∈kept i.val → I∉kept (i.val+1) →
        ∃ C : Jet, RowCaps C (t i) ∧ toJet C∉I ∧
          ∀ z S,Native (RingHom.ker (jetMarkHom z S)) (r i+1) (Q i) → jetAt C z S=0 := by
  classical
  choose S sub pass cap cut using fun i=>filter irr (avoid i) gs (caps i) js (jt i)
    parents on (r i) (small i)
  let kept (n : ℕ) := parents.filter (fun J=>∀ i : Fin 17, i.val<n → J∈S i)
  have spec {J n} : J∈kept n ↔ J∈parents ∧ ∀ i : Fin 17,i.val<n → J∈S i := mem_filter
  refine ⟨kept,?_,?_,?_,?_⟩
  · ext J
    simp [kept]
  · intro a b hab J inside
    obtain ⟨p,prior⟩ := spec.mp inside
    exact spec.mpr ⟨p,fun i h=>prior i (h.trans_le hab)⟩
  · intro i n hi c
    have stage : kept n⊆S i := fun _ mem=>(spec.mp mem).2 i hi
    exact (Nat.mul_le_mul_left _ (K1_14_2_2.mass_mono stage c)).trans (cap i c)
  · intro i J prev lost
    obtain ⟨p,prior⟩ := spec.mp prev
    apply cut i J p
    intro hit
    apply lost (spec.mpr ⟨p,?_⟩)
    intro j hj
    by_cases e : j=i
    · exact e ▸ hit
    · apply prior
      have diff : j.val≠i.val := fun eq=>e (Fin.ext eq)
      omega
#print axioms history
end Lower6960.ExceptionalStage

end
end Merged_R6960ExceptionalStage
