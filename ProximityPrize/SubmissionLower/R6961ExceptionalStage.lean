import ProximityPrize.SubmissionLower.R6960PrefixReceipt
import ProximityPrize.SubmissionLower.Fast069
import ProximityPrize.SubmissionLower.R6960HelperPrefix

set_option Elab.async false

-- merged module R6961PrefixStage
section Merged_R6961PrefixStage

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

end
end Merged_R6961PrefixStage

-- merged module R6961ExceptionalStage
section Merged_R6961ExceptionalStage

noncomputable section
set_option Elab.async false
namespace Lower6961.ExceptionalStage
open Polynomial Finset
open K1_14 (Jet Shape jetAt)
open K1_14_2 (Ambient toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual orderOn mass)
open K1_14_2_2_4 (pairCap)
open Lower6960.DifferentialContact (Native)
open K1_14_2_2_2_3 (jetEquiv jetEquiv_apply)
open Lower6960.PrefixRows (power_caps)
open Lower6961.PrefixStage (failed_contact)

/-- Intersect the passing dual parents with the power of their exceptional
factor; each failing parent gets a cutter bounded solely by the rescue row. -/
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
    apply Lower6960.HelperPrefix.exceptional_history G Q s t kept (r+1) (Nat.succ_pos _) c irr.ne_zero
      (fun hz=>avoid (hz ▸ dvd_zero G)) proper js jt (power_caps irr.ne_zero gs _) qt
    intro I hi
    obtain ⟨p,d,g⟩ := on I (spec.mp hi).1
    exact ⟨p,d,g,Lower6960.HelperPrefix.dual_order_of_tests p d Q r small
      (fun w hw=>(spec.mp hi).2 w (Nat.lt_succ_of_le hw))⟩
  · intro I inside fails
    exact failed_contact qt (fun pass=>fails (spec.mpr ⟨inside,pass⟩))

#print axioms filter

/-- The stage sets are nested even when the reserves decrease. A later set
inherits every earlier mass bound, and each newly lost parent has a cutter. -/
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
end Lower6961.ExceptionalStage

end
end Merged_R6961ExceptionalStage
