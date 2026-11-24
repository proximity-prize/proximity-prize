import ProximityPrize.SubmissionLower.R6960PrefixStage

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
    apply HelperPrefix.exceptional_history G Q s t kept (r+1) (Nat.succ_pos _) c irr.ne_zero
      (fun hz=>avoid (hz ▸ dvd_zero G)) proper js jt (power_caps irr.ne_zero gs _) qt
    intro I hi
    obtain ⟨p,d,g⟩ := on I (spec.mp hi).1
    exact ⟨p,d,g,HelperPrefix.dual_order_of_tests p d Q r small
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
end Lower6960.ExceptionalStage
