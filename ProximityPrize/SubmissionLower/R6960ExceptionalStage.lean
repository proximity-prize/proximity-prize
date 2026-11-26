import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup10
import ProximityPrize.SubmissionLower.DdZeLOjNb
import ProximityPrize.SubmissionLower.Gate6966Gate
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.R6960HelperPrefix
import ProximityPrize.SubmissionLower.R6960LineEulerFree
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCyclePrice
import ProximityPrize.SubmissionLower.R6960Low6960GeometryCut

section Merged6967_R6960ExceptionalStage
set_option Elab.async false




set_option Elab.async false

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
    (lo : 2359≤h) (hi : h≤33579) :
    ∃ (P : Fin 17→Jet) (out : Prepared P (fun i=>(bank i).shape) copies
          (evaluated Crt word helperBank.shape (helperCutoff h)) helperBank.shape),
      (out.exception=1 ∨ rescueDegrees out.exception) ∧
      (∀ i,P i∈evaluated Crt word (bank i).shape (cutoff h i)) ∧
      ∀ (_noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
        (z : K1.K) (S : (Polynomial K1.K)), MarkResidues D z S →
        (liftPoly S).natDegree ≤ 131071+h →
        ∀ hits : Finset K1.I, 179818≤hits.card →
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
    (lo : 2359≤h) (hi : h≤33579) (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0) :
    ∃ (P : Fin 17→Jet) (out : Prepared P (fun i=>(bank i).shape) copies
          (evaluated Crt word helperBank.shape (helperCutoff h)) helperBank.shape),
      (out.exception=1 ∨ rescueDegrees out.exception) ∧
      ∀ i (J : Ideal Ambient), Active J → dual J →
      (orderOn J (out.free i) (reserve i+1) ∧ orderOn J (out.helper^copies i) (reserve i+1) ∧
        chainCompatible (out.free i) (out.helper^copies i) J) ∨
      ∃ C : Jet, (RowCaps C (bank i).shape ∨ RowCaps C (HelperPrefix.timesShape (copies i) helperBank.shape)) ∧
        toJet C∉J ∧ ∀ z S, OnJet J z S → MarkResidues D z S →
          (liftPoly S).natDegree≤131071+h →
          ∀ hits : Finset K1.I, 179818≤hits.card →
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

end Merged6967_R6960ExceptionalStage

section Merged6967_R6960Low6960ActiveCycleMixed
set_option Elab.async false




set_option Elab.async false

-- merged module R6960Low6960SharedBentCaps
section Merged_R6960Low6960SharedBentCaps

-- merged module R6960Low6960ActiveCycleChart
section Merged_R6960Low6960ActiveCycleChart

set_option autoImplicit false
set_option Elab.async false

namespace Low6960ActiveCycle

noncomputable section

open Polynomial
open P3 (K)
open Low6960Prices (physicalDegree taylorLength)
open K1_13 (Row shape extend InBox Shape)
open Low48BentCycle (Family rawFamily)
open K1_13_6 (GeoField toGeneric)
open K1_13_6_2 (GeoJets5 actualPoint)
open K1_13_6_2_2 (generic5 rawGraph numerator denominator padded padded_last)
open Low6960GeometryCut_2 (Branch branch_box)
open MvPolynomial
open Low6960GeometryCut_2_1 (valuePolynomial value_section numerator_associated)

private theorem scalar_section {R : Family} {i : Fin 5} {D : GeoJets5}
    (h : Section R i D) (c : GeoField) : Section R i (MvPolynomial.C c * D) := by
  intro m hm
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
  exact h m (MvPolynomial.mem_support_iff.mpr fun hz => hm (mul_eq_zero_of_right _ hz))

private theorem sum_section {R : Family} {i : Fin 5} {ι : Type*} (S : Finset ι)
    (D : ι → GeoJets5) (h : ∀ j ∈ S, Section R i (D j)) :
    Section R i (∑ j ∈ S, D j) := by
  classical
  intro m hm
  obtain ⟨j, hj, hjm⟩ := Finset.mem_biUnion.mp (support_sum hm)
  exact h j hj m hjm

private theorem sub_section {R : Family} {i : Fin 5} {D E : GeoJets5}
    (hD : Section R i D) (hE : Section R i E) : Section R i (D - E) := by
  intro m hm
  exact (Finset.mem_union.mp (MvPolynomial.support_sub (Fin 5) D E hm)).elim (hD m) (hE m)

def Chart {f Q : Row 4} {l : ℕ} (R : Family) (b : Branch f Q l) : Prop :=
    Section R 2 b.graph ∧ ∃ E H : GeoJets5,
      Section R 3 E ∧ Associated (b.onGraph E) (b.localMap b.member) ∧
      Section R 4 H ∧ Associated (b.onGraph H) (b.localMap b.next) ∧
      ∀ x a : K, ∃ D, Section R 4 D ∧
        ∀ S : (Polynomial K), S.natDegree ≤ physicalDegree → ∀ h : b.Contains (actualPoint (extend S)),
          (b.liftedEval (actualPoint (extend S)) h D = 0 ↔ S.eval x = a)

private theorem recover {f Q : Row 4} {l : ℕ} {R : Family} (b : Branch f Q l)
    (hG : Section R 2 (generic5 (rawGraph b.g)))
    (hmem : Section R 3 (generic5 (padded b.g (taylorLength - 4) taylorLength)))
    (hden : Section R 4 (generic5 (denominator b.g (taylorLength - 3))))
    (hpad : ∀ i ≤ taylorLength + 1,
      Section R 4 (generic5 (padded b.g (taylorLength - 3) i))) : Chart R b := by
  have hGraph : generic5 (rawGraph b.g) = b.graph := by
    simp [rawGraph, Branch.graph, Branch.sigma, toGeneric, MvPolynomial.map_rename, map_ofNat]
  let k := taylorLength - 4
  have hk : k + 4 = taylorLength := by decide
  have hk' : (k + 1) + 4 = taylorLength + 1 := by decide
  have hE : Section R 3 (generic5 (padded b.g k (k + 4))) := by
    rw [hk]
    exact hmem
  have hH : Section R 4 (generic5 (padded b.g (k + 1) ((k + 1) + 4))) :=
    hpad _ (by omega)
  rw [padded_last] at hE hH
  have hm := numerator_associated b k
  have hn := numerator_associated b (k + 1)
  rw [hk] at hm
  rw [hk'] at hn
  refine ⟨hGraph ▸ hG, generic5 (numerator b.g k), generic5 (numerator b.g (k + 1)),
    hE, hm, hH, hn, ?_⟩
  intro x a
  have hM : taylorLength ≤ K1.p := by decide
  have hlen : taylorLength ≤ (k + 1) + 5 := by decide
  refine ⟨valuePolynomial taylorLength b.g (k + 1) x a, ?_, ?_⟩
  · unfold valuePolynomial
    apply sub_section
    · apply sum_section
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact scalar_section (R := R) (i := 4) (hpad i (by omega)) _
    · exact scalar_section (R := R) (i := 4) hden _
  · intro T hT h
    exact value_section hM b (k + 1) hlen x a T (Nat.lt_succ_of_le hT) h

theorem ordinary_chart {f Q : Row 4} {l : ℕ} (ht : 1 ≤ (shape f).t) (b : Branch f Q l) :
    Chart (rawFamily (caps (shape f).chamber)) b := by
  obtain ⟨hg, hbox⟩ := Low48BentSupport.chart_support (K1_13_7_1.shape_chamber f) ht (branch_box b)
  exact recover b hg ((hbox _).2 _ (by decide)) (hbox _).1
    (fun i hi => (hbox _).2 i hi)

theorem active_chart {f Q : Row 4} {l K : ℕ}
    (hK : Low6960Prices.ActiveFits f K) (ha : Low6960Prices.activeFitsPrice (shape f) K)
    (b : Branch f Q l) : Chart (activeRaw (shape f).chamber K) b := by
  let p := (shape f).chamber
  have ht : 1 ≤ p.t := by have H : 3 ≤ p.t := ha.1; omega
  have hc : 4 ≤ baseClip p K := ha.2.1
  obtain ⟨hK', hb, _, _, _⟩ := clip_bounds p 0 (p.b + p.j - K)
  have hKb : K ≤ p.b + p.j - baseClip p K := by
    change baseClip p K ≤ p.b + p.j - K at hK'
    omega
  have hFits : Low49ActiveSupport.Fits b.g (p.b + p.j - baseClip p K) := by
    have hsep := Low49ActiveSupport.separant_fits hK b.r
    exact fun m hm => (hsep m hm).trans hKb
  have hg : graphClip p K ≤ baseClip p K := (clip_bounds _ _ _).1
  obtain ⟨hG, hbox⟩ := Low49ActiveSupport.chart_support (K1_13_7_1.shape_chamber f) ht
    (branch_box b) (show 2 ≤ baseClip p K by omega) hFits hb hg
  have hchart (k : ℕ) := hbox k (liftClip p K k) (clip_bounds _ _ _).1
  exact recover b hG ((hchart (taylorLength - 4)).2 taylorLength (by decide))
    (hchart (taylorLength - 3)).1
    (fun i hi => (hchart (taylorLength - 3)).2 i hi)

end

end Low6960ActiveCycle

end Merged_R6960Low6960ActiveCycleChart

-- merged module R6960Low6960SharedBentCaps
section Merged_R6960Low6960SharedBentCaps
set_option Elab.async false
namespace Low6960SharedBentCaps
noncomputable section

open K1_13 (Shape Row shape)
open K1_13_6 (GeoField)
open Low6960Prices (taylorLength)
open Low6960ActiveCycle (Doubled Chart)
open Low48BentLattice (Cap Allowed Chamber latticePoints)
open Low48BentSupport (graph lifted)
open Low48BentCycle (Family rawFamily capFamily capSum ambient_cap integral mixedDegree)
open K1_13_6_2_4_1 (positiveDiagonal)
open MvPolynomial
open scoped BigOperators
open Low48BentCycle (slots ambient_list)

def caps (p q : Shape) : Fin 5 → Cap :=
  ![(p, 0), (q, 0), graph p, lifted p (taylorLength - 4), lifted p (taylorLength - 3)]

theorem caps_chamber {p q : Shape} (hb : p.j ≤ p.b) (ht : 1 ≤ p.t) (hj : 3 * p.t + 3 ≤ p.j) (hq : Chamber (q,0)) :
    ∀ i, Chamber (caps p q i) := by
  intro i
  fin_cases i
  · change Chamber (p, 0)
    exact ⟨hb, show 3 * p.t ≤ p.j by omega, Nat.zero_le _⟩
  · exact hq
  · exact Low48BentSupport.graph_chamber ht hj
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 4)
  · exact Low48BentSupport.lifted_chamber hb hj (by decide : 3 ≤ taylorLength - 3)

private theorem last_allowed {p q : Shape}
    (v : Fin 5) : Allowed (caps p q 4) (Finsupp.single v 1) := by
  let k := taylorLength - 3
  have hb' : 1 ≤ 1 + k * (p.b - 1) := by omega
  have hj' : 4 ≤ 4 + k * (p.j - 2) := by omega
  have ht' : 2 ≤ 2 + k * p.t := by omega
  have hd' : 1 ≤ min (1 + k) ((2 + k * p.t) / 2) := by omega
  fin_cases v <;> simp [caps, lifted, Allowed, ← show k = taylorLength - 3 from rfl] <;> omega

theorem ordinary_doubled {p q : Shape} :
    Doubled (rawFamily (caps p q)) (capFamily (caps p q)) where
  zero_mem i := by simp [rawFamily, Allowed]
  pair_mem _ _ ha _ hb := Low48BentSupport.raw_add ha hb
  last_coordinate := last_allowed

private def integr (a : Cap) : ℚ := integral a

private def signed (p q : Shape) : ℤ :=
  ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℤ) ^ (5 - J.card) *
    integral (Low48BentLattice.Sum J (caps p q))

private theorem base_signed (p q : Shape) :
    Low6960Prices.tiltedSurface p q = (signed p q).toNat := by
  change Low48Price.ambientMix (slots.map (caps p q)) = _
  exact ambient_list (caps p q)

private theorem base_normalize (p q : Shape) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (capSum (caps p q) (positiveDiagonal J))) = (signed p q : ℚ) := by
  have H := Low48BentPolarization.remove_baseline (caps p q)
  change _ = _ at H
  rw [show (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      integr (capSum (caps p q) (positiveDiagonal J))) =
      ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (Low48BentLattice.Sum J (caps p q)) from H]
  unfold signed
  push_cast
  rfl

private theorem ordinary_coeff (a : Cap) (ha : Chamber a) :
    (affineHilbertPolynomial (Ideal.comap
      (monomialMap GeoField (latticePoints a)).toRingHom ⊥)).coeff 5 = integr a / 60 := by
  rw [Low48BentVolume.ambient_coeff a ha]
  unfold integr integral
  rw [Low48BentVolume.cast_price_integral a]

theorem ordinary_budget {p q : Shape} (h : ∀ i, Chamber (caps p q i)) :
    (60 * 32 : ℚ) * mixedDegree (capFamily (caps p q)) ⊥ Finset.univ ≤
      (Low6960Prices.tiltedSurface p q : ℚ) := by
  rw [mul_assoc, ambient_cap (caps p q) h (fun a => integr a / 60) ordinary_coeff]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num : (60 : ℚ) ≠ 0),
    base_normalize, base_signed]
  exact_mod_cast (show signed p q ≤ ((signed p q).toNat : ℤ) by omega)


theorem chart {f Q : Row 4} {l : ℕ} (q : Shape) (ht : 1 ≤ (shape f).t)
    (b : Low6960GeometryCut_2.Branch f Q l) :
    Chart (rawFamily (caps (shape f).chamber q)) b := by
  have h := Low6960ActiveCycle.ordinary_chart ht b
  exact h

#print axioms ordinary_budget
#print axioms chart

end
end Low6960SharedBentCaps

end Merged_R6960Low6960SharedBentCaps

end Merged_R6960Low6960SharedBentCaps

-- merged module R6960Low6960ActiveCycleMixed
section Merged_R6960Low6960ActiveCycleMixed

set_option autoImplicit false
set_option Elab.async false

namespace Low6960ActiveCycle

noncomputable section

open Polynomial MvPolynomial
open P3 (K)
open Low6960GeometryCut (MixedMark CutInput MixedBound)
open Low6960GeometryCut_2 (Branch branch_of_mixed)
open Low6960Prices (primaryBox tiltedSurface)
open K1_13 (Row extend embed shape)
open Low48BentCycle (Family mixedDegree rawFamily capFamily)
open K1_13_6 (Pieces CurveSections toGeneric)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective Demand maximal_demand)
open K1_13_6_2_4 (oldEmbedding)
open scoped BigOperators

theorem mixed {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l budget : ℕ}
    {R B : Family} [∀ i, Finite (B i)]
    (input : CutInput Γ s f Q l) (hDB : Doubled R B)
    (hfbox : Section R 0 (oldEmbedding (toGeneric f)))
    (hQbox : Section R 1 (oldEmbedding (toGeneric Q)))
    (hchart : ∀ b : Branch f Q l, Chart R b)
    (hbudget : (60 * 32 : ℚ) * mixedDegree B ⊥ Finset.univ ≤ (budget : ℚ)) :
    MixedBound Γ s f Q l (60 * 32) budget := by
  classical
  let point (γ : K) := actualPoint (extend (s γ))
  let marked := Γ.filter (fun γ => MixedMark f Q l (extend (s γ)))
  let assign (γ : marked) : Branch f Q l :=
    Classical.choose (branch_of_mixed (Finset.mem_filter.mp γ.property).2)
  let branches := marked.attach.image assign
  let labels (b : Branch f Q l) :=
    marked.filter (fun γ => ∃ h : γ ∈ marked, assign ⟨γ, h⟩ = b)
  have label_sub (b : Branch f Q l) : labels b ⊆ Γ :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have contains_label (b : Branch f Q l) (γ : K) (hγ : γ ∈ labels b) :
      b.Contains (point γ) := by
    obtain ⟨h, rfl⟩ := (Finset.mem_filter.mp hγ).2
    exact Classical.choose_spec (branch_of_mixed (Finset.mem_filter.mp h).2)
  have labels_nonempty (b : Branch f Q l) (hb : b ∈ branches) : (labels b).Nonempty := by
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨γ.val, Finset.mem_filter.mpr ⟨γ.property, γ.property, rfl⟩⟩
  have available (b : Branch f Q l) : ∃ T ⊆ labels b,
      (b.Simple → T = labels b) ∧
      (b ∈ branches → ¬ b.Simple → 0 < T.card ∧ CurveSections (labels b) s T.card ∧
        Demand (labels b) s T) := by
    by_cases hs : b.Simple
    · exact ⟨labels b, Finset.Subset.rfl, fun _ => rfl, fun _ hn => (hn hs).elim⟩
    by_cases hb : b ∈ branches
    · obtain ⟨T, hsub, hd⟩ := maximal_demand (labels b) s (labels_nonempty b hb)
      exact ⟨T, hsub, fun h => (hs h).elim, fun _ _ => hd⟩
    · exact ⟨∅, Finset.empty_subset _, fun h => (hs h).elim, fun h _ => (hb h).elim⟩
  choose demanded demand_sub demand_simple demand_multiple using available
  let points (b : Branch f Q l) := (demanded b).image point
  have points_card (b : Branch f Q l) : (points b).card = (demanded b).card := by
    apply Finset.card_image_of_injOn
    intro γ hγ δ hδ heq
    exact input.distinct (label_sub b (demand_sub b hγ)) (label_sub b (demand_sub b hδ))
      (Polynomial.map_injective embed embed.injective (actualPoint_injective heq))
  have points_on (b : Branch f Q l) (p : JetPoint) (hp : p ∈ points b) : b.Contains p := by
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    exact contains_label b γ (demand_sub b hγ)
  have points_next (b : Branch f Q l) (p : JetPoint) (hp : p ∈ points b) :
      MvPolynomial.eval p b.next = 0 := by
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    apply b.next_actual (contains_label b γ (demand_sub b hγ))
    simpa only [Polynomial.natDegree_map] using input.degree γ (label_sub b (demand_sub b hγ))
  have bound5 := bound hDB f Q l input.small input.proper hfbox hQbox branches points
    (by
      intro b hb
      obtain ⟨hgraph, E, H, hE, hEeq, hH, hHeq, hvalue⟩ := hchart b
      refine ⟨hgraph, ⟨E, hE, hEeq⟩, points_on b, ?_⟩
      by_cases hs : b.Simple
      · exact Or.inr ⟨H, hH, b.lifted_proper_of_associated hHeq (b.next_proper hs),
          fun p hp hon => b.lifted_zero_of_associated hHeq hon (points_next b p hp)⟩
      rcases (demand_multiple b hb hs).2.2 with hone | ⟨x, a, hwit, heq⟩
      · exact Or.inl (by rw [points_card, hone])
      obtain ⟨D, hD, hEval⟩ := hvalue x a
      obtain ⟨δ, hδ, hδvalue⟩ := hwit
      have hδon := contains_label b δ hδ
      refine Or.inr ⟨D, hD, b.lifted_proper_of_nonzero (point δ) hδon ?_, ?_⟩
      · exact fun hzero => hδvalue ((hEval _ (input.degree δ (label_sub b hδ)) hδon).mp hzero)
      · intro p hp hon
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
        have hvalueγ := (Finset.mem_filter.mp (heq ▸ hγ)).2
        exact (hEval _ (input.degree γ (label_sub b (demand_sub b hγ))) hon).mpr hvalueγ)
  let simple := branches.filter Branch.Simple
  let multiple := branches.filter (fun b => ¬ b.Simple)
  let e := multiple.equivFin
  let C : Pieces Γ :=
    { n := multiple.card
      piece := fun i => labels (e.symm i).val
      subset := fun i => label_sub (e.symm i).val
      degree := fun i => (demanded (e.symm i).val).card }
  let B := simple.biUnion labels
  have hmultiple (i : Fin C.n) := Finset.mem_filter.mp (e.symm i).property
  refine ⟨C, B,
    fun i => (demand_multiple _ (hmultiple i).1 (hmultiple i).2).2.1,
    fun i => (demand_multiple _ (hmultiple i).1 (hmultiple i).2).1, ?_, ?_⟩
  · intro γ hγ hm
    have hmark : γ ∈ marked := Finset.mem_filter.mpr ⟨hγ, hm⟩
    let b := assign ⟨γ, hmark⟩
    have hb : b ∈ branches := Finset.mem_image.mpr ⟨_, Finset.mem_attach _ _, rfl⟩
    have hlabel : γ ∈ labels b := Finset.mem_filter.mpr ⟨hmark, hmark, rfl⟩
    by_cases hs : b.Simple
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨b, Finset.mem_filter.mpr ⟨hb, hs⟩, hlabel⟩)
    have hbm : b ∈ multiple := Finset.mem_filter.mpr ⟨hb, hs⟩
    apply Finset.mem_union_left _
    refine Finset.mem_biUnion.mpr ⟨e ⟨b, hbm⟩, Finset.mem_univ _, ?_⟩
    change γ ∈ labels (e.symm (e ⟨b, hbm⟩)).val
    simpa only [Equiv.symm_apply_apply] using hlabel
  · have htotal : C.total = ∑ b ∈ multiple, (demanded b).card := by
      calc
        C.total = ∑ b : multiple, (demanded b.val).card :=
          Equiv.sum_comp e.symm (fun b : multiple => (demanded b.val).card)
        _ = _ := by
          rw [Finset.univ_eq_attach]
          exact Finset.sum_attach multiple (fun b => (demanded b).card)
    have hsimple : (∑ b ∈ simple, b.weight * (points b).card) =
        ∑ b ∈ simple, (labels b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      have hs := (Finset.mem_filter.mp hb).2
      rw [points_card, demand_simple b hs, Branch.weight, ite_eq_left hs, one_mul]
    have hmult : (∑ b ∈ multiple, b.weight * (points b).card) = 2 * C.total := by
      rw [htotal, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hs := (Finset.mem_filter.mp hb).2
      rw [points_card, Branch.weight, ite_eq_right hs]
    have hpart : (∑ b ∈ simple, b.weight * (points b).card) +
        (∑ b ∈ multiple, b.weight * (points b).card) =
        ∑ b ∈ branches, b.weight * (points b).card :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hB : B.card ≤ ∑ b ∈ simple, (labels b).card := Finset.card_biUnion_le
    have hpay : 2 * C.total + B.card ≤ ∑ b ∈ branches, b.weight * (points b).card := by
      rw [← hpart, hsimple, hmult, Nat.add_comm (∑ b ∈ simple, (labels b).card)]
      exact Nat.add_le_add_left hB _
    have hcount := (mul_le_mul_of_nonneg_left bound5 (by norm_num : (0 : ℚ) ≤ 60 * 32)).trans
      hbudget
    have hcount' : (60 * 32) * l * (∑ b ∈ branches, b.weight * (points b).card) ≤
        budget := by
      apply (Nat.cast_le (α := ℚ)).mp
      push_cast
      simpa only [← mul_assoc, show (60 : ℚ) * 32 = 1920 by norm_num] using hcount
    exact (Nat.mul_le_mul_left ((60 * 32) * l) hpay).trans hcount'

theorem mixed_tilted : Low6960GeometryCut.c2Tilted := by
  intro Γ s f Q l input hguard
  let p := (shape f).chamber
  have hp := K1_13_7_1.shape_chamber f
  have ht : 1 ≤ p.t := input.small.2.1
  have hj : 3 * p.t + 3 ≤ p.j := hguard.1
  have hCh : ∀ i, Low48BentLattice.Chamber (caps p i) := caps_chamber hp.1 ht hj
  refine mixed (R := rawFamily (caps p)) (B := capFamily (caps p)) input
    ordinary_doubled ?_ ?_ ?_ ?_
  · exact Low48BentCycle.old_section ⟨le_max_left _ _, le_rfl, le_rfl⟩
  · exact Low48BentCycle.old_section input.box
  · exact ordinary_chart ht
  · exact ordinary_budget hCh

theorem mixed_active : Low6960GeometryCut.c2Active := by
  intro Γ s f Q l input K hK hQ hguard hactive
  let p := (shape f).chamber
  have ht3 : 3 ≤ p.t := hactive.1
  have hfits := caps_active hguard hactive
  have hc : 4 ≤ baseClip p K := hactive.2.1
  have hK' : baseClip p K ≤ p.b + p.j - K := (clip_bounds _ _ _).1
  have hsum : K + baseClip p K ≤ p.b + p.j := by omega
  refine mixed (R := activeRaw p K) (B := activeFamily p K) input
    (active_doubled hfits) ?_ ?_ ?_ ?_
  · exact old_section_active ⟨le_max_left _ _, le_rfl, le_rfl⟩ hK hsum
  · exact old_section_active input.box hQ (by decide : 5164 + 498 ≤ 4012 + 1650)
  · exact active_chart hK hactive
  · exact active_budget ht3 hfits

theorem proof : Low6960Prices.c6 := Low6960GeometryCut.proof mixed_tilted mixed_active

end

end Low6960ActiveCycle

#print axioms Low6960ActiveCycle.proof
#print axioms Low6960ActiveCycle.bound

end Merged_R6960Low6960ActiveCycleMixed

end Merged6967_R6960Low6960ActiveCycleMixed

section Merged6967_R6966ProofPadeChart
set_option Elab.async false





set_option Elab.async false

-- merged module R6966ProofPadeBankRank
section Merged_R6966ProofPadeBankRank

namespace Research6966.PadeBankRank
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset Module
open K1_14 (FX Seeds Jet Shape)
open K1_14_3 (SeedClosure SeedField fibreRow Surface Parent)
open K1_14_1 (CRTLift PoleData)
open PadeRank (Plane)
noncomputable section

private abbrev E := SeedClosure

private def seed : Seeds →ₐ[FX] E :=
  IsScalarTower.toAlgHom FX Seeds E

private theorem seed_eq : seed.toRingHom=K1_14_3.seedGeneric := by
  apply RingHom.ext
  exact IsScalarTower.algebraMap_apply Seeds SeedField E

def fibre : Jet →ₗ[FX] Plane E where
  toFun := fibreRow
  map_add' := by intro x y;simp [fibreRow]
  map_smul' := by
    intro r p
    ext j i
    simp only [fibreRow,coeff_map,coe_mapRingHom,AddMonoidAlgebra.coeff_smul_apply,RingHom.id_apply,←seed_eq]
    exact seed.toLinearMap.map_smul r _

private theorem fibre_inj : Function.Injective fibre :=
  map_injective _ (map_injective _ ((algebraMap SeedField E).injective.comp
    (IsFractionRing.injective Seeds SeedField)))

private def axes (U : Fin 2 → ℕ) (i:KoalaRect.AxisIndex U) : E :=
  seed (MvPolynomial.monomial (KoalaRect.axisExponent i) (1:FX))

def slots (U:Fin 2→ℕ) : Submodule FX E := Submodule.span FX (Set.range (axes U))

instance (U:Fin 2→ℕ) : FiniteDimensional FX (slots U) :=
  Module.Finite.span_of_finite _ (Set.finite_range _)

theorem slot_count (U:Fin 2→ℕ) : finrank FX (slots U)≤KoalaRect.area U := by
  classical
  refine (finrank_span_le_card _).trans ?_
  rw [Set.toFinset_card,←KoalaRect.axis_card]
  exact Fintype.card_range_le _

theorem seed_in_slots {U:Fin 2→ℕ} {p:Seeds} (cap:∀ z,p.degreeOf z≤U z) : seed p∈slots U := by
  classical
  have expand := congrArg seed (MvPolynomial.as_sum p)
  rw [map_sum] at expand
  rw [expand]
  apply Submodule.sum_mem
  intro e he
  obtain ⟨i,eq⟩:=KoalaRect.exists_axisIndex (U:=U) e
    (fun z=>(MvPolynomial.le_degreeOf_of_mem_support z he).trans (cap z))
  have member : axes U i∈slots U:=Submodule.subset_span ⟨i,rfl⟩
  have mul := (slots U).smul_mem (p.coeff e) member
  change (p.coeff e) • seed.toLinearMap (MvPolynomial.monomial _ 1) ∈ _ at mul
  rwa [←LinearMap.map_smul,MvPolynomial.smul_monomial,smul_eq_mul,mul_one,eq] at mul

/-- Generic scalar span of the genuine rectangular evaluated bank. -/
def rows {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→K1_14.L)
    (s:Shape) (W:ℕ) (U:Fin 2→ℕ) : Submodule E (Plane E) :=
  Submodule.span E (fibre '' (KoalaRect.rectEvaluated Crt word s W U : Set Jet))

theorem rows_shape {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→K1_14.L)
    (s:Shape) (W:ℕ) (U:Fin 2→ℕ) : rows Crt word s W U ≤ PadeRank.box E (s.B+1) (s.J+1) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨P,mem,rfl⟩ j i outside
  change ((fibreRow P).coeff j).coeff i = 0
  simp only [fibreRow,coeff_map,coe_mapRingHom]
  suffices orig: (P.coeff j).coeff i=0 by rw [orig,map_zero]
  by_contra ne
  obtain ⟨degree,slope,_⟩:=K1_14_1.evaluated_shape Crt word (KoalaRect.rectEvaluated_le Crt word s W U mem) j i ne
  exact outside (by simp [PadeRank.positions];omega)

instance {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→K1_14.L)
    (s:Shape) (W:ℕ) (U:Fin 2→ℕ) : FiniteDimensional E (rows Crt word s W U) := by
  exact Submodule.finiteDimensional_of_le (rows_shape Crt word s W U)

/-- The native axis rectangle is charged only once per independent generic jet. -/
theorem bank_dimension {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→K1_14.L)
    (s:Shape) (W:ℕ) (U:Fin 2→ℕ) : finrank FX (KoalaRect.rectEvaluated Crt word s W U) ≤
      finrank E (rows Crt word s W U) * KoalaRect.area U := by
  classical
  let V:=KoalaRect.rectEvaluated Crt word s W U
  let H:=rows Crt word s W U
  by_cases finite:FiniteDimensional FX ↥V
  · let f:↥V→ₗ[FX]H := (fibre.comp V.subtype).codRestrict (H.restrictScalars FX)
      (fun x=>Submodule.subset_span ⟨x.val,x.property,rfl⟩)
    let L:Plane E →ₗ[E] (ℕ×ℕ→E) := LinearMap.pi (fun t=>
      (Polynomial.lcoeff E t.2).comp ((Polynomial.lcoeff E[X] t.1).restrictScalars E))
    have inject:Function.Injective L := by
      intro x y eq
      ext j i
      exact congrFun eq (j,i)
    apply le_trans (BoundaryRank.slots_times_rank (slots U) _ H V rfl (L.comp H.subtype) f
      (inject.comp Subtype.val_injective) (fun _ _ eq=>Subtype.ext (fibre_inj (congrArg Subtype.val eq))) ?_)
    · exact Nat.mul_le_mul_left _ (slot_count U)
    · intro x t
      change ((fibreRow x.val).coeff t.1).coeff t.2 ∈ slots U
      simp only [fibreRow,coeff_map,coe_mapRingHom]
      rw [←seed_eq]
      exact seed_in_slots (KoalaRect.rectEvaluated_axis Crt word x.property t.1 t.2)
  · rw [show finrank FX (KoalaRect.rectEvaluated Crt word s W U)=0 from Module.finrank_of_not_finite finite]
    exact Nat.zero_le _

/-- Every vector of the generic span carries the certified order of the
actual bank at each genuine retained parent sheet. -/
theorem rows_contact {h A} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→K1_14.L)
    {s envelope:Shape} {W r:ℕ} (U:Fin 2→ℕ) (fits:TerminalBanks.inside s envelope)
    (small:r+1<K1.p) (cut:W+2*h*r<s.m*A)
    {parents:Finset Surface} (geo:∀ q∈parents,Parent q)
    (pass:∀ q∈parents,TerminalBanks.Pass Crt word A envelope q)
    {y v:E} (sheet:∃ q∈parents,K1_14_3.OnSeedFibre q y v) :
    ∀ Q∈rows Crt word s W U,Q∈(TerminalProjection.fibrePoint y v)^(r+1) := by
  obtain ⟨parent,mem,fiber⟩:=sheet
  let I:Ideal (Plane E):=(TerminalProjection.fibrePoint y v)^(r+1)
  apply (show rows Crt word s W U ≤ I.restrictScalars E from ?_)
  apply Submodule.span_le.mpr
  rintro _ ⟨P,inBank,rfl⟩
  exact TerminalBanks.retained_order Crt word (geo _ mem) (pass _ mem) fits small cut
    (KoalaRect.rectEvaluated_le Crt word s W U inBank) y v fiber

#print axioms bank_dimension
#print axioms rows_contact
end
end Research6966.PadeBankRank

end Merged_R6966ProofPadeBankRank

-- merged module R6966ProofPadeChart
section Merged_R6966ProofPadeChart

namespace Research6966.PadeChart
set_option maxHeartbeats 1000000
open Polynomial Finset Module
open PadeRank (Plane box)
open Pade (totalJet)
open K1_14_1_4 (substitute substitute_C substitute_X doubleMap)
open scoped Polynomial
noncomputable section
variable {K:Type*} [Field K]

def chart (a b u d:K) : Plane K →ₐ[K] Plane K where
  toRingHom := substitute (RingHom.id K) (C (C a*Polynomial.X+C b)) (C (C a)*Polynomial.X+C (C u*Polynomial.X+C d))
  commutes' r := by change substitute _ _ _ (C (C r))=C (C r);simp [substitute,K1_14_1.jetConstant]

private theorem linear_total (a b:K) : totalJet (C (C a*Polynomial.X+C b):Plane K)≤1 := by
  apply (Pade.totalJet_le _ 1).mpr
  intro j i nonzero
  by_cases j0:j=0
  · subst j
    have n : (C a*Polynomial.X+C b:K[X]).coeff i≠0 := by simpa using nonzero
    have cap:=le_natDegree_of_ne_zero n
    have lim := (natDegree_add_le (C a*Polynomial.X) (C b)).trans
      (max_le_max (natDegree_mul_le ..) le_rfl)
    simp only [natDegree_C,natDegree_X] at lim
    omega
  · exact False.elim (nonzero (by simp [coeff_C,j0]))

private theorem slope_total (a u d:K) : totalJet (C (C a)*Polynomial.X+C (C u*Polynomial.X+C d):Plane K)≤1 := by
  unfold totalJet
  rw [map_add]
  apply (MvPolynomial.totalDegree_add ..).trans (max_le _ (linear_total u d))
  apply (Pade.totalJet_le _ 1).mpr
  intro j i nz
  by_cases j1:j=1
  · subst j
    by_cases i0:i=0
    · omega
    · exact False.elim (nz (by simp [coeff_C_mul,coeff_C,i0]))
  · exact False.elim (nz (by simp [coeff_C_mul,coeff_X,Ne.symm j1,j1]))

theorem chart_box (a b u d:K) (B J:ℕ) {P:Plane K} (hp:P∈box K B J) :
    chart a b u d P∈box K B J := by
  classical
  let y : Plane K:=C (C a*Polynomial.X+C b)
  let v : Plane K:=C (C a)*Polynomial.X+C (C u*Polynomial.X+C d)
  change substitute (RingHom.id K) y v P ∈ _
  rw [P.as_sum_support_C_mul_X_pow,map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [map_mul,map_pow,(P.coeff j).as_sum_support_C_mul_X_pow]
  simp only [substitute_C,substitute_X,map_sum,map_mul,map_pow,Finset.sum_mul]
  simp only [coe_eval₂RingHom,eval₂_C,eval₂_X,RingHom.comp_apply,RingHom.id_apply]
  apply Submodule.sum_mem
  intro i hi
  let c := (P.coeff j).coeff i
  let m : Plane K := C (C c)*y^i*v^j
  change m∈_
  by_cases z:m=0
  · rw [z];exact Submodule.zero_mem _
  have active : (j,i)∈PadeRank.positions B J := by
    by_contra no
    exact (mem_support_iff.mp hi) (hp j i no)
  have caps:j<J ∧ j+i<B := by simp [PadeRank.positions] at active;omega
  apply (PadeRank.mem_box z).mpr
  constructor
  · have k0 : totalJet (C (C c):Plane K) ≤ 0 := by
      apply (Pade.totalJet_le _ _).mpr
      intro l t nz
      by_cases h:l=0
      · subst l
        by_cases g:t=0
        · omega
        · exact False.elim (nz (by simp [coeff_C,g]))
      · exact False.elim (nz (by simp [coeff_C,h]))
    have mul (p q:Plane K) : totalJet (p*q)≤totalJet p+totalJet q := by
      unfold totalJet;rw [map_mul];exact MvPolynomial.totalDegree_mul _ _
    have power (p:Plane K) (k:ℕ) : totalJet (p^k)≤totalJet p*k := by
      unfold totalJet;rw [map_pow];simpa only [Nat.mul_comm] using MvPolynomial.totalDegree_pow (Pade.jetVars p) k
    have hy:totalJet y≤1 := linear_total a b
    have hv:totalJet v≤1 := slope_total a u d
    have left:totalJet (y^i) ≤ i := (power y i).trans (by simpa only [one_mul] using Nat.mul_le_mul_right i hy)
    have right:totalJet (v^j) ≤ j := (power v j).trans (by simpa only [one_mul] using Nat.mul_le_mul_right j hv)
    have e:=mul (C (C c)*y^i) (v^j)
    have f:=mul (C (C c)) (y^i)
    change totalJet (C (C c)*y^i*v^j)<B
    omega
  · have vel:v.natDegree≤1 :=
      (natDegree_add_le (C (C a)*Polynomial.X:Plane K) (C (C u*Polynomial.X+C d))).trans
        (max_le ((show (C (C a)*Polynomial.X:Plane K).natDegree≤
          (C (C a):Plane K).natDegree+(Polynomial.X:Plane K).natDegree from natDegree_mul_le).trans (by simp))
          (by rw [natDegree_C];decide))
    have dy:y.natDegree=0:=natDegree_C _
    have cap: m.natDegree≤(C (C c)*y^i:Plane K).natDegree+(v^j).natDegree:=natDegree_mul_le ..
    have first: (C (C c)*y^i:Plane K).natDegree≤0 := (natDegree_mul_le ..).trans (by simp [dy,natDegree_pow])
    have second:(v^j).natDegree ≤ j := by rw [natDegree_pow];simpa using Nat.mul_le_mul_left j vel
    omega

#print axioms chart_box

set_option backward.isDefEq.respectTransparency false in
theorem chart_equiv (a b u d:K) (ne:a≠0) : Function.Bijective (chart a b u d) := by
  let T:=chart a b u d
  have inj:Function.Injective T := by
    apply (injective_iff_map_eq_zero T.toRingHom).mpr
    intro p zero
    by_contra pn
    exact (K1_14_1_4.affine_leading (RingHom.id K) Function.injective_id ne (b:=b)
      (C u*Polynomial.X+C d) pn).2.2 zero
  refine ⟨inj,fun P=>?_⟩
  by_cases zero:P=0
  · exact ⟨0,(map_zero _).trans zero.symm⟩
  let M:=box K (totalJet P+1) (P.natDegree+1)
  have inM:P∈M:=(PadeRank.mem_box zero).mpr ⟨Nat.lt_succ_self _,Nat.lt_succ_self _⟩
  let F:↥M→ₗ[K]M:=T.toLinearMap.restrict (fun Q hQ=>chart_box a b u d _ _ hQ)
  have : FiniteDimensional K ↥M := by dsimp only [M];infer_instance
  have injF:Function.Injective F:=fun x y eq=>Subtype.ext (inj (congrArg Subtype.val eq))
  have onto:Function.Surjective F:=LinearMap.surjective_of_injective (K:=K) (V:=↥M) (f:=F) injF
  obtain ⟨R,eq⟩:=onto ⟨P,inM⟩
  exact ⟨R.val,congrArg Subtype.val eq⟩

theorem chart_graph_primitive (a b u d:K) (ne:a≠0) {G:Pade.Row K} (gp:G.primitive) :
    (chart a b u d G.polynomial).IsPrimitive := by
  let e:=AlgEquiv.ofBijective (chart a b u d) (chart_equiv a b u d ne)
  let F:=FractionRing K[X]
  let f:=algebraMap K[X] F
  have inj:=IsFractionRing.injective K[X] F
  have ir:Irreducible G.polynomial := by
    apply (G.polynomial_primitive gp).irreducible_iff_irreducible_map_fraction_map (K:=F) |>.mpr
    apply Polynomial.irreducible_of_degree_eq_one
    have nz:G.polynomial.map f≠0:=(map_ne_zero_iff (mapRingHom f) (map_injective f inj)).mpr (G.polynomial_ne gp)
    change (G.polynomial.map f).degree=1
    rw [degree_eq_natDegree nz,
      natDegree_map_eq_of_injective inj,G.slope_degree gp]
    rfl
  have ir':Irreducible (e G.polynomial):=(MulEquiv.irreducible_iff e).mpr ir
  apply ir'.isPrimitive
  have cap:=K1_14_1_4.affine_leading (RingHom.id K) Function.injective_id ne (b:=b)
    (C u*Polynomial.X+C d) (G.polynomial_ne gp)
  change (chart a b u d G.polynomial).natDegree≠0
  exact (cap.1.trans (G.slope_degree gp)) ▸ one_ne_zero

#print axioms chart_graph_primitive

def window (K:Type*) [Field K] (S:Finset (ℕ×ℕ)) : Submodule K (Plane K) where
  carrier := {Q | ∀ j i,(j,i)∉S → (Q.coeff j).coeff i=0}
  zero_mem' := by simp
  add_mem' := by intro P Q hp hq j i outside;simp [hp j i outside,hq j i outside]
  smul_mem' := by intro r Q mem j i outside;simp [mem j i outside]

private def read (S:Finset (ℕ×ℕ)) : window K S→ₗ[K](S→K) where
  toFun Q t:=(Q.val.coeff t.val.1).coeff t.val.2
  map_add' := by intro P Q;funext t;simp
  map_smul' := by intro r P;funext t;simp

private theorem read_injective (S:Finset (ℕ×ℕ)) : Function.Injective (read (K:=K) S) := by
  intro P Q eq
  apply Subtype.ext
  ext j i
  by_cases yes:(j,i)∈S
  · exact congrFun eq ⟨(j,i),yes⟩
  · rw [P.property j i yes,Q.property j i yes]

/-- Only the unweighted inner rectangle is needed to measure the gain.
The whole physical window can have a ragged top edge. -/
theorem filtered_gain {G:Pade.Row K} (gp:G.primitive) (ys:Finset K) (v:K→K)
    (hits:∀ y∈ys,G.err v y=0) (k b j:ℕ) (S:Finset (ℕ×ℕ))
    (V:Submodule K (Plane K)) [FiniteDimensional K V]
    (T:Plane K→ₗ[K]Plane K) (inj:Function.Injective T)
    (bank:V≤(window K S).comap T) (inner:box K b j≤(window K S).comap T)
    (contact:∀ Q∈V,∀ y∈ys,Q∈(TerminalProjection.fibrePoint y (v y))^k) :
    finrank K V + PadeRank.gain G.graphDegree ys.card k b j ≤ S.card := by
  classical
  let full:=V ⊔ box K b j
  have fits:full≤(window K S).comap T:=sup_le bank inner
  let F:full→ₗ[K]window K S:=(T.comp full.subtype).codRestrict _ (fun q=>fits q.property)
  have recov:Function.Injective ((read S).comp F) :=
    (read_injective S).comp (fun _ _ eq=>Subtype.ext (inj (congrArg Subtype.val eq)))
  have width := LinearMap.finrank_le_finrank_of_injective recov
  rw [Module.finrank_pi,Fintype.card_coe] at width
  have gain:=PadeRank.gain_bound gp ys v hits k b j (V ⊓ box K b j) inf_le_right
    (fun Q h=>contact Q h.1)
  have dim:=Submodule.finrank_sup_add_finrank_inf_eq V (box K b j)
  rw [PadeRank.box_dimension] at dim
  change finrank K ↥(V ⊔ box K b j)≤S.card at width
  omega

#print axioms filtered_gain
end
end Research6966.PadeChart

end Merged_R6966ProofPadeChart

end Merged6967_R6966ProofPadeChart
