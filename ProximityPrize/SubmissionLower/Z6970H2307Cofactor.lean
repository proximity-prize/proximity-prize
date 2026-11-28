import ProximityPrize.SubmissionLower.Z6970ExpandedColumns
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Height2307Cofactor
noncomputable section

open K1_13 (Geom)
open K1_13_2_2 (JetExp gradeWeight oldWeight)
open ExpandedColumns6970 (jetColumns jetExponents)

open MvPolynomial
open scoped BigOperators

def fitsBox (b j t : ℕ) (m : JetExp) : Prop :=
  m.weight gradeWeight≤b ∧ m.weight oldWeight≤j ∧ m 3≤t

noncomputable instance (b j t : ℕ) (m : JetExp) : Decidable (fitsBox b j t m) := by
  unfold fitsBox
  infer_instance

noncomputable def ambCount (b j t : ℕ) : ℕ :=
  (jetColumns.filter (fitsBox b j t)).card

private theorem down {a b : JetExp} (h : a+b ∈ jetExponents) : b ∈ jetExponents := by
  obtain ⟨hB,hJ,hT,hcap⟩ := h
  change (a+b).weight gradeWeight ≤ 4024 at hB
  change (a+b).weight oldWeight ≤ 1679 at hJ
  change (a+b) 3 ≤ 500 at hT
  change (a+b) 1 + (a+b) 2 + (a+b) 3 ≤
    ExpandedTaper6970.cap ((a+b).weight gradeWeight) at hcap
  rw [map_add] at hB hJ hcap
  simp only [Finsupp.add_apply] at hT hcap
  have hc := ExpandedTaper6970.cap_antitone
    (show b.weight gradeWeight ≤ a.weight gradeWeight+b.weight gradeWeight by omega)
  exact ⟨by omega,by omega,by omega,by omega⟩

/-- The leading monomial remains in the ambient columns after removing a fixed factor. -/
private theorem lead_in_box {P Q : MvPolynomial (Fin 4) Geom} {b j : ℕ}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hB : P.totalDegree = b)
    (hJ : weightedTotalDegree oldWeight P = j)
    (support : ∀ m ∈ (P*Q).support, m ∈ jetExponents) :
    MonomialOrder.degLex.degree Q ∈ jetColumns.filter (fitsBox (4024-b) (1679-j) 500) := by
  let m := MonomialOrder.degLex.degree Q
  have hm : m ∈ Q.support := MonomialOrder.degLex.degree_mem_support hQ
  have hp := support _ (MonomialOrder.degLex.degree_mem_support (mul_ne_zero hP hQ))
  rw [MonomialOrder.degLex.degree_mul hP hQ] at hp
  have hd : m ∈ jetExponents := down hp
  have hdeg (w : Fin 4 → ℕ) (H : ∀ s ∈ (P*Q).support, s.weight w ≤ 4024) :
      weightedTotalDegree w (P*Q) ≤ 4024 :=
    Finset.sup_le H
  have bd : (P*Q).totalDegree ≤ 4024 := by
    rw [← weightedTotalDegree_one]
    exact hdeg gradeWeight (fun a ha => (support a ha).1)
  have id : weightedTotalDegree oldWeight (P*Q) ≤ 1679 :=
    Finset.sup_le fun a ha => (support a ha).2.1
  rw [totalDegree_mul_of_isDomain hP hQ,hB] at bd
  rw [weightedTotalDegree_mul _ _ _ hP hQ,hJ] at id
  have bq : m.weight gradeWeight ≤ Q.totalDegree := by
    rw [← weightedTotalDegree_one]
    exact le_weightedTotalDegree gradeWeight hm
  have jq : m.weight oldWeight ≤ weightedTotalDegree oldWeight Q :=
    le_weightedTotalDegree oldWeight hm
  change m ∈ jetColumns.filter (fitsBox (4024-b) (1679-j) 500)
  exact Finset.mem_filter.mpr ⟨ExpandedColumns6970.jetExponents_finite.mem_toFinset.mpr hd,
    ⟨show m.weight gradeWeight ≤ 4024-b by omega,
      show m.weight oldWeight ≤ 1679-j by omega,hd.2.2.1⟩⟩

noncomputable def remaining (b j : ℕ) : ℕ :=
  if b≤4024 ∧ j≤1679 then ambCount (4024-b) (1679-j) 500 else 0

/-- Projection to the surviving wide columns is injective on all cofactors of a fixed product. -/
theorem rank {r b j : ℕ} (P : MvPolynomial (Fin 4) Geom) (hP : P ≠ 0)
    (hB : P.totalDegree = b) (hJ : weightedTotalDegree oldWeight P = j)
    (e : Fin r → MvPolynomial (Fin 4) Geom) (hli : LinearIndependent Geom e)
    (hs : ∀ i m, m ∈ (e i).support → m ∈ jetExponents)
    (hd : ∀ i, P ∣ e i) :
    r ≤ remaining b j := by
  classical
  by_cases h0 : r=0
  · simp [h0]
  choose Q hQ using hd
  have hQne (i : Fin r) : Q i ≠ 0 := by
    intro hz
    exact hli.ne_zero i (by rw [hQ i,hz,mul_zero])
  have hQli : LinearIndependent Geom Q := by
    apply LinearIndependent.of_comp (LinearMap.mulLeft Geom P)
    have heq : (LinearMap.mulLeft Geom P) ∘ Q = e := funext fun i => (hQ i).symm
    rwa [heq]
  let U := restrictSupport Geom jetExponents
  let V := U.comap (LinearMap.mulLeft Geom P)
  let C := jetColumns.filter (fitsBox (4024-b) (1679-j) 500)
  let W := restrictSupport Geom (C : Set JetExp)
  have memV (i : Fin r) : Q i ∈ V := by
    change P * Q i ∈ U
    rw [← hQ i]
    exact (mem_restrictSupport_iff Geom).mpr (hs i)
  have projMem (q : V) : filterSupport (fun m => m∈C) q.val ∈ W := by
    apply (mem_restrictSupport_iff Geom).mpr
    intro m hm
    by_contra hmc
    have hc := mem_support_iff.mp hm
    rw [coeff_filterSupport] at hc
    exact hc (if_neg hmc)
  let project : V →ₗ[Geom] W :=
    ((filterSupport (fun m => m∈C)).domRestrict V).codRestrict W projMem
  have ker : LinearMap.ker project = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro q hz
    apply Subtype.ext
    by_contra hq
    have support : ∀ m ∈ (P*q.val).support, m ∈ jetExponents :=
      (mem_restrictSupport_iff Geom).mp q.property
    have member := lead_in_box hP hq hB hJ support
    have hc := congrArg (fun z : W => z.val.coeff (MonomialOrder.degLex.degree q.val)) hz
    change (filterSupport (fun m => m∈C) q.val).coeff _ = 0 at hc
    rw [coeff_filterSupport,if_pos member] at hc
    exact (MonomialOrder.degLex.coeff_degree_ne_zero_iff.mpr hq) hc
  have independent : LinearIndependent Geom (fun i => (⟨Q i,memV i⟩ : V)) :=
    LinearIndependent.of_comp V.subtype hQli
  have projected := (project.linearIndependent_iff_of_injOn
    (LinearMap.ker_eq_bot.mp ker).injOn).mpr independent
  letI : Module.Finite Geom W := restrictSupport_finite C.finite_toSet
  have dim : r ≤ Module.finrank Geom W := by simpa using projected.fintype_card_le_finrank
  rw [finrank_restrictSupport_finset] at dim
  let i : Fin r := ⟨0, Nat.pos_of_ne_zero h0⟩
  have capB : (e i).totalDegree ≤ 4024 := by
    rw [← weightedTotalDegree_one]
    exact Finset.sup_le fun a ha => (hs i a ha).1
  have capJ : weightedTotalDegree oldWeight (e i) ≤ 1679 :=
    Finset.sup_le fun a ha => (hs i a ha).2.1
  rw [hQ i, totalDegree_mul_of_isDomain hP (hQne i),hB] at capB
  rw [hQ i,weightedTotalDegree_mul _ _ _ hP (hQne i),hJ] at capJ
  simpa [remaining, show b≤4024 by omega,show j≤1679 by omega,C,ambCount] using dim

end
end Height2307Cofactor
