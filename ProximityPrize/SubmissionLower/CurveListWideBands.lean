import ProximityPrize.SubmissionLower.CurveListFiberBlock
import ProximityPrize.SubmissionLower.CurveListPairResultant
import ProximityPrize.SubmissionLower.CurveListTripleInterpolation

set_option maxRecDepth 8000
set_option maxHeartbeats 3000000

namespace CurveListWideBands
open CJ0 CJ0_3 MvPolynomial PolynomialDifferential CurveListJointWeight CurveListTripleSupport
open scoped Polynomial BigOperators
open private jetView jet_mul from ProximityPrize.SubmissionLower.CurveListPairInterpolation
open private lead lead_degree lead_mul jetView_ne_zero from ProximityPrize.SubmissionLower.CurveListTripleInterpolation
open private exponent exponent_degree from ProximityPrize.SubmissionLower.CurveListTripleSupport
open private eliminate eliminate_ne_zero eliminate_root eliminate_weight
  from ProximityPrize.SubmissionLower.CurveListPairResultant
open private input_total input_index output_index from ProximityPrize.SubmissionLower.RungSplit

noncomputable section

abbrev residualShape (s : Source) : Source := ⟨1,2*s.C*s.B,2*s.C*s.J,1,∅⟩

private theorem cover {A : ℕ} {w : Node → K} {s : Source} (hC : 0 < s.C)
    {P Q D U W : Equation} (hp : OrderTwo s P) (hq : OrderTwo s Q)
    (hpu : P = D*U) (hqw : Q = D*W) (hrel : IsRelPrime U W)
    (hroots : ∀ f ∈ close A w, differentialSpecialization Q f = 0) :
    ∃ F : DifferentialPolynomial K 1, OrderOne (residualShape s) F ∧
      ∀ f ∈ close A w, differentialSpecialization P f = 0 →
        differentialSpecialization D f = 0 ∨ differentialSpecialization F f = 0 := by
  have hu := orderTwo_of_dvd hp ⟨D,by rw [hpu,mul_comm]⟩
  have hw := orderTwo_of_dvd hq ⟨D,by rw [hqw,mul_comm]⟩
  have hb := eliminate_weight 1 s.B s.C jetDegreeWeight
    (by rw [input_total]; exact hu.2.1) (by rw [input_total]; exact hw.2.1) hu.2.2.2 hw.2.2.2 hC
  have hj := eliminate_weight 2 s.J s.C indexWeight
    (by rw [input_index]; exact hu.2.2.1) (by rw [input_index]; exact hw.2.2.1) hu.2.2.2 hw.2.2.2 hC
  rw [output_index,weightedTotalDegree_piSingle] at hj
  refine ⟨eliminate U W,⟨eliminate_ne_zero hu.1 hrel,hb.trans (le_max_left ..),hj.trans (le_max_left ..)⟩,?_⟩
  intro f hf hpf
  let ψ := (differentialSpecializationHom (d := 2) f).toRingHom
  have he : ψ (D*U) = 0 := by rw [← hpu]; exact hpf
  have hqf : ψ (D*W) = 0 := by rw [← hqw]; exact hroots f hf
  rw [map_mul] at he hqf
  by_cases hz : ψ D = 0
  · exact Or.inl hz
  · exact Or.inr (eliminate_root f ((mul_eq_zero.mp he).resolve_left hz) ((mul_eq_zero.mp hqf).resolve_left hz))

theorem lead_index {Q : Equation} (hq : Q ≠ 0) :
    lead Q 1 + 2*lead Q 2 ≤ Q.weightedTotalDegree indexWeight := by
  have he := le_weightedTotalDegree (Fin.val : Fin 3 → ℕ)
    (MonomialOrder.degLex.degree_mem_support (jetView_ne_zero hq))
  change (lead Q).weight Fin.val ≤ _ at he
  rw [weightedTotalDegree_optionEquivRight] at he
  change (lead Q).weight Fin.val ≤ Q.weightedTotalDegree indexWeight at he
  simpa [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,Nat.mul_comm] using he

abbrev IndexMark (s : Source) (low J : ℕ) :=
  Fin (s.B+1-low) × ((c : Fin ((s.J-J)/2+1)) × Fin (s.J-J-2*c.val+1))

def indexCharge (A : ℕ) {s : Source} {low J : ℕ} (j : IndexMark s low J) : ℕ :=
  s.m*A-N*(low+j.1.val)+s.J

def indexTarget {s : Source} {low J : ℕ} (m : JetExponent) (j : IndexMark s low J) : JetExponent :=
  let b := m 1+j.2.2.val
  let c := m 2+j.2.1.val
  Finsupp.equivFunOnFinite.symm ![low+j.1.val-(b+c),b,c]

theorem index_width {A : ℕ} {s : Source} {low J : ℕ} (hs : ShapeOK s)
    (m : JetExponent) (i : ColumnIndex A s) (j : IndexMark s low J)
    (he : exponent i = indexTarget m j) : width A s i.1.val ≤ indexCharge A j := by
  have hq : low+j.1.val ≤ i.1.val.q := by
    rw [← exponent_degree,he,Finsupp.degree_eq_sum]
    simp [indexTarget,Fin.sum_univ_succ]
    omega
  exact Nat.add_le_add (Nat.sub_le_sub_left (Nat.mul_le_mul_left N hq) _)
    (hs.support _ i.1.property).2.1

/-- Remove one index/total-degree corner; the auxiliary index may exceed the
    primary index by any amount. The quotient shifts form a triangular grid. -/
theorem refine_index {A R V low J stop : ℕ} {s : Source} (hs : ShapeOK s)
    (hf : ∀ j ∈ s.E, j.b+3*j.c ≤ V) (hw : s.m ≤ s.m*A-N*s.B)
    (hC : 0 < s.C) (hr : prefixRank s (s.B+1) ≤ R) (hJ : J ≤ s.J)
    (hroom : n*R + ∑ j : IndexMark s low J, indexCharge A j < Fintype.card (ColumnIndex A s))
    (w : Node → K) {P : Equation} (hP : OrderTwo {s with J := J} P) (hdeg : jetTotalDegree P ≤ stop) :
    ∃ (D : Equation) (G : DifferentialPolynomial K 1), OrderTwo {s with J := J} D ∧ jetTotalDegree D ≤ stop ∧
      (jetTotalDegree D < low ∨ D.weightedTotalDegree indexWeight < J) ∧ D ∣ P ∧ OrderOne (residualShape s) G ∧
      ∀ f ∈ close A w, differentialSpecialization P f = 0 →
        differentialSpecialization D f = 0 ∨ differentialSpecialization G f = 0 := by
  classical
  obtain ⟨Q,hQ,_,hroot,havoid⟩ := CurveListFiberBlock.avoid hs hf hw hr
    (indexTarget (lead P)) (indexCharge A) (index_width hs _) hroom w
  letI := UniqueFactorizationMonoid.toGCDMonoid Equation
  let D := gcd P Q
  obtain ⟨U,W,hPU,hQW,hUW⟩ := extract_gcd P Q
  change P = D*U at hPU
  change Q = D*W at hQW
  have hD : D ≠ 0 := by intro hz; exact hP.1 (by rw [hPU,hz,zero_mul])
  have hU : U ≠ 0 := by intro hz; exact hP.1 (by rw [hPU,hz,mul_zero])
  have hW : W ≠ 0 := by intro hz; exact hQ.1 (by rw [hQW,hz,mul_zero])
  have hineq := (congrArg jetTotalDegree hPU).trans (jet_mul hD hU)
  have hcut : jetTotalDegree D < low ∨ D.weightedTotalDegree indexWeight < J := by
    by_contra! hbig
    have hiP := (congrArg (weightedTotalDegree indexWeight) hPU).trans
      (weightedTotalDegree_mul indexWeight D U hD hU)
    have hiQ := (congrArg (weightedTotalDegree indexWeight) hQW).trans
      (weightedTotalDegree_mul indexWeight D W hD hW)
    have hi₁ : P.weightedTotalDegree indexWeight ≤ J := hP.2.2.1
    have hi₂ : Q.weightedTotalDegree indexWeight ≤ s.J := hQ.2.2.1
    have hu := lead_index hU
    have hw := lead_index hW
    have hu₁ : lead U 1 = 0 := by omega
    have hu₂ : lead U 2 = 0 := by omega
    have hc : lead W 2 < (s.J-J)/2+1 := by omega
    have hb : lead W 1 < s.J-J-2*lead W 2+1 := by omega
    have hp₁ : lead P 1 = lead D 1 := by rw [hPU,lead_mul hD hU,Finsupp.add_apply,hu₁,add_zero]
    have hp₂ : lead P 2 = lead D 2 := by rw [hPU,lead_mul hD hU,Finsupp.add_apply,hu₂,add_zero]
    have hq₁ : lead Q 1 = lead P 1+lead W 1 := by rw [hQW,lead_mul hD hW,Finsupp.add_apply,hp₁]
    have hq₂ : lead Q 2 = lead P 2+lead W 2 := by rw [hQW,lead_mul hD hW,Finsupp.add_apply,hp₂]
    have hqdeg := (congrArg jetTotalDegree hQW).trans (jet_mul hD hW)
    have hqmax : jetTotalDegree Q ≤ s.B := hQ.2.1
    have hj : (lead Q).degree-low < s.B+1-low := by rw [lead_degree]; omega
    let j : IndexMark s low J := (⟨(lead Q).degree-low,hj⟩,⟨⟨lead W 2,hc⟩,⟨lead W 1,hb⟩⟩)
    have he : lead Q = indexTarget (lead P) j := by
      have hdegQ : (lead Q).degree = lead Q 0 + lead Q 1 + lead Q 2 := by
        simp [Finsupp.degree_eq_sum,Fin.sum_univ_succ,Nat.add_assoc]
      have hdQ : low ≤ (lead Q).degree := by rw [lead_degree]; omega
      ext i
      fin_cases i <;> simp [indexTarget,j,hq₁,hq₂] <;> omega
    exact (havoid _ (MonomialOrder.degLex.degree_mem_support (jetView_ne_zero hQ.1))) ⟨j,he⟩
  have hp₀ : OrderTwo s P := ⟨hP.1,hP.2.1,hP.2.2.1.trans hJ,hP.2.2.2⟩
  obtain ⟨G,hG,hcov⟩ := cover hC hp₀ hQ hPU hQW (gcd_isUnit_iff_isRelPrime.mp hUW) hroot
  exact ⟨D,G,orderTwo_of_dvd hP ⟨U,hPU⟩,by omega,hcut,⟨U,hPU⟩,hG,hcov⟩

abbrev DegreeMark (d : ℕ) := {v : Fin 3 → Fin (d+1) // ∑ i, (v i).val ≤ d}

private def shift {d : ℕ} (v : DegreeMark d) : JetExponent :=
  Finsupp.equivFunOnFinite.symm fun i => (v.val i).val

theorem shift_deg {d : ℕ} (v : DegreeMark d) : (shift v).degree = ∑ i, (v.val i).val := by
  simp [shift,Finsupp.degree_eq_sum]

theorem shift_surj {d : ℕ} {e : JetExponent} (h : e.degree ≤ d) :
    ∃ v : DegreeMark d, e = shift v := by
  rw [Finsupp.degree_eq_sum] at h
  have hb (i : Fin 3) : e i < d+1 := Nat.lt_succ_of_le
    ((Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans h)
  let v : Fin 3 → Fin (d+1) := fun i => ⟨e i,hb i⟩
  refine ⟨⟨v,h⟩,?_⟩
  ext i
  simp [shift,v]

def degreeCharge (A : ℕ) (s : Source) (stop : ℕ) (v : DegreeMark (s.B-(stop+1))) : ℕ :=
  s.m*A-N*(stop+1+∑ i, (v.val i).val)+s.J

theorem degree_width {A stop : ℕ} {s : Source} (hs : ShapeOK s)
    (m : JetExponent) (hm : stop+1 ≤ m.degree) (i : ColumnIndex A s)
    (v : DegreeMark (s.B-(stop+1))) (he : exponent i = m+shift v) :
    width A s i.1.val ≤ degreeCharge A s stop v := by
  have hq := congrArg Finsupp.degree he
  rw [exponent_degree,map_add,shift_deg] at hq
  unfold width degreeCharge
  rw [hq]
  exact Nat.add_le_add (Nat.sub_le_sub_left (Nat.mul_le_mul_left N (Nat.add_le_add_right hm _)) _)
    (hs.support _ i.1.property).2.1

theorem drop_degree {A stop R V : ℕ} {s : Source} (hs : ShapeOK s)
    (hf : ∀ j ∈ s.E, j.b+3*j.c ≤ V) (hw : s.m ≤ s.m*A-N*s.B) (hC : 0 < s.C)
    (hr : prefixRank s (s.B+1) ≤ R)
    (hroom : n*R + ∑ v, degreeCharge A s stop v < Fintype.card (ColumnIndex A s))
    (w : Node → K) {P : Equation} (hP : OrderTwo s P) (hb : stop+1 ≤ jetTotalDegree P) :
    ∃ (D : Equation) (G : DifferentialPolynomial K 1), OrderTwo s D ∧ D ∣ P ∧
      jetTotalDegree D < jetTotalDegree P ∧ OrderOne (residualShape s) G ∧
      ∀ f ∈ close A w, differentialSpecialization P f = 0 →
        differentialSpecialization D f = 0 ∨ differentialSpecialization G f = 0 := by
  classical
  have hm : stop+1 ≤ (lead P).degree := (lead_degree P).symm ▸ hb
  obtain ⟨Q,hQ,_,hroots,havoid⟩ := CurveListFiberBlock.avoid hs hf hw hr
    (fun v => lead P+shift v) (degreeCharge A s stop) (degree_width hs _ hm) hroom w
  letI := UniqueFactorizationMonoid.toGCDMonoid Equation
  let D := gcd P Q
  obtain ⟨U,W,hPU,hQW,hUW⟩ := extract_gcd P Q
  change P = D*U at hPU
  change Q = D*W at hQW
  have hD : D ≠ 0 := by intro hz; exact hP.1 (by rw [hPU,hz,zero_mul])
  have hU : U ≠ 0 := by intro hz; exact hP.1 (by rw [hPU,hz,mul_zero])
  have hW : W ≠ 0 := by intro hz; exact hQ.1 (by rw [hQW,hz,mul_zero])
  have hdeg : jetTotalDegree D < jetTotalDegree P := by
    by_contra! hx
    have hsum₁ := (congrArg jetTotalDegree hPU).trans (jet_mul hD hU)
    have hsum₂ := (congrArg jetTotalDegree hQW).trans (jet_mul hD hW)
    have ht : jetTotalDegree Q ≤ s.B := hQ.2.1
    have hU0 : jetTotalDegree U = 0 := by omega
    have hW0 : jetTotalDegree W ≤ s.B-(stop+1) := by omega
    have hUlead := (Finsupp.degree_eq_zero_iff (lead U)).mp ((lead_degree U).trans hU0)
    have hlead : lead P = lead D := by rw [hPU,lead_mul hD hU,hUlead,add_zero]
    obtain ⟨v,hv⟩ := shift_surj ((lead_degree W).trans_le hW0)
    have hQlead : lead Q = lead P+shift v := by rw [hQW,lead_mul hD hW,← hlead,hv]
    exact (havoid _ (MonomialOrder.degLex.degree_mem_support (jetView_ne_zero hQ.1))) ⟨v,hQlead⟩
  obtain ⟨G,hG,hcov⟩ := cover hC hP hQ hPU hQW (gcd_isUnit_iff_isRelPrime.mp hUW) hroots
  exact ⟨D,G,orderTwo_of_dvd hP ⟨U,hPU⟩,⟨U,hPU⟩,hdeg,hG,hcov⟩

/-- Iterate degree drops; the common equation still divides the first one. -/
theorem refine_degree {A stop R V : ℕ} {s : Source} (hs : ShapeOK s)
    (hf : ∀ j ∈ s.E, j.b+3*j.c ≤ V) (hw : s.m ≤ s.m*A-N*s.B) (hC : 0 < s.C)
    (hr : prefixRank s (s.B+1) ≤ R)
    (hroom : n*R + ∑ v, degreeCharge A s stop v < Fintype.card (ColumnIndex A s))
    (w : Node → K) (d : ℕ) {P : Equation} (hP : OrderTwo s P) (hb : jetTotalDegree P ≤ stop+d) :
    ∃ (D : Equation) (G : List (DifferentialPolynomial K 1)), OrderTwo s D ∧ D ∣ P ∧
      jetTotalDegree D ≤ stop ∧ G.length ≤ d ∧ (∀ g ∈ G, OrderOne (residualShape s) g) ∧
      ∀ f ∈ close A w, differentialSpecialization P f = 0 →
        differentialSpecialization D f = 0 ∨ ∃ g ∈ G, differentialSpecialization g f = 0 := by
  induction d generalizing P with
  | zero => exact ⟨P,[],hP,dvd_rfl,hb,by simp,by simp,fun _ _ h => Or.inl h⟩
  | succ d ih =>
    by_cases hsmall : jetTotalDegree P ≤ stop
    · exact ⟨P,[],hP,dvd_rfl,hsmall,by simp,by simp,fun _ _ h => Or.inl h⟩
    obtain ⟨E,H,hE,hEP,he,hH,hcover⟩ := drop_degree hs hf hw hC hr hroom w hP (by omega)
    obtain ⟨D,G,hD,hDE,hd,hG,ha,hcov⟩ := ih hE (by omega)
    refine ⟨D,H::G,hD,hDE.trans hEP,hd,Nat.succ_le_succ hG,?_,?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hH
      · exact ha g hg
    · intro f hf hp
      rcases hcover f hf hp with he' | hh
      · rcases hcov f hf he' with hd' | ⟨g,hg,hz⟩
        · exact Or.inl hd'
        · exact Or.inr ⟨g,List.mem_cons_of_mem _ hg,hz⟩
      · exact Or.inr ⟨H,by simp,hh⟩

end
end CurveListWideBands
