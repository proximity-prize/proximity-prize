import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Fat6966Bank24000
import ProximityPrize.SubmissionLower.Fat6966Factors

section Merged6967_Final50Order
set_option Elab.async false



set_option Elab.async false

-- merged module PrimaryTaperActive
section Merged_PrimaryTaperActive

set_option Elab.async false

namespace PrimaryTaperActive

open K1_13 (Row)
open K1_13_2_2 (gradeWeight)
open MvPolynomial
open TaperColumns (jetExponents)
open TaperBudget (cap)

def Fits (P : Row 4) (n : ℕ) : Prop :=
  ∀ m ∈ P.support, m 0 + 2*m 1 + 2*m 2 + 2*m 3 ≤ n

theorem of_jets {P : Row 4} (h : ∀ m ∈ P.support, m ∈ jetExponents) :
    Fits P 5163 := by
  intro m hm
  have hz := h m hm
  let q := m.weight gradeWeight
  change q ≤ 4012 ∧ m.weight K1_13_2_2.oldWeight ≤ 1650 ∧ m 1 + m 2 + m 3 ≤ cap q at hz
  have hq : q = m 0 + m 1 + m 2 + m 3 := by
    simp [q, Finsupp.weight_eq_sum, Fin.sum_univ_four, gradeWeight, smul_eq_mul]
  obtain ⟨hqmax, _, hd⟩ := hz
  unfold cap at hd
  split at hd <;> omega





#print axioms of_jets
end PrimaryTaperActive

end Merged_PrimaryTaperActive

-- merged module Final50Order
section Merged_Final50Order
set_option Elab.async false
namespace Final50Order
noncomputable section
open K1_13 (Geom Row shape InBox Contact)
open P3 (I K)
abbrev TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) := Final50Price.TrueWeightLE P D
abbrev physicalDegree := Final50Price.physicalDegree
abbrev agreement := Final50Price.agreement
abbrev primaryBox := Final50Price.primaryBox
abbrev primaryCutoff := Final50Price.primaryCutoff
abbrev sourceRank := Wide50EulerPrimary.sourceRank agreement physicalDegree
abbrev layerWidth := Final50Price.layerWidth
abbrev layerNeed := Final50Price.layerNeed
abbrev Messages := Final50Price.Messages
abbrev ProperCut := Final50Price.ProperCut
abbrev LayerBudget := @Final50Price.LayerBudget
theorem sourceRank_eq : sourceRank = 993533597967758343 := by decide
theorem certified_layers : sourceRank / layerWidth + 1 = 21410054907182 := by decide
def PrimaryRank (w : I → K) : Prop :=
  ∃ e : Fin sourceRank → Row 4, LinearIndependent Geom e ∧
    ∀ i, InBox (shape (e i)) primaryBox ∧ TrueWeightLE (e i) primaryCutoff ∧
      PrimaryTaper.JetsBounded (e i) ∧ Contact w (e i)
end
end Final50Order
section
namespace Final50OrderProof
noncomputable section
open P3 (I K)
open Final50Order (TrueWeightLE primaryBox primaryCutoff layerWidth)
open K1_13 (Row InBox shape Contact)
def requiredOrder (T : ℕ) : ℕ :=
  (primaryCutoff - T) / layerWidth + 1
def BankRow (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) primaryBox ∧ TrueWeightLE P T ∧
    PrimaryTaper.JetsBounded P ∧ Contact w P
end
end Final50OrderProof
end
section
namespace Final50OrderProof
noncomputable section
open Polynomial
open P3 (I K node)
open Final50Order (agreement)
open Final50Order (Messages ProperCut TrueWeightLE physicalDegree primaryBox
  PrimaryRank primaryCutoff layerWidth layerNeed sourceRank)
open K1_13 (Geom embed extend Row shape InBox OrderAt indexDegree)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open scoped BigOperators
open P0_9_3 (exists_fresh specialization_bounds sum_by_layer)
def c1 : Prop :=
  ∀ (w : I → K) (T : ℕ) (P : Row 4), T ≤ primaryCutoff → BankRow w T P →
    ∀ S : (Polynomial Geom), S.natDegree ≤ physicalDegree →
      (∃ H : Finset I, agreement ≤ H.card ∧
        ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) →
      OrderAt P S (requiredOrder T)
def c2 : Prop :=
  ∀ (f P : Row 4) (Γ : Finset K) (s : K → (Polynomial K)) (d a : ℕ),
    Irreducible f → 0 < (shape f).t → (shape f).t < K1.p →
    InBox (shape P) primaryBox → TrueWeightLE P primaryCutoff →
    Final50Price.ActiveFits P 5164 →
    (∀ γ ∈ Γ, OrderAt P (extend (s γ)) d) →
    a < d → f ^ a ∣ P → (¬ f ^ (a + 1) ∣ P) →
    ProperCut f Γ s (d - a)
def c3 : Prop :=
  ∀ (w : I → K) (x : Geom), PrimaryRank w →
    (∀ i : I, x ≠ embed (node i)) →
    ∃ r : ℕ → ℕ, sourceRank ≤ ∑ T ∈ Finset.range (primaryCutoff + 1), r T ∧
      ∀ T ≤ primaryCutoff, ∃ e : Fin (r T) → Row 4,
        (∀ i, BankRow w T (e i)) ∧
        LinearIndependent Geom (fun i => symbolAt x (e i))
private theorem exists_availability (hc : c1) (hd : c2)
    {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} (hm : Messages w Γ s)
    {f : Row 4} (hirr : Irreducible f) (hpos : 0 < (shape f).t) (htop : (shape f).t < K1.p) :
    ∃ l : ℕ, (∀ T ≤ primaryCutoff, ∀ P, BankRow w T P → f ^ (requiredOrder T - l) ∣ P) ∧
      (0 < l → ProperCut f Γ s l) := by
  classical
  let admissible (l : ℕ) : Prop :=
    ∀ T ≤ primaryCutoff, ∀ P, BankRow w T P → f ^ (requiredOrder T - l) ∣ P
  have hex : ∃ l, admissible l := by
    refine ⟨primaryCutoff / layerWidth + 1, fun T _ P _ => ?_⟩
    have hle : requiredOrder T ≤ primaryCutoff / layerWidth + 1 :=
      Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le _ _)) _
    rw [Nat.sub_eq_zero_of_le hle, pow_zero]
    exact one_dvd P
  let l := Nat.find hex
  have hl : admissible l := Nat.find_spec hex
  refine ⟨l, hl, fun hlpos => ?_⟩
  have hbad : ¬ admissible (l - 1) := Nat.find_min hex (by omega)
  dsimp only [admissible] at hbad
  push Not at hbad
  obtain ⟨T, hT, P, hP, hnext⟩ := hbad
  have hle : l ≤ requiredOrder T := by
    by_contra! hlt
    have heq : requiredOrder T - (l - 1) = 0 := by omega
    exact hnext (by rw [heq, pow_zero]; exact one_dvd P)
  have hstep : requiredOrder T - (l - 1) = (requiredOrder T - l) + 1 := by omega
  have horder : ∀ γ ∈ Γ, OrderAt P (extend (s γ)) (requiredOrder T) := by
    intro γ hγ
    apply hc w T P hT hP
    · simpa only [extend, natDegree_map_eq_of_injective (RingHom.injective embed)] using
        hm.degree γ hγ
    · obtain ⟨H, hcard, hH⟩ := hm.hits γ hγ
      refine ⟨H, hcard, fun i hi => ?_⟩
      rw [extend, eval_map, eval₂_at_apply, hH i hi]
  have hweight : TrueWeightLE P primaryCutoff := fun m hm => (hP.2.1 m hm).trans hT
  have hactive : Final50Price.ActiveFits P 5164 :=
    fun m hm => (PrimaryTaperActive.of_jets hP.2.2.1 m hm).trans (by decide)
  have hcut := hd f P Γ s (requiredOrder T) (requiredOrder T - l) hirr hpos htop hP.1
    hweight hactive horder (by omega) (hl T hT P hP) (by rwa [hstep] at hnext)
  have heq : requiredOrder T - (requiredOrder T - l) = l := by omega
  rwa [heq] at hcut
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3)
    {w Γ s n} {f : Fin n → Row 4} (hm : Messages w Γ s) (hr : PrimaryRank w)
    (hirr : ∀ i, Irreducible (f i)) (hpos : ∀ i, 0 < (shape (f i)).t)
    (htop : ∀ i, (shape (f i)).t < K1.p)
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) :
    ∃ l : Fin n → ℕ, Final50Order.LayerBudget (fun i => shape (f i)) l ∧
      ∀ i, 0 < l i → ProperCut (f i) Γ s (l i) := by
  classical
  choose l hl hcut using fun i => exists_availability h1 h2 hm (hirr i) (hpos i) (htop i)
  obtain ⟨x, hx, hsup⟩ := exists_fresh f
  obtain ⟨r, hrank, hfamilies⟩ := h3 w x hr hx
  have hnz : ∀ i, symbolAt x (f i) ≠ 0 := by
    intro i hz
    have hzero := hsup i
    rw [hz, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at hzero
    exact (hirr i).ne_zero hzero
  let cost (k : ℕ) :=
    Final50Price.remaining (∑ i, (k + 1 - l i) * (shape (f i)).b)
      (∑ i, (k + 1 - l i) * (shape (f i)).j)
  have hcost : ∀ T ≤ primaryCutoff, r T ≤ cost ((primaryCutoff - T) / layerWidth) := by
    intro T hT
    obtain ⟨e, he, hei⟩ := hfamilies T hT
    let a (i : Fin n) := requiredOrder T - l i
    have hdiv (i : Fin (r T)) : (∏ j, f j ^ a j) ∣ e i := by
      apply Fintype.prod_dvd_of_isRelPrime
      · intro j k hjk
        have hj := hirr j
        have hk := hirr k
        exact (hj.isRelPrime_iff_not_dvd.mpr
          (fun h => hdiff j k hjk (hj.associated_of_dvd hk h))).pow
      · intro j
        exact hl j T hT (e i) (he i)
    have hbound := cofactor_rank n (fun i => symbolAt x (f i)) a hnz (r T)
      (fun i => symbolAt x (e i)) hei (fun i => by
        obtain ⟨hb, hj⟩ := specialization_bounds x (e i) (he i).1
        exact ⟨hb, hj, by simpa only [map_prod, map_pow] using map_dvd (symbolAt x) (hdiv i)⟩)
    have hb (i : Fin n) : (symbolAt x (f i)).totalDegree = (shape (f i)).b := by
      change (symbolAt x (f i)).totalDegree = (f i).totalDegree
      unfold MvPolynomial.totalDegree
      rw [hsup]
    have hj (i : Fin n) : symbolIndex (symbolAt x (f i)) = (shape (f i)).j := by
      change symbolIndex (symbolAt x (f i)) = indexDegree (f i)
      unfold symbolIndex indexDegree
      rw [hsup]
    have hs : r T ≤ Final50Price.symbolCount :=
      PrimaryTaper.symbol_rank x e (fun i => (he i).2.2.1) hei
    dsimp only [cost, Final50Price.remaining]
    apply le_min hs
    simpa only [a, requiredOrder, hb, hj] using hbound
  have hsum : sourceRank ≤ layerWidth * ∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k :=
    hrank.trans ((Finset.sum_le_sum fun T hT =>
      hcost T (Nat.le_of_lt_succ (Finset.mem_range.mp hT))).trans (sum_by_layer primaryCutoff layerWidth (by decide) cost))
  refine ⟨l, ?_, hcut⟩
  change layerNeed ≤ ∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k
  have hceil : layerWidth * (layerNeed - 1) < sourceRank := by decide
  by_contra! hsmall
  have hpred : (∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k) ≤
      layerNeed - 1 := by omega
  exact (not_le_of_gt hceil) (hsum.trans (Nat.mul_le_mul_left layerWidth hpred))
end
end Final50OrderProof
end
section
set_option maxRecDepth 12000
namespace Final50OrderProof_1
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P3 (I K node)
open Final50Order (agreement)
open Final50Order (TrueWeightLE physicalDegree primaryCutoff layerWidth)
open Final50OrderProof (BankRow requiredOrder)
open K1_13 (Geom embed Row jet Contact)
open K1_13_3_1 (line)
open scoped BigOperators
open K1_13_3_1 (eval_line line_contacts_zero)
open K1_13_3_1 (order_of_locator_lines)
private def Bounded (Q : Polynomial (Polynomial Geom)) (b : ℕ) : Prop :=
  ∀ j, (Q.coeff j).natDegree ≤ b + layerWidth * j
private theorem bounded_mul {F G : Polynomial (Polynomial Geom)} {a b : ℕ}
    (hF : Bounded F a) (hG : Bounded G b) : Bounded (F * G) (a + b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum, Nat.mul_add]
  omega
private theorem bounded_C (f : (Polynomial Geom)) {a : ℕ} (hf : f.natDegree ≤ a) :
    Bounded (Polynomial.C f) a := by
  intro j
  by_cases h : j = 0
  · simpa [h] using hf
  · simp [Polynomial.coeff_C, h]
private theorem bounded_prod {ι : Type*} (A : Finset ι)
    (f : ι → Polynomial (Polynomial Geom)) (b : ι → ℕ) (hf : ∀ i ∈ A, Bounded (f i) (b i)) :
    Bounded (∏ i ∈ A, f i) (∑ i ∈ A, b i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using bounded_C (1 : (Polynomial Geom)) (a := 0) (by simp)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact bounded_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
private theorem bounded_pow {f : Polynomial (Polynomial Geom)} {b : ℕ} (hf : Bounded f b) (n : ℕ) :
    Bounded (f ^ n) (b * n) := by
  induction n with
  | zero => simpa using bounded_C (1 : (Polynomial Geom)) (a := 0) (by simp)
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact bounded_mul ih hf
private theorem line_degree (P : Row 4) (S U : (Polynomial Geom)) (T : ℕ)
    (hP : TrueWeightLE P T) (hS : S.natDegree ≤ physicalDegree)
    (hU : U.natDegree ≤ agreement + 3) (j : ℕ) :
    ((line P S U).coeff j).natDegree ≤ T + layerWidth * j := by
  let b (i : Fin 4) : ℕ := physicalDegree - i.val
  let F (i : Fin 4) : Polynomial (Polynomial Geom) :=
    Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 4) : Bounded (F i) (b i) := by
    intro k
    have hs : (jet S i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le S i.val).trans (Nat.sub_le_sub_right hS _)
    have hu : (jet U i).natDegree ≤ b i + layerWidth := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi : i.val ≤ physicalDegree := (Nat.le_of_lt_succ i.isLt).trans (by decide)
      have hwidth : agreement + 3 = layerWidth + physicalDegree := by decide
      change agreement + 3 - i.val ≤ (physicalDegree - i.val) + layerWidth
      rw [hwidth, Nat.add_sub_assoc hi, Nat.add_comm layerWidth]
    change ((Polynomial.C (jet S i) + Polynomial.C (jet U i) *
      Polynomial.X).coeff k).natDegree ≤ b i + layerWidth * k
    rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
    by_cases h0 : k = 0
    · simpa [h0] using hs
    · by_cases h1 : k = 1
      · simpa [h1] using hu
      · simp [h0, h1]
  unfold line
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  have hterm := bounded_mul (bounded_C (P.coeff m) le_rfl)
    (bounded_prod m.support (fun i => F i ^ m i) (fun i => b i * m i)
      (fun i _ => bounded_pow (hF i) (m i))) j
  exact hterm.trans (Nat.add_le_add_right (hP m hm) _)
private theorem line_coeff_zero (w : I → K) (T : ℕ) (P : Row 4) (S : (Polynomial Geom))
    (hw : TrueWeightLE P T) (hc : Contact w P) (hS : S.natDegree ≤ physicalDegree)
    (A : Finset I) (hA : A.card = agreement)
    (hhit : ∀ i ∈ A, S.eval (embed (node i)) = embed (w i))
    (V : (Polynomial Geom)) (hV : V.natDegree ≤ 3) (j : ℕ)
    (hj : T + layerWidth * j ≤ primaryCutoff) :
    (line P S (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ agreement + 3 := by
    exact natDegree_mul_le.trans (by rw [locator_natDegree, hA]; exact Nat.add_le_add_left hV _)
  let Q := line P S U
  have hcontact (i : I) (hi : i ∈ A) (c : Geom) :
      (Polynomial.X - C (x i)) ^ 3000 ∣ Q.eval (C c) := by
    rw [show Q = line P S U from rfl, eval_line]
    apply hc
    have hL : L.eval (x i) = 0 := locator_eval_zero x A i hi
    have hU0 : U.eval (x i) = 0 := by simp [U, hL]
    simpa [x, eval_smul, hU0] using hhit i hi
  have hx : Function.Injective x :=
    (RingHom.injective embed).comp IRSProfile.domain.injective
  have hb := (line_degree P S U T hw hS hU j).trans hj
  have hdegree : (Q.coeff j).natDegree < 3000 * A.card := by
    rw [hA]
    exact hb.trans_lt (Nat.sub_lt (Nat.mul_pos (by decide) (by decide)) (by decide))
  exact line_contacts_zero Q A x hx 3000 hcontact j hdegree
theorem order_of_contact (w : I → K) (P : Row 4) {T : ℕ} (hT : T ≤ primaryCutoff)
    (hw : TrueWeightLE P T) (hc : Contact w P) {S : (Polynomial Geom)} (hS : S.natDegree ≤ physicalDegree)
    {H : Finset I} (hH : agreement ≤ H.card)
    (hits : ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) :
    K1_13.OrderAt P S (requiredOrder T) := by
  obtain ⟨A, hAH, hA⟩ := Finset.exists_subset_card_eq hH
  let x (i : I) := embed (node i)
  apply order_of_locator_lines P S (locator x A) (locator_monic x A).ne_zero
  intro V hV j hj
  apply line_coeff_zero w T P S hw hc hS A hA (fun i hi => hits i (hAH hi)) V hV j
  have hj' : j ≤ (primaryCutoff - T) / layerWidth := Nat.lt_succ_iff.mp hj
  have hq := Nat.div_mul_le_self (primaryCutoff - T) layerWidth
  rw [Nat.mul_comm _ layerWidth] at hq
  calc
    T + layerWidth * j ≤ T + layerWidth * ((primaryCutoff - T) / layerWidth) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left layerWidth hj') T
    _ ≤ T + (primaryCutoff - T) := Nat.add_le_add_left hq T
    _ = primaryCutoff := Nat.add_sub_of_le hT
theorem proof : Final50OrderProof.c1 := by
  intro w T P hT hP S hS hits
  obtain ⟨H, hH, hhits⟩ := hits
  exact order_of_contact w P hT hP.2.1 hP.2.2.2 hS hH hhits
end
end Final50OrderProof_1
end
section
namespace Final50OrderProof_2
noncomputable section
open Polynomial
open Final50Order (TrueWeightLE physicalDegree primaryBox primaryCutoff)
open K1_13 (Geom embed extend Row Shape shape InBox indexDegree)
open P0_9_3_2 (translateTop topHasse topHasse_coeff source_support sum_add_top total_add_top apply_add_top erase_top_add topHasse_order topHasse_zero exact_hasse_not_dvd)
private theorem topHasse_bounds (box : Shape) (T a : ℕ) (P : Row 4)
    (hb : InBox (shape P) box) (hw : TrueWeightLE P T) :
    InBox (shape (topHasse a P)) box ∧ TrueWeightLE (topHasse a P) T := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change (topHasse a P).totalDegree ≤ box.b
    apply Finset.sup_le
    intro m hm
    have hp := (MvPolynomial.le_totalDegree (source_support hm)).trans hb.1
    rw [total_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change indexDegree (topHasse a P) ≤ box.j
    apply Finset.sup_le
    intro m hm
    have hp := (Finset.le_sup (f := fun u : Fin 4 →₀ ℕ => u.sum (fun i k => i.val * k))
      (source_support hm)).trans hb.2.1
    rw [sum_add_top Fin.val] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change (topHasse a P).degreeOf 3 ≤ box.t
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have hp := (MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)).trans hb.2.2
    rw [apply_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · intro m hm
    have hp := hw _ (source_support hm)
    rw [sum_add_top (fun i => physicalDegree - i.val)] at hp
    rw [topHasse_coeff]
    have hc := Polynomial.natDegree_mul_le
      (p := (↑((m 3 + a).choose a) : (Polynomial Geom))) (q := P.coeff (m + Finsupp.single 3 a))
    rw [Polynomial.natDegree_natCast, zero_add] at hc
    exact (Nat.add_le_add_right hc _).trans ((Nat.add_le_add_left (Nat.le_add_right _ _) _).trans hp)
private theorem topHasse_one_not_dvd (f : Row 4) (hf : Irreducible f)
    (hpos : 0 < f.degreeOf 3) (hsmall : f.degreeOf 3 < K1.p) : ¬ f ∣ topHasse 1 f := by
  classical
  have hdeg : (topHasse 1 f).degreeOf 3 ≤ f.degreeOf 3 - 1 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have h := MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)
    rw [apply_add_top] at h
    omega
  have hnz : topHasse 1 f ≠ 0 := by
    have hsup : 0 < f.support.sup (fun m => m (3 : Fin 4)) := by
      rwa [← MvPolynomial.degreeOf_eq_sup]
    obtain ⟨u, hu, htop⟩ := (Finset.le_sup_iff hsup).mp (le_refl _)
    rw [← MvPolynomial.degreeOf_eq_sup] at htop
    have hupos : 0 < u 3 := hpos.trans_le htop
    have hult : u 3 < K1.p := (MvPolynomial.le_degreeOf_of_mem_support 3 hu).trans_lt hsmall
    let m := u.erase 3 + Finsupp.single 3 (u 3 - 1)
    have hsum : m + Finsupp.single 3 1 = u := by
      dsimp [m]
      rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel hupos, erase_top_add]
    have hm : m 3 + 1 = u 3 := by
      rw [← apply_add_top, hsum]
    have hc : (↑(u 3) : (Polynomial Geom)) ≠ 0 := by
      have : CharP Geom K1.p :=
        charP_of_injective_ringHom (RingHom.injective embed) K1.p
      intro hz
      have hz' : (↑(u 3) : Geom) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg (Polynomial.evalRingHom (0 : Geom)) hz
      exact (not_le_of_gt hult)
        (Nat.le_of_dvd hupos ((CharP.cast_eq_zero_iff Geom K1.p _).mp hz'))
    have hcoeff : (topHasse 1 f).coeff m ≠ 0 := by
      rw [topHasse_coeff, hm, hsum, Nat.choose_one_right]
      exact mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hu)
    intro hz
    exact hcoeff (by rw [hz]; rfl)
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro h
    exact hnz (by rw [hg, h, mul_zero])
  have h := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.ne_zero hg0
  rw [hg, h] at hdeg
  omega
theorem proof : Final50OrderProof.c2 := by
  intro f P Γ s d a hirr hpos htop hb hw ha hord _ hdiv hexact
  obtain ⟨hbox, hweight⟩ := topHasse_bounds primaryBox primaryCutoff a P hb hw
  have hp : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hproper : ¬ f ∣ topHasse a P :=
    exact_hasse_not_dvd translateTop topHasse_zero f P a hp
      (topHasse_one_not_dvd f hirr hpos htop) hdiv hexact
  have hactive : Final50Price.ActiveFits (topHasse a P) 5164 := by
    intro m hm
    have hh := ha _ (source_support hm)
    simp [Finsupp.add_apply] at hh
    omega
  exact ⟨topHasse a P, hproper, hbox, hweight, hactive, fun γ hγ =>
    topHasse_order a d P (extend (s γ)) (hord γ hγ)⟩
end
end Final50OrderProof_2
end
section
namespace Final50OrderProof_3
noncomputable section
open Polynomial
open P3 (I K node)
open Final50Order (TrueWeightLE physicalDegree primaryCutoff)
open Final50OrderProof (BankRow)
open K1_13 (Geom embed Row InBox shape indexDegree Contact atJet)
open K1_13_3 (Symbol symbolAt)
open P0_9_3 (jetEval jetEval_apply dvd_smul_poly coefficientArray symbolLinear linearFactor linearFactor_ne linearFactor_degree divide_specialization support_linear_mul)
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
private abbrev Exponent := Fin 4 →₀ ℕ
private def jetWeight (m : Exponent) : ℕ :=
  m.sum (fun i a => (physicalDegree - i.val) * a)
private theorem bankRow_iff {w : I → K} {T : ℕ} {P : Row 4} :
    BankRow w T P ↔
      (∀ m ∈ P.support, m.sum (fun _ a => a) ≤ 4012 ∧
        m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
        (P.coeff m).natDegree + jetWeight m ≤ T ∧ m ∈ TaperColumns.jetExponents) ∧ Contact w P := by
  simp only [BankRow, InBox, shape, indexDegree, MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_le_iff, Finset.sup_le_iff, TrueWeightLE, PrimaryTaper.JetsBounded]
  constructor
  · rintro ⟨⟨hb, hj, ht⟩, hT, hs, hc⟩
    exact ⟨fun m hm => ⟨hb m hm, hj m hm, ht m hm, hT m hm, hs m hm⟩, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2.1, fun m hm => (h m hm).2.2.1⟩,
      fun m hm => (h m hm).2.2.2.1, fun m hm => (h m hm).2.2.2.2, hc⟩
private def bank (w : I → K) (T : ℕ) : Submodule Geom (Row 4) where
  carrier := {P | BankRow w T P}
  zero_mem' := by
    apply bankRow_iff.mpr
    simp [Contact, atJet]
  add_mem' {P Q} hP hQ := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    obtain ⟨hQ, hq⟩ := bankRow_iff.mp hQ
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      have hor := Finset.mem_union.mp (MvPolynomial.support_add hm)
      have bounds :
          m.sum (fun _ a => a) ≤ 4012 ∧ m.sum (fun i a => i.val * a) ≤ 1650 ∧
            m 3 ≤ 550 ∧ jetWeight m ≤ T ∧ m ∈ TaperColumns.jetExponents := by
        rcases hor with h | h
        · obtain ⟨hb, hj, ht, hw, hjets⟩ := hP m h
          exact ⟨hb, hj, ht, by omega, hjets⟩
        · obtain ⟨hb, hj, ht, hw, hjets⟩ := hQ m h
          exact ⟨hb, hj, ht, by omega, hjets⟩
      obtain ⟨hb, hj, ht, hw, hjets⟩ := bounds
      refine ⟨hb, hj, ht, ?_, hjets⟩
      have hsum : ((P + Q).coeff m).natDegree ≤
          max (P.coeff m).natDegree (Q.coeff m).natDegree := by
        change ((P.coeff m) + (Q.coeff m)).natDegree ≤ _
        exact natDegree_add_le _ _
      have hdegree (R : Row 4) (hR : m ∈ R.support → (R.coeff m).natDegree + jetWeight m ≤ T) :
          (R.coeff m).natDegree ≤ T - jetWeight m := by
        by_cases h : m ∈ R.support
        · have := hR h
          omega
        · have hz : R.coeff m = 0 := by
            by_contra hnz
            exact h (MvPolynomial.mem_support_iff.mpr hnz)
          rw [hz, natDegree_zero]
          exact Nat.zero_le _
      have hp' := hdegree P (fun h => (hP m h).2.2.2.1)
      have hq' := hdegree Q (fun h => (hQ m h).2.2.2.1)
      have := hsum.trans (max_le hp' hq')
      omega
    · intro i S hS
      rw [← jetEval_apply, map_add, jetEval_apply, jetEval_apply]
      exact dvd_add (hp i S hS) (hq i S hS)
  smul_mem' c P hP := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      obtain ⟨hb, hj, ht, hw, hjets⟩ := hP m (MvPolynomial.support_smul hm)
      refine ⟨hb, hj, ht, ?_, hjets⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h : jetEval S (c • P) = c • jetEval S P := (jetEval S).map_smul c P
      rw [jetEval_apply, jetEval_apply] at h
      rw [h]
      exact dvd_smul_poly _ _ c (hp i S hS)
private instance finiteBank (w : I → K) (T : ℕ) : Module.Finite Geom (bank w T) := by
  classical
  let f : bank w T →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
    (coefficientArray T).comp (bank w T).subtype
  have hzero (Q : bank w T) (hQ : f Q = 0) : Q = 0 := by
    obtain ⟨P, hP⟩ := Q
    change BankRow w T P at hP
    apply Subtype.ext
    change P = 0
    apply MvPolynomial.ext
    intro m
    change _ = 0
    by_contra hnz
    have hm := MvPolynomial.mem_support_iff.mpr hnz
    have hT : (P.coeff m).natDegree ≤ T := (Nat.le_add_right _ _).trans (hP.2.1 m hm)
    let u : Fin 4 → Fin 4013 := fun i => ⟨m i, Nat.lt_succ_of_le <|
      (MvPolynomial.le_degreeOf_of_mem_support i hm).trans <|
        (P.degreeOf_le_totalDegree i).trans hP.1.1⟩
    apply hnz
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < T + 1
    · have hval := congrFun hQ (u, ⟨k, hk⟩)
      change (P.coeff (Finsupp.equivFunOnFinite.symm (fun i => (u i).val))).coeff k = 0 at hval
      have heq : Finsupp.equivFunOnFinite.symm (fun i => (u i).val) = m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro P Q h
  apply sub_eq_zero.mp
  have hz := f.map_sub P Q
  rw [h, sub_self] at hz
  exact hzero (P - Q) hz
private def bankEval (w : I → K) (x : Geom) (T : ℕ) : bank w T →ₗ[Geom] Symbol :=
  (symbolLinear x).comp (bank w T).subtype
private theorem mul_cutoff_iff (w : I → K) (x : Geom) (hx : ∀ i : I, x ≠ embed (node i))
    (T : ℕ) (P : Row 4) :
    BankRow w (T + 1) (MvPolynomial.C (linearFactor x) * P) ↔ BankRow w T P := by
  rw [bankRow_iff, bankRow_iff, support_linear_mul]
  apply and_congr
  · refine forall_congr' fun m => forall_congr' fun hm => ?_
    rw [MvPolynomial.coeff_C_mul, natDegree_mul (linearFactor_ne x)
      (MvPolynomial.mem_support_iff.mp hm), linearFactor_degree]
    constructor <;> rintro ⟨hb, hj, ht, hw, hJets⟩ <;>
      exact ⟨hb, hj, ht, by omega, hJets⟩
  · simp only [Contact, atJet, map_mul, MvPolynomial.eval_C]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro S
    apply forall_congr'
    intro hS
    generalize (3000 : ℕ) = m
    have hc : IsCoprime (linearFactor (embed (node i))) (linearFactor x) :=
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hx i).symm).isUnit
    have hd : IsCoprime (linearFactor (embed (node i)) ^ m) (linearFactor x) := hc.pow_left
    exact hd.dvd_mul_left_iff
private theorem zero_cutoff_kernel (w : I → K) (x : Geom) :
    LinearMap.ker (bankEval w x 0) = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro P hP
  change symbolAt x P.val = 0 at hP
  obtain ⟨Q, hQ⟩ := divide_specialization P.val x hP
  have hp : TrueWeightLE P.val 0 := P.property.2.1
  apply Subtype.ext
  change P.val = 0
  rw [← hQ]
  suffices Q = 0 by simp [this]
  apply MvPolynomial.ext
  intro m
  change _ = 0
  by_contra hnz
  have hm : m ∈ P.val.support := by
    rw [← hQ, support_linear_mul]
    exact MvPolynomial.mem_support_iff.mpr hnz
  have h := hp m hm
  rw [← hQ, MvPolynomial.coeff_C_mul, natDegree_mul (linearFactor_ne x) hnz,
    linearFactor_degree] at h
  omega
private theorem kernel_finrank (w : I → K) (x : Geom) (hx : ∀ i : I, x ≠ embed (node i))
    (T : ℕ) : Module.finrank Geom (LinearMap.ker (bankEval w x (T + 1))) =
      Module.finrank Geom (bank w T) := by
  let L : bank w T →ₗ[Geom] (LinearMap.ker (bankEval w x (T + 1))) :=
    LinearMap.codRestrict _ (LinearMap.codRestrict (bank w (T + 1))
      ((LinearMap.mulLeft Geom (MvPolynomial.C (linearFactor x))).comp (bank w T).subtype)
      (fun P => (mul_cutoff_iff w x hx T P.val).mpr P.property)) (fun P => by
        rw [LinearMap.mem_ker]
        simp only [bankEval, LinearMap.comp_apply, Submodule.subtype_apply,
          LinearMap.codRestrict_apply, LinearMap.mulLeft_apply]
        change symbolAt x (MvPolynomial.C (linearFactor x) * P.val) = 0
        have h0 : symbolAt x (MvPolynomial.C (linearFactor x)) = 0 := by
          simp only [symbolAt, linearFactor, MvPolynomial.map_C, Polynomial.coe_evalRingHom,
            Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, map_zero]
        rw [RingHom.map_mul, h0, zero_mul])
  have hL : Function.Bijective L := by
    have hnz : (MvPolynomial.C (linearFactor x) : Row 4) ≠ 0 := by
      simpa only [ne_eq, MvPolynomial.C_eq_zero] using linearFactor_ne x
    constructor
    · intro P Q h
      apply Subtype.ext
      have heq := congrArg (fun V : LinearMap.ker (bankEval w x (T + 1)) => V.val.val) h
      change MvPolynomial.C (linearFactor x) * P.val = MvPolynomial.C (linearFactor x) * Q.val at heq
      exact mul_left_cancel₀ hnz heq
    · intro P
      have h : symbolAt x P.val.val = 0 := LinearMap.mem_ker.mp P.property
      obtain ⟨Q, hQ⟩ := divide_specialization P.val.val x h
      have hmem : BankRow w (T + 1) (MvPolynomial.C (linearFactor x) * Q) := by
        rw [hQ]
        exact P.val.property
      refine ⟨⟨Q, (mul_cutoff_iff w x hx T Q).mp hmem⟩, Subtype.ext (Subtype.ext hQ)⟩
  exact (LinearEquiv.ofBijective L hL).finrank_eq.symm
theorem proof : Final50OrderProof.c3 := by
  classical
  intro w x hr hx
  let r (T : ℕ) := Module.finrank Geom (LinearMap.range (bankEval w x T))
  refine ⟨r, ?_, fun T _ => ?_⟩
  · have heq (T : ℕ) : Module.finrank Geom (bank w T) =
        ∑ V ∈ Finset.range (T + 1), r V := by
      induction T with
      | zero =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w 0) (V₂ := Symbol) (bankEval w x 0)
        rw [zero_cutoff_kernel, finrank_bot, Nat.add_zero] at h
        simpa only [Nat.zero_add, Finset.sum_range_one] using h.symm
      | succ T ih =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w (T + 1)) (V₂ := Symbol) (bankEval w x (T + 1))
        rw [kernel_finrank w x hx, ih, Nat.add_comm] at h
        rw [Finset.sum_range_succ]
        exact h.symm
    obtain ⟨e, he, hmem⟩ := hr
    have hi : LinearIndependent Geom (fun i => (⟨e i, hmem i⟩ : bank w primaryCutoff)) :=
      LinearIndependent.of_comp (bank w primaryCutoff).subtype he
    rw [← heq]
    simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank
  · let b := Module.finBasis Geom (LinearMap.range (bankEval w x T))
    choose e he using fun i : Fin (r T) => LinearMap.mem_range.mp (b i).property
    refine ⟨fun i => (e i).val, fun i => (e i).property, ?_⟩
    have h : LinearIndependent Geom (fun i => (b i).val) :=
      b.linearIndependent.map' (LinearMap.range (bankEval w x T)).subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have heq : (fun i => symbolAt x (e i).val) = fun i => (b i).val := funext he
    rwa [heq]
end
end Final50OrderProof_3
end
namespace Final50Order
noncomputable section
open K1_13 (Row shape)
open P3 (K)
open scoped Polynomial
export Final50OrderProof (BankRow requiredOrder)
export Final50OrderProof_1 (order_of_contact)
theorem messages_of_family {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt agreement M Γ) (hh : M.overhead ≤ 2413) :
    Messages M.word Γ F.scalar := by
  refine ⟨F.distinct, ?_, ?_⟩
  · intro γ hγ
    obtain hz | hd := (F.mark γ hγ).scalar_degree
    · simp [hz]
    · change ((F.scalar γ).natDegree : ℤ) ≤ (131072 : ℤ) - 1 + M.overhead at hd
      change (F.scalar γ).natDegree ≤ 133484
      omega
  · intro γ hγ
    let m := F.mark γ hγ
    exact ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩
theorem proper_layers_of_rank {w Γ s n} {f : Fin n → Row 4}
    (hm : Messages w Γ s) (hr : PrimaryRank w)
    (hirr : ∀ i, Irreducible (f i)) (hpos : ∀ i, 0 < (shape (f i)).t)
    (htop : ∀ i, (shape (f i)).t < K1.p)
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) :
    ∃ l : Fin n → ℕ, LayerBudget (fun i => shape (f i)) l ∧
      ∀ i, 0 < l i → ProperCut (f i) Γ s (l i) :=
  Final50OrderProof.of_children Final50OrderProof_1.proof
    Final50OrderProof_2.proof Final50OrderProof_3.proof
    hm hr hirr hpos htop hdiff
theorem primary_rank (w : P3.I → K) : PrimaryRank w :=
  Wide50EulerPrimary.primary_family agreement physicalDegree (by decide) (by decide)
    (by decide) w (n := sourceRank) le_rfl
theorem symbol_families : Final50OrderProof.c3 := Final50OrderProof_3.proof
theorem proper_layers {w Γ s n} {f : Fin n → Row 4}
    (hm : Messages w Γ s)
    (hirr : ∀ i, Irreducible (f i)) (hpos : ∀ i, 0 < (shape (f i)).t)
    (htop : ∀ i, (shape (f i)).t < K1.p)
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) :
    ∃ l : Fin n → ℕ, LayerBudget (fun i => shape (f i)) l ∧
      ∀ i, 0 < l i → ProperCut (f i) Γ s (l i) :=
  proper_layers_of_rank hm (primary_rank w) hirr hpos htop hdiff
end
end Final50Order

end Merged_Final50Order

end Merged6967_Final50Order

section Merged6967_Final50SurfaceLinearFour
set_option Elab.async false


set_option Elab.async false

-- merged module Final50SharedPrice
section Merged_Final50SharedPrice
set_option Elab.async false
set_option autoImplicit false
namespace Final50SharedPrice
open K1_13 (Shape chart ceilDiv mixed32 shape OnFactor extend)
open Final50Price (Messages SmallFactor ActiveFits ProperCut taylorLength primaryBox
  physicalPrice physicalDegree errors incidenceGap tiltedFits tiltedSurface)
open scoped Polynomial
abbrev slope : Shape := ⟨60,25,7⟩
inductive Surface where
  | ordinary
  | tilted
  deriving DecidableEq
def surfaceScale : Surface → ℕ
  | .ordinary => 32
  | .tilted => 1920
def surface (kind : Surface) (f q : Shape) : ℕ :=
  match kind with
  | .ordinary =>
    let p := f.chamber
    mixed32 p q (chart (taylorLength + 1) p) (chart (taylorLength + 2) p)
  | .tilted => tiltedSurface f.chamber q
def weights (kind : Surface) (f : Shape) : Shape :=
  let b := surface kind f ⟨1,0,0⟩
  let j := surface kind f ⟨1,1,0⟩ - b
  let t := surface kind f ⟨3,3,1⟩ - 3 * (b+j)
  ⟨b,j,t⟩
def coord (p : Shape) (i : Fin 3) : ℕ := (![p.b,p.j,p.t] : Fin 3 → ℕ) i
def expression (w q : Shape) (useIndex topIndex : Bool) : ℕ :=
  3*w.b*(if useIndex then q.j else q.b) + 3*w.j*q.j +
    w.t*(if topIndex then q.j else 3*q.t)
def deficit (r a : ℕ) (f : Shape) : Shape :=
  ⟨r*slope.b-a*f.b,r*slope.j-a*f.j,r*slope.t-a*f.t⟩
structure Rate where
  kind : Surface
  pivot : Fin 3
  split : ℕ
  topIndex : Bool
  amount : ℕ
def RateFits (f : Shape) (u : Rate) : Prop :=
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let w := weights u.kind f
  let target := 3 * surfaceScale u.kind * u.amount
  (u.kind = .tilted → tiltedFits f) ∧
  0 < u.split ∧ u.split*p < q ∧
  (∀ i, p * coord f i ≤ q * coord slope i) ∧
  (∀ useIndex : Bool, expression w slope useIndex u.topIndex ≤ target) ∧
  (∀ useIndex : Bool, expression w (deficit q p f) useIndex u.topIndex ≤ target*(q-u.split*p))
instance (f : Shape) (u : Rate) : Decidable (RateFits f u) := by
  unfold RateFits
  infer_instance
def additiveBase (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let h1 := chart (taylorLength+1) p
  let cont := ceilDiv ((errors+2*incidenceGap)*x.b*q.b*h1.b) incidenceGap
  let z := q.plus (p.scale 4)
  let cv := mixed32 p q z h + 2*x.t*mixed32 p p p h
  let pt := mixed32 p q z p + 2*x.t*mixed32 p p p p
  ceilDiv cont l + 2*physicalDegree*x.b*q.b +
    ceilDiv (errors*cv+2*incidenceGap*pt) (32*incidenceGap)
def nonsharedFee (x : Shape) (l : ℕ) : ℕ :=
  ceilDiv (2*x.b*primaryBox.b^2*(chart (taylorLength+2) x.chamber).b) l
def price (x : Shape) (l K : ℕ) (u : Rate) : ℕ :=
  ceilDiv (physicalPrice x l K + u.split*additiveBase x l + u.split*u.amount + 1)
    (u.split+1) + nonsharedFee x l
end Final50SharedPrice

end Merged_Final50SharedPrice

-- merged module Final50SurfaceLinearFour
section Merged_Final50SurfaceLinearFour

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 900000

namespace Final50SharedPrice

open K1_13 (Shape chart difference volume32)
open K1_13_8 (Valid)
open Final50Price (taylorLength)
open K1_13_8_2 (signedMixed signed_rotate signed_nonneg)

/-- Extract the three coefficients with the same probes as `weights`. The sign
conditions ensure that every subtraction in the natural-number probes is exact. -/
theorem surface_eq_weights_of_signed (kind : Surface) (f : Shape) (b j t : ℤ)
    (hb : 0 ≤ b) (hj : 0 ≤ j) (ht : 0 ≤ t)
    (h : ∀ q : Shape, (surface kind f q : ℤ) = b*q.b + j*q.j + t*q.t) (q : Shape) :
    surface kind f q = (weights kind f).b*q.b + (weights kind f).j*q.j +
      (weights kind f).t*q.t := by
  have hn (u : Shape) : surface kind f u = b.toNat*u.b + j.toNat*u.j + t.toNat*u.t := by
    apply Int.ofNat.inj
    change (surface kind f u : ℤ) = ((b.toNat*u.b + j.toNat*u.j + t.toNat*u.t : ℕ) : ℤ)
    rw [h u]
    push_cast
    rw [Int.toNat_of_nonneg hb, Int.toNat_of_nonneg hj, Int.toNat_of_nonneg ht]
  have hw : weights kind f = ⟨b.toNat,j.toNat,t.toNat⟩ := by
    unfold weights
    simp only [hn ⟨1,0,0⟩, hn ⟨1,1,0⟩, hn ⟨3,3,1⟩, Nat.mul_one, Nat.mul_zero,
      Nat.add_zero, Nat.add_sub_cancel_left]
    congr 1
    omega
  rw [hw]
  exact hn q



end Final50SharedPrice

end Merged_Final50SurfaceLinearFour

end Merged6967_Final50SurfaceLinearFour

section Merged6967_KoalaAllocationWeight
set_option Elab.async false


set_option Elab.async false

namespace KoalaAllocationWeight
open K1_13 (Shape)
open scoped BigOperators

def fullCharge (j t : ℕ) : Prop := 53 ≤ j ∨ 14 ≤ t

instance (j t : ℕ) : Decidable (fullCharge j t) := by unfold fullCharge; infer_instance

def weight (b j t : ℕ) : ℕ := if fullCharge j t then 352 else min (b+4*j) 352

theorem mono {b j t B J T : ℕ} (hb : b ≤ B) (hj : j ≤ J) (ht : t ≤ T) :
    weight b j t ≤ weight B J T := by
  by_cases h : fullCharge j t
  · have h' : fullCharge J T := h.imp (fun k => k.trans hj) (fun k => k.trans ht)
    simp [weight, h, h']
  · by_cases h' : fullCharge J T
    · simpa [weight, h, h'] using (min_le_right (b+4*j) 352)
    · simpa [weight, h, h'] using
        (min_le_min (Nat.add_le_add hb (Nat.mul_le_mul_left 4 hj)) (le_refl 352))

theorem sum_le {top n : ℕ} (htop : top ≤ 14) (a : Fin n → Shape) (hfits : Final50Price.Fits top a)
    (s : Finset (Fin n)) : (∑ i ∈ s, weight (a i).b (a i).j (a i).t) ≤ 352 := by
  classical
  have part (f : Fin n → ℕ) : ∑ i ∈ s, f i ≤ ∑ i, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  by_cases hall : ∃ i ∈ s, fullCharge (a i).j (a i).t
  · obtain ⟨i, hi, hc⟩ := hall
    have only (j : Fin n) (hji : j ≠ i) : False := by
      have pair (f : Fin n → ℕ) : f i+f j ≤ ∑ k, f k := by
        rw [← Finset.sum_pair (Ne.symm hji)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
      obtain ⟨ht,hj,_⟩ := hfits.1 j
      have hJ := (pair fun k => (a k).j).trans hfits.2.2.1
      have hT := (pair fun k => (a k).t).trans hfits.2.2.2
      rcases hc with h | h <;> omega
    have he : s = {i} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun j _ => by
      by_contra hne
      exact only j hne⟩
    rw [he, Finset.sum_singleton]
    simp [weight, hc]
  · have hw : ∀ i ∈ s, weight (a i).b (a i).j (a i).t ≤ (a i).b+4*(a i).j := by
      intro i hi
      simp [weight, show ¬ fullCharge (a i).j (a i).t from fun h => hall ⟨i,hi,h⟩]
    refine (Finset.sum_le_sum hw).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact Nat.add_le_add ((part _).trans hfits.2.1)
      (Nat.mul_le_mul_left 4 ((part _).trans hfits.2.2.1))

#print axioms sum_le
end KoalaAllocationWeight

end Merged6967_KoalaAllocationWeight

section Merged6967_HighCore82258Source
set_option Elab.async false



set_option Elab.async false

-- merged module GoldBranch7N1
section Merged_GoldBranch7N1
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_7_1
open P1_7 (Bank)
open P1_7_1 (nodeRows groupedPoleMoment)
open P1_7_1_2 (six_nodeRows sixPerNode)
open P1_7_1_3 (momentEstimate grouped_bound)
open P1_7_1_3_2 (ExactMoment)
structure BankOK (t : Bank) : Prop where
  nodes : nodeRows t.shape = t.nodeRows
  moment : groupedPoleMoment t.shape.B t.shape.J ≤ t.poleMoment ∧ t.shape.B < K1.p
theorem checked (t : Bank) {m B J N M : ℕ}
    (hm : t.shape.m = m) (hB : t.shape.B = B) (hJ : t.shape.J = J)
    (hN : t.nodeRows = N) (hM : t.poleMoment = M)
    (hmJ : 2*J ≤ m) (hJB : m+J ≤ B+1)
    (hnode : 262144 * sixPerNode (m-2*J) J = 6*N)
    (hchar : B < K1.p) (hbound : momentEstimate B J = M) : BankOK t := by
  have h := six_nodeRows t.shape (by rw [hm, hJ]; exact hmJ) (by rw [hm, hJ, hB]; exact hJB)
  rw [hm, hJ, hnode, ← hN] at h
  refine ⟨by omega, ?_⟩
  rw [hB, hJ, hM]
  exact ⟨(grouped_bound _ _).trans hbound.le, hchar⟩
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
end P3_7_1
end
section
namespace P3_7_1
open P3 (HighBand)
open P3_7 (Bank Stage terminal stages  )
open scoped P1_7_1_3_2
local notation "b!" depth "," grade "," deriv "," nodes "," moment ";" h =>
  checked _ (m := depth) (B := grade) (J := deriv) (N := nodes) (M := moment)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) h
end P3_7_1
end

end Merged_GoldBranch7N1

-- merged module HighCore82258Source
section Merged_HighCore82258Source

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

namespace HighCore82258
noncomputable section

open Polynomial
open P1 (K I p node twist)
open FrontCore82258 (AnchorModel AnchoredFamily AdjacentChart)
open K1_14 (L FX Seeds Equation Shape Jet Banks SeedBound liftPoly graphEval atX atMark
  jetAt triangle slots shapeSum)
open K1_14_1
open P1_7_1 (groupedPoleMoment nodeRows telescope)
open scoped BigOperators Polynomial
open P1_7_1 (pole_bound)



def fullCutoff (s : Shape) := s.m * agreement - 1
def buffered (h r : ℕ) (s : Shape) := fullCutoff s - 2*h*r
def RankFloor (h : ℕ) (t : Bank) (rows : Banks) : Prop :=
  ∀ W < t.shape.m * agreement,
    (∀ q ≤ t.shape.B, ∀ j ≤ min q t.shape.J, q * (131071-h) ≤ W+1+j) →
    triangle t.shape.U * shapeSum t.shape (fun q j => W+1+j - q*(131071-h)) ≤
      debit h t + ∑ w ∈ Finset.range (W+1), Module.finrank FX (rows t.shape w)
structure Source (b : Band) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) (rows : Banks) : Prop where
  nested : ∀ t, Listed b t → ∀ t', Listed b t' →
    t.shape.m = t'.shape.m → t.shape.B = t'.shape.B → t.shape.J = t'.shape.J →
    t.shape.U ≤ t'.shape.U → ∀ W W', W ≤ W' → rows t.shape W ≤ rows t'.shape W'
  necessary : ∀ t, Listed b t → ∀ W < t.shape.m * agreement, ∀ P ∈ rows t.shape W,
    ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0
  shape : ∀ t, Listed b t → ∀ W, ∀ P ∈ rows t.shape W, K1_14_3.RowCaps P t.shape
  leading : ∀ t, Listed b t → K1_14_3.LeadingFilter M.overhead.toNat rows t.shape
  shift : ∀ t, Listed b t → K1_14_3.SeedShift M.overhead.toNat rows t.shape
  floor_bound : ∀ t, Listed b t → RankFloor M.overhead.toNat t rows
structure BufferedPair (h : ℕ) (rows : Banks) (s : Stage) where
  free : Jet
  moving : Jet
  free_ne : free ≠ 0
  moving_ne : moving ≠ 0
  free_mem : free ∈ rows s.free.shape (buffered h s.reserve s.free.shape)
  moving_mem : moving ∈ rows s.moving.shape (buffered h s.reserve s.moving.shape)
  no_moving : K1_14_3.NoMovingCommon free moving
abbrev Pairs (b : Band) (h : ℕ) (rows : Banks) :=
  ∀ s ∈ stages b, BufferedPair h rows s


def crtWord {u del} (M : AnchorModel u del) : I → L :=
  fun i => algebraMap K L (M.word i)

structure ChartSource (b : Band) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) where
  poles : PoleData M.overhead.toNat
  crt : CRTLift poles
  node_avoids : ∀ i k, (poles.block i).eval (nodeL k) ≠ 0
  residues : ∀ γ ∈ Γ, MarkResidues poles (M.label γ) (F.scalar γ)
  source : Source b M F (evaluated crt (crtWord M))





end
end HighCore82258

end Merged_HighCore82258Source

end Merged6967_HighCore82258Source

section Merged6967_HighCore82258Terminal
set_option Elab.async false



set_option Elab.async false

-- merged module HighCore82258TerminalArithmetic
section Merged_HighCore82258TerminalArithmetic

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace HighCore82258TerminalArithmetic
open Finset
open K1_14 (Shape)
open HighCore82258 (agreement)
open HighCore82258 (Bank debit jointGain)
export P1_7_6 (orderEnd linearEnd Quad prefixProduct intervalProduct seedEnd yStart seedQuad scaledDebit)
def width (s : Shape) (h q j t : ℕ) : ℤ :=
  (s.m * agreement : ℕ) + (j : ℤ) - (131071 - (h : ℤ)) * q - 2 * (h : ℤ) * t
def surplus (h : ℕ) (b : Bank) (E v : ℕ) : ℤ :=
  (jointGain h b.shape E v : ℤ) - (debit h b : ℤ)
def colEnd (s : Shape) (h t : ℕ) : ℕ :=
  linearEnd (2*h*t) (131071-h) (s.m*agreement) (s.B+1)
def edgeShift (s : Shape) (h t : ℕ) : ℕ :=
  2*h*t + (131071-h)*colEnd s h t + 1 - s.m*agreement
def innerEnd (s : Shape) (h E v d t R : ℕ) : ℕ :=
  linearEnd (yStart E d t) (E-1) (colEnd s h t) (seedEnd s v d R)
def outerEnd (s : Shape) (h E v d t R : ℕ) : ℕ :=
  min (t+1-edgeShift s h t)
    (linearEnd (yStart E d t) (E-1) (colEnd s h t+1) (seedEnd s v d R))
def widthOrigin (s : Shape) (h t : ℕ) : ℤ :=
  (s.m*agreement : ℕ) + (t : ℤ) - 2*(h : ℤ)*t
def innerQuad (s : Shape) (h E d t : ℕ) : Quad :=
  let D : ℤ := (131071-h : ℕ)
  let k : ℤ := colEnd s h t
  let l : ℤ := yStart E d t
  let p : ℤ := (E-1 : ℕ)
  P1_7_6.Quad.ofLines (k-l) (-p) (2*widthOrigin s h t-D*(l+k-1)) (-2-D*p)
def outerQuad (s : Shape) (h t : ℕ) : Quad :=
  ⟨2*(widthOrigin s h t-((131071-h : ℕ) : ℤ)*colEnd s h t), -2, 0⟩
def phaseBlock (s : Shape) (h E v d t : ℕ) : ℤ :=
  let L := t-s.J
  let R := min t (orderEnd s E v-1)+1
  let c := seedQuad s v d
  intervalProduct c (innerQuad s h E d t) L (innerEnd s h E v d t R) +
    if colEnd s h t < s.B+1 then
      intervalProduct c (outerQuad s h t) L (outerEnd s h E v d t R)
    else 0
def blockSurplus (s : Shape) (N P h E v : ℕ) : ℤ :=
  (∑ t ∈ range (s.J+orderEnd s E v), (phaseBlock s h E v 0 t - phaseBlock s h E v 1 t)) -
    scaledDebit s N P h
def BlockChecks (s : Shape) (N P h E v : ℕ) : Prop :=
  0 < blockSurplus s N P h E v ∧ blockSurplus s N P h E v ≤ blockSurplus s N P (h+1) E v
end HighCore82258TerminalArithmetic
end
section
namespace HighCore82258TerminalArithmetic
open Finset
open K1_14 (Shape shapeSum slots)
open HighCore82258 (agreement)
open HighCore82258 (Bank debit jointGain)
open P1_7_6 (rise_of_convex)
theorem width_cast (s : Shape) (h q j t : ℕ) (hh : h ≤ 131071) :
    (↑(s.m * agreement + j - q * (131071-h) - 2*h*t : ℕ) : ℤ) =
      max 0 (width s h q j t) := by
  rw [Nat.sub_sub]
  have hd : (↑(131071-h : ℕ) : ℤ) = 131071 - h := Nat.cast_sub hh
  have he : (↑(s.m*agreement+j : ℕ) : ℤ) - (↑(q*(131071-h)+2*h*t : ℕ) : ℤ) =
      width s h q j t := by
    simp only [width, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hd]
    ring
  generalize s.m*agreement+j = x at *
  generalize q*(131071-h)+2*h*t = y at *
  by_cases hxy : y ≤ x
  · rw [Int.ofNat_sub hxy, he, max_eq_right (by omega)]
  · have hz : x-y = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz, Int.ofNat_zero, max_eq_left (by omega)]
private theorem width_convex (s : Shape) (h q j t : ℕ) :
    max 0 (width s (h+1) q j t) + max 0 (width s (h+1) q j t) ≤
      max 0 (width s h q j t) + max 0 (width s (h+2) q j t) := by
  have hlin : width s (h+1) q j t + width s (h+1) q j t =
      width s h q j t + width s (h+2) q j t := by
    simp only [width, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  by_cases hn : width s (h+1) q j t ≤ 0
  · rw [max_eq_left hn, zero_add]
    exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  · rw [max_eq_right (le_of_not_ge hn), hlin]
    exact add_le_add (le_max_right _ _) (le_max_right _ _)
private theorem weighted_convex (s : Shape) (h q j t c : ℕ) (hh : h+2 ≤ 131071) :
    let f := fun h => (↑(c * (s.m * agreement + j - q*(131071-h) - 2*h*t) : ℕ) : ℤ)
    f (h+1) + f (h+1) ≤ f h + f (h+2) := by
  dsimp only
  simp only [Nat.cast_mul, width_cast s h q j t (by omega),
    width_cast s (h+1) q j t (by omega), width_cast s (h+2) q j t hh, ← mul_add]
  exact mul_le_mul_of_nonneg_left (width_convex s h q j t) (Int.natCast_nonneg c)
private theorem gain_convex (s : Shape) (h E v : ℕ) (hh : h+2 ≤ 131071) :
    let f := fun h => (jointGain h s E v : ℤ)
    f (h+1) + f (h+1) ≤ f h + f (h+2) := by
  simp only [jointGain, shapeSum, Nat.cast_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro q _
  apply sum_le_sum
  intro j _
  let g := (q-j)/E
  let raw := fun k a => s.m*agreement+j-q*(131071-k)-2*k*(j+a)
  let A := fun k => (↑(∑ a ∈ range g, (slots s.U (a*v) - slots s.U ((a+1)*v))*raw k a : ℕ) : ℤ)
  let B := fun k => (↑(slots s.U (g*v)*raw k g : ℕ) : ℤ)
  simp only [Nat.cast_add]
  change A (h+1) + B (h+1) + (A (h+1) + B (h+1)) ≤ A h + B h + (A (h+2) + B (h+2))
  rw [add_add_add_comm (A (h+1)), add_add_add_comm (A h)]
  apply add_le_add
  · simp only [A, Nat.cast_sum]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro a _
    exact weighted_convex s h q j (j+a) (slots s.U (a*v) - slots s.U ((a+1)*v)) hh
  · exact weighted_convex s h q j (j+(q-j)/E) (slots s.U (((q-j)/E)*v)) hh
private theorem debit_affine (h : ℕ) (b : Bank) :
    (debit (h+1) b : ℤ) + (debit (h+1) b : ℤ) =
      (debit h b : ℤ) + (debit (h+2) b : ℤ) := by
  simp only [debit, P1_7.debit, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring
private theorem surplus_convex (h : ℕ) (b : Bank) (E v : ℕ) (hh : h+2 ≤ 131071) :
    surplus (h+1) b E v + surplus (h+1) b E v ≤
      surplus h b E v + surplus (h+2) b E v := by
  have hg := gain_convex b.shape h E v hh
  have hd := debit_affine h b
  dsimp only at hg
  unfold surplus
  omega
theorem strict_of_first_difference {lo h : ℕ} {b : Bank} {E v : ℕ}
    (hl : lo ≤ h) (hh : h < 131071)
    (hpos : 0 < surplus lo b E v) (hrise : surplus lo b E v ≤ surplus (lo+1) b E v) :
    debit h b < jointGain h b.shape E v := by
  have hmon := rise_of_convex (f := fun h => surplus h b E v)
    (fun n hn => surplus_convex n b E v (by omega)) hl hrise
  have hsur := hpos.trans_le hmon.1
  unfold surplus at hsur
  omega
end HighCore82258TerminalArithmetic
end
section
namespace HighCore82258TerminalArithmetic
open Finset
open K1_14 (Shape shapeSum slots triangle)
open HighCore82258 (agreement)
open HighCore82258 (jointGain)
open P1_7_6 (slots_anti sum_range_guard diagonal)
def phase (s : Shape) (h E v d : ℕ) : ℤ :=
  ∑ t ∈ range (s.J + orderEnd s E v), ∑ a ∈ Ico (t-s.J) (min t (orderEnd s E v-1)+1),
    (slots s.U ((a+d)*v) : ℤ) *
      ∑ q ∈ Ico (t-a+E*(a+d)) (s.B+1), max 0 (width s h q (t-a) t)
private theorem position_phases (s : Shape) (h E v q j : ℕ) (hh : h ≤ 131071)
    (he : 0 < E) (hq : q ≤ s.B) (hj : j ≤ q) :
    let c := fun a => slots s.U (a*v)
    let x := s.m*agreement+j-q*(131071-h)
    let g := (q-j)/E
    let f := fun d a => (c (a+d) : ℤ)*max 0 (width s h q j (j+a))
    (↑((∑ a ∈ range g, (c a - c (a+1))*(x-2*h*(j+a))) + c g*(x-2*h*(j+g)) : ℕ) : ℤ) =
      (∑ a ∈ range (orderEnd s E v), if j+E*(a+0) ≤ q then f 0 a else 0) -
      (∑ a ∈ range (orderEnd s E v), if j+E*(a+1) ≤ q then f 1 a else 0) := by
  dsimp only
  let g := (q-j)/E
  let f := fun d a => (slots s.U ((a+d)*v) : ℤ)*max 0 (width s h q j (j+a))
  have step (a : ℕ) : slots s.U ((a+1)*v) ≤ slots s.U (a*v) :=
    slots_anti _ (Nat.mul_le_mul_right v (by omega))
  have hdiff :
      (↑((∑ a ∈ range g, (slots s.U (a*v) - slots s.U ((a+1)*v)) *
          (s.m*agreement+j-q*(131071-h)-2*h*(j+a))) +
        slots s.U (g*v)*(s.m*agreement+j-q*(131071-h)-2*h*(j+g)) : ℕ) : ℤ) =
      (∑ a ∈ range (g+1), f 0 a) - ∑ a ∈ range g, f 1 a := by
    rw [sum_range_succ, Nat.cast_add, Nat.cast_sum]
    rw [show (∑ a ∈ range g, f 0 a) + f 0 g - (∑ a ∈ range g, f 1 a) =
        ((∑ a ∈ range g, f 0 a) - (∑ a ∈ range g, f 1 a)) + f 0 g by ring,
      ← sum_sub_distrib]
    simp only [Nat.cast_mul, width_cast s h _ _ _ hh, f, Nat.add_zero]
    have hs (a : ℕ) :
        (↑(slots s.U (a*v) - slots s.U ((a+1)*v) : ℕ) : ℤ) =
          (slots s.U (a*v) : ℤ) - slots s.U ((a+1)*v) := Int.ofNat_sub (step a)
    simp only [hs, sub_mul]
  rw [hdiff]
  have hz (d a : ℕ) (ha : orderEnd s E v ≤ a) (hg : a+d ≤ g) : f d a = 0 := by
    have hcap : g ≤ s.B/E := Nat.div_le_div_right (by omega)
    have hab : a < s.B/E+1 := by omega
    unfold orderEnd at ha
    split at ha
    · omega
    · rename_i hv
      have hlarge : s.U/v < a+d := by omega
      have hout : s.U < (a+d)*v := by
        by_contra! hm
        exact (Nat.not_le_of_lt hlarge) ((Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hv)).2 hm)
      simp [f, slots, Nat.not_le_of_lt hout]
  have hdiv (a d : ℕ) : j+E*(a+d) ≤ q ↔ a+d ≤ g := by
    rw [Nat.le_div_iff_mul_le he, Nat.mul_comm (a+d) E]
    omega
  rw [sum_range_guard (g+1) _ (fun a ha hb => hz 0 a ha (by omega)),
    sum_range_guard g _ (fun a ha hb => hz 1 a ha (by omega))]
  have hzero (a : ℕ) : j+E*a ≤ q ↔ a ≤ g := by simpa using hdiv a 0
  simp only [hzero, Nat.add_zero, Nat.lt_succ_iff, Nat.add_one_le_iff, f]
private def phaseQ (s : Shape) (h E v d : ℕ) : ℤ :=
  ∑ q ∈ range (s.B+1), ∑ j ∈ range (s.J+1), ∑ a ∈ range (orderEnd s E v),
    if j + E*(a+d) ≤ q then
      (slots s.U ((a+d)*v) : ℤ) * max 0 (width s h q j (j+a)) else 0
private theorem phaseQ_expand (s : Shape) (h E v d q : ℕ) :
    (∑ j ∈ range (min q s.J+1), ∑ a ∈ range (orderEnd s E v),
      if j+E*(a+d) ≤ q then (slots s.U ((a+d)*v) : ℤ)*max 0 (width s h q j (j+a)) else 0) =
    ∑ j ∈ range (s.J+1), ∑ a ∈ range (orderEnd s E v),
      if j+E*(a+d) ≤ q then (slots s.U ((a+d)*v) : ℤ)*max 0 (width s h q j (j+a)) else 0 := by
  apply sum_subset (range_mono (Nat.succ_le_succ (min_le_right _ _)))
  intro j hj hnot
  simp only [mem_range, Nat.lt_succ_iff, le_min_iff] at hj hnot
  apply sum_eq_zero
  intro a _
  rw [ite_eq_right (by omega)]
private theorem gain_eq_phaseQ (s : Shape) (h E v : ℕ) (hh : h ≤ 131071) (he : 0 < E) :
    (jointGain h s E v : ℤ) = phaseQ s h E v 0 - phaseQ s h E v 1 := by
  unfold jointGain shapeSum phaseQ
  push_cast only [Nat.cast_sum]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro q hq
  rw [← phaseQ_expand s h E v 0 q, ← phaseQ_expand s h E v 1 q, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  rw [mem_range, Nat.lt_succ_iff] at hq hj
  exact position_phases s h E v q j hh he hq (hj.trans (min_le_left _ _))
private theorem phaseQ_eq (s : Shape) (h E v d : ℕ) : phaseQ s h E v d = phase s h E v d := by
  have hR : orderEnd s E v-1+1 = orderEnd s E v := by
    apply Nat.sub_add_cancel
    unfold orderEnd
    split
    · exact Nat.succ_pos _
    · exact le_min (Nat.succ_pos _) (Nat.succ_pos _)
  unfold phaseQ phase
  rw [sum_comm]
  conv_lhs =>
    enter [2, j]
    rw [sum_comm]
  conv_lhs =>
    rw [← hR]
    rw [diagonal]
  rw [Nat.add_assoc, hR]
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro a ha
  have hta : t-a+a = t := Nat.sub_add_cancel (by have := (mem_Ico.mp ha).2; omega)
  rw [mul_sum, ← sum_filter]
  have hf : (range (s.B+1)).filter (fun q => t-a+E*(a+d) ≤ q) =
      Ico (t-a+E*(a+d)) (s.B+1) := by
    ext q
    simp only [mem_range, mem_filter, mem_Ico]
    tauto
  rw [hf, hta]
theorem gain_eq_phases (s : Shape) (h E v : ℕ) (hh : h ≤ 131071) (he : 0 < E) :
    (jointGain h s E v : ℤ) = phase s h E v 0 - phase s h E v 1 := by
  rw [gain_eq_phaseQ s h E v hh he, phaseQ_eq, phaseQ_eq]
end HighCore82258TerminalArithmetic
end
section
namespace HighCore82258TerminalArithmetic
open Finset
open HighCore82258 (agreement)
open K1_14 (Shape)
open K1_14_2_1 (twice_sum_linear)
export P1_7_6 (lt_linearEnd)
private theorem width_eq_cast (s : Shape) (h q j t : ℕ) (hh : h ≤ 131071) :
    width s h q j t = (↑(s.m*agreement+j : ℕ) : ℤ) -
      (↑(2*h*t+(131071-h)*q : ℕ) : ℤ) := by
  simp only [width, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hh, Nat.cast_ofNat]
  ring
theorem width_sum (s : Shape) (h t j l : ℕ) (hh : h ≤ 131071) (hj : j ≤ 131071-h) :
    (∑ q ∈ Ico l (s.B+1), max 0 (width s h q j t)) =
      (∑ q ∈ Ico l (colEnd s h t), width s h q j t) +
        if colEnd s h t < s.B+1 ∧ l ≤ colEnd s h t ∧ edgeShift s h t ≤ j then
          width s h (colEnd s h t) j t else 0 := by
  let k := colEnd s h t
  let D := 131071-h
  have hk (q : ℕ) : q < k ↔ q < s.B+1 ∧ 2*h*t + D*q < s.m*agreement :=
    lt_linearEnd _ _ _ _ _
  have hkB : k ≤ s.B+1 := by
    by_contra! h
    exact (Nat.lt_irrefl _) ((hk (s.B+1)).mp h).1
  have hpos (q : ℕ) (hq : q < k) : 0 ≤ width s h q j t := by
    have hp := ((hk q).mp hq).2
    rw [width_eq_cast s h q j t hh]
    change 2*h*t+D*q < s.m*agreement at hp
    change 0 ≤ (↑(s.m*agreement+j : ℕ) : ℤ) - (↑(2*h*t+D*q : ℕ) : ℤ)
    omega
  have hsum : (∑ q ∈ Ico l k, max 0 (width s h q j t)) = ∑ q ∈ Ico l k, width s h q j t := by
    apply sum_congr rfl
    intro q hq
    exact max_eq_right (hpos q (mem_Ico.mp hq).2)
  by_cases hb : k < s.B+1
  · have hbase : s.m*agreement ≤ 2*h*t + D*k := by
      by_contra! he
      exact (Nat.lt_irrefl _) ((hk k).mpr ⟨hb,he⟩)
    have hzero (q : ℕ) (hq : k < q) : max 0 (width s h q j t) = 0 := by
      have hm : D*(k+1) ≤ D*q := Nat.mul_le_mul_left D (by omega)
      rw [Nat.mul_add, Nat.mul_one] at hm
      apply max_eq_left
      rw [width_eq_cast s h q j t hh]
      change j ≤ D at hj
      change (↑(s.m*agreement+j : ℕ) : ℤ) - (↑(2*h*t+D*q : ℕ) : ℤ) ≤ 0
      omega
    have hrestrict :
        (∑ q ∈ Ico l (s.B+1), max 0 (width s h q j t)) =
          ∑ q ∈ Ico l (k+1), max 0 (width s h q j t) := by
      symm
      apply sum_subset
      · intro q hq
        obtain ⟨ha,he⟩ := mem_Ico.mp hq
        exact mem_Ico.mpr ⟨ha,by omega⟩
      · intro q hq hn
        obtain ⟨ha,he⟩ := mem_Ico.mp hq
        exact hzero q (by
          by_contra! hle
          exact hn (mem_Ico.mpr ⟨ha,by omega⟩))
    change _ = (∑ q ∈ Ico l k, _) + if k < s.B+1 ∧ l ≤ k ∧ edgeShift s h t ≤ j then _ else _
    rw [hrestrict]
    by_cases hl : l ≤ k
    · rw [sum_Ico_succ_top hl, hsum]
      simp only [hb, hl, true_and]
      congr 1
      have hsign : 0 < width s h k j t ↔ edgeShift s h t ≤ j := by
        rw [width_eq_cast s h k j t hh]
        change (0 : ℤ) < (↑(s.m*agreement+j : ℕ) : ℤ) - (↑(2*h*t+D*k : ℕ) : ℤ) ↔
          2*h*t+D*k+1-s.m*agreement ≤ j
        omega
      by_cases hw : edgeShift s h t ≤ j
      · rw [ite_eq_left hw, max_eq_right ((hsign.mpr hw).le)]
      · rw [ite_eq_right hw, max_eq_left (by have := mt hsign.mp hw; omega)]
    · have he : Ico l (k+1) = ∅ := Ico_eq_empty_of_le (by omega)
      have hf : Ico l k = ∅ := Ico_eq_empty_of_le (by omega)
      simp [he,hf,hl]
  · have he : k = s.B+1 := by omega
    change _ = (∑ q ∈ Ico l k, _) + if k < s.B+1 ∧ l ≤ k ∧ edgeShift s h t ≤ j then _ else _
    rw [← he, hsum]
    simp
theorem twice_width_interval (s : Shape) (h t j l k : ℕ) (hh : h ≤ 131071)
    (hl : l ≤ k) :
    2 * (∑ q ∈ Ico l k, width s h q j t) =
      ((k : ℤ)-l) * (2*((s.m*agreement : ℕ)+(j : ℤ)-2*(h : ℤ)*t) -
        ((131071-h : ℕ) : ℤ)*((l : ℤ)+k-1)) := by
  rw [sum_Ico_eq_sum_range]
  have hf (a : ℕ) : width s h (l+a) j t =
      width s h l j t + (-((131071-h : ℕ) : ℤ))*(a : ℤ) := by
    simp only [width, Nat.cast_add, Nat.cast_sub hh, Nat.cast_ofNat]
    ring
  simp_rw [hf]
  rw [twice_sum_linear]
  simp only [Nat.cast_sub hl, width, Nat.cast_sub hh, Nat.cast_ofNat]
  ring
end HighCore82258TerminalArithmetic
end
section
namespace HighCore82258TerminalArithmetic
open Finset
open HighCore82258 (agreement)
open K1_14 (Shape slots triangle)
open HighCore82258 (debit)
open P1_7_6 (intervalProduct_eq)
open P1_7_6 (lt_seedEnd yStart_eq seedQuad_eq sum_clipped)
private theorem widthOrigin_eq (s : Shape) (h t a q : ℕ) (hh : h ≤ 131071) (ha : a ≤ t) :
    width s h q (t-a) t = widthOrigin s h t - a - ((131071-h : ℕ) : ℤ)*q := by
  simp only [width, widthOrigin, Nat.cast_sub hh, Nat.cast_sub ha, Nat.cast_ofNat]
  ring
private theorem innerQuad_eq (s : Shape) (h E d t a : ℕ) (hh : h ≤ 131071)
    (he : 0 < E) (ha : a ≤ t) (hl : t-a+E*(a+d) ≤ colEnd s h t) :
    2*(∑ q ∈ Ico (t-a+E*(a+d)) (colEnd s h t), width s h q (t-a) t) =
      (innerQuad s h E d t).eval a := by
  rw [twice_width_interval s h t (t-a) _ _ hh hl, innerQuad, P1_7_6.Quad.eval_ofLines,
    yStart_eq E d t a he ha]
  simp only [widthOrigin, Nat.cast_sub ha, Nat.cast_add, Nat.cast_mul]
  ring
private theorem outerQuad_eq (s : Shape) (h t a : ℕ) (hh : h ≤ 131071) (ha : a ≤ t) :
    2*width s h (colEnd s h t) (t-a) t = (outerQuad s h t).eval a := by
  rw [widthOrigin_eq s h t a _ hh ha]
  simp only [outerQuad, P1_7_6.Quad.eval]
  ring
theorem phaseBlock_eq (s : Shape) (h E v d t : ℕ)
    (hh : h ≤ 131071) (hj : s.J ≤ 131071-h) (he : 0 < E) :
    240*(∑ a ∈ Ico (t-s.J) (min t (orderEnd s E v-1)+1),
      (slots s.U ((a+d)*v) : ℤ) *
        ∑ q ∈ Ico (t-a+E*(a+d)) (s.B+1), max 0 (width s h q (t-a) t)) =
      phaseBlock s h E v d t := by
  let L := t-s.J
  let R := min t (orderEnd s E v-1)+1
  let k := colEnd s h t
  let l := fun a => t-a+E*(a+d)
  let c := fun a => (slots s.U ((a+d)*v) : ℤ)
  let inner := fun a => ∑ q ∈ Ico (l a) k, width s h q (t-a) t
  let outer := fun a =>
    if k < s.B+1 ∧ l a ≤ k ∧ edgeShift s h t ≤ t-a then width s h k (t-a) t else 0
  let R₁ := innerEnd s h E v d t R
  let R₂ := outerEnd s h E v d t R
  have ht (a : ℕ) (ha : a < R) : a ≤ t :=
    (Nat.le_of_lt_succ ha).trans (min_le_left _ _)
  have hcore (a : ℕ) : a < R₁ ↔ a < R ∧ (a+d)*v ≤ s.U ∧ l a < k := by
    simp only [R₁, innerEnd, lt_linearEnd, lt_seedEnd]
    constructor
    · rintro ⟨⟨ha,hv⟩,hk⟩
      exact ⟨ha,hv,by simpa only [l,yStart_eq E d t a he (ht a ha)] using hk⟩
    · rintro ⟨ha,hv,hk⟩
      exact ⟨⟨ha,hv⟩,by simpa only [l,yStart_eq E d t a he (ht a ha)] using hk⟩
  have hedge (a : ℕ) :
      a < R₂ ↔ a < R ∧ (a+d)*v ≤ s.U ∧ l a ≤ k ∧ edgeShift s h t ≤ t-a := by
    simp only [R₂, outerEnd, lt_min_iff, lt_linearEnd, lt_seedEnd]
    constructor
    · rintro ⟨hs,⟨ha,hv⟩,hk⟩
      refine ⟨ha,hv,?_,by omega⟩
      simpa only [l,yStart_eq E d t a he (ht a ha), Nat.lt_succ_iff] using hk
    · rintro ⟨ha,hv,hk,hs⟩
      refine ⟨by have := ht a ha; omega,⟨ha,hv⟩,?_⟩
      simpa only [l,yStart_eq E d t a he (ht a ha), Nat.lt_succ_iff] using hk
  have hw (a : ℕ) (ha : a ∈ Ico L R) :
      (∑ q ∈ Ico (l a) (s.B+1), max 0 (width s h q (t-a) t)) = inner a + outer a := by
    obtain ⟨ha₀,_⟩ := mem_Ico.mp ha
    exact width_sum s h t (t-a) (l a) hh ((by dsimp [L] at ha₀; omega : t-a ≤ s.J).trans hj)
  have hsplit :
      (∑ a ∈ Ico L R, c a * ∑ q ∈ Ico (l a) (s.B+1), max 0 (width s h q (t-a) t)) =
        (∑ a ∈ Ico L R, c a * inner a) + (∑ a ∈ Ico L R, c a * outer a) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun a ha => by rw [hw a ha, mul_add])
  have normalize (x y : ℤ) : 4*(x*y) = (2*x)*(2*y) := by ring
  have hi :
      4*(∑ a ∈ Ico L R, c a * inner a) =
        ∑ a ∈ Ico L R₁, (seedQuad s v d).eval a * (innerQuad s h E d t).eval a := by
    rw [mul_sum]
    apply sum_clipped (fun a ha => ((hcore a).mp ha).1)
    · intro a ha hn
      have haR := (mem_Ico.mp ha).2
      by_cases hv : (a+d)*v ≤ s.U
      · have hl : k ≤ l a := by
          by_contra! hl
          exact (Nat.not_lt_of_ge hn) ((hcore a).mpr ⟨haR,hv,hl⟩)
        simp [inner, Ico_eq_empty_of_le hl]
      · simp [c, slots, hv]
    · intro a ha
      obtain ⟨haR,hv,hl⟩ := (hcore a).mp (mem_Ico.mp ha).2
      rw [normalize, seedQuad_eq s v d a hv, ← innerQuad_eq s h E d t a hh he (ht a haR) hl.le]
  have ho :
      240*(∑ a ∈ Ico L R, c a * outer a) =
        if k < s.B+1 then intervalProduct (seedQuad s v d) (outerQuad s h t) L R₂ else 0 := by
    by_cases hk : k < s.B+1
    · rw [ite_eq_left hk, ← intervalProduct_eq, show (240 : ℤ) = 60*4 by decide, mul_assoc, mul_sum]
      congr 1
      apply sum_clipped (fun a ha => ((hedge a).mp ha).1)
      · intro a ha hn
        have haR := (mem_Ico.mp ha).2
        by_cases hv : (a+d)*v ≤ s.U
        · have hbound : ¬(k < s.B+1 ∧ l a ≤ k ∧ edgeShift s h t ≤ t-a) :=
            fun ⟨_,hl,hs⟩ => (Nat.not_lt_of_ge hn) ((hedge a).mpr ⟨haR,hv,hl,hs⟩)
          simp only [outer, ite_eq_right hbound, mul_zero]
        · simp [c, slots, hv]
      · intro a ha
        obtain ⟨haR,hv,hl,hs⟩ := (hedge a).mp (mem_Ico.mp ha).2
        rw [normalize, seedQuad_eq s v d a hv, ← outerQuad_eq s h t a hh (ht a haR)]
        simp only [outer, hk, hl, hs, and_self, ite_true]
        rfl
    · simp [outer, hk]
  change _ = intervalProduct _ _ L R₁ + if k < s.B+1 then intervalProduct _ _ L R₂ else 0
  rw [hsplit, mul_add, ho, ← intervalProduct_eq (seedQuad s v d) (innerQuad s h E d t), ← hi]
  ring
theorem blockSurplus_eq (b : HighCore82258.Bank) (h E v : ℕ)
    (hh : h ≤ 131071) (hj : b.shape.J ≤ 131071-h) (he : 0 < E) :
    blockSurplus b.shape b.nodeRows b.poleMoment h E v = 240*surplus h b E v := by
  unfold blockSurplus scaledDebit surplus debit P1_7.debit
  rw [gain_eq_phases b.shape h E v hh he, mul_sub]
  push_cast
  congr 1
  unfold phase
  rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  rw [phaseBlock_eq _ _ _ _ _ _ hh hj he, phaseBlock_eq _ _ _ _ _ _ hh hj he]
end HighCore82258TerminalArithmetic
end
section
namespace HighCore82258TerminalArithmetic
open Finset
open K1_14 (Shape)
open HighCore82258 (agreement)
open P1_7_6 (intervalProduct_eq)
open P1_7_6_4 (Core corePrefix diagonalCore)
open P1_7_6 (lt_seedEnd)
def bankCore (s : Shape) (h E v d k : ℕ) : Core :=
  let D : ℤ := (131071-h : ℕ)
  let p : ℤ := (E-1 : ℕ)
  let w : ℤ := (E*d : ℕ)
  ⟨k,E*d,E-1,seedEnd s v d (orderEnd s E v),seedQuad s v d,
    ⟨(k : ℤ)-w,-p⟩, ⟨2*(s.m*agreement : ℕ)-D*(w+k-1),-2-D*p⟩,
    2-4*(h : ℤ)-D⟩
def outerPart (s : Shape) (h E v d t : ℕ) : ℤ :=
  if colEnd s h t < s.B+1 then
    intervalProduct (seedQuad s v d) (outerQuad s h t) (t-s.J)
      (outerEnd s h E v d t (min t (orderEnd s E v-1)+1))
  else 0
private theorem diagonal_eq (s : Shape) (h E v d t k : ℕ) (hk : colEnd s h t = k) :
    phaseBlock s h E v d t = 60*diagonalCore (bankCore s h E v d k) s.J t + outerPart s h E v d t := by
  let C := bankCore s h E v d k
  let R := min t (orderEnd s E v-1)+1
  change intervalProduct (seedQuad s v d) (innerQuad s h E d t) (t-s.J)
      (innerEnd s h E v d t R) + outerPart s h E v d t =
    60*diagonalCore C s.J t + outerPart s h E v d t
  rw [← intervalProduct_eq, diagonalCore, ← sum_filter]
  congr 2
  have hmem : Ico (t-s.J) (innerEnd s h E v d t R) =
      (range C.cap).filter (fun a => a ≤ t ∧ t < a+(s.J+1) ∧ t+(C.offset+C.step*a) < C.column) := by
    have hend : 0 < orderEnd s E v := by
      unfold orderEnd
      split
      · exact Nat.succ_pos _
      · exact lt_min (Nat.succ_pos _) (Nat.succ_pos _)
    ext a
    simp only [mem_Ico, mem_filter, mem_range, C, bankCore, innerEnd, lt_linearEnd, lt_seedEnd,
      hk, yStart, R]
    omega
  apply sum_congr hmem
  intro a _
  have ht : (innerQuad s h E d t).eval a = C.term a t := by
    simp only [C, bankCore, Core.term, P1_7_6_4.Line.at, innerQuad, hk, P1_7_6.Quad.eval_ofLines,
      widthOrigin, yStart, Nat.cast_add]
    ring
  rw [ht]
  rfl
private theorem colEnd_lt (s : Shape) (h t q : ℕ) :
    q < colEnd s h t ↔ q < s.B+1 ∧ 2*h*t+(131071-h)*q < s.m*agreement :=
  lt_linearEnd _ _ _ _ _
private theorem outer_sum (s : Shape) (h E v d l r k : ℕ) (hJ : s.J < 2*h)
    (hk : ∀ t ∈ Ico l r, colEnd s h t = k) :
    (∑ t ∈ Ico l r, outerPart s h E v d t) = if l < r then outerPart s h E v d l else 0 := by
  by_cases hl : l < r
  · rw [ite_eq_left hl]
    have hkl := hk l (mem_Ico.mpr ⟨le_rfl,hl⟩)
    apply sum_eq_single l
    · intro t ht hne
      have hat : l+1 ≤ t := by have := (mem_Ico.mp ht).1; omega
      have hkt := hk t ht
      unfold outerPart
      rw [hkt]
      split
      next hb =>
        have htop : s.m*agreement ≤ 2*h*l+(131071-h)*k := by
          by_contra! hpos
          exact (Nat.lt_irrefl _) (hkl ▸ (colEnd_lt s h l k).mpr ⟨hb,hpos⟩)
        have hstep := Nat.mul_le_mul_left (2*h) hat
        rw [Nat.mul_add, Nat.mul_one] at hstep
        have he : s.J < edgeShift s h t := by unfold edgeShift; rw [hkt]; omega
        have hz : outerEnd s h E v d t (min t (orderEnd s E v-1)+1) ≤ t-s.J :=
          (min_le_left _ _).trans (by omega)
        exact ite_eq_right (not_lt_of_ge hz)
      next => rfl
    · exact fun h => (h (mem_Ico.mpr ⟨le_rfl,hl⟩)).elim
  · simp [hl, Ico_eq_empty_of_le (Nat.le_of_not_gt hl)]
def groupValue (s : Shape) (h E v d l r k : ℕ) : ℤ :=
  if l < r then
    let C := bankCore s h E v d k
    corePrefix C s.J r - corePrefix C s.J l + 6*outerPart s h E v d l
  else 0
theorem groupValue_eq (s : Shape) (h E v d l r k : ℕ) (hJ : s.J < 2*h)
    (hk : ∀ t ∈ Ico l r, colEnd s h t = k) :
    groupValue s h E v d l r k = 6*(∑ t ∈ Ico l r, phaseBlock s h E v d t) := by
  unfold groupValue
  by_cases hl : l < r
  · rw [ite_eq_left hl]
    let C := bankCore s h E v d k
    change corePrefix C s.J r - corePrefix C s.J l + 6*outerPart s h E v d l = _
    have hs : (∑ t ∈ Ico l r, phaseBlock s h E v d t) =
        ∑ t ∈ Ico l r, (60*diagonalCore C s.J t + outerPart s h E v d t) :=
      sum_congr rfl fun t ht => diagonal_eq s h E v d t k (hk t ht)
    rw [hs, sum_add_distrib, ← mul_sum, outer_sum s h E v d l r k hJ hk, ite_eq_left hl]
    simp only [corePrefix, Core.prefix_eq, diagonalCore]
    rw [sum_Ico_eq_sub _ hl.le]
    ring
  · simp [hl, Ico_eq_empty_of_le (Nat.le_of_not_gt hl)]
end HighCore82258TerminalArithmetic
end
section
namespace HighCore82258TerminalArithmetic
open Finset
open K1_14 (Shape)
open HighCore82258 (agreement)
open P0_10_5 (Row scan)
open P0_10_5 (scan_sum)
def boundary (s : Shape) (h n i : ℕ) : ℕ :=
  if i = 0 then 0
  else linearEnd ((131071-h)*(s.B+1-i)) (2*h) (s.m*agreement) n
private theorem lt_boundary (s : Shape) (h n i t : ℕ) (hi : 0 < i) (hB : i ≤ s.B+1) :
    t < boundary s h n i ↔ t < n ∧ s.B+1-i < colEnd s h t := by
  have hb : s.B+1-i < s.B+1 := by omega
  simp only [boundary, ite_eq_right (Nat.ne_of_gt hi), colEnd, lt_linearEnd, hb, true_and, add_comm]
private theorem boundary_step (s : Shape) (h n i : ℕ) (hi : i+1 ≤ s.B+1) :
    boundary s h n i ≤ boundary s h n (i+1) := by
  by_cases hz : i = 0
  · simp [hz,boundary]
  by_contra! hn
  let t := boundary s h n (i+1)
  obtain ⟨ht,hk⟩ := (lt_boundary s h n i t (by omega) (by omega)).mp hn
  exact (Nat.lt_irrefl _) ((lt_boundary s h n (i+1) t (by omega) hi).mpr ⟨ht,by omega⟩)
private theorem group_column (s : Shape) (h n i t : ℕ) (hi : i+1 ≤ s.B+1)
    (ht : t ∈ Ico (boundary s h n i) (boundary s h n (i+1))) :
    colEnd s h t = s.B+1-i := by
  obtain ⟨hl,hr⟩ := mem_Ico.mp ht
  obtain ⟨htn,hq⟩ := (lt_boundary s h n (i+1) t (by omega) hi).mp hr
  have hu : colEnd s h t ≤ s.B+1-i := by
    by_contra! hh
    by_cases hz : i = 0
    · subst i
      have he : s.B+1 < colEnd s h t := by simpa using hh
      exact (Nat.lt_irrefl _) ((lt_linearEnd _ _ _ _ _).mp he).1
    · exact (not_lt_of_ge hl) ((lt_boundary s h n i t (by omega) (by omega)).mpr ⟨htn,hh⟩)
  omega
private theorem sum_groups (s : Shape) (h n count : ℕ) (hc : count ≤ s.B+1) (f : ℕ → ℤ) :
    (∑ i ∈ range count, ∑ t ∈ Ico (boundary s h n i) (boundary s h n (i+1)), f t) =
      ∑ t ∈ range (boundary s h n count), f t := by
  induction count with
  | zero => simp [boundary]
  | succ i ih =>
    rw [sum_range_succ, ih (by omega : i ≤ s.B+1), sum_range_add_sum_Ico f (boundary_step s h n i hc)]
def runValue (s : Shape) (h E v n i : ℕ) : ℤ :=
  let l := boundary s h n i
  let r := boundary s h n (i+1)
  let k := s.B+1-i
  groupValue s h E v 0 l r k - groupValue s h E v 1 l r k
def runRow (s : Shape) (h E v n i : ℕ) : Row :=
  ⟨true,runValue s h E v n i,runValue s (h+1) E v n i⟩
private theorem run_sum (s : Shape) (h E v n count : ℕ) (hc : count ≤ s.B+1)
    (hJ : s.J < 2*h) (hb : boundary s h n count = n) :
    (∑ i ∈ range count, runValue s h E v n i) =
      6*(∑ t ∈ range n, (phaseBlock s h E v 0 t - phaseBlock s h E v 1 t)) := by
  conv_rhs => rw [← hb, ← sum_groups s h n count hc, mul_sum]
  apply sum_congr rfl
  intro i hi
  have hc' : i+1 ≤ s.B+1 := Nat.le_trans (mem_range.mp hi) hc
  have hk := fun t ht => group_column s h n i t hc' ht
  rw [runValue, groupValue_eq _ _ _ _ _ _ _ _ hJ hk,
    groupValue_eq _ _ _ _ _ _ _ _ hJ hk, sum_sub_distrib]
  ring
theorem checks_of_runs (s : Shape) (N P h E v n count : ℕ) (left next cost costNext : ℤ)
    (hn : s.J+orderEnd s E v = n) (hc : count ≤ s.B+1) (hJ : s.J < 2*h)
    (hb : boundary s h n count = n) (hbNext : boundary s (h+1) n count = n)
    (hs : scan (runRow s h E v n) 0 count = ⟨true,left,next⟩)
    (hl : 6*scaledDebit s N P h = cost) (hr : 6*scaledDebit s N P (h+1) = costNext)
    (hp : cost < left) (hd : left+costNext ≤ next+cost) :
    BlockChecks s N P h E v := by
  have hbase := scan_sum (runRow s h E v n) 0 count false
  have hnext := scan_sum (runRow s h E v n) 0 count true
  rw [hs] at hbase hnext
  simp only [Bool.false_eq_true, ite_false, ite_true, Nat.zero_add, runRow] at hbase hnext
  rw [run_sum s h E v n count hc hJ hb] at hbase
  rw [run_sum s (h+1) E v n count hc (by omega) hbNext] at hnext
  unfold BlockChecks blockSurplus
  rw [hn]
  omega
end HighCore82258TerminalArithmetic
end
section
namespace HighCore82258TerminalArithmetic
open K1_14 (Shape)
open P0_10_5 (Row scan joinRows)
inductive Parts (f : ℕ → Row) (last : ℕ) : ℕ → ℕ → ℤ → ℤ → Prop
  | final {a : ℕ} {gain next : ℤ} :
      scan f a last = ⟨true, gain, next⟩ → Parts f last a last gain next
  | more {a count : ℕ} {gain next restGain restNext : ℤ} :
      scan f a 16 = ⟨true, gain, next⟩ → Parts f last (a+16) count restGain restNext →
      Parts f last a (16+count) (gain+restGain) (next+restNext)
theorem Parts.scan_eq {f : ℕ → Row} {last a count : ℕ} {gain next : ℤ}
    (parts : Parts f last a count gain next) : scan f a count = ⟨true, gain, next⟩ := by
  induction parts with
  | final h => exact h
  | @more a count gain next restGain restNext h _ ih =>
    exact joinRows a 16 count _ _ h ih rfl
theorem certify {s : Shape} {N P h E v n last count : ℕ}
    {gain next cost costNext : ℤ}
    (parts : Parts (runRow s h E v n) last 0 count gain next)
    (hn : s.J+orderEnd s E v = n) (hc : count ≤ s.B+1) (hJ : s.J < 2*h)
    (hb : boundary s h n count = n) (hbNext : boundary s (h+1) n count = n)
    (hl : 6*scaledDebit s N P h = cost) (hr : 6*scaledDebit s N P (h+1) = costNext)
    (hp : cost < gain) (hd : gain+costNext ≤ next+cost) :
    BlockChecks s N P h E v :=
  checks_of_runs s N P h E v n count gain next cost costNext
    hn hc hJ hb hbNext parts.scan_eq hl hr hp hd
end HighCore82258TerminalArithmetic
end

end Merged_HighCore82258TerminalArithmetic

-- merged module HighCore82258Terminal
section Merged_HighCore82258Terminal

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82258Terminal

open HighCore82258
open HighCore82258TerminalArithmetic
open K1_14 (Shape)

private def GradeChecks (t : Bank) (h : ℕ) : ℕ → List Grade → Prop
  | _, [] => True
  | e, g :: gs =>
    BlockChecks ({t.shape with U := g.slots}) t.nodeRows t.poleMoment h e (g.seedCap+1) ∧
      GradeChecks t h (e+1) gs

private theorem grade_at (t : Bank) (h : ℕ) (gs : List Grade) (e : ℕ)
    (hc : GradeChecks t h e gs) (i : Fin gs.length) :
    BlockChecks {t.shape with U := (gs.get i).slots} t.nodeRows t.poleMoment h (i.val+e) ((gs.get i).seedCap+1) := by
  induction gs generalizing e with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    rcases i with ⟨_ | j, hj⟩
    · simpa [GradeChecks] using hc.1
    · have h' := ih (e+1) hc.2 ⟨j, by simpa using hj⟩
      simpa only [List.get_cons_succ, Nat.succ_add, Nat.add_succ] using h'

set_option quotPrecheck false
local notation "last!" l "," r => Parts.final (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel))
local notation "more!" l "," r "," p => Parts.more (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel)) p
local notation "block!" nn "," k "," l "," r "," p => certify
  (n := nn) (last := k) (cost := l) (costNext := r) p
  (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide) (by decide)

namespace h2395
local notation "S" u => (⟨7550,10506,2218,u⟩ : Shape)
local notation "N" => 0x2cfea55aa80000
local notation "P" => 0x129e297a45c0c
private theorem r0 : BlockChecks (S 180000) N P 2536 27 0 :=
  block! 2608,12,0x3bc0bd135a821094f82045800,0x3bc0bf52a131d269f4439bf00,(more! 0x32aa532a25b41e6fd81f3dae0,0x32b052fea7d109e80717fc900,(more! 0x860bf7ce67370c53504dc5a0,0x85d697777d266dac22e40fc0,(last! 0xb5b0c05effeda7f253290c0,0xb31c31071b0f2e9946f8e40)))
private theorem r1 : BlockChecks (S 172349) N P 2536 1 339 :=
  block! 2727,1,0x36c8e62f2113c445e214b5000,0x36c8e855f3f9e7c3fbffd0200,(more! 0x2d3d4346c8cda08a5eb03cc20,0x2d42c56164964bc01333f0760,(more! 0x7de571ec27b1e6635b8ac1a0,0x7dc205d888f6b8a770fb3560,(more! 0x1ad4b539d8cf3c8b04204d40,0x1aa13bb300d07937f6b5a4a0,(last! 0x75fc8c8fca550176340,0x49a5106669ec5a6c500))))
private theorem r2 : BlockChecks (S 173304) N P 2536 2 334 :=
  block! 2737,1,0x3764a2c9e149d49830b5e9800,0x3764a4f3c1892d4f8b810e700,(more! 0x2dc6bc78609897232cde1da00,0x2dcc4e7abaab8fdaf472622a0,(more! 0x7f286d5ac159c540f434d480,0x7f03e53cc3e97c6df3727560,(more! 0x1ab593c576a7bc8eac0a2780,0x1a8248a691eb5b49e7638fe0,(last! 0x63fbd0ffa1d82efb6ac0,0x53a6087148188bc8f500))))
private theorem r3 : BlockChecks (S 179574) N P 2536 3 328 :=
  block! 2766,2,0x3b78790cf33d2be596ee7e800,0x3b787b4add63063d0c3eea900,(more! 0x311253b5b651c5cd511d65800,0x311850c7152d740a6e1c0f080,(more! 0x88b5261c0c29b5a315a88d00,0x888de3bfd77bfb252b22c780,(more! 0x1da72b88f463f991fea3ad80,0x1d7052c494f643d6f10a4880,(last! 0x603cf5ccfe3cfc8b83680,0x5a06ff47f4328dc60cd00))))
private theorem r4 : BlockChecks (S 177387) N P 2536 4 323 :=
  block! 2768,2,0x3a082b3dd649e3390e55d2000,0x3a082d74c31b8ab75a4e99400,(more! 0x2ffe0ae7d226b1390bec45a00,0x3003e212b0099eb56868ce2a0,(more! 0x85105d1a989629e4eee61480,0x84e8e2413d48a5b03ed56f00,(more! 0x1b8c1c3a2be2b0048cd1be40,0x1b57c8193a39cc50dd8eb940,(last! 0x58c12eb72defd49ab0c20,0x53331329c32b0655677c0))))
private theorem r5 : BlockChecks (S 175478) N P 2536 5 318 :=
  block! 2770,2,0x38ca5e388fbb01cbe5967e800,0x38ca606962abb22a4f5fea900,(more! 0x2f10819d6e9b860b69a4eb480,0x2f163813f4cd65415b825d700,(more! 0x81e77af28432e29e6f395ac0,0x81bfbe9907d7d7b85c93eda0,(more! 0x19b0ffa70e3f1c5514dbf940,0x197ee9f2e69e3891232b3900,(last! 0x54f22959740e37c5e33c0,0x4fde4fbfa3aaa52b58b40))))
private theorem r6 : BlockChecks (S 176977) N P 2536 6 312 :=
  block! 2786,3,0x39c39fd94e6e80bfbaf563000,0x39c3a20eebcd75ea7926c6e00,(more! 0x2fe7ec148d7532f9cc6202b40,0x2fedbc05d0f440705df2f3de0,(more! 0x840603a519b2f67193f89e40,0x83dceee6f1fe060ffce1abc0,(more! 0x19abdd8f42ca39c06fa2bf40,0x1979ac7b50c8e9a22aa2aaa0,(last! 0x95b27ebcaa2e24c9fb8c0,0x8eb43b17e39e12c0fd620))))
private theorem r7 : BlockChecks (S 177384) N P 2536 7 306 :=
  block! 2798,4,0x3a07aab2d9f19395ee5c91800,0x3a07ace9c44ee11c5ba32f700,(more! 0x302f0fb7e300271b9a737ddc0,0x3034e68a1f9f5dfc8964799a0,(more! 0x8474fc4999624509681ac9c0,0x844aea6df194acbf2725a620,(more! 0x19088be514ee06512ccee0a0,0x18d6f872b431bb64eae0d120,(last! 0xc2784dca6c56ef53ae8e0,0xbaa7b1c0ea81d0fbef200))))
private theorem r8 : BlockChecks (S 176903) N P 2536 8 300 :=
  block! 2808,4,0x39b74514b7870839b6612c000,0x39b7474a185aa78254bd3f800,(more! 0x2fff1aae1ffb57e23d0e8d340,0x3004e92540101c85987a07ec0,(more! 0x838444e962a51dcc4237b080,0x83598971eb4839175e3f8940,(more! 0x17f14d83ab6fac80c7a9bac0,0x17c0e53c3571489bb1fe46c0,(last! 0xd13ff0ed55c3bd7f57440,0xc9964d8c09eee6788ffc0))))
private theorem r9 : BlockChecks (S 178309) N P 2536 9 293 :=
  block! 2827,5,0x3aa2e3b09ac5b8a55e2141000,0x3aa2e5ea79f0b7b659524ba00,(more! 0x30ce35c5132a7adc405338f00,0x30d41c49dbb2b80d357d4bac0,(more! 0x85809f057829ad6a2777b100,0x85548c2fd9bc36fef2e30d60,(more! 0x17b9a094ea188258210c9b80,0x17891fea16abe2f879479660,(last! 0x109f1f9ab14be9e81e2880,0x1018626f376a3f55730980))))
private theorem r10 : BlockChecks (S 178543) N P 2536 10 286 :=
  block! 2843,5,0x3aca48ce2325d0c4d862e8000,0x3aca4b08c1c4395baddc89000,(more! 0x30ff8fe0930cfbe330e38f000,0x31057a4f7c1d04d2cac568000,(more! 0x85ac72404b8828da250bb540,0x857f783c0df68eb6bc643060,(more! 0x16ee3aabf366b63a359e3200,0x16be5bc6819b1bf94fbc6100,(last! 0x10e1f16409e58fd13f5140,0x1062ce61d837d4241a4ea0))))
private theorem r11 : BlockChecks (S 179864) N P 2536 11 278 :=
  block! 2865,6,0x3ba9a6345a4e00436abcd9800,0x3ba9a87331b87e33a1fe34700,(more! 0x31c6a42ac974c9435a25cfbc0,0x31cca55ec696bc049a2a1ea20,(more! 0x878af186f3ebb222c42dc680,0x875ca581abb1c589f01eeee0,(more! 0x16940902cde1efc42d111a60,0x16640e96e30609e7557bd460,(last! 0x11261affcf05b424a225c0,0x10ace102e711d3b3630300))))
private theorem r12 : BlockChecks (S 179838) N P 2536 12 270 :=
  block! 2885,7,0x3ba53cb17fb1429ca0dcaa800,0x3ba53ef041d60a28a36b4a100,(more! 0x31d529a42fc8cc35ac1b6f540,0x31db2a3d3b352eda027bd7260,(more! 0x87507539f5c485a062be5cc0,0x872164200520d1846e3ee420,(more! 0x15a33fd2c81518b4d82056e0,0x1573fcf334469dde1f5a57a0,(last! 0xd7bdfb510b49272bb50c0,0xd19c342183215e475d1c0))))
private theorem r13 : BlockChecks (S 178760) N P 2536 13 262 :=
  block! 2901,8,0x3aeedd0d67cc19a33bf021800,0x3aeedf48b7f54343531619700,(more! 0x315218500ab4979b201e73340,0x3158060c6d5613e2e9d4852a0,(more! 0x8574b7dca63b43ebabe69880,0x85455a1e526271bf22971940,(more! 0x144f7c38e909f18e21f97520,0x1421911d41a5442d2e2a7fa0,(last! 0x817d4dac31b4c11812bc0,0x7d489b0bdb87492deb640))))
private theorem r14 : BlockChecks (S 179370) N P 2536 14 252 :=
  block! 2930,9,0x3b55ed64e68ef3619bd95c800,0x3b55efa229cce7e1e9d6cf500,(more! 0x31b7ac81cf277587be9428c40,0x31bda49e59129a9d19779fcc0,(more! 0x863a80bdd05c00b845291600,0x860a2e2255276940ef194280,(more! 0x13a5930ada9dd3455be01bc0,0x1377e0276aef0e4c65a32800,(last! 0x3fa8f4b04c5472cea9500,0x3d00f9389119d757a46c0))))
private theorem r15 : BlockChecks (S 179648) N P 2536 15 241 :=
  block! 2919,8,0x3b850386bea4500106e2b5800,0x3b8505c4e555803a9c0871f00,(more! 0x31ef050350d4130606e0562e0,0x31f501bb31ff98fe51f5a3a40,(more! 0x867ea9617502ee22ad2b6880,0x864d91614b40251ca56dc200,(more! 0x12e032b5559cbc151233f940,0x12b2e40da91164c866c12280,(last! 0x10c44c6c01091221c3080,0xfa337981f0aba4923960))))
private theorem r16 : BlockChecks (S 179554) N P 2536 16 229 :=
  block! 2875,7,0x3b751594d19c683d3b50d0800,0x3b7517d2ab6540203952d3d00,(more! 0x31f1cdf27076794b016c49500,0x31f7c8cb8bff9414e16095ea0,(more! 0x8631d43c208f94b3fc4398c0,0x86002dfe2e18dea951f7c560,(more! 0x12029cfda3266852143f4660,0x11d5e9fbc9224cec163d9fc0,(last! 0x90c6d728b261b6efc00,0x726cf10147678557840))))
private theorem r17 : BlockChecks (S 179916) N P 2536 17 215 :=
  block! 2837,5,0x3bb279b75f5a0fe4113d37800,0x3bb27bf6614ffa9cb1e409300,(more! 0x32334c9c0b40215ea2b66a320,0x32394d7d8f663ebbdea849360,(more! 0x869dcb14119e96e3b24d6f80,0x866b731461ec1ecefaf18380,(more! 0x115506d0eade86c78cfaf6e0,0x1128a46cef9fffb3cf498420,(last! 0x0,0x0))))
private theorem r18 : BlockChecks (S 179883) N P 2536 18 200 :=
  block! 2802,4,0x3bacdfb83d10572fc26772000,0x3bace1f724066441d1667d400,(more! 0x323cb89f980e6c0f0aa52dd00,0x3242b8abc6ba44f23de953e40,(more! 0x86702ff047949c297df5fc40,0x863d603a83f56ed2e4a9ee00,(more! 0x109241d6910c80e9d2ee9cc0,0x1066645d736b4ec75dcc15c0,(last! 0x0,0x0))))
private theorem r19 : BlockChecks (S 179596) N P 2536 19 184 :=
  block! 2771,3,0x3b7c3360d78e143f576257800,0x3b7c359ed3b3d7b083229d300,(more! 0x32219e84ab31f5d4945facc80,0x322799532b9cd5752b551dae0,(more! 0x85e13d4bcafd50c12ce60f40,0x85ae1fa2865bba6e216bd1a0,(more! 0xfc81093626a5800ee8d11e0,0xf9cd3e0318a48a4c463d940,(last! 0x0,0x0))))
private theorem r20 : BlockChecks (S 179633) N P 2536 20 166 :=
  block! 2744,1,0x3b8278a5bdbf006f65f473000,0x3b827ae3d82a6ed1a19f60e00,(more! 0x323308a57e80b161051be1ba0,0x323903d5c7f62999d7ac9c640,(more! 0x85d6a402df42b7ec617cc6a0,0x85a320d48264e56cbf9837a0,(more! 0xf205c4e17fe6a95e04fee00,0xef57f234a81fb725faebba0,(last! 0x0,0x0))))
private theorem r21 : BlockChecks (S 179890) N P 2536 21 146 :=
  block! 2719,16,0x3bae0fe0fa30ef5b3add08800,0x3bae121fe6e123afa6d11ed00,(more! 0x326299ce2235d3591eae2be00,0x32689931c9eb77d44c926bc60,(more! 0x8627000a775589b133d0bd60,0x85f30a57cf893699d2e77760,(last! 0xe90613e5bad6aef7a09a940,0xe65b44b10597f2a54dbaa80)))
private theorem r22 : BlockChecks (S 179925) N P 2536 22 125 :=
  block! 2696,16,0x3bb400da166403740418f9000,0x3bb403191fb6fc1440d646a00,(more! 0x32724bdb85e541c160a3aef40,0x32784b9a121af1c089da3c680,(more! 0x8622651ebc0c4e95cce098e0,0x85ee1fb1980830e4a7fb7b40,(last! 0xdf8eb0c1413338d43daca40,0xdce88436986bb3a546480c0)))
private theorem r23 : BlockChecks (S 179808) N P 2536 23 103 :=
  block! 2675,15,0x3ba0259d2fdefd13cbd025800,0x3ba027dbd97840f11b6927f00,(more! 0x326be9425d2e130dea29db9a0,0x3271e6ba7fa5289c6e58fece0,(more! 0x85e46b96b24e463e79f6e800,0x85aff02de78a0051cb47bca0,(last! 0xd5f5a3de293cd4241bbd020,0xd35516affcd27b76ba85b40)))
private theorem r24 : BlockChecks (S 179897) N P 2536 24 79 :=
  block! 2656,14,0x3baf400cbe6c340265629f000,0x3baf424bb0d68f992e4bc0600,(more! 0x3281f1f74938d959f99a7f6c0,0x3287f0bd3a45df93a2d779920,(more! 0x85fb748f8fa8222eccf75fa0,0x85c6b470481f22148cd19b60,(last! 0xcd96d154625cc8854dffa20,0xcaf946c07517b52a91ee380)))
private theorem r25 : BlockChecks (S 179864) N P 2536 25 54 :=
  block! 2639,13,0x3ba9a6345a4e00436abcd9800,0x3ba9a87331b87e33a1fe34700,(more! 0x328637752ae2b0a45fc6b75a0,0x328c356d41e64fe5231ffb6c0,(more! 0x85e4b42b0ca4291a83e2baa0,0x85afc375c3d5037a6d23dfa0,(last! 0xc52383eb03909f4c808ebe0,0xc289ce9b12266d50ce52aa0)))
private theorem r26 : BlockChecks (S 180000) N P 2536 26 27 :=
  block! 2623,13,0x3bc0bd135a821094f82045800,0x3bc0bf52a131d269f4439bf00,(more! 0x32a1db7a4843f931689bacaa0,0x32a7db946a242ca9c12cd66e0,(more! 0x86140b405ae227fc14091040,0x85dedd78c2b3610c41b5a7e0,(last! 0xbda0ec69bd9321766644e40,0xbb08ede85a2e27e939813e0)))
theorem none : BlockChecks (terminal .h2395).shape (terminal .h2395).nodeRows
    (terminal .h2395).poleMoment (start .h2395) (threshold .h2395 Option.none) 0 := r0
theorem all : GradeChecks (terminal .h2395) (start .h2395) 1 (grades .h2395) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,trivial⟩
end h2395

namespace h7773
local notation "S" u => (⟨124,173,32,u⟩ : Shape)
local notation "N" => 0xc4fd80000
local notation "P" => 0x15c66e5
private theorem r0 : BlockChecks (S 900) N P 7773 8 0 :=
  block! 54,1,0x1b3cc3c11c249e440,0x1b3cc71f4a35e9580,(last! 0x1b44034829a1c5c40,0x1b440b0132a3efce0)
private theorem r1 : BlockChecks (S 821) N P 7773 1 27 :=
  block! 63,1,0x16b4691bfccae8780,0x16b46c2e9238bb500,(last! 0x16b469e60cf39a680,0x16b47065d051b2120)
private theorem r2 : BlockChecks (S 771) N P 7773 2 26 :=
  block! 62,1,0x140c8975326695d00,0x140c8c57ef5305e00,(last! 0x140c907ab565f9380,0x140c96636d8c3b740)
private theorem r3 : BlockChecks (S 796) N P 7773 3 24 :=
  block! 66,2,0x155b30a8b220bf240,0x155b33a35b4de0980,(last! 0x155b34cc89b45ea60,0x155b3afff981a4da0)
private theorem r4 : BlockChecks (S 855) N P 7773 4 21 :=
  block! 73,3,0x189ade77390253e00,0x189ae1aa576bf9400,(last! 0x189ae1c092142b7e0,0x189ae8aae50a3f6c0)
private theorem r5 : BlockChecks (S 879) N P 7773 5 17 :=
  block! 67,2,0x19fe04ee09e5aec00,0x19fe08381f97ac800,(last! 0x19fe0de212de406c0,0x19fe1519ad30c4f80)
private theorem r6 : BlockChecks (S 900) N P 7773 6 11 :=
  block! 61,1,0x1b3cc3c11c249e440,0x1b3cc71f4a35e9580,(last! 0x1b3cccb63cd44c040,0x1b3cd43274f8314e0)
private theorem r7 : BlockChecks (S 899) N P 7773 7 4 :=
  block! 57,1,0x1b2d6acfe1cdcfd00,0x1b2d6e2d1ae6c1e00,(last! 0x1b2d770f87d996c00,0x1b2d7e8890a242a40)
theorem none : BlockChecks (terminal .h7773).shape (terminal .h7773).nodeRows
    (terminal .h7773).poleMoment (start .h7773) (threshold .h7773 Option.none) 0 := r0
theorem all : GradeChecks (terminal .h7773) (start .h7773) 1 (grades .h7773) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,trivial⟩
end h7773

set_option maxHeartbeats 800000

private theorem checks (b : Band) (hb : b ≠ .h2367) (x : Test b) :
    let t := tested b x
    BlockChecks t.shape t.nodeRows t.poleMoment (start b) (threshold b x) (seedThreshold b x) := by
  have hn : BlockChecks (terminal b).shape (terminal b).nodeRows (terminal b).poleMoment
      (start b) (threshold b Option.none) 0 := by
    cases b with
    | h2367 => exact False.elim (hb rfl)
    | h2395 => exact h2395.none
    | h7773 => exact h7773.none
  have hc : GradeChecks (terminal b) (start b) 1 (grades b) := by
    cases b with
    | h2367 => exact False.elim (hb rfl)
    | h2395 => exact h2395.all
    | h7773 => exact h7773.all
  cases x with
  | none => exact hn
  | some i => exact grade_at _ _ _ _ hc i


end HighCore82258Terminal

end Merged_HighCore82258Terminal

end Merged6967_HighCore82258Terminal
