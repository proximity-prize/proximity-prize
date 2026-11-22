import ProximityPrize.SubmissionLower.Low53At2389Price
import ProximityPrize.SubmissionLower.PuncturedCompactPrimaryLayers
import ProximityPrize.SubmissionLower.PrimaryTaperFamily

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000
namespace Low53At2389Order
noncomputable section

open Polynomial
open P3 (I K node)
open K1_13 (Geom embed extend Row shape InBox indexDegree OrderAt Contact)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open Low53At2389Price (agreement physicalDegree primaryBox primaryCutoff layerWidth layerNeed
  Messages ProperCut LayerBudget TrueWeightLE)
open scoped BigOperators Polynomial
open private exists_fresh specialization_bounds sum_by_layer
  from ProximityPrize.SubmissionLower.PortLowBase
open private PuncturedCompactPrimary.exists_availability
  from ProximityPrize.SubmissionLower.PuncturedCompactPrimaryLayers

export Low53At2389Price (agreement physicalDegree primaryBox primaryCutoff layerWidth layerNeed
  Messages ProperCut LayerBudget TrueWeightLE)

abbrev sourceRank : ℕ := layerWidth * (layerNeed - 1) + 1

theorem certified_layers : layerNeed ≤ sourceRank / layerWidth + 1 := by decide

abbrev requiredOrder (T : ℕ) :=
  PuncturedCompactPrimary.requiredOrder agreement physicalDegree T

def BankRow (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) primaryBox ∧ TrueWeightLE P T ∧ PrimaryTaper.JetsBounded P ∧ Contact w P

def PrimaryRank (w : I → K) : Prop :=
  ∃ e : Fin sourceRank → Row 4, LinearIndependent Geom e ∧
    ∀ i, BankRow w primaryCutoff (e i)

private theorem contact_empty (w : I → K) (P : Row 4) :
    PuncturedCompactPrimary.Contact w ∅ P ↔ Contact w P := by
  simp only [PuncturedCompactPrimary.Contact, Contact, Finset.notMem_empty, not_false_eq_true, true_implies]

private theorem bank_empty {w : I → K} {T : ℕ} {P : Row 4} :
    PuncturedCompactPrimary.BankRow physicalDegree w ∅ T P ↔ BankRow w T P := by
  unfold PuncturedCompactPrimary.BankRow BankRow
  rw [contact_empty]
  rfl

theorem symbol_families (w : I → K) (x : Geom) (hr : PrimaryRank w)
    (hx : ∀ i : I, x ≠ embed (node i)) :
    ∃ r : ℕ → ℕ, sourceRank ≤ ∑ T ∈ Finset.range (primaryCutoff + 1), r T ∧
      ∀ T ≤ primaryCutoff, ∃ e : Fin (r T) → Row 4,
        (∀ i, BankRow w T (e i)) ∧
        LinearIndependent Geom (fun i => symbolAt x (e i)) := by
  obtain ⟨f,hf,hmem⟩ := hr
  obtain ⟨r,hr,h⟩ := PuncturedCompactPrimary.symbol_layers physicalDegree w ∅ x hx
    ⟨f,hf,fun i => bank_empty.mpr (hmem i)⟩
  refine ⟨r,hr,fun T hT => ?_⟩
  obtain ⟨e,he,hei⟩ := h T hT
  exact ⟨e,fun i => bank_empty.mp (he i),hei⟩

theorem order_of_contact (w : I → K) (P : Row 4) {T : ℕ} (hT : T ≤ primaryCutoff)
    (hw : TrueWeightLE P T) (hc : Contact w P) {S : Geom[X]} (hS : S.natDegree ≤ physicalDegree)
    {H : Finset I} (hH : agreement ≤ H.card)
    (hits : ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) :
    OrderAt P S (requiredOrder T) :=
  PuncturedCompactPrimary.order_of_contact (by decide : 0 < agreement)
    (by decide : 3 < physicalDegree) (by decide) w ∅ P hT hw
    ((contact_empty w P).mpr hc) hS hH (by simp) hits

theorem messages_of_family {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt agreement M Γ) (hh : M.overhead ≤ 2389) :
    Messages M.word Γ F.scalar := by
  refine ⟨F.distinct, ?_, ?_⟩
  · intro γ hγ
    obtain hz | hd := (F.mark γ hγ).scalar_degree
    · simp [hz]
    · change ((F.scalar γ).natDegree : ℤ) ≤ (131072 : ℤ) - 1 + M.overhead at hd
      change (F.scalar γ).natDegree ≤ 133460
      omega
  · intro γ hγ
    let m := F.mark γ hγ
    exact ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩

/-- Compatible proper cuts from a single punctured family of independent symbols. -/
theorem proper_layers_of_rank {w : I → K} {Γ : Finset K} {s : K → K[X]} {n : ℕ}
    {f : Fin n → Row 4} (hm : Messages w Γ s) (hprimary : PrimaryRank w)
    (hirr : ∀ i, Irreducible (f i)) (hpos : ∀ i, 0 < (shape (f i)).t)
    (htop : ∀ i, (shape (f i)).t < K1.p)
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) :
    ∃ l : Fin n → ℕ, LayerBudget (fun i => shape (f i)) l ∧
      ∀ i, 0 < l i → ProperCut (f i) Γ s (l i) := by
  classical
  let hmsg : PuncturedCompactPrimary.Messages agreement physicalDegree w Γ s ∅ :=
    ⟨hm.degree, fun γ hγ => by
      obtain ⟨H,hH,hh⟩ := hm.hits γ hγ
      exact ⟨H,hH,by simp,hh⟩⟩
  choose l hl hcut using fun i => PuncturedCompactPrimary.exists_availability
    (by decide) (by decide) (by decide) hmsg (hirr i) (hpos i) (htop i)
  obtain ⟨x,hx,hsup⟩ := exists_fresh f
  obtain ⟨r,hrank,hfamilies⟩ := symbol_families w x hprimary hx
  have hnz : ∀ i, symbolAt x (f i) ≠ 0 := by
    intro i hz
    have hzero := hsup i
    rw [hz, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at hzero
    exact (hirr i).ne_zero hzero
  let cost (k : ℕ) :=
    Low53At2389Price.remaining (∑ i, (k + 1 - l i) * (shape (f i)).b)
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
        exact hl j T hT (e i) (bank_empty.mpr (he i))
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
    have hs : r T ≤ Low53At2389Price.symbolCount :=
      PrimaryTaper.symbol_rank x e (fun i => (he i).2.2.1) hei
    dsimp only [cost, Low53At2389Price.remaining]
    apply le_min hs
    have hreq : PuncturedCompactPrimary.requiredOrder agreement physicalDegree T =
        (primaryCutoff - T) / layerWidth + 1 := rfl
    simpa only [a, requiredOrder, hreq, hb, hj] using hbound
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

#print axioms proper_layers_of_rank
end
end Low53At2389Order
