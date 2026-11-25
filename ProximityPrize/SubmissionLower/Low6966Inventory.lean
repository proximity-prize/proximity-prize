import ProximityPrize.SubmissionLower.R6960Low6960SurfaceLinearFour
import ProximityPrize.SubmissionLower.GoldBranch6N8
import ProximityPrize.SubmissionLower.Final50Price
import ProximityPrize.SubmissionLower.KoalaRetainedCut
import ProximityPrize.SubmissionLower.R6960Anchor6966
import ProximityPrize.SubmissionLower.Low6966Order
import ProximityPrize.SubmissionLower.Low6966Retained

set_option Elab.async false











-- merged module R6960Low6966Inventory
section Merged_R6960Low6966Inventory
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
namespace LowProfile6966
noncomputable section
open Finset Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K I node)
open K1_13 (Geom extend Row Shape shape InBox atJet indexDegree OnFactor)
open K1_13_1 (anchorLead anchorLead_ne indexDegree_eq)
open Final50Price (ActiveFits)
open Final50GeoCover (activeDegree activeFits_iff)
open K1_13_1 (coeff_flatten anchorLead_term index_bounds)
open scoped BigOperators Polynomial Classical
abbrev anchorCutoff : ℕ := 106*agreement-1+58
def fullCap (top : ℕ) : Shape := ⟨142, 58, top⟩
def Fits (top : ℕ) {n : ℕ} (a : Fin n → Shape) : Prop :=
  (∀ i, K1_13_8.Valid (a i)) ∧ (∑ i, (a i).b) ≤ 142 ∧ (∑ i, (a i).j) ≤ 58 ∧
    (∑ i, (a i).t) ≤ top
def LowerRow (top : ℕ) (g : Row 3) : Prop :=
  g≠0 ∧ g.totalDegree≤142-top ∧ indexDegree g≤58-3*top ∧ TrueWeightLE g anchorCutoff
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0<(shape f).t ∧ InBox (shape f) (fullCap 15) ∧ TrueWeightLE f anchorCutoff
theorem trueWeight_iff {n D : ℕ} (P : Row n) :
    TrueWeightLE P D ↔
      ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).weightedTotalDegree
        (fun v => v.elim 1 (fun i => physicalDegree - i.val)) ≤ D := by
  classical
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  constructor
  · intro h u hu
    have hc : (P.coeff u.some).coeff (u none) ≠ 0 := by
      rw [← coeff_flatten, Finsupp.optionElim_some]
      exact MvPolynomial.mem_support_iff.mp hu
    have hm : u.some ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr (fun hz => hc (by simp [hz]))
    have hi := Polynomial.le_natDegree_of_ne_zero hc
    rw [← Finsupp.optionElim_some u, Finsupp.weight_optionElim, one_mul]
    apply (Nat.add_le_add_right hi _).trans
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using h _ hm
  · intro h m hm
    let d := (P.coeff m).natDegree
    have hc : (P.coeff m).coeff d ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    have hu : m.optionElim d ∈ ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).support :=
      MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten])
    have hb := h _ hu
    rw [Finsupp.weight_optionElim, one_mul] at hb
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hb
theorem differentialWeight_eq : differentialWeight (d := 3) physicalDegree =
    fun v => v.elim 1 (fun i => physicalDegree - i.val) := by
  funext v
  cases v <;> rfl
section FactorCover
open MvPolynomial UniqueFactorizationMonoid
theorem lower_of_anchor (P : Row 4) (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨142, 58, 15⟩) (hw : TrueWeightLE P anchorCutoff) :
    LowerRow (shape P).t (anchorLead P) := by
  refine ⟨anchorLead_ne hP, ?_, ?_, ?_⟩
  · have hb := (Euler50GeoLead.lead_degree P hP).trans hbox.1
    change (anchorLead P).totalDegree + (shape P).t ≤ 142 at hb
    change (anchorLead P).totalDegree ≤ 142 - (shape P).t
    omega
  · have hj := (Euler50GeoLead.lead_index P hP).trans hbox.2.1
    change indexDegree (anchorLead P) + 3 * (shape P).t ≤ 58 at hj
    change indexDegree (anchorLead P) ≤ 58 - 3 * (shape P).t
    omega
  · intro m hm
    obtain ⟨u, hu, hc, h⟩ := anchorLead_term P m hm
    have hle := h (fun i => physicalDegree - i.val)
    rw [← hc]
    apply (Nat.add_le_add_left _ _).trans (hw u hu)
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm, Fin.val_castSucc] using hle
theorem factor_small {P f : Row 4} (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨142, 58, 15⟩) (hw : TrueWeightLE P anchorCutoff)
    (hf : Irreducible f) (ht : 0 < (shape f).t) (hd : f ∣ P) : SmallFactor f := by
  refine ⟨hf, ht, ⟨?_, ?_, ?_⟩, ?_⟩
  · have h := weightedTotalDegree_le_of_dvd (1 : Fin 4 → ℕ) hd hP
    rw [weightedTotalDegree_one, weightedTotalDegree_one] at h
    exact h.trans hbox.1
  · have h := weightedTotalDegree_le_of_dvd (fun i => i.val) hd hP
    rw [← indexDegree_eq, ← indexDegree_eq] at h
    exact h.trans hbox.2.1
  · have h := weightedTotalDegree_le_of_dvd (Pi.single (3 : Fin 4) 1) hd hP
    simp only [weightedTotalDegree_piSingle] at h
    exact h.trans hbox.2.2
  · let e := MvPolynomial.optionEquivRight Geom (Fin 4)
    have hd' : e.symm f ∣ e.symm P := _root_.map_dvd e.symm hd
    have hP' : e.symm P ≠ 0 := fun h => hP (e.symm.injective (h.trans (map_zero _).symm))
    exact (trueWeight_iff f).mpr
      ((weightedTotalDegree_le_of_dvd _ hd' hP').trans ((trueWeight_iff P).mp hw))
end FactorCover
structure Inventory (Γ : Finset K) (s : K→(Polynomial K)) where
  top : ℕ
  top_le : top≤15
  g : Row 3
  lower : LowerRow top g
  low : Finset K
  low_sub : low⊆Γ
  low_vanish : ∀ γ∈low,atJet g (extend (s γ))=0
  n : ℕ
  factor : Fin n→Row 4
  small : ∀ i,SmallFactor (factor i)
  different : ∀ i j,i≠j → ¬Associated (factor i) (factor j)
  fits : Fits top (fun i=>shape (factor i))
  active : (∑ i,activeDegree (factor i))≤178
  order : Fin n→ℕ
  layers : LayerBudget (fun i=>shape (factor i)) order
  proper : ∀ i,0<order i → ProperCut (factor i) Γ s (order i)
  zeros : Finset (Fin n)
  zero_iff : ∀ i,i∈zeros ↔ order i=0
  retained : zeros=∅ ∨ (Low6966Retained.Box (Low6966Retained.combined (fun i=>shape (factor i)) zeros) ∧
    1≤(Low6966Retained.combined (fun i=>shape (factor i)) zeros).t ∧
    (Low6966Retained.combined (fun i=>shape (factor i)) zeros).t≤2)
  pieces : Fin n→Finset K
  piece_sub : ∀ i,pieces i⊆Γ
  on_factor : ∀ i γ,γ∈pieces i → OnFactor (factor i) (extend (s γ))
  off_retained : ∀ i∉zeros,∀ γ∈pieces i,atJet (∏ j∈zeros,factor j) (extend (s γ))≠0
  book : Finset K
  book_cap : book.card≤56000
  fat : Low6966Fat.FatEquations
  fat_at : ∀ i γ,γ∈pieces i → Low6966Fat.Holds fat (extend (s γ))
  cover_count : Γ.card ≤ book.card+low.card+∑ i,(pieces i).card
theorem inventory_of_family {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179769 M Γ) (lo : 1≤M.overhead) (hi : M.overhead≤2329) :
    Nonempty (Inventory Γ F.scalar) := by
  obtain ⟨P,hP,hbox,hact,weight,vanish⟩ := Anchor6966.anchor_of_family M F hi
  have hw : TrueWeightLE P anchorCutoff := by
    apply (trueWeight_iff P).mpr
    rw [← differentialWeight_eq,←differentialWeightedDegree]
    exact weight
  obtain ⟨n,f,factors,different,prodDvd,covers⟩ := KoalaRetainedCut.anchor_factors hP
  let top := (shape P).t
  have htop : top≤15 := hbox.2.2
  have small (i : Fin n) : SmallFactor (f i) := factor_small hP hbox hw
    (factors i).1 (factors i).2.1 (factors i).2.2
  have fits : Fits top (fun i => shape (f i)) := by
    refine ⟨fun i => ⟨(factors i).2.1,index_bounds (f i)⟩,?_,?_,?_⟩
    · have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 4 → ℕ) Finset.univ f hP prodDvd
      simp only [MvPolynomial.weightedTotalDegree_one] at h
      exact h.trans hbox.1
    · have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd Fin.val Finset.univ f hP prodDvd
      simp only [← indexDegree_eq] at h
      exact h.trans hbox.2.1
    · have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd (Pi.single (3 : Fin 4) 1) Finset.univ f hP prodDvd
      change (∑ i, (f i).degreeOf 3) ≤ P.degreeOf 3
      simpa only [MvPolynomial.weightedTotalDegree_piSingle] using h
  have active : (∑ i, activeDegree (f i)) ≤ 178 :=
    (MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd (![1,2,2,2] : Fin 4 → ℕ)
      Finset.univ f hP prodDvd).trans ((activeFits_iff P 178).mp hact)
  have hchar (i : Fin n) : (shape (f i)).t<K1.p := (small i).2.2.1.2.2.trans_lt (by decide)
  have hm := Low6966Order.messages_of_family M F hi
  obtain ⟨ord,layers,proper⟩ := Low6966Order.proper_layers hm (fun i=>(small i).1)
    (fun i=>(small i).2.1) hchar different
  let zeros := (univ : Finset (Fin n)).filter fun i=>ord i=0
  have zero_iff (i : Fin n) : i∈zeros ↔ ord i=0 := by simp [zeros]
  have retained := Low6966Retained.no_cut_shape _ _ fits.1 layers zeros
    (fun i hi=>(zero_iff i).mp hi)
  obtain ⟨book,E,booked,fat⟩ := fat_of_family M F lo hi
  obtain ⟨low,piece,lowSub,lowOn,sub,on,off,total⟩ := KoalaRetainedCut.priority_pieces
    (fun i => (factors i).2.2) F.scalar book zeros (fun γ hγ => covers _ (vanish γ hγ))
  exact ⟨⟨top,htop,K1_13_1.anchorLead P,lower_of_anchor P hP hbox hw,low,lowSub,lowOn,
    n,f,small,different,fits,active,ord,layers,proper,zeros,zero_iff,retained,piece,sub,
    (fun i γ hγ=>(on i γ hγ).2),off,book,booked,E,(fun i γ hγ=>fat γ (sub i hγ) (on i γ hγ).1),total⟩⟩
#print axioms inventory_of_family
end
end LowProfile6966

end Merged_R6960Low6966Inventory
