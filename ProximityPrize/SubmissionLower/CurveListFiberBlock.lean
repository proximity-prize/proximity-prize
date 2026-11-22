import ProximityPrize.SubmissionLower.CurveListTripleSupport

set_option Elab.async false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

namespace CurveListFiberBlock
open CJ0 MvPolynomial PolynomialDifferential CurveListJointWeight CurveListTripleSupport
open scoped Polynomial BigOperators
open private jetView from ProximityPrize.SubmissionLower.CurveListPairInterpolation
open private exponent column_eq_of_exponent from ProximityPrize.SubmissionLower.CurveListTripleSupport

noncomputable section

def marked {ι : Type*} (target : ι → JetExponent) (e : JetExponent) : Prop := ∃ j, e = target j
instance {ι : Type*} [Fintype ι] (target : ι → JetExponent) (e : JetExponent) : Decidable (marked target e) := by
  unfold marked
  infer_instance

/-- Remove finitely many complete coefficient fibers, charging each by its physical width. -/
theorem avoid {A V R : ℕ} {ι : Type*} [Fintype ι] {s : Source} (hs : ShapeOK s)
    (hf : ∀ j ∈ s.E, j.b+3*j.c ≤ V) (hw : s.m ≤ s.m*A-N*s.B)
    (hp : prefixRank s (s.B+1) ≤ R) (target : ι → JetExponent) (widthCap : ι → ℕ)
    (hcap : ∀ (i : ColumnIndex A s) (j : ι), exponent i = target j → width A s i.1.val ≤ widthCap j)
    (hroom : n*R + ∑ j, widthCap j < Fintype.card (ColumnIndex A s)) (w : Node → K) :
    ∃ Q : DifferentialPolynomial K 2, OrderTwo s Q ∧ Q.weightedTotalDegree (jetWeight 3) ≤ V ∧
      (∀ f ∈ close A w, differentialSpecialization Q f = 0) ∧
      ∀ e ∈ (jetView Q).support, ¬ marked target e := by
  classical
  let T := {i : ColumnIndex A s // marked target (exponent i)}
  let choose (i : T) := Classical.choose i.property
  have choose_spec (i : T) : exponent i.val = target (choose i) := Classical.choose_spec i.property
  let enc (i : T) : (j : ι) × Fin (widthCap j) :=
    ⟨choose i,⟨i.val.2.val,i.val.2.isLt.trans_le (hcap i.val (choose i) (choose_spec i))⟩⟩
  have henc : Function.Injective enc := by
    intro i j hij
    have hj : choose i = choose j := congrArg Sigma.fst hij
    have hv : i.val.2.val = j.val.2.val :=
      congrArg (fun z : (j : ι) × Fin (widthCap j) => z.2.val) hij
    apply Subtype.ext
    exact column_eq_of_exponent ((choose_spec i).trans (by rw [hj, ← choose_spec j])) hv
  have hb : Fintype.card T ≤ ∑ j, widthCap j := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_le_of_injective enc henc
  let keep : {i : ColumnIndex A s // ¬ marked target (exponent i)} ↪ ColumnIndex A s :=
    ⟨Subtype.val,Subtype.val_injective⟩
  have hkeep : n*R < Fintype.card {i : ColumnIndex A s // ¬ marked target (exponent i)} := by
    rw [Fintype.card_subtype_compl]
    change n*R < Fintype.card (ColumnIndex A s) - Fintype.card T
    omega
  obtain ⟨Q,hQ,hQv,hroots,hQsupp⟩ := CurveListCornerSource.interpolation_in_columns
    keep hs hf hw hp hkeep w
  refine ⟨Q,hQ,hQv,hroots,?_⟩
  intro e he hem
  let a := ((jetView Q).coeff e).natDegree
  have hc : ((jetView Q).coeff e).coeff a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (mem_support_iff.mp he)
  rw [optionEquivRight_coeff_coeff] at hc
  obtain ⟨i,hi⟩ := hQsupp _ (mem_support_iff.mpr hc)
  change e.optionElim a = (column A s i.val).exponent at hi
  have heq : e = exponent i.val := by
    simpa only [Finsupp.some_optionElim] using congrArg Finsupp.some hi
  exact i.property (heq ▸ hem)

end
end CurveListFiberBlock
