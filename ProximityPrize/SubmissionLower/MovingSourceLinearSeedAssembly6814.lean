import ProximityPrize.SubmissionLower.MovingSourceDenominatorSeeds6814
namespace ProximityPrize.SubmissionLower.MovingSourceLinearSeedAssembly6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators Classical
open RCN002 RCN074 RCN086 RCN095 RCN135 RCN136 RCN174 RCN238 RCN243 RCN244 RCN264 RCN330
open MovingSourceLinearFlow6814 MovingSourceReducedGamma6814
open MovingSourceProperSeedCount6814 MovingSourceConstantSeeds6814 MovingSourcePersistentSeeds6814
open MovingSourceDenominatorSeeds6814

private theorem card_four_union {A : Type} [DecidableEq A] (s a b c : Finset A) :
    (s∪(a∪(b∪c))).card≤s.card+(a.card+(b.card+c.card)) :=
  (Finset.card_union_le s _).trans (Nat.add_le_add_left
    ((Finset.card_union_le a _).trans (Nat.add_le_add_left (Finset.card_union_le b c) _)) _)

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

theorem linear_seed_cover
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (J : WholeSpaceCube6814.Poly (K:=K)) :
    Gamma.card≤(denominatorSeeds S J).card+
      ((∑ C : ProperLinearComponent S hfirst (linearH J), (stageSeeds S C.1).card)+
        ((∑ C : ConstantComponent S, (stageSeeds S C.1).card)+
          (∑ C : PersistentComponent S, (stageSeeds S C.1).card))) := by
  let proper := Finset.univ.biUnion (fun C : ProperLinearComponent S hfirst (linearH J) => stageSeeds S C.1)
  let constant := Finset.univ.biUnion (fun C : ConstantComponent S => stageSeeds S C.1)
  let persistent := Finset.univ.biUnion (fun C : PersistentComponent S => stageSeeds S C.1)
  have hproperCard : proper.card≤∑ C : ProperLinearComponent S hfirst (linearH J), (stageSeeds S C.1).card :=
    Finset.card_biUnion_le
  have hconstantCard : constant.card≤∑ C : ConstantComponent S, (stageSeeds S C.1).card :=
    Finset.card_biUnion_le
  have hpersistentCard : persistent.card≤∑ C : PersistentComponent S, (stageSeeds S C.1).card :=
    Finset.card_biUnion_le
  have hcover : Gamma⊆denominatorSeeds S J∪(proper∪(constant∪persistent)) := by
    intro gamma hg
    by_cases hdenom : MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (surfaceMap (polynomialEmbedding K) (linearH J))=0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hg,hdenom⟩)
    have hreg : MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (regularitySurface (polynomialEmbedding K) S.F)≠0 := by
      rw [regularitySurface,selectedPoint_evaluation]
      exact S.regular gamma hg
    have htail : MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))=0 :=
      selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F S.selected gamma RCN326.w (RCN326.w+1)
        (S.degree_le gamma hg) (S.solution gamma hg) (by omega)
    obtain ⟨C,hon⟩ := exists_regular_component (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
      (regularitySurface (polynomialEmbedding K) S.F)
      (selectedPoint (polynomialEmbedding K) S.selected gamma) (S.on_component gamma hg) htail hreg
    have hCS : gamma∈stageSeeds S C := Finset.mem_filter.mpr ⟨hg,hon⟩
    have hH : surfaceMap (polynomialEmbedding K) (linearH J)∉C.1 := fun hh => hdenom (hon hh)
    apply Finset.mem_union_right
    by_cases hconstant : IsAlgebraic (GenericField K) (coordinate (GenericField K) C.1 2)
    · apply Finset.mem_union_right
      apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨⟨C,hconstant⟩,Finset.mem_univ _,hCS⟩
    rcases (local_order_tail_dichotomy S (canonicalLocalDVRFamily S hfirst) C hfirst).2 with hd | hall
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨⟨C,hconstant,hH,hd⟩,Finset.mem_univ _,hCS⟩
    · apply Finset.mem_union_right
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨⟨C,hconstant,hall⟩,Finset.mem_univ _,hCS⟩
  calc
    _≤(denominatorSeeds S J∪(proper∪(constant∪persistent))).card := Finset.card_le_card hcover
    _≤(denominatorSeeds S J).card+(proper.card+(constant.card+persistent.card)) := card_four_union _ _ _ _
    _≤_ := Nat.add_le_add_left (Nat.add_le_add hproperCard
      (Nat.add_le_add hconstantCard hpersistentCard)) _

end
end ProximityPrize.SubmissionLower.MovingSourceLinearSeedAssembly6814
