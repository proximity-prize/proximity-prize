import ProximityPrize.SubmissionLower.MovingSourceDenominatorSeeds6814

/-! Exhaustive seed coverage for the linear owner: denominator zeros,
constant parameter, proper delay, or the old persistent/tangent branch.
All four counts are proved before the final arithmetic is assembled. -/
namespace ProximityPrize.SubmissionLower.MovingSourceLinearSeedAssembly6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators Classical
open RCN002 RCN074 RCN086 RCN095 RCN135 RCN136 RCN174 RCN238 RCN243 RCN244 RCN264 RCN330
open MovingSourceLinearFlow6814 MovingSourceReducedRoutes6814 MovingSourceReducedGamma6814
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

/-- Complete checked-cell linear-owner count. No cardinality inequality
or exceptional-component classification is an input. The remaining
profile hypotheses are the ordinary stage geometry and received-word
agreement bounds required by the pre-existing tangent consumer. -/
theorem checked_linear_owner_seed_count
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hp : p=2130706433) (he : errorCap=80889)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : LinearRoute S.F J)
    (hS : PolynomialInFlag ⟨3504,45,12⟩ S.G)
    (hFY : S.F.degreeOf 1≤57) (hFR : S.F.degreeOf 2≤12) (hFZ : S.F.degreeOf 3≤3561)
    (hnodes : S.nodes.card=262144)
    (hagreement : ∀ gamma∈Gamma, 181255≤(S.agreementFiber gamma).card)
    (bound seedCap slopeCap : ℕ) (hshort : RCN326.w+1≤bound) (hchar : bound<p)
    (hbox : S.F∈globalCoefficientBox K bound RCN326.w seedCap slopeCap) :
    Gamma.card≤80505967991416918 := by
  have hH := linear_denominator_proper S J hroute
  have hsmall : flagMixed ⟨3504,45,12⟩ reducedFirstFlag unitZFlag<p := by
    rw [hp]
    exact checked_gamma_budget.2
  have hd := checked_denominator_seed_count S hp he J hroute hS hFY hFR hFZ hnodes hagreement
  have hpr := checked_proper_linear_seed_count S hp hfirst J hroute hS
  have hc := (constant_seed_sum_le S hfirst J hroute hH ⟨3504,45,12⟩ hS).trans_eq constant_checked_budget
  have ht := persistent_seed_sum_le S hfirst J hroute hH ⟨3504,45,12⟩ hS hsmall
    181255 bound seedCap slopeCap (by omega) hagreement (by decide)
    hshort hchar hbox
  have htCost : (errorCap+1)*flagMixed ⟨3504,45,12⟩ reducedFirstFlag unitYZFlag=497878763753400 := by
    rw [he]
    exact persistent_checked_budget
  have ht' := ht.trans_eq htCost
  calc
    Gamma.card≤_ := linear_seed_cover S hfirst J
    _≤3067534234414+(80004988562225019+(33131204085+497878763753400)) :=
      Nat.add_le_add hd (Nat.add_le_add hpr (Nat.add_le_add hc ht'))
    _=80505967991416918 := by decide +kernel

theorem checked_linear_owner_seed_count_fits :
    80505967991416918<272069082261391681 := by decide +kernel

#print axioms linear_seed_cover
#print axioms checked_linear_owner_seed_count
end
end ProximityPrize.SubmissionLower.MovingSourceLinearSeedAssembly6814
