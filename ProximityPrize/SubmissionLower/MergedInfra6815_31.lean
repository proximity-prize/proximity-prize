import ProximityPrize.SubmissionLower.MergedInfra6815_30
import ProximityPrize.SubmissionLower.MovingSourceGenericField6814
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.MovingSourcePersistentSeeds6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN002 RCN022 RCN042 RCN074 RCN086 RCN095 RCN135 RCN136 RCN159 RCN174
open RCN238 RCN243 RCN244 RCN264 RCN312 RCN341
open MovingSourceProjectionFamily6814 MovingSourceGammaProjections6814 MovingSourceLinearCycleFamily6814
open MovingSourceFrameZeroCount6814 MovingSourceProperSeedCount6814 MovingSourceReducedGamma6814
open MovingSourceLinearFlow6814

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

abbrev PersistentComponent (S : Stage K I Gamma x p flag errorCap stageSupport) :=
  {C : FirstTailComponent S //
    Transcendental (GenericField K) (coordinate (GenericField K) C.1 2) ∧
      ∀ delay, globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1+delay)∈C.1}

end
end ProximityPrize.SubmissionLower.MovingSourcePersistentSeeds6814
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.MovingSourceDenominatorSeeds6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators Classical
open RCN001 RCN051 RCN068 RCN074 RCN086 RCN095 RCN135 RCN136 RCN238 RCN243 RCN244 RCN264
open MovingSourceLinearFlow6814 MovingSourceCarrierField6814
open MovingSourceFlatBaseChange6814 MovingSourceGenericField6814 MovingSourceReducedGamma6814

variable {K I : Type} [Field K]

theorem surfaceMap_relPrime (F H : MvPolynomial (Fin 4) K) (hF : F≠0) (hrel : IsRelPrime F H) :
    IsRelPrime (surfaceMap (polynomialEmbedding K) F) (surfaceMap (polynomialEmbedding K) H) := by
  have hFc : collectX K F≠0 := fun hz => hF ((collectX K).injective (hz.trans (map_zero _).symm))
  exact generic_coefficient_map_relPrime K (collectX K F) (collectX K H) hFc
    (isRelPrime_equiv (collectX K).toRingEquiv F H hrel)

variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

def denominatorSeeds (S : Stage K I Gamma x p flag errorCap stageSupport)
    (J : WholeSpaceCube6814.Poly (K:=K)) : Finset K :=
  Gamma.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
    (surfaceMap (polynomialEmbedding K) (linearH J))=0)

end
end ProximityPrize.SubmissionLower.MovingSourceDenominatorSeeds6814
end MergedPart1
section MergedPart2
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
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingSourceCoupledClearing6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open MvPolynomial RCN095 RCN136 RCN207
open MovingSourceClearing6814 WholeSpaceCube6814 WholeSpaceCubeUniform6814

variable {K E : Type} [Field K] [Field E]
local notation "Poly5" => MvPolynomial (Fin 5) K

def slope (P : Poly5) := weightedTotalDegree slopeWeights P
def middle (P : Poly5) := weightedTotalDegree middleWeights P
def total (P : Poly5) := weightedTotalDegree totalWeights P
def order (P : Poly5) := P.degreeOf 1
def ordinaryFlag (P : Poly5) : FlagDegree := ⟨total P-middle P,middle P+order P-slope P,slope P⟩

theorem source_nested (P : Poly5) :
    middle P≤total P ∧ order P≤middle P ∧ 2*order P≤slope P ∧ slope P≤middle P+order P := by
  have hcoef (e) (he : e∈P.support) :
      e 1+e 2+e 3≤middle P ∧ 2*e 1+e 3≤slope P ∧ e 1≤order P := by
    refine ⟨?_,?_,MvPolynomial.monomial_le_degreeOf _ he⟩
    · simpa [middle,weight_coords,middleWeights] using MvPolynomial.le_weightedTotalDegree middleWeights he
    · simpa [MovingSourceCoupledClearing6814.slope,weight_coords,slopeWeights,Nat.mul_comm] using MvPolynomial.le_weightedTotalDegree slopeWeights he
  refine ⟨?_,?_,?_,?_⟩
  · apply Finset.sup_le
    intro e he
    have ht : Finsupp.weight totalWeights e≤total P := MvPolynomial.le_weightedTotalDegree totalWeights he
    simp only [weight_coords,middleWeights,totalWeights] at ht ⊢
    simp at ht ⊢
    omega
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hh := hcoef e he
    omega
  · have h : order P≤slope P/2 := MvPolynomial.degreeOf_le_iff.mpr (by
      intro e he
      have hh := hcoef e he
      omega)
    omega
  · apply Finset.sup_le
    intro e he
    have hh := hcoef e he
    simp [weight_coords,slopeWeights]
    omega

theorem ordinaryFlag_cumulative (P : Poly5) :
    (ordinaryFlag P).all=slope P ∧
    (ordinaryFlag P).yz+(ordinaryFlag P).all=middle P+order P ∧
    (ordinaryFlag P).zOnly+(ordinaryFlag P).yz+(ordinaryFlag P).all=total P+order P := by
  have hh := source_nested P
  dsimp only [ordinaryFlag]
  omega

private theorem cleared_weight
    (w : Fin 3 → ℕ) (P : Polynomial (MvPolynomial (Fin 3) E))
    (s cap drop a b : ℕ) (hcap : drop*s≤cap) (hbalance : drop+a=b)
    (H Q : MvPolynomial (Fin 3) E)
    (hP : ∀ j : Fin (s+1), RCN372.wt w (P.coeff j.val)≤cap-drop*j.val)
    (hH : RCN372.wt w H≤a) (hQ : RCN372.wt w Q≤b) :
    RCN372.wt w (SecondJetClearedHelper.cleared P s H Q)≤cap+s*a := by
  unfold SecondJetClearedHelper.cleared
  apply RCN372.wt_finset_sum_le
  intro j _
  have hp := hP j
  have hh := (RCN372.wt_pow_le w H (s-j.val)).trans (Nat.mul_le_mul_left _ hH)
  have hq := (RCN372.wt_pow_le w Q j.val).trans (Nat.mul_le_mul_left _ hQ)
  have hm := RCN372.wt_mul_le w (P.coeff j.val) (H^(s-j.val))
  have hn := RCN372.wt_mul_le w (P.coeff j.val*H^(s-j.val)) (Q^j.val)
  have hj : j.val≤s := Nat.le_of_lt_succ j.isLt
  have hsub := Nat.sub_add_cancel ((Nat.mul_le_mul_left drop hj).trans hcap)
  have hs := Nat.sub_add_cancel hj
  nlinarith

theorem coefficient_weights
    (phi : Polynomial K →+* E) (P : Poly5) (j : ℕ) :
    RCN372.wt RCN125.sWeight ((coefficients phi P).coeff j)≤slope P-2*j ∧
    RCN372.wt RCN125.ysWeight ((coefficients phi P).coeff j)≤middle P-j ∧
    RCN372.wt RCN125.totalWeight ((coefficients phi P).coeff j)≤total P-j := by
  have hb : ∀ e∈P.support, 2*e 1+e 3≤slope P ∧ e 1+e 2+e 3≤middle P ∧
      e 1+e 2+e 3+e 4≤total P := by
    intro e he
    refine ⟨?_,?_,?_⟩
    · simpa [MovingSourceCoupledClearing6814.slope,weight_coords,slopeWeights,Nat.mul_comm] using MvPolynomial.le_weightedTotalDegree slopeWeights he
    · simpa [middle,weight_coords,middleWeights] using MvPolynomial.le_weightedTotalDegree middleWeights he
    · simpa [total,weight_coords,totalWeights] using MvPolynomial.le_weightedTotalDegree totalWeights he
  have hw := SecondJetHelperWeights.derivative_coefficient_weights P (slope P) (middle P) (total P) 0 j hb
  simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hw
  have hs := RCN130.surfaceMap_nested_weights_le phi ((SecondJetCoefficients.asS P).coeff j)
  rw [coefficients,Polynomial.coeff_map]
  exact ⟨hs.1.trans hw.1,hs.2.1.trans hw.2.1,hs.2.2.trans hw.2.2⟩

theorem movingCut_ordinaryFlag
    (phi : Polynomial K →+* E) (P : Poly5)
    (Q A : MvPolynomial (Fin 3) E) (target : E)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A) :
    PolynomialInFlag (ordinaryFlag P) (movingCut phi P (order P) Q A target) := by
  have hn := source_nested P
  have hcoeff := coefficient_weights phi P
  have hAf := twice_linear_flag A hA
  have hQf := inFlag_sub_poly (inFlag_const (2 • unitAllFlag) target) hQ
  have hR := cleared_weight RCN125.sWeight (coefficients phi P) (order P) (slope P) 2 0 2
    hn.2.2.1 rfl (2*A) (MvPolynomial.C target-Q) (fun j => (hcoeff j.val).1)
    (RCN125.wt_s_le_of_inFlag hAf) (RCN125.wt_s_le_of_inFlag hQf)
  have hM := cleared_weight RCN125.ysWeight (coefficients phi P) (order P) (middle P) 1 1 2
    (by simpa using hn.2.1) rfl (2*A) (MvPolynomial.C target-Q) (fun j => by simpa only [one_mul] using (hcoeff j.val).2.1)
    (RCN125.wt_ys_le_of_inFlag hAf) (RCN125.wt_ys_le_of_inFlag hQf)
  have hT := cleared_weight RCN125.totalWeight (coefficients phi P) (order P) (total P) 1 1 2
    (by simpa using hn.2.1.trans hn.1) rfl (2*A) (MvPolynomial.C target-Q) (fun j => by simpa only [one_mul] using (hcoeff j.val).2.2)
    (RCN125.wt_total_le_of_inFlag hAf) (RCN125.wt_total_le_of_inFlag hQf)
  intro e he
  have er := (MvPolynomial.le_weightedTotalDegree RCN125.sWeight he).trans hR
  have em := (MvPolynomial.le_weightedTotalDegree RCN125.ysWeight he).trans hM
  have et := (MvPolynomial.le_weightedTotalDegree RCN125.totalWeight he).trans hT
  rw [RCN372.weight_fin3] at er em et
  simp [RCN125.sWeight,RCN125.ysWeight,RCN125.totalWeight] at er em et
  have hc := ordinaryFlag_cumulative P
  change e 1≤_ ∧ e 0+e 1≤_ ∧ e 0+e 1+e 2≤_
  rw [hc.2.2,hc.2.1,hc.1]
  exact ⟨er,em,et⟩

end
end ProximityPrize.SubmissionLower.MovingSourceCoupledClearing6814
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.MovingSourceSameSourceBudget6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
open MvPolynomial RCN095 WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingSourceCoupledClearing6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814

variable {K : Type} [Field K]
local notation "Poly5" => MvPolynomial (Fin 5) K

theorem pair_degrees_le (P J D : Poly5) (hP : P≠0) (hJ : J≠0) (hD : D≠0)
    (hcop : IsRelPrime J D) (hJP : J∣P) (hDP : D∣P) :
    (∀ w : Fin 5 → ℕ, weightedTotalDegree w J+weightedTotalDegree w D≤weightedTotalDegree w P) ∧
      order J+order D≤order P := by
  obtain ⟨R,hR⟩ := hcop.mul_dvd hJP hDP
  have hRne : R≠0 := by intro hz; apply hP; rw [hR,hz,mul_zero]
  constructor
  · intro w
    rw [hR,weight_mul _ _ _ (mul_ne_zero hJ hD) hRne,weight_mul _ _ _ hJ hD]
    omega
  · change J.degreeOf 1+D.degreeOf 1≤P.degreeOf 1
    rw [hR,degreeOf_mul_eq (mul_ne_zero hJ hD) hRne,degreeOf_mul_eq hJ hD]
    omega

end
end ProximityPrize.SubmissionLower.MovingSourceSameSourceBudget6814
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.MovingSourceTripleRootInvariants6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000

def inv2 {R : Type*} [CommRing R] (a b c d e : R) : R := 12*a*e-3*b*d+c^2
def inv3 {R : Type*} [CommRing R] (a b c d e : R) : R :=
  72*a*c*e+9*b*c*d-27*a*d^2-27*b^2*e-2*c^3

theorem triple_factor_invariants {R : Type*} [CommRing R] (u v t : R) :
    inv2 u (v-3*u*t) (3*u*t^2-3*v*t) (3*v*t^2-u*t^3) (-v*t^3)=0 ∧
    inv3 u (v-3*u*t) (3*u*t^2-3*v*t) (3*v*t^2-u*t^3) (-v*t^3)=0 := by
  constructor <;> simp only [inv2,inv3] <;> ring

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

theorem depressed_root (h2 : (2 : K)≠0) (h3 : (3 : K)≠0)
    (p q r : K) (hI : p^2+12*r=0) (hJ : 8*p^3+27*q^2=0) :
    ∃ t : K, t^4+p*t^2+q*t+r=0 := by
  by_cases hp : p=0
  · have hr : r=0 := by
      have hh : (12 : K)*r=0 := by simpa only [hp,zero_pow (by decide : 2≠0),zero_add] using hI
      have h12 : (12 : K)≠0 := by
        have he : (12 : K)=3*2^2 := by ring
        rw [he]
        exact mul_ne_zero h3 (pow_ne_zero _ h2)
      exact (mul_eq_zero.mp hh).resolve_left h12
    exact ⟨0,by simp [hr]⟩
  · refine ⟨-3*q/(4*p),?_⟩
    have hnum : 81*q^4-48*p^3*q^2+256*p^4*r=0 := by
      apply (mul_eq_zero.mp (show (3 : K)*(81*q^4-48*p^3*q^2+256*p^4*r)=0 from ?_)).resolve_left h3
      linear_combination (9*q^2-8*p^3)*hJ+64*p^4*hI
    have h4 : (4 : K)≠0 := by
      have he : (4 : K)=2^2 := by ring
      rw [he]
      exact pow_ne_zero _ h2
    field_simp
    linear_combination hnum

theorem quartic_has_root_of_invariants
    (h2 : (2 : K)≠0) (h3 : (3 : K)≠0)
    (a b c d e : K) (ha : a≠0) (hI : inv2 a b c d e=0) (hJ : inv3 a b c d e=0) :
    ∃ t : K, a*t^4+b*t^3+c*t^2+d*t+e=0 := by
  let p := c/a-3*b^2/(8*a^2)
  let q := d/a-b*c/(2*a^2)+b^3/(8*a^3)
  let r := e/a-b*d/(4*a^2)+b^2*c/(16*a^3)-3*b^4/(256*a^4)
  have h4 : (4 : K)≠0 := by
    have he : (4 : K)=2^2 := by ring
    rw [he]; exact pow_ne_zero _ h2
  have h8 : (8 : K)≠0 := by
    have he : (8 : K)=2^3 := by ring
    rw [he]; exact pow_ne_zero _ h2
  have h16 : (16 : K)≠0 := by
    have he : (16 : K)=2^4 := by ring
    rw [he]; exact pow_ne_zero _ h2
  have h256 : (256 : K)≠0 := by
    have he : (256 : K)=2^8 := by ring
    rw [he]; exact pow_ne_zero _ h2
  have hIe : p^2+12*r=inv2 a b c d e/a^2 := by
    dsimp only [p,r,inv2]
    field_simp
    ring
  have hJe : 8*p^3+27*q^2=(6*a*p*inv2 a b c d e-inv3 a b c d e)/a^3 := by
    dsimp only [p,q,inv2,inv3]
    field_simp
    ring
  have hIp : p^2+12*r=0 := by rw [hIe,hI,zero_div]
  have hJp : 8*p^3+27*q^2=0 := by rw [hJe,hI,hJ,mul_zero,sub_self,zero_div]
  obtain ⟨t,ht⟩ := depressed_root h2 h3 p q r hIp hJp
  refine ⟨t-b/(4*a),?_⟩
  have he : a*(t-b/(4*a))^4+b*(t-b/(4*a))^3+c*(t-b/(4*a))^2+d*(t-b/(4*a))+e=
      a*(t^4+p*t^2+q*t+r) := by
    dsimp only [p,q,r]
    field_simp
    ring
  rw [he,ht,mul_zero]

theorem cubic_has_root_of_inv3
    (h3 : (3 : K)≠0) (b c d e : K) (hb : b≠0) (hJ : inv3 0 b c d e=0) :
    ∃ t : K, b*t^3+c*t^2+d*t+e=0 := by
  refine ⟨-c/(3*b),?_⟩
  field_simp
  dsimp only [inv3] at hJ
  linear_combination -hJ

end
end ProximityPrize.SubmissionLower.MovingSourceTripleRootInvariants6814
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.MovingSourceTripleRootPolynomial6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open Polynomial MovingSourceTripleRootInvariants6814

def polynomialInv2 {R : Type*} [CommRing R] (P : Polynomial R) : R :=
  inv2 (P.coeff 4) (P.coeff 3) (P.coeff 2) (P.coeff 1) (P.coeff 0)
def polynomialInv3 {R : Type*} [CommRing R] (P : Polynomial R) : R :=
  inv3 (P.coeff 4) (P.coeff 3) (P.coeff 2) (P.coeff 1) (P.coeff 0)

theorem map_inv2 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (P : Polynomial R) :
    f (polynomialInv2 P)=polynomialInv2 (P.map f) := by
  simp [polynomialInv2,inv2,map_ofNat]
theorem map_inv3 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (P : Polynomial R) :
    f (polynomialInv3 P)=polynomialInv3 (P.map f) := by
  simp [polynomialInv3,inv3,map_ofNat]

theorem triple_product_invariants {R : Type*} [CommRing R] (u v t : R) :
    polynomialInv2 ((Polynomial.X-C t)^3*(C u*Polynomial.X+C v))=0 ∧
      polynomialInv3 ((Polynomial.X-C t)^3*(C u*Polynomial.X+C v))=0 := by
  have he : (Polynomial.X-C t)^3*(C u*Polynomial.X+C v)=
      C u*Polynomial.X^4+C (v-3*u*t)*Polynomial.X^3+C (3*u*t^2-3*v*t)*Polynomial.X^2+
        C (3*v*t^2-u*t^3)*Polynomial.X+C (-v*t^3) := by
    simp only [map_sub,map_mul,map_pow,map_neg,map_ofNat]
    ring
  rw [he]
  simp only [polynomialInv2,polynomialInv3,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
  norm_num only
  simp only [ite_true,ite_false,add_zero,zero_add]
  exact triple_factor_invariants u v t

theorem invariants_of_triple_root {K : Type} [Field K]
    (P : Polynomial K) (hP : P≠0) (hs : P.natDegree≤4) (t : K)
    (hroot : (Polynomial.X-C t)^3∣P) : polynomialInv2 P=0 ∧ polynomialInv3 P=0 := by
  obtain ⟨Q,hQ⟩ := hroot
  have hQne : Q≠0 := by intro hz; exact hP (by rw [hQ,hz,mul_zero])
  have hdegree := hs
  rw [hQ,natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero t)) hQne,natDegree_pow,natDegree_X_sub_C] at hdegree
  obtain ⟨u,v,hform⟩ := exists_eq_X_add_C_of_natDegree_le_one (show Q.natDegree≤1 by omega)
  rw [hQ,hform]
  exact triple_product_invariants u v t

theorem degree_four_form {R : Type*} [CommRing R] (P : Polynomial R) (h : P.natDegree≤4) :
    P=C (P.coeff 4)*Polynomial.X^4+C (P.coeff 3)*Polynomial.X^3+C (P.coeff 2)*Polynomial.X^2+
      C (P.coeff 1)*Polynomial.X+C (P.coeff 0) := by
  have hh := P.as_sum_range_C_mul_X_pow' (show P.natDegree<5 by omega)
  conv_lhs => rw [hh]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one]
  ring

theorem root_of_small_degree_invariants {K : Type} [Field K]
    (h2 : (2 : K)≠0) (h3 : (3 : K)≠0)
    (P : Polynomial K) (hP : P≠0) (hs : P.natDegree=3 ∨ P.natDegree=4)
    (hI : polynomialInv2 P=0) (hJ : polynomialInv3 P=0) : ∃ t : K, P.eval t=0 := by
  have hform := degree_four_form P (by omega)
  rcases hs with hs | hs
  · have hb : P.coeff 3≠0 := by
      rw [←hs]
      exact leadingCoeff_ne_zero.mpr hP
    have ha : P.coeff 4=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have hJ' : inv3 0 (P.coeff 3) (P.coeff 2) (P.coeff 1) (P.coeff 0)=0 := by
      simpa only [polynomialInv3,ha] using hJ
    obtain ⟨t,ht⟩ := cubic_has_root_of_inv3 h3 _ _ _ _ hb hJ'
    refine ⟨t,?_⟩
    conv_lhs => rw [hform]
    simpa only [eval_add,eval_mul,eval_pow,eval_C,eval_X,ha,zero_mul,zero_add] using ht
  · have ha : P.coeff 4≠0 := by
      rw [←hs]
      exact leadingCoeff_ne_zero.mpr hP
    obtain ⟨t,ht⟩ := quartic_has_root_of_invariants h2 h3 _ _ _ _ _ ha hI hJ
    refine ⟨t,?_⟩
    conv_lhs => rw [hform]
    simpa only [eval_add,eval_mul,eval_pow,eval_C,eval_X] using ht

theorem irreducible_small_invariants_not_both_zero {K : Type} [Field K]
    (h2 : (2 : K)≠0) (h3 : (3 : K)≠0)
    (P : Polynomial K) (hP : Irreducible P) (hs : P.natDegree=3 ∨ P.natDegree=4) :
    ¬(polynomialInv2 P=0 ∧ polynomialInv3 P=0) := by
  rintro ⟨hi,hj⟩
  obtain ⟨t,ht⟩ := root_of_small_degree_invariants h2 h3 P hP.ne_zero hs hi hj
  have ha := (irreducible_X_sub_C t).associated_of_dvd hP (dvd_iff_isRoot.mpr ht)
  have hd := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated ha)
  rw [natDegree_X_sub_C] at hd
  omega

end
end ProximityPrize.SubmissionLower.MovingSourceTripleRootPolynomial6814
end MergedPart6
