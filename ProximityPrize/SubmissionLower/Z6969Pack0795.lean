import ProximityPrize.Benchmark.TargetLower
import Mathlib.Tactic
import ProximityPrize.SubmissionLower.DdZZ6ou4c
import ProximityPrize.SubmissionLower.FrontBranch12
import ProximityPrize.SubmissionLower.FrontBranch3
import ProximityPrize.SubmissionLower.HighCore82258Pairs

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Profile
section Z6969Source2214
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 24000
set_option linter.constructorNameAsVariable false

namespace Research6969.Profile
open ProximityPrize.Benchmark ToyProblem CoreDefinitions ProximityGap
open scoped NNReal
abbrev p : ℕ := 2899368181980161361
abbrev q : ℕ := 9223372036854649837
abbrev agreement : ℕ := 179740
abbrev listCap : ℕ := 52000088471619
abbrev scalarCap : ℕ := 274928728022923468

private theorem of_cross_power {x : ℝ≥0} {a d : ℕ} (hd : 0 < d)
    (h : x ^ d * 2 ^ a ≤ 1) : x ≤ (2 : ℝ≥0) ^ (-(a : ℝ) / d) := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  apply (NNReal.rpow_le_rpow_iff hd').mp
  rw [← NNReal.rpow_mul, div_mul_cancel₀ _ hd'.ne', NNReal.rpow_natCast,
    NNReal.rpow_neg, NNReal.rpow_natCast, ← one_div]
  exact (le_div_iff₀ (by positivity)).mpr h
theorem score :
    (1 - claimedRadius p q) ^ IRSProfile.repetitions ≤ (2 : ℝ≥0) ^ (-((6969 : ℝ) / 100)) := by
  let x : ℝ≥0 := (1 - claimedRadius p q) ^ 128
  have small : claimedRadius p q ≤ 1 := by
    unfold claimedRadius
    exact (div_le_one (by positivity)).mpr (by norm_num)
  have diff : 1 - claimedRadius p q = (6324003854874488476 : ℝ≥0) / q := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub small]
    norm_num [claimedRadius]
  have upper : x * 2 ^ 69 ≤ (619693289293 : ℝ≥0) / 1000000000000 := by
    dsimp only [x]
    rw [diff, div_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast (show (6324003854874488476 : ℕ) ^ 128 * 2 ^ 69 * 1000000000000 ≤
      619693289293 * q ^ 128 by decide +kernel)
  change x ≤ _
  rw [← neg_div]
  apply of_cross_power (a := 6969) (d := 100) (by decide)
  calc
    x ^ 100 * 2 ^ 6969 = (x * 2 ^ 69) ^ 100 * 2 ^ 69 := by
      rw [mul_pow, mul_assoc, ← pow_mul (2 : ℝ≥0), ← pow_add]
    _ ≤ ((619693289293 : ℝ≥0) / 1000000000000) ^ 100 * 2 ^ 69 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left' upper _) (by positivity)
    _ ≤ 1 := by
      rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)]
      exact_mod_cast (show (619693289293 : ℕ) ^ 100 * 2 ^ 69 ≤ 1000000000000 ^ 100 by decide +kernel)

theorem admissible : claimedRadius p q ∈ Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [claimedRadius,IRSProfile.minRelativeDistance]

theorem threshold {s:ℕ} (h:(262144:ℝ)*(1-((claimedRadius p q:ℝ≥0):ℝ))≤s) : agreement≤s := by
  have strict:(179739:ℝ)<262144*(1-((claimedRadius p q:ℝ≥0):ℝ)) := by norm_num [claimedRadius]
  exact (show 179739<s by exact_mod_cast strict.trans_le h)

theorem field_budget : (scalarCap+listCap)*2^128≤(0x7f000001:ℕ)^6 := by decide +kernel
theorem reduced : Nat.Coprime p q := by decide +kernel

abbrev errors : ℕ := 262144 - agreement
abbrev link : ℕ := agreement - 131072
abbrev heightCap : ℕ := errors + 1 - link - 2
abbrev fieldSize : ℕ := (0x7f000001 : ℕ) ^ 6
abbrev fieldCap : ℕ := 274980728111395087
abbrev rankFee : ℕ := 71879381565923
abbrev anchorFee : ℕ := 71879381846871
abbrev markBudget : ℕ := 274784969259510674

theorem errors_exact : errors = 82404 := rfl
theorem link_exact : link = 48668 := rfl
theorem height_exact : heightCap = 33735 := rfl

theorem field_cap_exact : fieldSize / 2 ^ 128 = fieldCap := by decide +kernel
theorem rank_fee_exact : link + 0x7f000001 * heightCap = rankFee := by decide +kernel
theorem anchor_fee_exact :
    0x7f000001 * heightCap + 2 * heightCap + 262144 + 2 = anchorFee := by decide +kernel
theorem scalar_cap_exact : markBudget + anchorFee + rankFee = scalarCap := by decide +kernel
theorem mark_budget_exact : fieldCap - listCap - anchorFee - rankFee = markBudget := by
  decide +kernel

theorem threshold_exact :
    (179739 : ℝ) < 262144 * (1 - ((claimedRadius p q : ℝ≥0) : ℝ)) ∧
      262144 * (1 - ((claimedRadius p q : ℝ≥0) : ℝ)) < 179740 := by
  constructor <;> norm_num [claimedRadius]

theorem next_score_scaled_witness :
    619693289292 * q ^ 128 ≤
      (6324003854874488476 : ℕ) ^ 128 * 2 ^ 69 * 1000000000000 ∧
    (1000000000000 : ℕ) ^ 100 < 619693289292 ^ 100 * 2 ^ 70 := by
  constructor <;> decide +kernel

end Research6969.Profile
end Z6969Source2214

-- Source: ProximityPrize.SubmissionLower.ProfileList
section Z6969Source2215
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000

namespace Research6969.ProfileList
noncomputable section
open i4 PolynomialDifferential
open P5_8 (Equation small bo8 Moments small_shape donor_shape)
abbrev A := Profile.agreement
abbrev donorMargin : ℕ := 25851446690343340

theorem agreement_ok :aRk A:=⟨by decide,by decide,by decide,by decide⟩
theorem donor_width :bo8.m≤bo8.m*A-N*bo8.B:= by decide
private theorem stack_le {a :ℕ} {s :Source} {r :ℕ} (hs :Rz s)
    (hw:s.m≤ s.m*a-N*s.B) (hr :aWw s (s.B+1)≤ r) (w:Node→K) :
    Vv a s w≤n*r := by
  have ht:axY s (s.B+1) := by
    intro j hj hj'
    have :=(hs.support j hj).1
    omega
  exact (cw9.proof a s hs hw w).trans
    (Nat.mul_le_mul_left _ ((a9M.proof a s (s.B+1) hs hw le_rfl ht).trans hr))
theorem small_equation (w:Node→K) :
    ∃ Q:Equation,ato small Q ∧ ∀ f∈close A w,differentialSpecialization Q f=0:= by
  obtain ⟨hr,hm⟩:=P5_8_1.of_children q1EkR5c.proof qokZnNd.proof q2aXx2a.proof
  have hw:small.m≤ small.m*A-N*small.B:= by decide
  have hR:=stack_le small_shape hw hr w
  have hdim:=cqa A small small_shape hw
  rcases hm with ⟨hT,hS,hV⟩
  rw [hT,hS,hV] at hdim
  have hnum :n*232369+N*610160<small.m*A*12850+205216:= by decide
  have hlt:Vv A small w<Fintype.card (apU A small) := by omega
  obtain ⟨Q,hQ,hwt,hlocal⟩:=interpolant small_shape hw w hlt
  exact ⟨Q,hQ,specializes hwt hlocal⟩
theorem donor_surplus (w : Node → K) :
    Vv A bo8 w + donorMargin ≤ Fintype.card (apU A bo8) := by
  obtain ⟨hr, hm⟩ := P5_8_2.of_children qHvCGFa.proof qNtJgmd.proof qZtSHva.proof P6_8_1.proof
  have hR:=stack_le donor_shape donor_width hr w
  have hdim:=cqa A bo8 donor_shape donor_width
  rcases hm with ⟨hT,hS,hV⟩
  rw [hT,hS,hV] at hdim
  have hnum :n*0x62703852f02+donorMargin+N*0x1098bf757c00 =
      bo8.m*A*0x12e20e912+0x5e143ee4d6c:= by decide
  omega


end
end Research6969.ProfileList
end Z6969Source2215

-- Source: ProximityPrize.SubmissionLower.ProfileListCompanion
section Z6969Source2216
set_option autoImplicit true
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

namespace Research6969.ProfileList
noncomputable section
open i4 PolynomialDifferential MvPolynomial
open P5_8 (Jn Equation caps bo8 smallCaps donorCaps Gq tariffShape properDegree componentCap)
open scoped Polynomial BigOperators

def DonorSurplus (w:Node→K) :Prop :=
  Vv A bo8 w+donorMargin≤Fintype.card (apU A bo8)
structure Allocation (a :Jn) :Prop where
  total:a.B≤83
  index :a.J≤25
  top:a.C≤11
  top_total:a.C≤a.B
  top_index :2*a.C≤a.J
  index_total:a.J≤a.B+a.C
  capacity :0<a.B→donorMargin≤(gap A+2)*Gq a
structure Companion (Q:Equation) (w:Node→K) where
  common :Equation
  common_ne :common≠0
  allocation :Allocation (caps common)
  jO:Equation
  leftNative :Equation
  azo:Q=jO*leftNative
  removed_support : ∃ l:ℕ,apQ.initial jO∣apQ.initial common^l
  right:BL 2
  right_ne :right≠0
  coprime :IsRelPrime (apQ.initial leftNative) right
  left_band : let s := (smallCaps.wD (caps common)).repair
              apQ.initial leftNative∈aFz.GS s.B s.J s.C
  right_band : let s := (donorCaps.wD (caps common)).repair
               right∈aFz.GS s.B s.J s.C
  roots : ∀ f∈close A w,differentialSpecialization common f≠0 →
    MvPolynomial.eval (apQ.ahT f) (apQ.initial leftNative)=0 ∧
    MvPolynomial.eval (apQ.ahT f) right=0
def Companion.left {Q:Equation} {w:Node→K} (d:Companion Q w) :=
  apQ.initial d.leftNative

end
end Research6969.ProfileList

open _root_ renaming Fin.sum_univ_succ → zCS, Int.reduceAdd → z10, Int.reduceDiv → zS8, Int.reduceMod → z6y, Int.reduceSub → zci, MvPolynomial.eval → zY9, Nat.add_le_add_left → z3b, Nat.sub_le_sub_right → zIu, Polynomial → zM1, Polynomial.C → z1z, Polynomial.coeff_C → zFI, RingHom.injective → zyB, Submodule.subset_span → zBO
section
set_option autoImplicit true
namespace Research6969.ProfileList
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative gR
open aR (ao embed extend af jet Z8 wU)
open i4 (K Node node N gap close)
open P5_8 (bo8 Equation)
open P5_8_3 (rows)
open anj (line bdm bfX)
open bzr (cX8)
open qC8CERb (coeffForm specialize Yw shift_jetDerivative coeff_iterate_zero atJet_eq_const)
def lastCut:ℕ:=bo8.m*A - 1
def step:ℕ:=gap A+2
private def Bounded (F:zM1 (Polynomial ao)) (b:ℕ) :Prop :=
  ∀ j,(F.coeff j).natDegree≤b+step*j
private theorem afg {F G:zM1 (Polynomial ao)} {a b:ℕ}
    (hF:Bounded F a) (hG:Bounded G b) :Bounded (F*G) (a+b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum,Nat.mul_add]
  omega
private theorem aCs (f :(Polynomial ao)) {a :ℕ} (hf :f.natDegree≤a) :
    Bounded (z1z f) a := by
  intro j
  by_cases h:j=0
  · simpa [h] using hf
  · simp [zFI,h]
private theorem bmr {ι:Type*} (s :Finset ι)
    (f :ι→zM1 (Polynomial ao)) (b:ι→ℕ) (hf : ∀ i∈s,Bounded (f i) (b i)) :
    Bounded (∏ i∈s,f i) (∑ i∈s,b i) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using aCs (1 :(Polynomial ao)) (a :=0) (by simp)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    exact afg (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk=>hf k (Finset.mem_insert_of_mem hk))
private theorem aMs {f :zM1 (Polynomial ao)} {b:ℕ} (hf :Bounded f b) (n:ℕ) :
    Bounded (f^n) (b*n) := by
  induction n with
  | zero=>simpa using aCs (1 :(Polynomial ao)) (a :=0) (by simp)
  | succ n ih =>
    rw [pow_succ,Nat.mul_succ]
    exact afg ih hf
private abbrev weight (i:Fin 3) :ℕ:=N - i.val
private theorem avr (P:af 3) (S U:(Polynomial ao)) (T:ℕ)
    (hP : ∀ e∈P.support,(P.coeff e).natDegree+e.sum (fun i k=>weight i*k)≤T)
    (hS:S.natDegree≤N) (hU:U.natDegree≤A+2) (j:ℕ) :
    ((line P S U).coeff j).natDegree≤T+step*j:= by
  let F (i:Fin 3) :zM1 (Polynomial ao) :=
    z1z (jet S i)+Polynomial.C (jet U i)*Polynomial.X
  have hF (i:Fin 3) :Bounded (F i) (weight i) := by
    intro k
    have hs : (jet S i).natDegree≤weight i :=
      (natDegree_hasseDeriv_le S i.val).trans (zIu hS _)
    have hu: (jet U i).natDegree≤weight i+step:= by
      refine (natDegree_hasseDeriv_le U i.val).trans ((zIu hU _).trans ?_)
      have hi:=i.isLt
      change 179742 - i.val≤(131071 - i.val)+48671
      omega
    change ((z1z (jet S i)+Polynomial.C (jet U i) *
      Polynomial.X).coeff k).natDegree≤weight i+step*k
    rw [Polynomial.coeff_add,zFI,Polynomial.coeff_C_mul_X]
    by_cases h0:k=0
    · simpa [h0] using hs
    · by_cases h1 :k=1
      · simpa [h1] using hu
      · simp [h0,h1]
  unfold line
  rw [MvPolynomial.eval₂_eq,Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  have hterm :=afg (aCs (P.coeff m) le_rfl)
    (bmr m.support (fun i=>F i^m i) (fun i=>weight i*m i)
      (fun i _=>aMs (hF i) (m i))) j
  exact hterm.trans (Nat.add_le_add_right (hP m hm) _)
set_option maxRecDepth 12000 in
theorem paid_root {w:Node→K} {T:ℕ} {R:Equation} {i:Fin 3} {r :ℕ}
    (hR:R∈rows w T) (hcut:T+r*step≤lastCut) {f :(Polynomial K)}
    (hf :f∈close A w) :differentialSpecialization (jetDerivative R i r) f=0:= by
  classical
  let P:=coeffForm (MvPolynomial.map embed R)
  let S:=extend f
  have hS:S.natDegree≤N := by
    apply Polynomial.natDegree_map_le.trans
    by_cases h:f=0
    · simp [h]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt h).2 hf.1)
  obtain ⟨s,hsub,hs⟩:=Finset.exists_subset_card_eq hf.2
  let x (k :Node) :ao:=embed (node k)
  let L:=mL x s
  have horder :wU P S (r+1) := by
    apply bfX P S L (S8 x s).ne_zero
    intro V hV j hj
    have hU: (L*V).natDegree≤A+2 :=
      natDegree_mul_le.trans (by
        change (mL x s).natDegree+V.natDegree≤A+2
        rw [ZQ,hs]
        exact z3b hV _)
    have hd: ((line P S (L*V)).coeff j).natDegree<bo8.m*s.card:= by
      have hle :T+step*j≤lastCut:= by
        rw [Nat.mul_comm r step] at hcut
        exact (z3b (Nat.mul_le_mul_left step (Nat.lt_succ_iff.mp hj)) T).trans hcut
      rw [hs]
      exact ((avr P S _ T (Yw hR) hS hU j).trans hle).trans_lt
        (Nat.sub_lt (Nat.mul_pos (by decide :0<bo8.m) (by decide :0<A)) Nat.one_pos)
    have hx :Function.Injective x :=(zyB embed).comp node.injective
    apply cX8 _ s x hx bo8.m _ j hd
    intro k hk c
    have hhit :=(Finset.mem_filter.mp (hsub hk)).2
    have hag: (S+c•(L*V)).eval (x k)=embed (w k) := by
      have hL:L.eval (x k)=0:=arK x s k hk
      rw [eval_add,eval_smul,eval_mul,hL,zero_mul,smul_zero,add_zero]
      change (f.map embed).eval (embed (node k))= _
      rw [eval_map,eval₂_hom,hhit]
    have hr :R ∈ ⨅ k :Node,(localConstraintAt (d:=2) bo8.m (node k) (w k)).ker :=hR.2
    have hc:SatisfiesLocalConstraints bo8.m (node k) (w k) R :=
      ((Submodule.mem_iInf _).mp hr k)
    rw [bdm,specialize]
    exact X_sub_C_pow_dvd_differentialSpecialization_of_contact _ _ _ _ hag
      (hc.map embed _ _ _ _)
  apply (Polynomial.map_injective embed (zyB embed))
  rw [map_differentialSpecialization,Polynomial.map_zero,← specialize,atJet_eq_const,
    shift_jetDerivative]
  apply coeff_iterate_zero i (Z8 P S) (D:=r+1) _ r 0 (by simp)
  intro e he
  by_contra hne
  exact (not_le_of_gt he) (horder e (MvPolynomial.mem_support_iff.mpr hne))
end
end Research6969.ProfileList
end
section
set_option autoImplicit true
namespace Research6969.ProfileList
noncomputable section
open i4 PolynomialDifferential MvPolynomial Finset ReedSolomon.HiddenDerivative
open ProximityPrize.Benchmark UniqueFactorizationMonoid
open P5_8 (Equation small smallCaps bo8 donorCaps donor_shape Jn caps Gq)
open P5_8_3 (rows nativeBand dM powerCaps layerBound layerCost mem_nativeBand actual_caps initial_caps repair_band c54)
open scoped Polynomial BigOperators
open P5_8_3 (mem_rows derivative_band initial_mul)
open P5_8_3 (cofactor_eq group_cutoffs)
open qmRQvQa (matrix_dimension)
open qmRQvQa (S6 telescope caps_pow)
set_option maxHeartbeats 500000
set_option maxRecDepth 1800
private def necessary (w:Node→K) :Set Equation :=
  {P | ∃ (T:ℕ) (R:Equation) (i:Fin 3) (r :ℕ),
    R∈rows w T∧T+r*step≤lastCut∧P=jetDerivative R i r}
private def necessarySpace (w:Node→K) :Submodule K Equation :=
  Submodule.span K (necessary w)
private def powerAt (T:ℕ) :ℕ:=(lastCut - T)/step+1
private theorem choose_row {w:Node→K} {Q:Equation} (hQ:ato small Q)
    (hnonzero : ∃ P∈necessarySpace w,P≠0) :
    ∃ P∈necessarySpace w,P≠0 ∧
      ∀ F:Equation,Irreducible F→F∣Q→0<jetTotalDegree F→F∣P →
        ∀ R∈necessarySpace w,F∣R:= by
  classical
  let S:=necessarySpace w
  let _:StrongNormalizationMonoid Equation :=UniqueFactorizationMonoid.strongNormalizationMonoid
  let factors :=normalizedFactors Q
  let bad:=factors.toFinset.filter
    (fun F=>0<jetTotalDegree F ∧ ∃ R∈S,¬ F∣R)
  have hprod: (∏ F∈bad,F)∣Q :=
    ((Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)).trans
      (Multiset.toFinset_prod_dvd_prod factors)).trans (prod_normalizedFactors hQ.1).dvd
  have hcard:bad.card≤83:= calc
    bad.card = ∑ _F∈bad,(1 :ℕ) := by simp
    _ ≤ ∑ F∈bad,jetTotalDegree F :=
      Finset.sum_le_sum fun F hF=>(Finset.mem_filter.mp hF).2.1
    _≤jetTotalDegree Q :=
      sum_weightedTotalDegree_le_of_prod_dvd jetDegreeWeight bad id hQ.1 hprod
    _≤83:=hQ.2.1
  have hfield :83≤Nat.card K:= by
    rw [Nat.card_eq_fintype_card]
    exact (show 83≤Fintype.card Node by rw [IRSProfile.card_index]; decide).trans
      (Fintype.card_le_of_injective node node.injective)
  let blocked (F:Equation) :Submodule K S :=
    ((Ideal.span ({F} : Set Equation)).restrictScalars K).comap S.subtype
  have hmem (F:Equation) (R:S) :R∈blocked F↔F∣(R:Equation) :=
    Ideal.mem_span_singleton
  have hpick : ∃ P:S,(P:Equation)≠0 ∧ ∀ F∈bad,¬ F∣(P:Equation) := by
    rcases bad.eq_empty_or_nonempty with hbad | ⟨F,hF⟩
    · obtain ⟨P,hP,hP0⟩:=hnonzero
      exact ⟨⟨P,hP⟩,hP0,by simp [hbad]⟩
    · have hproper (G:Equation) (hG:G∈bad) :blocked G ≠ ⊤ := by
        obtain ⟨R,hR,hnd⟩:=(Finset.mem_filter.mp hG).2.2
        intro he
        exact hnd ((hmem G ⟨R,hR⟩).mp (he ▸ Submodule.mem_top))
      obtain ⟨P,hP⟩:=Submodule.exists_forall_notMem_of_card_le bad blocked hproper
        (hcard.trans hfield)
      have hav (G:Equation) (hG:G∈bad) : ¬ G∣(P:Equation) :=
        fun hd=>hP G hG ((hmem G P).mpr hd)
      exact ⟨P,fun hz=>hav F hF (hz ▸ dvd_zero F),hav⟩
  obtain ⟨P,hP0,hP⟩:=hpick
  refine ⟨P.val,P.property,hP0,?_⟩
  intro F hF hdQ hdeg hdP R hR
  by_contra hn
  obtain ⟨G,hG,ha⟩:=exists_mem_normalizedFactors_of_dvd hQ.1 hF hdQ
  have hdegG:0<jetTotalDegree G :=
    hdeg.trans_le (weightedTotalDegree_le_of_dvd jetDegreeWeight ha.dvd
      (ne_zero_of_mem_normalizedFactors hG))
  have hbad:G∈bad:=Finset.mem_filter.mpr
    ⟨Multiset.mem_toFinset.mpr hG,hdegG,R,hR,fun hd=>hn (ha.dvd.trans hd)⟩
  exact hP G hbad (ha.dvd_iff_dvd_left.mp hdP)
private theorem necessary_band (w:Node→K) :necessarySpace w≤nativeBand donorCaps := by
  apply Submodule.span_le.mpr
  rintro P ⟨T,R,i,r,hR,_,rfl⟩
  exact derivative_band ((mem_rows.mp hR).1) i r
private theorem necessary_root {w:Node→K} {P:Equation} (hP:P∈necessarySpace w)
    {f :(Polynomial K)} (hf :f∈close A w) :differentialSpecialization P f=0:= by
  have hle :necessarySpace w≤(differentialSpecializationHom (d:=2) f).toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨T,R,i,r,hR,hp,rfl⟩
    exact paid_root hR hp hf
  exact hle hP
private theorem necessary_nonzero {w:Node→K} (hs :DonorSurplus w) :
    ∃ P∈necessarySpace w,P≠0:= by
  have hp:0<donorMargin:= by decide
  have hr :Vv A bo8 w<Fintype.card (apU A bo8) :=
    (Nat.lt_add_of_pos_right hp).trans_le hs
  obtain ⟨P,hP,hT,hloc⟩:=interpolant donor_shape donor_width w hr
  refine ⟨P,zBO ⟨lastCut,P,0,0,?_,?_,(jetDerivative_zero ..).symm⟩,hP.1⟩
  · exact mem_rows.mpr ⟨mem_nativeBand.mpr hP.2,Nat.le_sub_one_of_lt hT,hloc⟩
  · simp
private theorem bound_cost (a :Jn) (l:ℕ) :layerBound a l≤layerCost a l:= by
  by_cases hf :dM (powerCaps a l) donorCaps
  · simpa only [layerBound,layerCost,ite_eq_left hf] using qfaXGOd.proof (donorCaps.wD (powerCaps a l))
  · simp only [layerBound,layerCost,ite_eq_right hf,le_refl]
private theorem cutoff_cost (a :Jn) (ha :0<a.B) :
    (∑ T∈range (lastCut+1),layerCost a (powerAt T))≤ step*Gq a := by
  rw [cofactor_eq a ha]
  refine group_cutoffs lastCut step (donorCaps.B/a.B) (by decide) (fun i=>layerCost a (i+1)) ?_
  intro i hi
  exact ite_eq_right (fun h=>(Nat.not_succ_le_self i)
    (((Nat.le_div_iff_mul_le ha).mpr h.1).trans hi))
private theorem cutoff_rank (w:Node→K) (G:Equation) (hG:G≠0)
    (hs :DonorSurplus w) (hd : ∀ T≤lastCut,∀ R∈rows w T,G^powerAt T∣R) :
    donorMargin ≤ ∑ T∈range (lastCut+1),layerBound (caps G) (powerAt T) := by
  have h:=matrix_dimension A bo8 donor_shape (by decide) (by decide) w (rows w lastCut)
    (fun _ hc hw hl=>mem_rows.mpr ⟨hc,Nat.le_sub_one_of_lt hw,hl⟩)
  have hdim:=Nat.le_of_add_le_add_left (hs.trans h)
  refine hdim.trans (telescope w lastCut (fun T=>layerBound (caps G) (powerAt T)) ?_)
  intro T hT
  rw [layerBound,← caps_pow G hG]
  exact S6 w T _ (pow_ne_zero _ hG) (hd T hT)
theorem companion_exists (w : Node → K) (Q : Equation) (hQ : ato small Q)
    (hroot : ∀ f ∈ close A w, differentialSpecialization Q f = 0) :
    Nonempty (Companion Q w) := by
  have hs : DonorSurplus w := donor_surplus w
  obtain ⟨P,hP,hPn,havoid⟩:=choose_row hQ (necessary_nonzero hs)
  obtain ⟨d⟩:=qVHZuid.proof Q P hQ.1 hPn
  have hn:d.divisor≠0:= fun hz=>hQ.1 (d.azo.trans (by rw [hz,zero_mul]))
  have hR:d.right≠0:= fun hz=>hPn (d.az7.trans (by rw [hz,mul_zero]))
  have hG:=ne_zero_of_dvd_ne_zero hn d.common_dvd
  have hGQ:d.common∣Q:=d.common_dvd.trans ⟨d.left,d.azo⟩
  have hCaps :dM (caps d.common) smallCaps :=(apQ.eHq hQ hGQ).2
  obtain ⟨hcB,hcJ,hJC⟩:=actual_caps (apQ.initial d.common)
  rw [initial_caps] at hcB hcJ hJC
  have hpower (T:ℕ) (ht:T≤lastCut) (R:Equation) (hR:R∈rows w T) :
      d.common^powerAt T∣R:= by
    apply d.combine
    intro F hF hFQ hFP hpos
    apply qyOiD7d.proof F R (powerAt T) hF hpos (apQ.eHq hQ hFQ).2.1 (mem_rows.mp hR).1
    intro i r hr
    have hmul :=(Nat.le_div_iff_mul_le (show 0<step by decide)).mp
      (Nat.le_of_lt_succ (show r<(lastCut - T)/step+1 from hr))
    have hpaid :T+r*step≤lastCut:= by omega
    exact havoid F hF hFQ hpos hFP _ (zBO ⟨T,R,i,r,hR,hpaid,rfl⟩)
  have halloc:Allocation (caps d.common) := by
    refine ⟨hCaps.1,hCaps.2.1,hCaps.2.2,hcB,hcJ,hJC,fun hb => ?_⟩
    exact (cutoff_rank w d.common hG hs hpower).trans
      ((sum_le_sum fun T _=>bound_cost (caps d.common) (powerAt T)).trans (cutoff_cost _ hb))
  have hl:=(congrArg apQ.initial d.azo).trans (initial_mul _ _)
  have hr :=(congrArg apQ.initial d.az7).trans (initial_mul _ _)
  refine ⟨⟨d.common,hG,halloc,d.divisor,d.left,d.azo,d.support,
    apQ.initial d.right,apQ.b6j hR,q0KdFsb.proof _ _ d.coprime,?_,?_,?_⟩⟩
  · apply repair_band
    rw [initial_caps]
    exact c54 hQ.1 d.common_dvd d.azo hQ.2
  · apply repair_band
    rw [initial_caps]
    exact c54 hPn d.common_dvd d.az7 (mem_nativeBand.mp (necessary_band w hP))
  · intro f hf hgf
    have hg:zY9 (apQ.ahT f) (apQ.initial d.common)≠0:= by
      rw [apQ.bHS]
      exact (map_ne_zero_iff _ apQ.bch).mpr hgf
    obtain ⟨l,hd⟩:=d.support
    have hd' := map_dvd (zY9 (apQ.ahT f)) hd
    rw [map_pow] at hd'
    have hdn:=ne_zero_of_dvd_ne_zero (pow_ne_zero l hg) hd'
    have hzL:=congrArg (zY9 (apQ.ahT f)) hl
    have hzR:=congrArg (zY9 (apQ.ahT f)) hr
    rw [apQ.bHS,hroot f hf,map_zero,map_mul] at hzL
    rw [apQ.bHS,necessary_root hP hf,map_zero,map_mul] at hzR
    exact ⟨(mul_eq_zero.mp hzL.symm).resolve_left hdn,(mul_eq_zero.mp hzR.symm).resolve_left hdn⟩
end
end Research6969.ProfileList
end
end Z6969Source2216

-- Source: ProximityPrize.SubmissionLower.ProfileListTariff
section Z6969Source2217
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 24000

namespace Research6969.ProfileList

open i4 Finset
open P5_8 (Jn Gq small smallCaps donorCaps chartCaps tariffShape tW properDegree componentCap)
open P5_8_6 (dNb cofactor_zero cofactor_index emptySum extendSum capRow)
open scoped BigOperators

private theorem excluded {b j n v : ℕ}
    (h : Gq ⟨b, j, 0⟩ = ∑ i ∈ range n, capRow b j i)
    (hs : (∑ i ∈ range n, capRow b j i) = v)
    (hv : 48671 * v < donorMargin) : (gap A + 2) * Gq ⟨b, j, 0⟩ < donorMargin := by
  rw [h, hs]
  exact hv

local notation:65 s:65 " +[" len "," val "]" => extendSum (n := len) (y := val) s rfl

private theorem cutoff_0 : (gap A + 2) * Gq ⟨26, 0, 0⟩ < donorMargin := by
  refine excluded (n := 240) (v := 0x77c3b8bef6) (cofactor_zero 26) ?_ (by decide)
  exact emptySum (capRow 26 0)
    +[32,0x22b1764fc0] +[32,0x1cbbd5afc0] +[32,0x16c6350fc0] +[32,0x10d0946fc0]
    +[32,0xadaf3cfc0] +[32,0x4fdfe9e6f] +[32,0xe3d5ecc7] +[16,0x2dae500]

private theorem cutoff_1 : (gap A + 2) * Gq ⟨24, 1, 0⟩ < donorMargin := by
  refine excluded (n := 260) (v := 0x7a7717d471) (cofactor_index 24 1 (by decide)) ?_ (by decide)
  exact emptySum (capRow 24 1)
    +[32,0x226aeb5208] +[32,0x1c2bc6d908] +[32,0x1648737008] +[32,0x10bebd1708]
    +[32,0xb8c6fce08] +[32,0x6af60c3e9] +[32,0x2637b9980] +[32,0x39e6b100]
    +[4,0x245e0]

private theorem cutoff_2 : (gap A + 2) * Gq ⟨23, 2, 0⟩ < donorMargin := by
  refine excluded (n := 271) (v := 0x7776392413) (cofactor_index 23 2 (by decide)) ?_ (by decide)
  exact emptySum (capRow 23 2)
    +[32,0x2205bd59f0] +[32,0x1b3ee415f0] +[32,0x1528a851f0] +[32,0xfbaca0df0]
    +[32,0xaed0949f0] +[32,0x6b72605f0] +[32,0x314a3c3a7] +[32,0x93a38434]
    +[15,0x1aebc98]

private theorem cutoff_3 : (gap A + 2) * Gq ⟨21, 3, 0⟩ < donorMargin := by
  refine excluded (n := 297) (v := 0x779fb74ef1) (cofactor_index 21 3 (by decide)) ?_ (by decide)
  exact emptySum (capRow 21 3)
    +[32,0x21bc824338] +[32,0x1a9a758838] +[32,0x146ddf5d38] +[32,0xf264bc238]
    +[32,0xab346b738] +[32,0x7045c3c38] +[32,0x409185138] +[32,0x1b2906aab]
    +[32,0x411da1fc] +[9,0x2b12c2]

private theorem cutoff_4 : (gap A + 2) * Gq ⟨18, 4, 0⟩ < donorMargin := by
  refine excluded (n := 347) (v := 0x7962302047) (cofactor_index 18 4 (by decide)) ?_ (by decide)
  exact emptySum (capRow 18 4)
    +[32,0x218d574810] +[32,0x1a329c6c10] +[32,0x13fb039010] +[32,0xece8cb410]
    +[32,0xa9537d810] +[32,0x73704fc10] +[32,0x49bf42010] +[32,0x2ac054410]
    +[32,0x14f386810] +[32,0x6dcf0987] +[27,0x76e7e30]

private theorem cutoff_5 : (gap A + 2) * Gq ⟨13, 5, 0⟩ < donorMargin := by
  refine excluded (n := 391) (v := 0x7b92d42d20) (cofactor_index 13 5 (by decide)) ?_ (by decide)
  exact emptySum (capRow 13 5)
    +[32,0x21916d1f00] +[32,0x1a3fdb9700] +[32,0x1412caff00] +[32,0xef19f5700]
    +[32,0xac3bc9f00] +[32,0x77086d700] +[32,0x4df61ff00] +[32,0x2f7b21700]
    +[32,0x1a0db1f00] +[32,0xc2411700] +[32,0x4347ff00] +[32,0xb53d700]
    +[7,0x118920]

private theorem cutoff_6 : (gap A + 2) * Gq ⟨6, 6, 0⟩ < donorMargin := by
  refine excluded (n := 326) (v := 0x7a020c2306) (cofactor_index 6 6 (by decide)) ?_ (by decide)
  exact emptySum (capRow 6 6)
    +[32,0x21c51c2070] +[32,0x1aac175a70] +[32,0x1482079470] +[32,0xf3cccce70]
    +[32,0xad2470870] +[32,0x738564270] +[32,0x464da7c70] +[32,0x24db3b670]
    +[32,0xe8c1f070] +[32,0x2be52a70] +[6,0x31aca6]

private theorem cutoff_7 : (gap A + 2) * Gq ⟨4, 7, 0⟩ < donorMargin := by
  refine excluded (n := 279) (v := 0x6ce2c95f64) (cofactor_index 4 7 (by decide)) ?_ (by decide)
  exact emptySum (capRow 4 7)
    +[32,0x2170641c30] +[32,0x19becd5830] +[32,0x13136f4430] +[32,0xd6bfde030]
    +[32,0x8c62d2c30] +[32,0x51fb12830] +[32,0x2763dd430] +[32,0xc7873030]
    +[23,0x10876de4]

private def cutoff : ℕ → ℕ
  | 0 => 26
  | 1 => 24
  | 2 => 23
  | 3 => 21
  | 4 => 18
  | 5 => 13
  | _ => 6

private theorem reject {a : Jn}
    (capacity : 0 < a.B → donorMargin ≤ (gap A + 2) * Gq a) {b j : ℕ}
    (hp : 0 < b) (hB : b ≤ a.B) (hJ : j ≤ a.J)
    (hr : (gap A + 2) * Gq ⟨b, j, 0⟩ < donorMargin) : False :=
  (not_le_of_gt hr) ((capacity (hp.trans_le hB)).trans
    (Nat.mul_le_mul_left _ (dNb hp hB hJ (Nat.zero_le a.C))))

private theorem limits {b j c : ℕ}
    (capacity : 0 < b → donorMargin ≤ (gap A + 2) * Gq ⟨b, j, c⟩)
    (top : c ≤ b) (index : j ≤ b + c) : j ≤ 6 ∧ b < cutoff j := by
  have hj : j ≤ 6 := by
    by_contra! h
    exact reject (a := ⟨b, j, c⟩) capacity (by decide : 0 < 4)
      (show 4 ≤ b by omega) (show 7 ≤ j by omega) cutoff_7
  have hc : (gap A + 2) * Gq ⟨cutoff j, j, 0⟩ < donorMargin := by
    interval_cases j
    all_goals simp only [cutoff]
    · exact cutoff_0
    · exact cutoff_1
    · exact cutoff_2
    · exact cutoff_3
    · exact cutoff_4
    · exact cutoff_5
    · exact cutoff_6
  have hp : 0 < cutoff j := by interval_cases j <;> decide
  exact ⟨hj, Nat.lt_of_not_ge fun hb => reject (a := ⟨b, j, c⟩) capacity hp hb le_rfl hc⟩

def lowFee (s : Source) : ℕ := errors A * R₁ s + gap A * H s ^ 2
def regularFee (s : Source) : ℕ := errors A * (2 * R₂ s) + gap A * s.B
def commonFee (a : Jn) : ℕ :=
  lowFee (tariffShape a) + if a.C = 0 then 0 else regularFee (tariffShape a)

def offCommonFee (a : Jn) : ℕ :=
  errors A * properDegree a + gap A * componentCap a

private theorem exact_chart :
    chartCaps = ⟨21495235, 6160222, 2752440⟩ := by
  have ha : a₀ small = 21495235 := rfl
  have hd : D small = 6160222 := rfl
  have he : e small = 2752440 := by
    have hx : t * (small.C - 1) + k - 2 = 2752440 := rfl
    have hy : D small / 2 = 3080111 := by rw [hd]
    rw [e, hx, hy]
    exact min_eq_left (by decide)
  unfold chartCaps
  rw [ha, hd, he]

private theorem low_eq : lowFee small = 18080644949566800 := by
  have hH : H small = 1622 := rfl
  have hI : I₁ small = 283 := rfl
  have ha : a₁ small = 0x1953e058 := rfl
  have hd : d₁ small = 0x469fa7d := rfl
  have hr : R₁ small = 0x33160a2d17 := by rw [R₁, hH, hd, hI, ha]
  rw [lowFee, hr, hH]
  rfl

private def fee (r n : ℕ) := 82404 * r + 48669 * n

private def total (a : Jn) : ℕ :=
  let s := tariffShape a
  fee (R₁ s) (H s ^ 2) + (if a.C = 0 then 0 else fee (2 * R₂ s) s.B) +
    fee (tW (smallCaps.wD a).repair (donorCaps.wD a).repair
      ⟨21495235, 6160222, 2752440⟩) (componentCap a) + 18080644949566800

private theorem total_eq (a : Jn) :
    commonFee a + offCommonFee a + lowFee small = total a := by
  have herr : errors A = 82404 := rfl
  have hgap : gap A = 48669 := rfl
  rw [low_eq]
  simp only [total, commonFee, offCommonFee, properDegree, exact_chart, lowFee, regularFee,
    herr, hgap, fee]

private def Band (b stop j c : ℕ) : Prop :=
  ∀ i, b ≤ i → i < stop → total ⟨i, j, c⟩ ≤ 2530792305825209757

private theorem done {b j c : ℕ} : Band b b j c := by
  intro i hl hu
  omega

private theorem bandCons {b stop j c v : ℕ}
    (he : total ⟨b, j, c⟩ = v) (hv : v ≤ 2530792305825209757)
    (ht : Band (b + 1) stop j c) : Band b stop j c := by
  intro i hl hu
  by_cases h : i = b
  · rwa [h, he]
  · exact ht i (by omega) hu

local notation:65 val:66 " |+| " tail:65 => bandCons (v := val) rfl (by decide) tail

private theorem cost_0_0 : Band 0 26 0 0 :=
  0x1b617e293753981 |+| 0x1b44dfe130bb908 |+| 0x1b2841992a3b4c9 |+| 0x1b0ba46aca4c515 |+|
  0x1aef073c6a8cdd5 |+| 0x1ad26a0e0afcf09 |+| 0x1ab5ccdfab9c8b1 |+| 0x1a992fb14c6bacd |+|
  0x1a7c9282ed6a55d |+| 0x1a5ff5548e98861 |+| 0x1a4358262ff63d9 |+| 0x1a26baf7d1837c5 |+|
  0x1a0a1dc97340425 |+| 0x19ed809b152c8f9 |+| 0x19d0e36cb748641 |+| 0x19b4463e5993bfd |+|
  0x1997a90ffc0ea2d |+| 0x197b0be19eb90d1 |+| 0x195e6eb34192fe9 |+| 0x1941d184e49c775 |+|
  0x1925345687d5775 |+| 0x190897282b3dfe9 |+| 0x18ebf9f9ced60d1 |+| 0x18cf5ccb729da2d |+|
  0x18b2bf9d1694bfd |+| 0x1896226ebabb641 |+|
  done

private theorem cost_1_0 : Band 1 24 1 0 :=
  0x1ab8ed5d57a28d0 |+| 0x1a9c55af32d1451 |+| 0x1a7fbf1ab49145d |+| 0x1a6328863680cdd |+|
  0x1a4691f1b89fdd1 |+| 0x1a29fb5d3aee739 |+| 0x1a0d64c8bd6c915 |+| 0x19f0ce34401a365 |+|
  0x19d4379fc2f7629 |+| 0x19b7a10b4604161 |+| 0x199b0a76c94050d |+| 0x197e73e24cac12d |+|
  0x1961dd4dd0475c1 |+| 0x194546b954122c9 |+| 0x1928b024d80c845 |+| 0x190c19905c36635 |+|
  0x18ef82fbe08fc99 |+| 0x18d2ec676518b71 |+| 0x18b655d2e9d12bd |+| 0x1899bf3e6eb927d |+|
  0x187d28a9f3d0ab1 |+| 0x186092157917b59 |+| 0x1843fb80fe8e475 |+|
  done

private theorem cost_2_0 : Band 2 23 2 0 :=
  0x1a1016788eb2375 |+| 0x19f387471f37139 |+| 0x19d6f815afeb771 |+| 0x19ba68e440cf61d |+|
  0x199dd9b2d1e2d3d |+| 0x19814a816325cd1 |+| 0x1964bb4ff4984d9 |+| 0x19482c1e863a555 |+|
  0x192b9ced180be45 |+| 0x190f0dbbaa0cfa9 |+| 0x18f27e8a3c3d981 |+| 0x18d5ef58ce9dbcd |+|
  0x18b96027612d68d |+| 0x189cd0f5f3ec9c1 |+| 0x188041c486db569 |+| 0x1863b29319f9985 |+|
  0x18472361ad47615 |+| 0x182a943040c4b19 |+| 0x180e04fed471891 |+| 0x17f175cd684de7d |+|
  0x17d4e69bfc59cdd |+|
  done

private theorem cost_2_1 : Band 1 23 2 1 :=
  0x1c4fac639e135fa |+| 0x1c331ce1b51cd2b |+| 0x1eeac98079f6bf4 |+| 0x21a2761f3f00331 |+|
  0x245a22be04392e2 |+| 0x2711cf5cc9a1b07 |+| 0x29c97bfb8f39ba0 |+| 0x2c81289a55014ad |+|
  0x2f38d5391af862e |+| 0x31f081d7e11f023 |+| 0x34a82e76a77528c |+| 0x375fdb156dfad69 |+|
  0x3a1787b434b00ba |+| 0x3ccf3452fb94c7f |+| 0x3f86e0f1c2a90b8 |+| 0x423e8d9089ecd65 |+|
  0x44f63a2f5160286 |+| 0x47ade6ce190301b |+| 0x4a65936ce0d5624 |+| 0x4d1d400ba8d74a1 |+|
  0x4fd4ecaa7108b92 |+| 0x528c99493969af7 |+|
  done

private theorem cost_3_0 : Band 3 21 3 0 :=
  0x1967aa9bf96ca29 |+| 0x194b22a55d06d39 |+| 0x192e9aaec0d08bd |+| 0x191212b824c9cb5 |+|
  0x18f58ac188f2921 |+| 0x18d902caed4ae01 |+| 0x18bc7ad451d2b55 |+| 0x189ff2ddb68a11d |+|
  0x18836ae71b70f59 |+| 0x1866e2f08087609 |+| 0x184a5af9e5cd52d |+| 0x182dd3034b42cc5 |+|
  0x18114b0cb0e7cd1 |+| 0x17f4c31616bc551 |+| 0x17d83b1f7cc0645 |+| 0x17bbb328e2f3fad |+|
  0x179f2b324957189 |+| 0x1782a33bafe9bd9 |+|
  done

private theorem cost_3_1 : Band 2 21 3 1 :=
  0x29cc6a562a6c2c5 |+| 0x29afe16e233c5f0 |+| 0x36261dc9f9bf135 |+| 0x429c5a25d0714ee |+|
  0x4f129681a75311b |+| 0x5b88d2dd7e645bc |+| 0x67ff0f3955a52d1 |+| 0x74754b952d1585a |+|
  0x80eb87f104b5657 |+| 0x8d61c44cdc84cc8 |+| 0x99d800a8b483bad |+| 0xa64e3d048cb2306 |+|
  0xb2c4796065102d3 |+| 0xbf3ab5bc3d9db14 |+| 0xcbb0f218165abc9 |+| 0xd8272e73ef474f2 |+|
  0xe49d6acfc86368f |+| 0xf113a72ba1af0a0 |+| 0xfd89e3877b2a325 |+|
  done

private theorem cost_4_0 : Band 4 18 4 0 :=
  0x18aee3241d260f9 |+| 0x189263faae01545 |+| 0x1875e4d13f0c205 |+| 0x185965a7d046739 |+|
  0x183ce67e61b04e1 |+| 0x18206754f349afd |+| 0x1803e82b851298d |+| 0x17e76902170b091 |+|
  0x17cae9d8a933009 |+| 0x17ae6aaf3b8a7f5 |+| 0x1791eb85ce11855 |+| 0x17756c5c60c8129 |+|
  0x1758ed32f3ae271 |+| 0x173c6e0986c3c2d |+|
  done

private theorem cost_4_1 : Band 3 18 4 1 :=
  0x41a85b7028a99a8 |+| 0x418bd9eb30566c5 |+| 0x58111edbdb38b9e |+| 0x6e9663cc864a8eb |+|
  0x851ba8bd318beac |+| 0x9ba0edaddcfcce1 |+| 0xb226329e889d38a |+| 0xc8ab778f346d2a7 |+|
  0xdf30bc7fe06ca38 |+| 0xf5b601708c9ba3d |+| 0x10c3b466138fa2b6 |+| 0x122c08b51e5883a3 |+|
  0x13945d0429245d04 |+| 0x14fcb15333f32ed9 |+| 0x166505a23ec4f922 |+|
  done

private theorem cost_4_2 : Band 2 18 4 2 :=
  0x5490b9338895979 |+| 0x54743877bd40854 |+| 0x5457b7bbf203369 |+| 0x753c75c4c02fcba |+|
  0x962133cd8f4a04f |+| 0xb705f1d65f51e28 |+| 0xd7eaafdf3047645 |+| 0xf8cf6de8022a8a6 |+|
  0x119b42bf0d4fb54b |+| 0x13a98e9f9a8b9c34 |+| 0x15b7da8027d65d61 |+| 0x17c62660b52ff8d2 |+|
  0x19d4724142986e87 |+| 0x1be2be21d00fbe80 |+| 0x1df10a025d95e8bd |+| 0x1fff55e2eb2aed3e |+|
  done

private theorem cost_5_0 : Band 5 13 5 0 :=
  0x1806b2b0764cbdd |+| 0x17ea3ac1da3d575 |+| 0x17cdc2d33e5d781 |+| 0x17b14ae4a2ad201 |+|
  0x1794d2f6072c4f5 |+| 0x17785b076bdb05d |+| 0x175be318d0b9439 |+| 0x173f6b2a35c7089 |+|
  done

private theorem cost_5_1 : Band 4 13 5 1 :=
  0x6393b7823d57997 |+| 0x63773c9726cb2ae |+| 0x840b895378f7323 |+| 0xa49fd60fcb52c0c |+|
  0xc53422cc1dddd69 |+| 0xe5c86f88709873a |+| 0x1065cbc44c38297f |+| 0x126f10901169c438 |+|
  0x1478555bd69e5765 |+|
  done

private theorem cost_5_2 : Band 3 13 5 2 :=
  0x9e173568bc17bca |+| 0x9dfabb46d28969f |+| 0x9dde4124e912dae |+| 0xd7980f2319925bb |+|
  0x11151dd214aff80c |+| 0x14b0bab1f7d5a4a1 |+| 0x184c5791db0a2b7a |+| 0x1be7f471be4d8c97 |+|
  0x1f839151a19fc7f8 |+| 0x231f2e318500dd9d |+|
  done

private theorem cost_6_1 : Band 5 6 6 1 :=
  0x8f7db889df38ff2 |+|
  done

private theorem cost_6_2 : Band 4 6 6 2 :=
  0x10163dd0c47c9993 |+| 0x101476a4d6d17e5a |+|
  done

private theorem cost_6_3 : Band 3 6 6 3 :=
  0x11eabcd5e0275e6b |+| 0x11e8f5b6854c24f0 |+| 0x11e72e972a7267af |+|
  done

private theorem total_le {b j c : ℕ} (hj : j ≤ 6) (hb : b < cutoff j)
    (hc : 2 * c ≤ j) (ht : c ≤ b) (hi : j ≤ b + c) :
    total ⟨b, j, c⟩ ≤ 2530792305825209757 := by
  have hc' : c ≤ j / 2 := by omega
  interval_cases j
  all_goals interval_cases c
  · exact cost_0_0 b (by omega) hb
  · exact cost_1_0 b (by omega) hb
  · exact cost_2_0 b (by omega) hb
  · exact cost_2_1 b (by omega) hb
  · exact cost_3_0 b (by omega) hb
  · exact cost_3_1 b (by omega) hb
  · exact cost_4_0 b (by omega) hb
  · exact cost_4_1 b (by omega) hb
  · exact cost_4_2 b (by omega) hb
  · exact cost_5_0 b (by omega) hb
  · exact cost_5_1 b (by omega) hb
  · exact cost_5_2 b (by omega) hb
  · have hstop : b < 6 := hb
    omega
  · exact cost_6_1 b (by omega) hb
  · exact cost_6_2 b (by omega) hb
  · exact cost_6_3 b (by omega) hb

theorem list_tariff (a : Jn)
    (capacity : 0 < a.B → donorMargin ≤ (gap A + 2) * Gq a)
    (hc : 2 * a.C ≤ a.J) (ht : a.C ≤ a.B) (hi : a.J ≤ a.B + a.C) :
    commonFee a + offCommonFee a + lowFee small ≤ gap A * Profile.listCap := by
  rcases a with ⟨b, j, c⟩
  obtain ⟨hj, hb⟩ := limits capacity ht hi
  rw [total_eq]
  exact (total_le hj hb hc ht hi).trans (by decide)

end Research6969.ProfileList
end Z6969Source2217

-- Source: ProximityPrize.SubmissionLower.ProfileProtocol
section Z6969Source2218
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000
set_option linter.constructorNameAsVariable false

namespace Research6969.ProfileProtocol
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem
open FrobeniusLocator ProximityPrize.Benchmark
open Sol1.OneCount Sol1.FiniteRowProjection
abbrev I := P3.I
abbrev K := P3.K
abbrev Words := P3.Words
abbrev node := P3.node
abbrev k := P3.k
open scoped NNReal

abbrev agreement := Profile.agreement
abbrev radiusNumerator := Profile.p
abbrev radiusDenominator := Profile.q
abbrev listCap := Profile.listCap
abbrev scalarCap := Profile.scalarCap
def queryRadius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator
def radius : ℝ := queryRadius
def BadFamily (u : Words) (Γ : Finset K) : Prop :=
  ∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius

theorem agreement_of_threshold {s : ℕ}
    (hs : (Fintype.card I : ℝ) * (1-radius) ≤ s) : agreement ≤ s := by
  rw [IRSProfile.card_index] at hs
  exact Profile.threshold hs
theorem query_score : (1 - queryRadius) ^ IRSProfile.repetitions ≤ claimedError 6969 := by
  simpa [queryRadius,claimedError] using Profile.score
theorem query_admissible : queryRadius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := Profile.admissible
theorem scalar_projection_room : scalarCap + 1 < (0x7f000001 : ℕ) ^ 6 := by decide
theorem list_projection_room : (listCap + 1) ^ 2 < (0x7f000001 : ℕ) ^ 6 := by decide
theorem close_agreement_ge (f w : I → A16)
    (hd : (δᵣ(w,f) : ℝ) ≤ radius) : agreement ≤ agreementCard f w := by
  classical
  have hpos : 0 < Fintype.card I := by rw [IRSProfile.card_index]; decide
  have hposR : (0 : ℝ) < Fintype.card I := by exact_mod_cast hpos
  have hradius : radius =
      1 - ((Fintype.card I : ℝ) * (1 - radius)) / Fintype.card I := by
    rw [mul_comm, mul_div_cancel_right₀ _ hposR.ne']
    ring
  have hagree := (Code.relHammingDist_le_one_sub_div_iff hpos).mp
    (show (δᵣ(w,f) : ℝ) ≤ 1 - ((Fintype.card I : ℝ) * (1 - radius)) / Fintype.card I by
      rwa [← hradius])
  have hcard : Code.agree f w ≤ agreementCard f w := by
    unfold Code.agree agreementCard
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi
  exact (agreement_of_threshold hagree).trans hcard
theorem squared_lambda_le (hlist : CJ0.ScalarList agreement listCap) :
    Code.Lambda (squaredCode : Set (I → A16)) radius ≤ (listCap : ℕ∞) :=
  CJ0.squared_lambda_le hlist (Sol1.C64.native_field_card ▸ list_projection_room.le)
    radius close_agreement_ge
def nativeBadSlopes (U : Sol1.C64.NativePair) : Finset K := by
  classical
  exact Finset.univ.filter fun γ => IsMCA (AffineLineGenerator K) IRSProfile.code γ U radius
theorem native_cap_of_scalar_cap
    (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) (U : Sol1.C64.NativePair) :
    (nativeBadSlopes U).card ≤ scalarCap := by
  classical
  apply Sol1.C64.restricted_interleaved_card_le IRSProfile.baseCode
    (⊤ : ModuleCode I K K) radius scalarCap
    (by rw [Sol1.C64.native_field_card]; exact scalar_projection_room.le)
    (fun u _ Γ hΓ => hscalar u Γ hΓ) U (by simp) (nativeBadSlopes U)
  intro γ hγ
  change γ ∈ Finset.univ.filter (fun z => IsMCA (AffineLineGenerator K)
    IRSProfile.code z U radius) at hγ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
  rw [Sol1.C64.native_code_eq] at hγ
  exact hγ
theorem mca_error_le_of_scalar_cap (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) :
    mcaError (AffineLineGenerator K) IRSProfile.code radius ≤
      (scalarCap : ENNReal) / (Fintype.card K : ENNReal) := by
  classical
  refine iSup_le fun U => ?_
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  change ENNReal.ofReal (((nativeBadSlopes U).card : ℝ) / Fintype.card K) ≤ _
  calc
    _ ≤ ENNReal.ofReal ((scalarCap : ℝ) / Fintype.card K) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right (by exact_mod_cast native_cap_of_scalar_cap hscalar U)
        (by positivity)
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]
theorem error_budget :
    (scalarCap + listCap) * 2 ^ 128 ≤ (0x7f000001 : ℕ) ^ 6 := Profile.field_budget
theorem gamma_error_le_of_scalar_cap (hlist : CJ0.ScalarList agreement listCap)
    (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) :
    ToyProblem.certifiedGammaError IRSProfile.code queryRadius ≤ reductionTarget := by
  have hNat := ENat.toNat_le_of_le_natCast (squared_lambda_le hlist)
  have hList :
      ((Code.Lambda (squaredCode : Set (I → A16)) radius).toNat : ENNReal) /
        (Fintype.card K : ENNReal) ≤ (listCap : ENNReal) / Fintype.card K :=
    ENNReal.div_le_div_right (by exact_mod_cast hNat) _
  have hreal : ((scalarCap + listCap : ℕ) : ℝ) / Fintype.card K ≤ (1 : ℝ) / 2 ^ 128 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    norm_num only [one_mul]
    exact_mod_cast (Sol1.C64.native_field_card ▸ error_budget :
      (scalarCap + listCap) * 2 ^ 128 ≤ Fintype.card K)
  have hENN : ((scalarCap + listCap : ℕ) : ENNReal) / Fintype.card K ≤
      (1 : ENNReal) / 2 ^ 128 := by
    have h := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast, ENNReal.ofReal_div_of_pos (by positivity)] at h
    simpa using h
  rw [← ENNReal.coe_le_coe, ToyProblem.coe_certifiedGammaError]
  calc
    _ ≤ (scalarCap : ENNReal) / Fintype.card K + (listCap : ENNReal) / Fintype.card K :=
      add_le_add (mca_error_le_of_scalar_cap hscalar) hList
    _ = ((scalarCap + listCap : ℕ) : ENNReal) / Fintype.card K := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ 128 := hENN
    _ = (reductionTarget : ENNReal) := by
      norm_num [reductionTarget, ProximityGap.prizeThreshold]
theorem protocol_claim_of_scalar_cap (hlist : CJ0.ScalarList agreement listCap)
    (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) :
    ProtocolClaim 6969 radiusNumerator radiusDenominator where
  admissible := query_admissible
  reduction := gamma_error_le_of_scalar_cap hlist hscalar
  score := query_score

/-- The list bound and the uniform bound on bad slopes suffice for the soundness claim. -/
theorem of_bad_slopes (hlist : CJ0.ScalarList agreement listCap)
    (bound : ∀ (u : Words) (Γ : Finset K),
    (∀ γ ∈ Γ, Principal.BadSlope node (u 0) (u 1) k agreement γ) → Γ.card ≤ scalarCap) :
    ProtocolClaim 6969 radiusNumerator radiusDenominator := by
  apply protocol_claim_of_scalar_cap hlist
  intro u Γ hΓ
  apply bound u Γ
  intro γ hγ
  let : NeZero k := ⟨by decide⟩
  exact Principal.isMCA_implies_badSlope node u k agreement radius
    (fun _ h => agreement_of_threshold h) γ (hΓ γ hγ)


theorem bad_mark (u : Words) (γ : K)
    (hγ : IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius) :
    Nonempty (P1.BadMarkAt agreement u γ) := by
  let : NeZero k := ⟨by decide⟩
  obtain ⟨S, hS, ⟨P, hP, he⟩, hn⟩ :=
    Principal.isMCA_implies_badSlope node u k agreement radius
      (fun _ h => agreement_of_threshold h) γ hγ
  exact ⟨⟨S, P, hS, hP, he, hn⟩⟩

theorem anchored_list_count (hlist : CJ0.ScalarList agreement listCap)
    {u deleted} (M : P1.ModelAt Profile.heightCap u deleted) (Γ : Finset K)
    (F : P1.FamilyAt agreement M Γ) (hw : M.overhead ≤ 0) :
    Γ.card ≤ listCap :=
  P1.anchored_list_count hlist M Γ F hw

end
end Research6969.ProfileProtocol
end Z6969Source2218

-- Source: ProximityPrize.SubmissionLower.ProfileListAssembly
section Z6969Source2219
set_option autoImplicit true
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

open P6_8 (FactorCharts)

open _root_ renaming Fin.last → zym, Finset → zJe, Finset.sum_add_distrib → zfW, Finset.sum_mul → zkq, Fintype.card → zhP, Fintype.equivFinOfCardEq → zFl, MvPolynomial.eval → zY9, Nat.add_le_add → z9f, Nat.add_le_add_left → z3b, Nat.cast_nonneg → zqJ, Nat.le_add_right → z8K, Nat.mul_add → zws, Nat.mul_le_mul_left → zBI
section
set_option autoImplicit true
namespace Research6969.ProfileList
noncomputable section
open i4 MvPolynomial Finset Filter
open P5_8 (Jn Equation ProperCharts caps smallCaps donorCaps chartCaps properDegree componentCap)
open P5_8_5
open scoped BigOperators Polynomial
open P5_8_5 (cp0)
open P5_8_5 (within mix_mono mix_symm jetCaps_ok repair_ok bct floor_mix)
open qTS2oyd (addCaps jetCaps_mul)
open i4 (aTZ)
private theorem image_slope {L R:BL 2} (hL:L≠0) (hR:R≠0)
    (hrel :IsRelPrime L R) (F:ProperCharts L R)
    (hd : ∀ i,(affineHilbertPolynomial (F.ideal i)).natDegree=1) :
    (∑ i,affineDegree (F.ideal i))≤ mix (jetCaps L) (jetCaps R) chartCaps := by
  obtain ⟨shift,hshift⟩:=qIWmIFe.proof F
  obtain ⟨hu₁,hu₂,hu₃⟩:=A9
  have hu:=(tendsto_add_atTop_nat shift).eventually
    (qTS2oyd.proof L R hL hR hrel chartCaps hu₁ hu₂ hu₃)
  have he : ∀ᶠ m:ℕ in atTop,∀ i:Fin F.count,
      (affineHilbertPolynomial (F.ideal i)).eval (m:ℚ) =
        (affineHilbertFunction (F.ideal i) m:ℚ) :=
    eventually_all.mpr fun i=>eventually_eval_affineHilbertPolynomial (F.ideal i)
  let s := ∑ i,affineDegree (F.ideal i)
  let t := ∑ i,(affineHilbertPolynomial (F.ideal i)).coeff 0
  let M:=mix (jetCaps L) (jetCaps R) chartCaps
  let B:=boxDifference chartCaps (jetCaps L) (jetCaps R) 0
  have hle : ∀ᶠ m:ℕ in atTop,s*(m:ℚ)+t≤M*(m:ℚ)+(M*shift+B) := by
    filter_upwards [he,hu] with m hm hq
    have hs :s*(m:ℚ)+t=(∑ i,affineHilbertFunction (F.ideal i) m:ℕ) := by
      rw [Nat.cast_sum,zkq,← zfW]
      exact Finset.sum_congr rfl fun i _=>(linear_eval _ (hd i) _).symm.trans (hm i)
    rw [hs]
    refine ((Nat.cast_le (α:=ℚ)).mpr (hshift m)).trans ?_
    rw [boxDifference_linear,Nat.cast_add,mul_add,add_assoc] at hq
    exact hq
  exact cp0 hle
private def sumCaps {ι:Type*} (s :zJe ι) (a :ι→Jn) :Jn :=
  ⟨∑ i∈s,(a i).B,∑ i∈s,(a i).J,∑ i∈s,(a i).C⟩
private theorem eOT {ι:Type*} (s :zJe ι) (p:ι→BL 2)
    (h: (∏ i∈s,p i)≠0) :jetCaps (∏ i∈s,p i)=sumCaps s (jetCaps ∘ p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [jetCaps,sumCaps]
    rw [← MvPolynomial.C_1,weightedTotalDegree_C]
  | insert i s hi ih =>
    rw [prod_insert hi] at h ⊢
    rw [jetCaps_mul (left_ne_zero_of_mul h) (right_ne_zero_of_mul h),ih (right_ne_zero_of_mul h)]
    simp [sumCaps,addCaps,hi]
private theorem sum_mix {ι:Type*} (s :zJe ι) (a :ι→Jn) (b u:Jn) :
    (∑ i∈s,mix (a i) b u)=mix (sumCaps s a) b u:= by
  simp only [mix,sumCaps,Nat.cast_sum,zkq,zfW]
private theorem caps_mono {L R:BL 2} (h:L∣R) (hR:R≠0) :
    within (jetCaps L) (jetCaps R) := by
  obtain ⟨V,rfl⟩:=h
  rw [jetCaps_mul (left_ne_zero_of_mul hR) (right_ne_zero_of_mul hR)]
  exact ⟨z8K ..,z8K ..,z8K ..⟩
private theorem left_ne {Q:Equation} {w:Node→K} (hQ:Q≠0) (d:Companion Q w) :
    d.left≠0:= by
  apply apQ.b6j
  rw [d.azo] at hQ
  exact right_ne_zero_of_mul hQ
theorem ePy {Q:Equation} {w:Node→K} (hQ:Q≠0) (d:Companion Q w)
    {F:FactorCharts d.left d.right} {T:zJe (Polynomial K)}
    (ht: (T:Set (Polynomial K))⊆close A w)
    (hcover : ∀ f∈T,∃ i j,Gp f∈(F.charts i).image j) :
    gap A*T.card≤ offCommonFee (caps d.common) := by
  classical
  let p (i:Fin F.count) :=apQ.initial (F.factor i)
  have hL:=left_ne hQ d
  have hdvd (i:Fin F.count) :p i∣d.left :=
    (dvd_prod_of_mem p (mem_univ i)).trans F.bKQ
  have hn (i:Fin F.count) :p i≠0:=ne_zero_of_dvd_ne_zero hL (hdvd i)
  have hrel (i:Fin F.count) :IsRelPrime (p i) d.right:=d.coprime.of_dvd_left (hdvd i)
  let I:=Σ i:Fin F.count,Fin (F.charts i).count
  let C (i:I) :=(F.charts i.1).ideal i.2
  have dim (i:I) : (affineHilbertPolynomial (C i)).natDegree=1 :=
    (enK (F.charts i.1) i.2).2.trans
      (dOy (hn i.1) (hrel i.1) ((F.charts i.1).minimal i.2))
  let a :=(smallCaps.wD (caps d.common)).repair
  let b:=(donorCaps.wD (caps d.common)).repair
  have hs :jetCaps (∏ i,p i)=sumCaps univ (jetCaps ∘ p) :=
    eOT _ _ (ne_zero_of_dvd_ne_zero hL F.bKQ)
  have ha :within (sumCaps univ (jetCaps ∘ p)) a := by
    rw [← hs]
    exact ⟨(caps_mono F.bKQ hL).1.trans (aFz.aIz.mp d.left_band).1,
      (caps_mono F.bKQ hL).2.1.trans (aFz.aIz.mp d.left_band).2.1,
      (caps_mono F.bKQ hL).2.2.trans (aFz.aIz.mp d.left_band).2.2⟩
  have hb:within (jetCaps d.right) b:=aFz.aIz.mp d.right_band
  have hcount:zhP I≤ componentCap (caps d.common) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    calc
      _ ≤ ∑ i,(p i).totalDegree*d.right.totalDegree :=
        sum_le_sum fun i _=>component_count (hn i) (hrel i) (F.charts i)
      _=(sumCaps univ (jetCaps ∘ p)).B*(jetCaps d.right).B :=
        (zkq ..).symm
      _≤_:=Nat.mul_le_mul (ha.1.trans (by rfl)) (hb.1.trans (by rfl))
  have hdeg: (∑ i,affineDegree (C i))≤(properDegree (caps d.common) :ℚ) := by
    have hsum: (∑ i,affineDegree (C i))≤ mix a b chartCaps := by
      obtain ⟨_,hc,hj⟩:=A9
      have h₁:=mix_mono ha (jetCaps_ok d.right) hc.le hj.le
      have h₂:mix (jetCaps d.right) a chartCaps≤ mix b a chartCaps :=
        mix_mono hb (repair_ok (smallCaps.wD (caps d.common))) hc.le hj.le
      rw [mix_symm (jetCaps d.right) a,mix_symm b a] at h₂
      calc
        _ = ∑ i,∑ j,affineDegree (C ⟨i,j⟩) :=Fintype.sum_sigma _
        _ ≤ ∑ i,mix (jetCaps (p i)) (jetCaps d.right) chartCaps :=
          sum_le_sum fun i _=>image_slope (hn i) d.right_ne (hrel i) (F.charts i) (fun j=>dim ⟨i,j⟩)
        _=mix (sumCaps univ (jetCaps ∘ p)) (jetCaps d.right) chartCaps :=
          sum_mix _ (jetCaps ∘ p) _ _
        _≤_:=h₁.trans h₂
    choose z hz using fun i:I=>linear_degree_integral (C i) (dim i)
    have hint : (∑ i,affineDegree (C i))=((∑ i,z i:ℤ) :ℚ) := by simp [hz,Int.cast_sum]
    have hfloor :=(Int.floor_mono hsum).trans_eq (floor_mix a b chartCaps (repair_ok _) (repair_ok _) bct)
    rw [hint,Int.floor_intCast] at hfloor
    rw [hint]
    exact_mod_cast hfloor
  let part (i:I) :=T.filter fun f=>Gp f∈(F.charts i.1).image i.2
  have hc:T.card ≤ ∑ i,(part i).card:= by
    apply (card_le_card (t:=univ.biUnion part) ?_).trans card_biUnion_le
    intro f hf
    obtain ⟨i,j,hij⟩:=hcover f hf
    exact mem_biUnion.mpr ⟨⟨i,j⟩,mem_univ _,mem_filter.mpr ⟨hf,hij⟩⟩
  have hp (i:I) : (gap A:ℚ)*(part i).card≤(errors A:ℚ)*affineDegree (C i)+gap A :=
    (aTZ (T:=part i) (fun _ hf=>ht (mem_filter.mp hf).1) agreement_ok
      (enK (F.charts i.1) i.2).1 (dim i)
      (fun _ hf=>zeroLocus_vanishingIdeal_le _ (mem_filter.mp hf).2)).1
  have hq: (T.card:ℚ) ≤ ∑ i,((part i).card:ℚ) := by exact_mod_cast hc
  have hbill: (gap A:ℚ)*T.card≤(errors A:ℚ)*properDegree (caps d.common) +
      gap A*componentCap (caps d.common) := calc
    _≤(gap A:ℚ) * ∑ i,((part i).card:ℚ) :=mul_le_mul_of_nonneg_left hq (zqJ _)
    _ = ∑ i,(gap A:ℚ)*(part i).card:=mul_sum ..
    _≤_:=sum_le_sum fun i _=>hp i
    _=(errors A:ℚ)*(∑ i,affineDegree (C i))+gap A*zhP I:= by
      rw [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,card_univ,mul_comm (zhP I:ℚ)]
    _≤_:=add_le_add (mul_le_mul_of_nonneg_left hdeg (zqJ _))
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hcount) (zqJ _))
  unfold offCommonFee
  exact_mod_cast hbill
end
end Research6969.ProfileList
end
section
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Research6969.ProfileList
noncomputable section
open i4 apQ MvPolynomial PolynomialDifferential UniqueFactorizationMonoid
open P5_8 (small small_shape ProperCharts chartOpen ke)
open scoped Polynomial BigOperators
open cxa (cVd cfE)
local instance :StrongNormalizationMonoid Equation :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
private theorem charts (G:Equation) (R:BL 2) (hG:ato small G) :
    ∃ F:ProperCharts (initial G) R,∀ f :(Polynomial K),f.degree<k →
      differentialSpecialization G f=0 →
      differentialSpecialization (separant G (zym 2)) f≠0 →
      zY9 (ahT f) R=0 → ∃ j,Gp f∈F.image j:= by
  classical
  let S:=(ke (initial G) R).minimalPrimesFinset.filter fun J=>T4 G∉J
  let e :Fin S.card ≃ ↥S:=(zFl (Fintype.card_coe S)).symm
  have he (i:Fin S.card) :=Finset.mem_filter.mp (e i).property
  have hm (i:Fin S.card) : (e i).val∈(ke (initial G) R).minimalPrimes :=
    Ideal.mem_minimalPrimesFinset.mp (he i).1
  let F:ProperCharts (initial G) R := {
    count:=S.card
    component:= fun i=>(e i).val
    distinct :=Subtype.val_injective.comp e.injective
    minimal:=hm
    bY:= fun _=>bY G (initial G)
    den_reg:= fun i h=>(he i).2 ((hm i).isPrime.mem_of_pow_mem t h)
    bands := fun _=> by
      simp only [bY]
      exact ⟨b0p hG,fun j =>
        eFC (G:=G) small_shape hG (cxb.proof small small_shape G hG) j⟩
    recover := fun _ x hx j=>a2o G (initial G) x (fun hz=>hx.2 (by
      change zY9 x (T4 G^t)=0
      rw [map_pow,hz,zero_pow (by decide :t≠0)])) j }
  refine ⟨F,?_⟩
  intro f hf hroot hsep hR
  let ev :=zY9 (ahT f)
  have hL:ev (initial G)=0:= by rw [bHS,hroot,map_zero]
  have hS:ev (T4 G)≠0:= by
    rw [eom]
    exact (map_ne_zero_iff RG bch).mpr hsep
  have hcut:ke (initial G) R≤RingHom.ker ev := by
    simp only [ke,Ideal.span_insert,sup_le_iff,Ideal.span_singleton_le_iff_mem]
    exact ⟨hL,hR⟩
  let: (RingHom.ker ev).IsPrime :=RingHom.ker_isPrime ev
  obtain ⟨J,hJ,hpoint⟩:=Ideal.exists_minimalPrimes_le hcut
  let v : ↥S:=⟨J,Finset.mem_filter.mpr
    ⟨Ideal.mem_minimalPrimesFinset.mpr hJ,fun h=>hS (hpoint h)⟩⟩
  let i:=e.symm v
  refine ⟨i,ahT f,?_,dIj G (initial G) f hf hroot hS⟩
  change ahT f∈chartOpen (e i).val (bY G (initial G))
  rw [e.apply_symm_apply v]
  exact ⟨fun _ h=>hpoint h,by
    change ev (T4 G^t)≠0
    rw [map_pow]
    exact pow_ne_zero _ hS⟩
theorem factor_charts {w:Node→K} {Q:Equation} (hQ:ato small Q)
    (d:Companion Q w) :
    ∃ F:FactorCharts d.left d.right,
      ∀ f∈close A w,ae8 Q f→differentialSpecialization d.common f≠0 →
        ∃ i j,Gp f∈(F.charts i).image j:= by
  classical
  have hLn:d.leftNative≠0:= fun h =>
    hQ.1 (d.azo.trans (by rw [h,mul_zero]))
  have hLQ:d.leftNative∣Q:=⟨d.jO,d.azo.trans (mul_comm _ _)⟩
  let S:=(normalizedFactors d.leftNative).toFinset
  let e :Fin S.card ≃ ↥S:=(zFl (Fintype.card_coe S)).symm
  let G (i:Fin S.card) :=(e i).val
  have hG (i:Fin S.card) :ato small (G i) :=
    eHq hQ ((dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (e i).property)).trans hLQ)
  choose C hC using fun i=>charts (G i) d.right (hG i)
  have hprod: (∏ i,initial (G i))∣d.left:= by
    have hs : (∏ g∈S,g)∣d.leftNative :=
      (Multiset.toFinset_prod_dvd_prod _).trans (prod_normalizedFactors hLn).dvd
    have hm:=map_dvd cVd hs
    rw [map_prod] at hm
    change (∏ g∈S,initial g)∣d.left at hm
    have he : (∏ i,initial (G i)) = ∏ g∈S,initial g :=
      (e.prod_comp (fun g : ↥S=>initial g.val)).trans (Finset.prod_coe_sort S initial)
    rwa [he]
  refine ⟨⟨S.card,G,hprod,C⟩,?_⟩
  intro f hf hr ho
  obtain ⟨g,hgi,hgd,hgr,hgs⟩:=hr
  have hgL:g∣d.leftNative := by
    rw [d.azo] at hgd
    rcases hgi.prime.dvd_mul.mp hgd with h | h
    · obtain ⟨l,hl⟩:=d.removed_support
      have hz :=map_dvd (zY9 (ahT f)) ((map_dvd cVd h).trans hl)
      change zY9 (ahT f) (initial g) ∣
        zY9 (ahT f) (initial d.common^l) at hz
      rw [bHS,hgr,map_zero,zero_dvd_iff,map_pow,bHS] at hz
      exact (pow_ne_zero l ((map_ne_zero_iff RG bch).mpr ho) hz).elim
    · exact h
  obtain ⟨g',hmem,hassoc⟩:=exists_mem_normalizedFactors_of_dvd hLn hgi hgL
  obtain ⟨hroot,hsep⟩:=cfE hassoc hgr hgs
  let v : ↥S:=⟨g',Multiset.mem_toFinset.mpr hmem⟩
  let i:=e.symm v
  have hi:G i=g' := congrArg Subtype.val (e.apply_symm_apply v)
  obtain ⟨j,hj⟩:=hC i f hf.1 (by rwa [hi]) (by rwa [hi]) (d.roots f hf ho).2
  exact ⟨i,j,hj⟩
end
end Research6969.ProfileList
end
section
set_option autoImplicit true
namespace Research6969.ProfileList
noncomputable section
open i4 Finset PolynomialDifferential MvPolynomial
open P5_8 (Jn Equation caps tariffShape)
open scoped Polynomial BigOperators
private theorem add_tail (h:ℕ) :h+h*(h-1)=h^2 := by
  cases h with
  | zero=>rfl
  | succ h=>rw [Nat.succ_sub_one]; ring
private theorem first_order {s :Source} (hs :Rz s) {w:Node→K} {T:zJe (Polynomial K)}
    (ht: (T:Set (Polynomial K))⊆close A w) (ha :aRk A) {Q:DifferentialPolynomial K 1}
    (hq:bRZ s Q) (hroot : ∀ f∈T,differentialSpecialization Q f=0) :
    gap A*T.card≤lowFee s := by
  classical
  let U:=T.filter (ae8 Q)
  let V:=T.filter fun f => ¬ ae8 Q f
  obtain ⟨F,hF,hcov⟩:=byX.proof s hs Q hq
  have hcap:=cOg (T:=U) (fun _ hf=>ht (mem_filter.mp hf).1) ha (Or.inl rfl)
    F (cxe.proof s hs F hF) (fun f hf =>
      hcov f (ht (mem_filter.mp hf).1).1 (mem_filter.mp hf).2)
  have hU:gap A*U.card≤errors A*R₁ s+gap A*F.count:= by
    have hcast:gap A*U.card≤errors A*(1*R₁ s)+gap A*F.count:= by
      exact_mod_cast hcap
    simpa only [one_mul] using hcast
  obtain ⟨G,hG,hd,htail⟩:=cxf.proof s hs Q hq
  have hV:V.card≤H s*(H s-1) := by
    apply (Polynomial.card_le_degree_of_subset_roots (p:=G) ?_).trans hd
    intro f hf
    obtain ⟨hfT,hsing⟩:=mem_filter.mp (show f∈V from hf)
    exact (Polynomial.mem_roots hG).mpr (htail f (ht hfT).1 (hroot f hfT) hsing)
  have hsizes :U.card+V.card=T.card:=card_filter_add_card_filter_not ..
  calc
    gap A*T.card=gap A*U.card+gap A*V.card:= by rw [← zws,hsizes]
    _≤(errors A*R₁ s+gap A*H s)+gap A*(H s*(H s-1)) :=
      z9f (hU.trans (z3b (zBI _ hF.count) _))
        (zBI _ hV)
    _=lowFee s := by rw [lowFee,add_assoc,← zws,add_tail]
theorem nonregular_count {s :Source} (hs :Rz s) {w:Node→K} {T:zJe (Polynomial K)}
    (ht: (T:Set (Polynomial K))⊆close A w) (ha :aRk A) {Q:Equation}
    (hq:ato s Q)
    (hroot : ∀ f∈T,differentialSpecialization Q f=0 ∧ ¬ ae8 Q f) :
    gap A*T.card≤lowFee s := by
  obtain ⟨Q₁,hQ₁,hᵣ⟩:=a9N.proof s hs Q hq
  exact first_order hs ht ha hQ₁ (fun f hf=>hᵣ f (ht hf).1 (hroot f hf).1 (hroot f hf).2)
private theorem ceY {s :Source} (hs :Rz s) {w:Node→K} {T:zJe (Polynomial K)}
    (ht: (T:Set (Polynomial K))⊆close A w) (ha :aRk A) {Q:Equation}
    (hq:ato s Q) (hreg : ∀ f∈T,ae8 Q f) :
    gap A*T.card≤ regularFee s := by
  obtain ⟨F,hF,hcov⟩:=apQ.of_children cxa.proof cxb.proof s hs Q hq
  have hcap:=cOg ht ha (Or.inr rfl) F
    (aFz.of_children cxc.proof cxd.proof s hs F hF)
    (fun f hf=>hcov f (ht hf).1 (hreg f hf))
  have hcast:gap A*T.card≤errors A*(2*R₂ s)+gap A*F.count:= by
    exact_mod_cast hcap
  exact hcast.trans (z3b (zBI _ hF.count) _)
private theorem tariff_shape {a :Jn} (ha :Allocation a) :Rz (tariffShape a) := by
  obtain ⟨hB,hJ,_,_,hc,_,_⟩:=ha
  have hbound:max 2 (max a.B a.J)≤83:= by omega
  have hchar :max N (83*(83-1))<p:= by decide
  refine ⟨Nat.zero_lt_one,?_,?_,?_,?_,?_,?_⟩
  · change 0< max 1 a.C
    omega
  · change 2*max 1 a.C≤ max 2 a.J
    omega
  · change max 2 a.J≤ max 2 (max a.B a.J)
    omega
  · exact (max_le_max le_rfl (Nat.mul_le_mul hbound (Nat.sub_le_sub_right hbound 1))).trans_lt hchar
  · intro j hj
    simp [tariffShape] at hj
  · intro j hj _
    simp [tariffShape] at hj
private theorem no_regular_of_zero_top {Q:Equation} (hQ:Q≠0) (hz : (caps Q).C=0)
    (f :(Polynomial K)) : ¬ ae8 Q f := by
  rintro ⟨G,_,hd,_,hs⟩
  have htop:=weightedTotalDegree_le_of_dvd (Pi.single (some (zym 2)) 1) hd hQ
  rw [weightedTotalDegree_piSingle,weightedTotalDegree_piSingle] at htop
  change Q.degreeOf (some (zym 2))=0 at hz
  rw [hz] at htop
  change differentialSpecialization (pderiv (some (zym 2)) G) f≠0 at hs
  rw [pderiv_eq_zero_of_degreeOf_eq_zero (Nat.eq_zero_of_le_zero htop)] at hs
  exact hs (map_zero (differentialSpecializationHom f))
theorem common_count {w:Node→K} {T:zJe (Polynomial K)} (ht: (T:Set (Polynomial K))⊆close A w)
    (ha :aRk A) {Q:Equation} (hq:Q≠0) (halloc:Allocation (caps Q))
    (hroot : ∀ f∈T,differentialSpecialization Q f=0) :
    gap A*T.card≤ commonFee (caps Q) := by
  classical
  let a :=caps Q
  let s :=tariffShape a
  have hshape :Rz s :=tariff_shape halloc
  have horder :ato s Q:= by
    refine ⟨hq,?_,?_,?_⟩
    · change a.B≤ max 2 (max a.B a.J)
      omega
    · exact le_max_right 2 a.J
    · exact le_max_right 1 a.C
  by_cases hz :a.C=0
  · rw [commonFee,ite_eq_left hz,add_zero]
    exact nonregular_count hshape ht ha horder
      (fun f hf=>⟨hroot f hf,no_regular_of_zero_top hq hz f⟩)
  · let U:=T.filter (ae8 Q)
    let V:=T.filter fun f => ¬ ae8 Q f
    have hU:=ceY (T:=U) hshape (fun _ hf=>ht (mem_filter.mp hf).1) ha horder
      (fun _ hf=>(mem_filter.mp hf).2)
    have hV:=nonregular_count (T:=V) hshape (fun _ hf=>ht (mem_filter.mp hf).1) ha horder
      (fun f hf=>⟨hroot f (mem_filter.mp hf).1,(mem_filter.mp hf).2⟩)
    have hsizes :U.card+V.card=T.card:=card_filter_add_card_filter_not ..
    rw [← hsizes,zws,commonFee,ite_eq_right hz,add_comm (lowFee s)]
    exact z9f hU hV
end
end Research6969.ProfileList
end
section
set_option autoImplicit true
namespace Research6969.ProfileList
noncomputable section
open i4 PolynomialDifferential Finset
open P5_8 (Equation small small_shape)
open scoped Polynomial
theorem scalar_list : CJ0.ScalarList A Profile.listCap := by
  change i4.axW A Profile.listCap
  classical
  intro w
  have hfin: (close A w).Finite :=
    ReedSolomon.closePolynomialSet_finite node w (show k≤A from agreement_ok.gt_degree)
  obtain ⟨Q,hQ,hroot⟩:=small_equation w
  obtain ⟨d⟩ := companion_exists w Q hQ hroot
  obtain ⟨F,hF⟩:=factor_charts hQ d
  let T:=hfin.toFinset
  let commonMarks :=T.filter fun f=>differentialSpecialization d.common f=0
  let offCommon :=T.filter fun f=>differentialSpecialization d.common f≠0
  let U:=offCommon.filter (ae8 Q)
  let V:=offCommon.filter fun f => ¬ ae8 Q f
  have ht (f :(Polynomial K)) (hf :f∈T) :f∈close A w:=hfin.mem_toFinset.mp hf
  have hs (f :(Polynomial K)) (hf :f∈offCommon) :f∈close A w:=ht f (mem_filter.mp hf).1
  have hz :=common_count (T:=commonMarks) (fun f hf=>ht f (mem_filter.mp hf).1) agreement_ok
    d.common_ne d.allocation (fun _ hf=>(mem_filter.mp hf).2)
  have hu:=ePy hQ.1 d (F:=F) (T:=U) (fun f hf=>hs f (mem_filter.mp hf).1)
    (fun f hf=>hF f (hs f (mem_filter.mp hf).1) (mem_filter.mp hf).2
      (mem_filter.mp (mem_filter.mp hf).1).2)
  have hv :=nonregular_count (T:=V) small_shape (fun f hf=>hs f (mem_filter.mp hf).1)
    agreement_ok hQ (fun f hf=>⟨hroot f (hs f (mem_filter.mp hf).1),(mem_filter.mp hf).2⟩)
  have hzs :commonMarks.card+offCommon.card=T.card:=card_filter_add_card_filter_not ..
  have huv :U.card+V.card=offCommon.card:=card_filter_add_card_filter_not ..
  have hcard:gap A*T.card≤gap A*Profile.listCap:= by
    rw [← hzs,← huv,← add_assoc,zws,zws]
    exact (z9f (z9f hz hu) hv).trans (list_tariff _ d.allocation.capacity d.allocation.top_index
      d.allocation.top_total d.allocation.index_total)
  exact ⟨hfin,by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact Nat.le_of_mul_le_mul_left hcard (Nat.sub_pos_of_lt agreement_ok.gt_degree)⟩
end
end Research6969.ProfileList
end


namespace Research6969.ProfileProtocol

open FrobeniusLocator ProximityPrize.Benchmark

theorem protocol_of_bad_slopes
    (bound : ∀ (u : Words) (Γ : Finset K),
      (∀ γ ∈ Γ, Principal.BadSlope node (u 0) (u 1) k agreement γ) →
        Γ.card ≤ scalarCap) :
    ProtocolClaim 6969 radiusNumerator radiusDenominator :=
  of_bad_slopes ProfileList.scalar_list bound


end Research6969.ProfileProtocol
end Z6969Source2219

-- Source: ProximityPrize.SubmissionLower.ProfileFrontMain
section Z6969Source2220
set_option autoImplicit true
-- merged module Front6969Rank2
section Merged_Front6969Rank2

-- merged module R6960Front6969Params
section Merged_R6960Front6969Params

set_option Elab.async false
set_option autoImplicit true
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace Front6969
noncomputable section
open Polynomial Matrix CoreDefinitions Code FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators NNReal
export P0 (K I Words node p blockLength k Frac Bivar TypeAtMostOne coefficientBlocks
  extendSeed IsCommonGCD atSlope seed liftX twist amplitudeDegree sixNorm columnRank
  threeU threeV sameDirection relationOn)
abbrev Rung := P1.Rung
abbrev target : Rung := ⟨179740, 2899368181980161361, 9223372036854649837, 2292, 274928728022923468, 52000088471619⟩
abbrev agreement := target.agreement
abbrev radiusNumerator := target.numerator
abbrev radiusDenominator := target.denominator
abbrev lowCutoff : ℤ := target.lowEnd
abbrev scalarCap := target.mcaBound
abbrev listCap := target.listBound
abbrev t : ℕ := blockLength - agreement
abbrev L : ℕ := agreement - k
abbrev heightCap : ℕ := t + 1 - L - 2
abbrev rankFee : ℕ := 71879381565923
abbrev anchorFee : ℕ := 71879381846871
abbrev budget : ℕ := 0x3d0ed83eb28710f
def queryRadius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator
def radius : ℝ := queryRadius
def BadFamily (u : Words) (Γ : Finset K) : Prop :=
  ∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius
abbrev BadMarkAt := P1.BadMarkAt
abbrev BadMark := BadMarkAt agreement
def ordinary (u : Words) := hankel node (u 0) (u 1) L t
def twoBlock (u : Words) := stacked p node (u 0) (u 1) L t
def firstRank (u : Words) := GenericLayer.genericRank (ordinary u)
def stackRank (u : Words) := GenericLayer.genericRank (twoBlock u)
def nullity (u : Words) := GenericLayer.genericNullity (twoBlock u)
def Normal (u : Words) (γ : K) : Prop :=
  ((twoBlock u).map (evalRingHom γ)).rank = stackRank u
def normalSlopes (u : Words) (Γ : Finset K) : Finset K := by
  classical exact Γ.filter (Normal u)
def abnormalSlopes (u : Words) (Γ : Finset K) : Finset K := by
  classical exact Γ.filter (fun γ => ¬ Normal u γ)
def HomogeneousPrincipal (u : Words) : Prop :=
  ∃ (a : ℕ) (g : (Polynomial Frac)), g ≠ 0 ∧ g.natDegree ≤ a ∧ a ≤ t ∧
    ∀ P : (Polynomial Frac), P.natDegree ≤ t →
      (((twoBlock u).map (algebraMap (Polynomial K) Frac)).mulVec (fun i => P.coeff i.val) = 0 ↔
        ∃ Q : (Polynomial Frac), Q.natDegree ≤ t - a ∧ P = g * Q)
abbrev coefficientStack (u : Words) := coefficientBlocks p node (u 0) (u 1) L t
def ConstantKernel (u : Words) : Prop :=
  stackRank u = (coefficientStack u).rank
def FrontRemainder (u : Words) : Prop :=
  2 ≤ nullity u ∧ firstRank u = L ∧ ¬ TypeAtMostOne u ∧
    ¬ HomogeneousPrincipal u ∧ ¬ ConstantKernel u
structure TwoActive (u : Words) where
  a : ℕ
  b : ℕ
  c : ℕ
  ab : a ≤ b
  active : b ≤ t
  inactive : t < c
  top : c ≤ k
  degreeSum : a + b + c = 2 * k + 2
  nullitySum : nullity u + a + b = 2 * (t + 1)
  level : Strata.HasLevelHilbertFunction
    (fun s j => algebraMap (Polynomial K) Frac (Principal.parameterSyndromes p node (u 0) (u 1) s j))
    k a b c
def TwoActive.height {u : Words} (T : TwoActive u) := (k + 1) - T.c
abbrev Relation {u : Words} (T : TwoActive u) :=
  Strata.PolynomialRelationCertificate p node (u 0) (u 1) k T.height
def leftU {u : Words} {T : TwoActive u} (R : Relation T) : Bivar :=
  Principal.assemble (fun j => R.coefficients (0, j))
def leftV {u : Words} {T : TwoActive u} (R : Relation T) : Bivar :=
  Principal.assemble (fun j => R.coefficients (1, j))
def fixedNodes {u : Words} {T : TwoActive u} (R : Relation T) : Finset I := by
  classical
  exact Finset.univ.filter fun i =>
    (leftU R).eval (C (node i)) = 0 ∧ (leftV R).eval (C (node i)) = 0
def FixedLeftGCD {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  ∃ G : (Polynomial K), IsCommonGCD (G.map (algebraMap K Frac))
    (extendSeed (leftU R)) (extendSeed (leftV R))
def MovingGCD {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  ¬ FixedLeftGCD R ∧ ∃ G : (Polynomial Frac), G ≠ 0 ∧ G ∣ extendSeed (leftU R) ∧
    G ∣ extendSeed (leftV R) ∧ (fixedNodes R).card < G.natDegree
def InvalidLeft {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  max (leftU R).natDegree (leftV R).natDegree < T.height ∨
    ∃ G : (Polynomial K), G ≠ 0 ∧ G.map Polynomial.C ∣ leftU R ∧ G.map Polynomial.C ∣ leftV R ∧
      ¬ G ∣ locator node Finset.univ
structure SaturatedAt {u : Words} {T : TwoActive u} (R : Relation T)
    {γ : K} (M : BadMark u γ) : Prop where
  U_ne : atSlope (leftU R) γ ≠ 0
  V_ne : atSlope (leftV R) γ ≠ 0
  degree_eq : max (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree =
    T.height
  gcd_errors : ∃ errors : Finset I,
    (∀ i ∈ errors, M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i) ∧
    IsCommonGCD (locator node errors) (atSlope (leftU R) γ) (atSlope (leftV R) γ)
  fixed_errors : ∀ i ∈ fixedNodes R, M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i
  valid : ¬ InvalidLeft R
def NormalSaturation {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  ∀ γ, Normal u γ → ∀ M : BadMark u γ, SaturatedAt R M
structure Reduction (u : Words) (T : TwoActive u) (R : Relation T) where
  U : Bivar
  V : Bivar
  output : Bivar
  height : ℕ
  height_eq : height + (fixedNodes R).card = T.height
  max_degree : max U.natDegree V.natDegree = height
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  coprime : IsCoprime (extendSeed U) (extendSeed V)
  U_factor : leftU R = liftX (locator node (fixedNodes R)) * U
  V_factor : leftV R = liftX (locator node (fixedNodes R)) * V
  output_factor : R.output = liftX (locator node (fixedNodes R)) * output
  output_degree : output.degree < (k + height : ℕ)
  deleted_error : ∀ γ, Normal u γ → ∀ M : BadMark u γ, ∀ i ∈ fixedNodes R,
    M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i
structure RankThree (u : Words) (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) where
  rank_eq : columnRank D.U D.V = 3
  α : Fin 2 → (Polynomial K)
  β : Fin 2 → (Polynomial K)
  a : (Polynomial K)
  b : (Polynomial K)
  a_ne : a ≠ 0
  b_ne : b ≠ 0
  α_primitive : IsCoprime (α 0) (α 1)
  β_primitive : IsCoprime (β 0) (β 1)
  first_degree : a.natDegree + amplitudeDegree (β 0) (β 1) ≤ D.height
  second_degree : b.natDegree + amplitudeDegree (α 0) (α 1) ≤ D.height
  same_direction : sameDirection D.U D.V (threeU a β) (threeV b α)
  output : Bivar
  output_degree : output.degree < (k + D.height : ℕ)
  nodes : relationOn u (fixedNodes R) (threeU a β) (threeV b α) output
def Parallel {u T R D} (B : RankThree u T R D) : Prop :=
  B.α = B.β
def Nonparallel {u T R D} (B : RankThree u T R D) : Prop :=
  B.α 0 * B.β 1 - B.α 1 * B.β 0 ≠ 0
def UnitNorm {u T R D} (B : RankThree u T R D) : Prop :=
  sixNorm B.a = sixNorm B.b
abbrev ModelAt := P1.ModelAt
abbrev MarkAt := @P1.MarkAt
abbrev FamilyAt := @P1.FamilyAt
abbrev ModelAt.overhead := @P1.ModelAt.overhead
abbrev ModelAt.label := @P1.ModelAt.label
abbrev ModelAt.amplitude := @P1.ModelAt.amplitude
abbrev ModelAt.decoder := @P1.ModelAt.decoder
abbrev AnchorModel := ModelAt heightCap
abbrev AnchorMark {u deleted} (M : AnchorModel u deleted) := MarkAt (A := agreement) M
abbrev AnchoredFamily {u deleted} (M : AnchorModel u deleted) := FamilyAt agreement M
abbrev AnchorModel.overhead {u deleted} (M : AnchorModel u deleted) := ModelAt.overhead M
abbrev AnchorModel.label {u deleted} (M : AnchorModel u deleted) := ModelAt.label M
abbrev AnchorModel.amplitude {u deleted} (M : AnchorModel u deleted) := ModelAt.amplitude M
abbrev AnchorModel.decoder {u deleted} (M : AnchorModel u deleted) {γ : K} (B : BadMark u γ) :=
  ModelAt.decoder M B
abbrev lowCap : ℕ := 274784969259510674
abbrev highCap : ℕ := 274784969259510674
end
end Front6969
end

end Merged_R6960Front6969Params

-- merged module R6960Front6969Cases
section Merged_R6960Front6969Cases

set_option Elab.async false

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
namespace Front6969
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open K1_8 (seedInclusion seedInclusion_injective extendSeed_injective
  lift_locator_dvd coprime_after_factor)
open K1_8 (certificate_output_zero)
open P1 (eval_liftX constantsInFrac extend_liftX)
private theorem mem_fixed_iff {u : Words} {T : TwoActive u} (R : Relation T) (i : I) :
    i ∈ fixedNodes R ↔ (leftU R).eval (C (node i)) = 0 ∧ (leftV R).eval (C (node i)) = 0 := by
  classical
  simp [fixedNodes]
private theorem fixed_case_maximal {u : Words} {T : TwoActive u} (R : Relation T)
    (hi : ¬ InvalidLeft R) (hf : FixedLeftGCD R) :
    ∀ H : (Polynomial Frac), H ∣ extendSeed (leftU R) → H ∣ extendSeed (leftV R) →
      H ∣ extendSeed (liftX (locator node (fixedNodes R))) := by
  classical
  obtain ⟨g, hg, hgu, hgv, hgmax⟩ := hf
  change g.map constantsInFrac ≠ 0 at hg
  change g.map constantsInFrac ∣ _ at hgu hgv
  change ∀ H : (Polynomial Frac), H ∣ extendSeed (leftU R) → H ∣ extendSeed (leftV R) →
    H ∣ g.map constantsInFrac at hgmax
  have hg0 : g ≠ 0 := by
    intro hz
    exact hg (by rw [hz, Polynomial.map_zero])
  let g₀ := g * C g.leadingCoeff⁻¹
  have hm : g₀.Monic := monic_mul_leadingCoeff_inv hg0
  have hnorm (P : (Polynomial Frac)) (hd : g.map constantsInFrac ∣ P) :
      g₀.map constantsInFrac ∣ P := by
    apply ((Polynomial.map_dvd_map' constantsInFrac).mpr ?_).trans hd
    exact (dvd_mul_leadingCoeff_inv hg0).mp dvd_rfl
  have hlift (P : Bivar) (hd : g.map constantsInFrac ∣ extendSeed P) :
      liftX g₀ ∣ P := by
    apply (Polynomial.map_dvd_map seedInclusion seedInclusion_injective (hm.map Polynomial.C)).mp
    change extendSeed (liftX g₀) ∣ extendSeed P
    rw [extend_liftX]
    exact hnorm _ hd
  have hu := hlift _ hgu
  have hv := hlift _ hgv
  have hdom : g₀ ∣ locator node Finset.univ := by
    by_contra h
    exact hi (Or.inr ⟨g₀, hm.ne_zero, hu, hv, h⟩)
  obtain ⟨S, _, _, t, ht, hS⟩ :=
    Strata.split_divisor_locator_factor node IRSProfile.domain.injective Finset.univ g₀ hm.ne_zero hdom
  have hsub : S ⊆ fixedNodes R := by
    intro i his
    have hz : g₀.eval (node i) = 0 := by
      rw [hS, eval_smul, locator_eval_zero node S i his, smul_zero]
    have hlzero : (liftX g₀).eval (C (node i)) = 0 := by
      rw [eval_liftX, hz, C_0]
    obtain ⟨U, hU⟩ := hu
    obtain ⟨V, hV⟩ := hv
    exact (mem_fixed_iff R i).mpr ⟨by rw [hU, eval_mul, hlzero, zero_mul],
      by rw [hV, eval_mul, hlzero, zero_mul]⟩
  have hg₀dvd : g₀ ∣ locator node (fixedNodes R) := by
    rw [hS, Polynomial.smul_eq_C_mul, (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ht)).mul_left_dvd]
    exact Strata.locator_dvd_of_eval_zero node IRSProfile.domain.injective S _
      (fun i his => locator_eval_zero node _ i (hsub his))
  intro H hU hV
  rw [extend_liftX]
  exact (hgmax H hU hV).trans
    ((Polynomial.map_dvd_map' constantsInFrac).mpr
      ((dvd_mul_right g (C g.leadingCoeff⁻¹)).trans hg₀dvd))
theorem fixed_gcd {u : Words} {T : TwoActive u} (R : Relation T)
    (hu : leftU R ≠ 0) (hm : ¬ MovingGCD R) (hi : ¬ InvalidLeft R) :
    IsCommonGCD (extendSeed (liftX (locator node (fixedNodes R))))
      (extendSeed (leftU R)) (extendSeed (leftV R)) := by
  classical
  let S := fixedNodes R
  let Δ := liftX (locator node S)
  let A := extendSeed (leftU R)
  let B := extendSeed (leftV R)
  have hΔ : Δ.Monic := (locator_monic node S).map Polynomial.C
  have hΔ0 : extendSeed Δ ≠ 0 := (hΔ.map seedInclusion).ne_zero
  have hA0 : A ≠ 0 :=
    fun h => hu (extendSeed_injective (h.trans (Polynomial.map_zero _).symm))
  have hΔA : extendSeed Δ ∣ A := by
    exact Polynomial.map_dvd seedInclusion
      (lift_locator_dvd S (leftU R) (fun i h => ((mem_fixed_iff R i).mp h).1))
  have hΔB : extendSeed Δ ∣ B := by
    exact Polynomial.map_dvd seedInclusion
      (lift_locator_dvd S (leftV R) (fun i h => ((mem_fixed_iff R i).mp h).2))
  refine ⟨hΔ0, hΔA, hΔB, ?_⟩
  by_cases hf : FixedLeftGCD R
  · exact fixed_case_maximal R hi hf
  let G := EuclideanDomain.gcd A B
  have hGA : G ∣ A := EuclideanDomain.gcd_dvd_left _ _
  have hGB : G ∣ B := EuclideanDomain.gcd_dvd_right _ _
  have hG : G ≠ 0 := fun hz => hA0 (zero_dvd_iff.mp (hz ▸ hGA))
  have hGd : G.natDegree ≤ S.card := by
    apply Nat.le_of_not_gt
    exact fun h => hm ⟨hf, G, hG, hGA, hGB, h⟩
  have hΔd : (extendSeed Δ).natDegree = S.card := by
    rw [extend_liftX, natDegree_map_eq_of_injective constantsInFrac.injective, locator_natDegree]
  obtain ⟨q, hq⟩ := EuclideanDomain.dvd_gcd hΔA hΔB
  change G = extendSeed Δ * q at hq
  have hq0 : q ≠ 0 := by intro h; exact hG (by rw [hq, h, mul_zero])
  have hd := congrArg Polynomial.natDegree hq
  rw [natDegree_mul hΔ0 hq0, hΔd] at hd
  have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
  have hqU : IsUnit q := by
    rw [hqC, isUnit_C, isUnit_iff_ne_zero]
    intro hz
    exact hq0 (by rwa [hz, C_0] at hqC)
  intro H hHA hHB
  have hHG : H ∣ G := EuclideanDomain.dvd_gcd hHA hHB
  rwa [hq, hqU.dvd_mul_right] at hHG
theorem puncture {u : Words} {T : TwoActive u} (R : Relation T)
    (hs : NormalSaturation R) (hw : ∃ γ, Normal u γ ∧ Nonempty (BadMark u γ))
    (hgcd : IsCommonGCD (extendSeed (liftX (locator node (fixedNodes R))))
      (extendSeed (leftU R)) (extendSeed (leftV R))) : Nonempty (Reduction u T R) := by
  classical
  obtain ⟨γ, hγ, ⟨M⟩⟩ := hw
  have h := hs γ hγ M
  let B := fixedNodes R
  let G := liftX (locator node B)
  have hG : G.Monic := (locator_monic node B).map Polynomial.C
  have hGd : G.natDegree = B.card := by
    change ((locator node B).map Polynomial.C).natDegree = _
    rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective, locator_natDegree]
  obtain ⟨U, hU⟩ := lift_locator_dvd B (leftU R)
    (fun i hi => (mem_fixed_iff R i |>.mp hi).1)
  obtain ⟨V, hV⟩ := lift_locator_dvd B (leftV R)
    (fun i hi => (mem_fixed_iff R i |>.mp hi).2)
  obtain ⟨W, hW⟩ := lift_locator_dvd B R.output (fun i hi => by
    have hroot := (mem_fixed_iff R i).mp hi
    exact certificate_output_zero R i hroot.1 hroot.2)
  have hu : U ≠ 0 := by
    intro hz
    apply h.U_ne
    rw [hU, hz, mul_zero, atSlope, Polynomial.map_zero]
  have hv : V ≠ 0 := by
    intro hz
    apply h.V_ne
    rw [hV, hz, mul_zero, atSlope, Polynomial.map_zero]
  have hdeg : max (leftU R).natDegree (leftV R).natDegree = T.height := by
    apply le_antisymm (max_le (R.x_degree 0) (R.x_degree 1))
    exact Nat.le_of_not_gt fun hlt => h.valid (Or.inl hlt)
  have hdu := congrArg Polynomial.natDegree hU
  have hdv := congrArg Polynomial.natDegree hV
  change (leftU R).natDegree = (G * U).natDegree at hdu
  change (leftV R).natDegree = (G * V).natDegree at hdv
  rw [natDegree_mul hG.ne_zero hu, hGd] at hdu
  rw [natDegree_mul hG.ne_zero hv, hGd] at hdv
  let H := max U.natDegree V.natDegree
  have hH : H + B.card = T.height := by
    dsimp [H]
    omega
  have hout : W.degree < (k + H : ℕ) := by
    by_cases hzero : W = 0
    · rw [hzero, degree_zero]
      exact WithBot.bot_lt_coe _
    have hRout : R.output ≠ 0 := by rw [hW]; exact mul_ne_zero hG.ne_zero hzero
    have hd := (natDegree_lt_iff_degree_lt hRout).mpr R.output_degree
    rw [hW] at hd
    change (G * W).natDegree < _ at hd
    rw [natDegree_mul hG.ne_zero hzero, hGd] at hd
    exact (natDegree_lt_iff_degree_lt hzero).mp (by omega)
  have hcop : IsCoprime (extendSeed U) (extendSeed V) := by
    apply coprime_after_factor (extendSeed G) _ _ hgcd.1
      (fun hz => hu (extendSeed_injective (hz.trans (Polynomial.map_zero _).symm)))
    intro Q hqu hqv
    apply hgcd.2.2.2 Q
    · rw [hU, extendSeed, Polynomial.map_mul]
      exact hqu
    · rw [hV, extendSeed, Polynomial.map_mul]
      exact hqv
  exact ⟨⟨U, V, W, H, hH, rfl, hu, hv, hcop, hU, hV, hW, hout,
    fun γ hn M => (hs γ hn M).fixed_errors⟩⟩
end
end Front6969
end
section
set_option maxRecDepth 12000
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
namespace Front6969
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem
open FrobeniusLocator ProximityPrize.Benchmark
open Sol1.OneCount Sol1.FiniteRowProjection
open scoped NNReal
abbrev agreement_of_threshold := @Research6969.ProfileProtocol.agreement_of_threshold
theorem bad_slope (u : Words) (γ : K)
    (hγ : IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius) :
    Principal.BadSlope node (u 0) (u 1) k agreement γ := by
  let : NeZero k := ⟨by decide⟩
  exact Principal.isMCA_implies_badSlope node u k agreement radius
    (fun _ hT => agreement_of_threshold hT) γ hγ
theorem bad_mark (u : Words) (Γ : Finset K) (hΓ : BadFamily u Γ) (γ : K) (hγ : γ ∈ Γ) :
    Nonempty (BadMark u γ) := by
  obtain ⟨S, hS, ⟨P, hP, he⟩, hn⟩ := bad_slope u γ (hΓ γ hγ)
  exact ⟨⟨S, P, hS, hP, he, hn⟩⟩
end
end Front6969
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace Front6969
noncomputable section
open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
theorem firstRank_le (u : Words) : firstRank u ≤ L := by
  simpa only [firstRank, GenericLayer.genericRank, Fintype.card_fin] using
    Matrix.rank_le_card_height ((ordinary u).map (algebraMap (Polynomial K) Frac))
theorem actual_stackRank (u : Words) : stackRank u = t + 1 - nullity u := by
  have h := GenericLayer.rank_add_nullity (twoBlock u)
  simp only [Fintype.card_fin] at h
  change stackRank u + nullity u = t + 1 at h
  omega
theorem relation_height_balance {u : Words} (T : TwoActive u) :
    L + T.height + nullity u = t + 1 := by
  exact Strata.relation_degree_nullity_balance k L t (nullity u) T.a T.b T.c
    (by decide) T.top T.degreeSum (by have := T.nullitySum; omega)
theorem relation_height_le {u : Words} (hu : FrontRemainder u) (T : TwoActive u) :
    T.height ≤ heightCap := by
  have h := relation_height_balance T
  have hr := hu.1
  change 48668 + T.height + nullity u = 82405 at h
  change T.height ≤ 33735
  omega
def relation_of_two_active {u : Words} (hu : FrontRemainder u) (T : TwoActive u) :
    Relation T := by
  have hline := Strata.generic_relation_line_of_level p node (u 0) (u 1)
    k T.a T.b T.c T.top T.degreeSum T.ab (T.active.trans_lt T.inactive)
    ((show 1 ≤ t by decide).trans_lt T.inactive) T.level
  have hH := relation_height_le hu T
  apply Strata.polynomialRelationCertificate_of_nullity_one p (by decide)
    node (u 0) (u 1) node.injective Native.native_domain_fixed
    k k T.height (by rw [IRSProfile.card_index]; decide)
    (hH.trans (by decide)) _ hline
  rw [Sol1.C64.native_field_card]
  exact (Nat.mul_le_mul_right p (show 2 * T.height + 2 ≤ 2 * heightCap + 2 by omega)).trans_lt
    (by decide)
theorem rank_fee_exact : L + p * heightCap = rankFee := by decide
theorem anchor_fee_exact : p * heightCap + 2 * heightCap + blockLength + 2 = anchorFee := by
  decide
theorem rank_exceptions (u : Words) (hu : FrontRemainder u) (Γ : Finset K) :
    (abnormalSlopes u Γ).card ≤ rankFee := by
  classical
  have h := Strata.two_block_rank_exception_count p node (u 0) (u 1) L t (nullity u)
    (actual_stackRank u) hu.2.1 (abnormalSlopes u Γ) (fun γ hγ => by
      rw [← actual_stackRank u]
      exact (Finset.mem_filter.mp hγ).2)
  have hs : t + 1 - nullity u - L ≤ heightCap := by
    have hr := hu.1
    change 82405 - nullity u - 48668 ≤ 33735
    omega
  exact h.trans ((Nat.add_le_add_left (Nat.mul_le_mul_left p hs) L).trans_eq rank_fee_exact)
open P0 (type_one_bad_count_of_syndromes)
theorem type_one_count (u : Words) (htype : TypeAtMostOne u)
    (Γ : Finset K) (hΓ : BadFamily u Γ) : Γ.card ≤ 1 := by
  have hk : k ≤ Fintype.card I := by rw [IRSProfile.card_index]; decide
  exact type_one_bad_count_of_syndromes node (u 0) (u 1) node.injective
    k agreement p hk (by decide) htype Γ (fun γ hγ => bad_slope u γ (hΓ γ hγ))
theorem deficient_count (u : Words) (Γ : Finset K) (hrank : firstRank u < L)
    (hΓ : BadFamily u Γ) : Γ.card ≤ 310811 := by
  have h := K1_3.deficient_hankel_count node (u 0) (u 1) node.injective
    k L t (firstRank u) (by rw [IRSProfile.card_index]; decide) hrank rfl Γ
    (fun γ hγ => bad_slope u γ (hΓ γ hγ))
  rw [IRSProfile.card_index] at h
  exact h.trans (Nat.add_le_add_left (Nat.le_of_lt_succ hrank) blockLength)
theorem principal_count (u : Words) (Γ : Finset K) (hprincipal : HomogeneousPrincipal u)
    (hΓ : BadFamily u Γ) : Γ.card ≤ 734130640077284 := by
  obtain ⟨a, g, hg, hga, ha, hkernel⟩ := hprincipal
  have hsum : a + (t - a) = t := by omega
  let φ := algebraMap (Polynomial K) Frac
  have hcertificate : Principal.PrincipalAt
      (fun b j => φ (Principal.parameterSyndromes p node (u 0) (u 1) b j)) k a (t - a) := by
    refine { generator := g, nonzero := hg, degree_bound := hga, kernel_eq := ?_ }
    intro f
    rw [hsum, Principal.recurrence_kernel_iff_matrix, Principal.recurrenceMatrix_parameter]
    change (f.natDegree ≤ t ∧ ((twoBlock u).map φ).mulVec (fun i => f.coeff i.val) = 0) ↔
      ∃ Q : (Polynomial Frac), Q.natDegree ≤ t - a ∧ f = g * Q
    constructor
    · rintro ⟨hf, hker⟩
      exact (hkernel f hf).mp hker
    · rintro ⟨Q, hQ, rfl⟩
      have hdegree : (g * Q).natDegree ≤ t :=
        natDegree_mul_le.trans ((Nat.add_le_add hga hQ).trans_eq hsum)
      exact ⟨hdegree, (hkernel _ hdegree).mpr ⟨Q, hQ, rfl⟩⟩
  have h := Principal.generic_principal_bad_count_coarse φ
    (IsFractionRing.injective (Polynomial K) Frac) p (by decide) node node.injective
    Native.native_domain_fixed (u 0) (u 1) k k a (t - a)
    (by rw [IRSProfile.card_index]; decide)
    (hsum.trans_lt (show t < k by decide)) hcertificate Γ (fun γ hγ => by
      rw [hsum]
      exact bad_slope u γ (hΓ γ hγ))
  rw [IRSProfile.card_index] at h
  exact h.trans ((Nat.mul_le_mul_left p (Nat.add_le_add_left ha blockLength)).trans (by decide))
open P0 (constantRankCount nativeMoments independent_nativeMoments)
theorem constant_count (u : Words) (Γ : Finset K) (hu : ConstantKernel u)
    (hΓ : BadFamily u Γ) : Γ.card ≤ 175580863611365 := by
  let φ := algebraMap (Polynomial K) Frac
  have hrank : ((twoBlock u).map φ).rank = stackRank u := rfl
  have hconstant : (coefficientBlocks p node (u 0) (u 1) L t).rank = stackRank u := hu.symm
  have hcount := constantRankCount φ (IsFractionRing.injective (Polynomial K) Frac)
    p (by decide) node node.injective Native.native_domain_fixed
    (u 0) (u 1) k agreement L t (by decide) (by decide)
    (by rw [IRSProfile.card_index]; decide) (stackRank u) hrank hconstant
    Γ (fun γ hγ => bad_slope u γ (hΓ γ hγ))
  have hr : stackRank u ≤ t + 1 := by
    rw [actual_stackRank]
    exact Nat.sub_le _ _
  exact hcount.trans ((Nat.mul_le_mul_left p hr).trans_eq (by decide))
open K1_1
private theorem locator_matrix (u : Words) :
    Principal.recurrenceMatrix (nativeMoments u) k t =
      (twoBlock u).map (algebraMap (Polynomial K) Frac) :=
  Principal.recurrenceMatrix_parameter (algebraMap (Polynomial K) Frac)
    p node (u 0) (u 1) k t
private theorem locator_nullity (u : Words) :
    sliceDim (nativeMoments u) k (t + 1) = nullity u := by
  rw [sliceDim_succ (nativeMoments u) k t, locator_matrix]
  rfl
private theorem principal_of_one_active (u : Words) (a : ℕ) (ha : a ≤ t)
    (hone : sliceDim (nativeMoments u) k (a+1) = 1)
    (hnull : nullity u = (t + 1)-a) : HomogeneousPrincipal u := by
  have hpos : 0 < sliceDim (nativeMoments u) k (a+1) := by omega
  have hdim : sliceDim (nativeMoments u) k (t + 1) = (t-a)+1 := by
    rw [locator_nullity]
    omega
  obtain ⟨g, hg, hdeg, hfac⟩ := principal_of_slice (nativeMoments u) k a t
    ha (by decide) hpos hdim
  refine ⟨a, g, hg, hdeg, ha, fun P hP => ?_⟩
  rw [← locator_matrix]
  exact hfac P hP
theorem two_active_of_positive (u : Words) (hpos : 0 < nullity u)
    (hind : ¬ TypeAtMostOne u) (hnp : ¬ HomogeneousPrincipal u) : Nonempty (TwoActive u) := by
  obtain ⟨a, b, c, hab, hbc, hc, hsum, hdim⟩ := level_profile
    (nativeMoments u) k (independent_nativeMoments u hind)
  have hloc := hdim (t + 1) (by decide)
  rw [locator_nullity] at hloc
  have hthree : 3 * t < 2 * k + 2 := by decide
  have hinactive : t < c := by omega
  have ha : a ≤ t := by omega
  have hb : b ≤ t := by
    by_contra hb
    have hsmall := hdim (a+1) (by omega)
    exact hnp (principal_of_one_active u a ha (by omega) (by omega))
  refine ⟨⟨a, b, c, hab, hb, hinactive, hc, hsum, by omega, ?_⟩⟩
  exact level_of_profile _ _ _ _ _ hdim
theorem two_active_nullity {u : Words} (T : TwoActive u) : 2 ≤ nullity u := by
  have := T.ab
  have := T.active
  have := T.nullitySum
  omega
open P1 (excludes_full_rank)
private theorem bad_excludes_full_rank (u : Words) (γ : K) (M : BadMark u γ) :
    ((twoBlock u).map (evalRingHom γ)).rank ≠ t + 1 := by
  classical
  let S := Finset.univ \ M.support
  have hs : S.card ≤ t := by
    dsimp [S]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, IRSProfile.card_index]
    have := M.agreement
    change 179740 ≤ _ at this
    change 262144 - _ ≤ 82404
    omega
  exact excludes_full_rank p node node.injective Native.native_domain_fixed (u 0) (u 1) γ k L t
    (by rw [IRSProfile.card_index]; decide) M.decoder M.degree S hs
    (fun i hi => (M.hits i (by simpa [S] using hi)).symm)
theorem full_column_count (u : Words) (Γ : Finset K) (hfirst : firstRank u = L)
    (hz : nullity u = 0) (hΓ : BadFamily u Γ) : Γ.card ≤ 71883642978789 := by
  have hr := actual_stackRank u
  rw [hz] at hr
  apply (Strata.two_block_rank_exception_count p node (u 0) (u 1) L t 0 hr hfirst Γ ?_).trans_eq
  · decide
  · intro γ hγ
    obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγ
    exact bad_excludes_full_rank u γ M
theorem shortened_guards {u T R} (D : Reduction u T R) (hu : FrontRemainder u) :
    k + 3 * D.height ≤ blockLength - (fixedNodes R).card ∧
    k + D.height ≤ agreement ∧ D.height < p - 1 := by
  have hb := relation_height_le hu T
  have he := D.height_eq
  change T.height ≤ 33735 at hb
  change 131072 + 3 * D.height ≤ 262144 - _ ∧ 131072 + D.height ≤ 179740 ∧ D.height < 0x7f000000
  omega
end
end Front6969
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace Front6969
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open K1_8 (seedInclusion seedInclusion_injective extendSeed_injective extendSeedHom AmplitudeDirection)
open K1_8 (transfer_at)
open K1_8 (threeU_height threeV_height common_multiplier multiplier_degree_zero seed_scalar_coeff descend_scalar proportional_amplitudes rescale_threeU)
open P0_4 (threeU_eq relationOn_eq columnRank_eq)
open P0_4 (sameDirection_eq threeV_eq)
private theorem reduced_scaled_relation {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (e : (Polynomial K)) :
    relationOn u (fixedNodes R) (C e * D.U) (C e * D.V) (C e * D.output) := by
  let G := liftX (locator node (fixedNodes R))
  have hG : ∀ i ∉ fixedNodes R, G.eval (C (node i)) ≠ 0 := by
    intro i hi
    change (K1.liftX (locator node (fixedNodes R))).eval (C (node i)) ≠ 0
    rw [K1_8.eval_liftX, C_ne_zero]
    exact fun hz => hi ((Principal.locator_eval_zero_iff node
      ProximityPrize.Benchmark.IRSProfile.domain.injective _ i).mp hz)
  rw [relationOn_eq]
  exact @transfer_at u K1.p k T.height R (fixedNodes R) G D.U D.V D.output
    hG D.U_factor D.V_factor D.output_factor e
private theorem seed_multiplier {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (P Q : Bivar) (hcross : sameDirection D.U D.V P Q)
    (hp : P.natDegree ≤ D.height) (hq : Q.natDegree ≤ D.height) :
    ∃ e : (Polynomial K), P = C e * D.U ∧ Q = C e * D.V := by
  have hext (F : Bivar) : (extendSeedHom F).natDegree = F.natDegree :=
    natDegree_map_eq_of_injective seedInclusion_injective F
  have hne (F : Bivar) (hF : F ≠ 0) : extendSeedHom F ≠ 0 :=
    fun hz => hF (extendSeed_injective (hz.trans (Polynomial.map_zero _).symm))
  have hxy : extendSeedHom D.U * extendSeedHom Q = extendSeedHom D.V * extendSeedHom P := by
    have h := congrArg extendSeedHom hcross
    simpa only [map_mul] using h
  have hcop : IsCoprime (extendSeedHom D.U) (extendSeedHom D.V) := D.coprime
  obtain ⟨E, heP, heQ⟩ := common_multiplier hcop hxy
  have hEd := multiplier_degree_zero (hne _ D.U_ne) (hne _ D.V_ne) heP heQ
    (by simpa only [hext] using D.max_degree)
    (by simpa only [hext] using hp) (by simpa only [hext] using hq)
  let s := E.coeff 0
  have hE : E = C s := eq_C_of_natDegree_eq_zero hEd
  rw [hE] at heP heQ
  let G := liftX (locator node (fixedNodes R))
  have hLeftU : extendSeedHom (G * P) = C s * extendSeedHom (leftU R) := by
    rw [D.U_factor]
    change extendSeedHom (G * P) = C s * extendSeedHom (G * D.U)
    rw [map_mul, map_mul, heP]
    exact mul_left_comm _ _ _
  have hLeftV : extendSeedHom (G * Q) = C s * extendSeedHom (leftV R) := by
    rw [D.V_factor]
    change extendSeedHom (G * Q) = C s * extendSeedHom (G * D.V)
    rw [map_mul, map_mul, heQ]
    exact mul_left_comm _ _ _
  let F : Fin 2 → Bivar := ![G * P, G * Q]
  let A : Fin 2 × Fin (T.height + 1) → (Polynomial K) :=
    fun j => (F j.1).coeff j.2.val
  have hA : ∀ j, seedInclusion (A j) = s * seedInclusion (R.coefficients j) := by
    rw [Prod.forall, Fin.forall_fin_two]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have hc := seed_scalar_coeff j.val hLeftU
      rw [leftU, Principal.assemble_coeff] at hc
      have e1 : A (0, j) = (G * P).coeff j.val := by simp only [A, F, Matrix.cons_val_zero]
      have h3 : seedInclusion (A (0, j)) = s * seedInclusion (R.coefficients (0, j)) := by
        rw [e1, hc]
      exact h3
    · have hc := seed_scalar_coeff j.val hLeftV
      rw [leftV, Principal.assemble_coeff] at hc
      have e1 : A (1, j) = (G * Q).coeff j.val := by
        simp only [A, F, Matrix.cons_val_one, Matrix.cons_val_zero]
      have h3 : seedInclusion (A (1, j)) = s * seedInclusion (R.coefficients (1, j)) := by
        rw [e1, hc]
      exact h3
  obtain ⟨e, he⟩ := descend_scalar R.coefficients A R.primitive s hA
  have hmapC : extendSeedHom (C e) = C s := by
    change (C e).map seedInclusion = C s
    rw [Polynomial.map_C, he]
  refine ⟨e, extendSeed_injective ?_, extendSeed_injective ?_⟩
  · change extendSeedHom P = extendSeedHom (C e * D.U)
    rw [map_mul, hmapC, heP]
  · change extendSeedHom Q = extendSeedHom (C e * D.V)
    rw [map_mul, hmapC, heQ]
private theorem canonical_output {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (P Q : Bivar) (hcross : sameDirection D.U D.V P Q)
    (hp : P.natDegree ≤ D.height) (hq : Q.natDegree ≤ D.height) :
    ∃ W : Bivar, W.degree < (k + D.height : ℕ) ∧ relationOn u (fixedNodes R) P Q W := by
  obtain ⟨e, rfl, rfl⟩ := seed_multiplier D P Q hcross hp hq
  refine ⟨C e * D.output, ?_, ?_⟩
  · have hdeg : (C e * D.output).degree ≤ D.output.degree := by
      simpa only [smul_eq_C_mul] using degree_smul_le e D.output
    exact hdeg.trans_lt D.output_degree
  · exact reduced_scaled_relation D e
theorem rank_three_branch {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (hr : columnRank D.U D.V = 3) (S : AmplitudeDirection D.U D.V)
    (ha : S.a.natDegree + amplitudeDegree (S.β 0) (S.β 1) ≤ D.height)
    (hb : S.b.natDegree + amplitudeDegree (S.α 0) (S.α 1) ≤ D.height) :
    ∃ B : RankThree u T R D, Nonparallel B ∨ Parallel B := by
  have hdir : sameDirection D.U D.V (threeU S.a S.β) (threeV S.b S.α) := by
    rw [threeU_eq, threeV_eq, sameDirection_eq]
    exact S.direction
  have hUdeg : (threeU S.a S.β).natDegree ≤ D.height := by
    rw [threeU_eq]
    exact (threeU_height _ _).trans ha
  have hVdeg : (threeV S.b S.α).natDegree ≤ D.height := by
    rw [threeV_eq]
    exact (threeV_height _ _).trans hb
  obtain ⟨W, hW, hnodes⟩ := canonical_output D _ _ hdir hUdeg hVdeg
  by_cases hd : S.α 0 * S.β 1 - S.α 1 * S.β 0 = 0
  · obtain ⟨t, ht, htβ⟩ := proportional_amplitudes S.α_primitive S.β_primitive (sub_eq_zero.mp hd)
    have htσ : twist t ≠ 0 := fun hz => ht (twist.injective (hz.trans (map_zero twist).symm))
    let a := S.a * C (twist t)
    have heq (i : Fin 2) : (S.β i).map twist = C (twist t) * (S.α i).map twist := by
      rw [htβ i, Polynomial.map_mul, Polynomial.map_C]
    have hU : threeU a S.α = threeU S.a S.β :=
      (threeU_eq _ _).trans ((rescale_threeU S.a S.α S.β (twist t) heq).trans (threeU_eq _ _).symm)
    have hdeg (i : Fin 2) : (S.β i).natDegree = (S.α i).natDegree := by
      rw [htβ i, natDegree_C_mul ht]
    have ha' : a.natDegree + amplitudeDegree (S.α 0) (S.α 1) ≤ D.height := by
      simpa only [a, natDegree_mul_C htσ, amplitudeDegree, hdeg] using ha
    have hdir' : sameDirection D.U D.V (threeU a S.α) (threeV S.b S.α) := by
      rw [hU]
      exact hdir
    have hn : relationOn u (fixedNodes R) (threeU a S.α) (threeV S.b S.α) W := by
      rw [hU]
      exact hnodes
    exact ⟨⟨hr, S.α, S.α, a, S.b, mul_ne_zero S.a_ne (C_ne_zero.mpr htσ), S.b_ne,
      S.α_primitive, S.α_primitive, ha', hb, hdir', W, hW, hn⟩, Or.inr rfl⟩
  · exact ⟨⟨hr, S.α, S.β, S.a, S.b, S.a_ne, S.b_ne,
      S.α_primitive, S.β_primitive, ha, hb, hdir, W, hW, hnodes⟩, Or.inl hd⟩
theorem classify_fixed {u : Words} (hfront : FrontRemainder u) (T : TwoActive u)
    (R : Relation T) (hmove : ¬ MovingGCD R) (hinvalid : ¬ InvalidLeft R)
    (hsat : NormalSaturation R) (hw : ∃ γ, Normal u γ ∧ Nonempty (BadMark u γ)) :
    ∃ D : Reduction u T R, columnRank D.U D.V = 4 ∨
      ∃ B : RankThree u T R D, Nonparallel B ∨ Parallel B := by
  have hu : leftU R ≠ 0 := by
    obtain ⟨γ, hγ, ⟨M⟩⟩ := hw
    intro hz
    exact (hsat γ hγ M).U_ne (by rw [atSlope, hz, Polynomial.map_zero])
  obtain ⟨D⟩ := puncture R hsat hw (fixed_gcd R hu hmove hinvalid)
  refine ⟨D, ?_⟩
  rcases K1_8.rank_cases D.U D.V D.U_ne D.V_ne with hfour | hthree
  · exact Or.inl ((columnRank_eq _ _).trans hfour)
  · obtain ⟨S⟩ := K1_8_1.proof D.U D.V D.U_ne D.V_ne hthree
    have hsmall := (shortened_guards D hfront).2.2
    obtain ⟨ha, hb⟩ := K1_8_2.proof D.U D.V D.height D.U_ne D.V_ne D.coprime D.max_degree hsmall S
    exact Or.inr (rank_three_branch D ((columnRank_eq _ _).trans hthree) S ha hb)
end
end Front6969
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace Front6969
open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open K1_6 (certificate_shifts_annihilate_generic)
open K1_6 (lift_common_divisor specialize_factor eval_atSlope root_outside_of_dvd_locator common_node_count)
private theorem certificate_shifts_annihilate {u : Words} {T : TwoActive u} (R : Relation T)
    (s : ℕ) (hL : T.height + s = L) :
    (K1_6.shifts (fun b => Principal.assemble (fun j => R.coefficients (b, j))) L s).transpose *
      twoBlock u = 0 := by
  have hsize : k + (48667 + 1) + t ≤ Fintype.card I := by
    rw [IRSProfile.card_index]
    decide
  exact certificate_shifts_annihilate_generic p node (u 0) (u 1) IRSProfile.domain.injective
    Native.native_domain_fixed (algebraMap (Polynomial K) Frac) (IsFractionRing.injective (Polynomial K) Frac)
    k T.height 48667 t s hL hsize R _ (fun _ => rfl)
private theorem moving_has_new_node {u : Words} {T : TwoActive u} (R : Relation T)
    (hMoving : MovingGCD R) {γ : K} {M : BadMark u γ} (hSat : SaturatedAt R M) :
    ∃ i ∉ fixedNodes R,
      (atSlope (leftU R) γ).eval (node i) = 0 ∧ (atSlope (leftV R) γ).eval (node i) = 0 := by
  classical
  obtain ⟨G, hG, hGU, hGV, hg⟩ := hMoving.2
  obtain ⟨D, hD, hd, hDU, hDV⟩ := lift_common_divisor hG hGU hGV
  obtain ⟨A, hA⟩ := hDU
  obtain ⟨B, hB⟩ := hDV
  obtain ⟨hAU, hAUdeg⟩ := specialize_factor hD hA hSat.U_ne
  obtain ⟨hBV, hBVdeg⟩ := specialize_factor hD hB hSat.V_ne
  change atSlope (leftU R) γ = atSlope D γ * atSlope A γ at hAU
  change atSlope (leftV R) γ = atSlope D γ * atSlope B γ at hBV
  change (atSlope (leftU R) γ).natDegree + D.natDegree ≤
    (leftU R).natDegree + (atSlope D γ).natDegree at hAUdeg
  change (atSlope (leftV R) γ).natDegree + D.natDegree ≤
    (leftV R).natDegree + (atSlope D γ).natDegree at hBVdeg
  have hdeg : D.natDegree ≤ (atSlope D γ).natDegree := by
    have hU := R.x_degree 0
    have hV := R.x_degree 1
    change (leftU R).natDegree ≤ T.height at hU
    change (leftV R).natDegree ≤ T.height at hV
    have hMax := hSat.degree_eq
    rcases le_total (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree with h | h
    · rw [max_eq_right h] at hMax
      omega
    · rw [max_eq_left h] at hMax
      omega
  obtain ⟨errors, _, hGCD⟩ := hSat.gcd_errors
  have hDvd := hGCD.2.2.2 (atSlope D γ) ⟨atSlope A γ, hAU⟩ ⟨atSlope B γ, hBV⟩
  have hCard : (fixedNodes R).card < (atSlope D γ).natDegree := by omega
  obtain ⟨i, hiFixed, hi⟩ := root_outside_of_dvd_locator (F := K) (ι := I)
    node IRSProfile.domain.injective errors (fixedNodes R) (atSlope D γ) hDvd hCard
  exact ⟨i, hiFixed, by rw [hAU, eval_mul, hi, zero_mul], by rw [hBV, eval_mul, hi, zero_mul]⟩
open P1 (count_bound)
private theorem normal_growth_count {u : Words} {T : TwoActive u} (R : Relation T)
    (hHeight : ∀ i, (R.coefficients i).natDegree ≤ 6944165320)
    (hMoving : MovingGCD R) (hSat : NormalSaturation R) (Γ : Finset K)
    (hBad : BadFamily u Γ) (hNormal : ∀ γ ∈ Γ, Normal u γ) :
    Γ.card ≤ 1820371273646080 := by
  classical
  let U (i : I) := (leftU R).eval (C (node i))
  let V (i : I) := (leftV R).eval (C (node i))
  have hU (i) : (U i).natDegree ≤ 6944165320 := by
    dsimp only [U, leftU]
    rw [Strata.assemble_nodePolynomial]
    exact Principal.nodePolynomial_natDegree_le _ (fun j => hHeight (0, j)) _
  have hV (i) : (V i).natDegree ≤ 6944165320 := by
    dsimp only [V, leftV]
    rw [Strata.assemble_nodePolynomial]
    exact Principal.nodePolynomial_natDegree_le _ (fun j => hHeight (1, j)) _
  have hNew (γ : K) (hγ : γ ∈ Γ) :
      ∃ i, ¬ (U i = 0 ∧ V i = 0) ∧ (U i).eval γ = 0 ∧ (V i).eval γ = 0 := by
    refine (Front6969.bad_mark u Γ hBad γ hγ).elim (fun M => ?_)
    obtain ⟨i, hi, hu, hv⟩ := moving_has_new_node R hMoving (hSat γ (hNormal γ hγ) M)
    have hNZ : ¬ (U i = 0 ∧ V i = 0) := by
      simpa only [fixedNodes, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact ⟨i, hNZ, (eval_atSlope (leftU R) γ (node i)).symm.trans hu,
      (eval_atSlope (leftV R) γ (node i)).symm.trans hv⟩
  exact count_bound (c := Γ.card) (n := Fintype.card I) (n' := 262144)
    (H := 6944165320) (b := 1820371273646080) IRSProfile.card_index
    (common_node_count U V 6944165320 Γ hU hV hNew) rfl
theorem moving_count (u : Words) (front : FrontRemainder u) (T : TwoActive u)
    (R : Relation T) (moving : MovingGCD R) (saturated : NormalSaturation R)
    (Γ : Finset K) (bad : BadFamily u Γ) (normal : ∀ γ ∈ Γ, Normal u γ) :
    Γ.card ≤ 1820371273646080 := by
  let P (b : Fin 2) : Bivar := Principal.assemble (fun j => R.coefficients (b, j))
  let s := L - T.height
  have hP : ∀ b, (P b).natDegree ≤ T.height := R.x_degree
  have hBalance := relation_height_balance T
  have hHeight := relation_height_le front T
  change T.height ≤ 33735 at hHeight
  have hsDef : s = 48668 - T.height := rfl
  have hSum : T.height + s = L := by change T.height + s = 48668; omega
  have hs : 14933 ≤ s := by omega
  have hRank : GenericLayer.genericRank (twoBlock u) + s = 2 * L := by
    change stackRank u + s = _
    rw [actual_stackRank u]
    change 48668 + T.height + nullity u = 82405 at hBalance
    change 82405 - nullity u + s = 97336
    omega
  have hCoordinates : K1_6.pairCoordinates P T.height = R.coefficients := by
    funext i
    exact Principal.assemble_coeff (fun j => R.coefficients (i.1, j)) i.2
  have hPrim : PrimitiveVector.IsPrimitive (K1_6.pairCoordinates P T.height) := by
    rw [hCoordinates]
    exact R.primitive
  have hKernel := certificate_shifts_annihilate R s hSum
  obtain ⟨hMinors, H, hH, rows, hRows⟩ :=
    K1_6_1.proof K T.height L s P hSum (by omega) hP hPrim
  have hBound := K1_6_2.proof K L (t + 1) s p (twoBlock u) (K1_6.shifts P L s)
    (by decide) hRank hKernel (stacked_entry_natDegree p node (u 0) (u 1) L t) hMinors rows
  rw [hRows] at hBound
  have hProduct : 14933 * H ≤ s * H := Nat.mul_le_mul_right H hs
  have hCeiling : L * (p + 1) = 103697220729912 := rfl
  rw [hCeiling] at hBound
  have hCap : H ≤ 6944165320 := by omega
  apply normal_growth_count R _ moving saturated Γ bad normal
  intro i
  rw [← hCoordinates]
  exact (hH i.1 i.2.val).trans hCap
end Front6969
end
set_option backward.isDefEq.respectTransparency false
namespace Front6969
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
def c1 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T), NormalSaturation R
def c2 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D),
    NormalSaturation R → Parallel B → ¬ UnitNorm B →
    ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) → Γ.card ≤ t + 1
def c3 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D),
    NormalSaturation R → Nonparallel B →
    ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) → Γ.card ≤ 250000000000000000
def c4 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T) (D : Reduction u T R),
    NormalSaturation R → columnRank D.U D.V = 4 →
    ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) → Γ.card ≤ 250000000000000000
def c5 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D),
    NormalSaturation R → Parallel B → UnitNorm B →
    ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) →
    Γ.card ≤ anchorFee ∨
      ∃ book : Finset K, book ⊆ Γ ∧ book.card ≤ anchorFee ∧
        ∃ M : AnchorModel u (fixedNodes R), Nonempty (AnchoredFamily M (Γ \ book))
def c6 : Prop :=
  ∀ u deleted (M : AnchorModel u deleted) Γ, AnchoredFamily M Γ →
    1 ≤ M.overhead → M.overhead ≤ lowCutoff →
    Γ.card ≤ lowCap
def c7 : Prop :=
  ∀ u deleted (M : AnchorModel u deleted) Γ, AnchoredFamily M Γ →
    lowCutoff + 1 ≤ M.overhead → M.overhead ≤ (heightCap : ℤ) →
    Γ.card ≤ highCap
theorem mem_normalSlopes {u : Words} {Γ : Finset K} {γ : K} :
    γ ∈ normalSlopes u Γ ↔ γ ∈ Γ ∧ Normal u γ := by
  classical exact Finset.mem_filter
theorem normal_badFamily {u : Words} {Γ : Finset K} (hΓ : BadFamily u Γ) :
    BadFamily u (normalSlopes u Γ) :=
  fun γ hγ => hΓ γ (mem_normalSlopes.mp hγ).1
theorem normal_on_normalSlopes {u : Words} {Γ : Finset K} :
    ∀ γ ∈ normalSlopes u Γ, Normal u γ :=
  fun _ hγ => (mem_normalSlopes.mp hγ).2
theorem add_rank_exceptions (u : Words) (hu : FrontRemainder u) (Γ : Finset K)
    (b : ℕ) (hb : (normalSlopes u Γ).card ≤ b) :
    Γ.card ≤ b + rankFee := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s := Γ) (p := Normal u)]
  exact Nat.add_le_add hb (rank_exceptions u hu Γ)
theorem low_with_reserve : lowCap + anchorFee + rankFee = 274928728022923468 := by decide
theorem nonpositive_with_reserve : listCap + anchorFee + rankFee = 195758851884413 := by decide
private theorem coherent_count (h5 : c5) (h6 : c6) (h7 : c7) (hlist : CJ0.ScalarList agreement listCap)
    (u : Words) (hu : FrontRemainder u) (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D) (hsat : NormalSaturation R)
    (hp : Parallel B) (hn : UnitNorm B) (Γ : Finset K) (hΓ : BadFamily u Γ) :
    Γ.card ≤ scalarCap := by
  classical
  let N := normalSlopes u Γ
  rcases h5 u hu T R D B hsat hp hn N (normal_badFamily hΓ) normal_on_normalSlopes with
    hcheap | ⟨book, hs, hb, M, ⟨F⟩⟩
  · exact (add_rank_exceptions u hu Γ _ hcheap).trans (by decide)
  · have htotal : Γ.card ≤ (N \ book).card + book.card + rankFee :=
      add_rank_exceptions u hu Γ _ (Finset.card_sdiff_add_card_eq_card hs).ge
    have hreserve (b : ℕ) (h : (N \ book).card ≤ b) : Γ.card ≤ b + anchorFee + rankFee :=
      htotal.trans (Nat.add_le_add_right (Nat.add_le_add h hb) rankFee)
    have hwmax : M.overhead ≤ (heightCap : ℤ) := by
      have hh := M.height_bound
      change (M.E.natDegree : ℤ) - M.factor.natDegree - amplitudeDegree M.A₀ M.A₁ ≤ heightCap
      omega
    by_cases hw₀ : M.overhead ≤ 0
    · exact (hreserve _ (P1.anchored_list_count hlist M _ F hw₀)).trans
        (nonpositive_with_reserve.le.trans (by decide))
    by_cases hwL : M.overhead ≤ lowCutoff
    · exact (hreserve _ (h6 u _ M _ F (by omega) hwL)).trans
        (low_with_reserve.le.trans (by decide))
    · exact (hreserve _ (h7 u _ M _ F (by omega) hwmax)).trans (by decide)
private theorem scalar_count (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (h5 : c5) (h6 : c6) (h7 : c7) (hlist : CJ0.ScalarList agreement listCap)
    (u : Words) (Γ : Finset K) (hΓ : BadFamily u Γ) : Γ.card ≤ scalarCap := by
  classical
  by_cases hdef : firstRank u < L
  · exact (deficient_count u Γ hdef hΓ).trans (by decide)
  have hfirst := Nat.le_antisymm (firstRank_le u) (Nat.le_of_not_gt hdef)
  by_cases hz : nullity u = 0
  · exact (full_column_count u Γ hfirst hz hΓ).trans (by decide)
  by_cases htype : TypeAtMostOne u
  · exact (type_one_count u htype Γ hΓ).trans (by decide)
  by_cases hprincipal : HomogeneousPrincipal u
  · exact (principal_count u Γ hprincipal hΓ).trans (by decide)
  by_cases hconstant : ConstantKernel u
  · exact (constant_count u Γ hconstant hΓ).trans (by decide)
  obtain ⟨T⟩ := two_active_of_positive u (Nat.pos_of_ne_zero hz) htype hprincipal
  have hu : FrontRemainder u := ⟨two_active_nullity T, hfirst, htype, hprincipal, hconstant⟩
  let R := relation_of_two_active hu T
  have hsat := h1 u hu T R
  let N := normalSlopes u Γ
  have hN := normal_badFamily hΓ
  have hnormal := @normal_on_normalSlopes u Γ
  by_cases hmoving : MovingGCD R
  · exact (add_rank_exceptions u hu Γ _ (moving_count u hu T R hmoving hsat N hN hnormal)).trans
      (by decide)
  have hnone (he : N = ∅) : Γ.card ≤ scalarCap :=
    (add_rank_exceptions u hu Γ 0 (by rw [show normalSlopes u Γ = ∅ from he]; simp)).trans
      (by decide)
  by_cases hinvalid : InvalidLeft R
  · apply hnone
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro γ hγ
    obtain ⟨hγΓ, hnγ⟩ := mem_normalSlopes.mp hγ
    obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγΓ
    exact (hsat γ hnγ M).valid hinvalid
  by_cases hne : N.Nonempty
  · obtain ⟨γ, hγ⟩ := hne
    obtain ⟨hγΓ, hnγ⟩ := mem_normalSlopes.mp hγ
    obtain ⟨D, hfour | ⟨B, hnp | hpar⟩⟩ := classify_fixed hu T R hmoving hinvalid hsat
      ⟨γ, hnγ, bad_mark u Γ hΓ γ hγΓ⟩
    · exact (add_rank_exceptions u hu Γ _ (h4 u hu T R D hsat hfour N hN hnormal)).trans
        (by decide)
    · exact (add_rank_exceptions u hu Γ _ (h3 u hu T R D B hsat hnp N hN hnormal)).trans
        (by decide)
    · by_cases hn : UnitNorm B
      · exact coherent_count h5 h6 h7 hlist u hu T R D B hsat hpar hn Γ hΓ
      · exact (add_rank_exceptions u hu Γ _ (h2 u hu T R D B hsat hpar hn N hN hnormal)).trans
          (by decide)
  · exact hnone (Finset.not_nonempty_iff_eq_empty.mp hne)

/-- The seven rank and height cases suffice for the protocol at 82,404 errors. -/
theorem of_children (hlist : CJ0.ScalarList agreement listCap) (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) (h6 : c6) (h7 : c7) :
    ProtocolClaim 6969 2899368181980161361 9223372036854649837 :=
  Research6969.ProfileProtocol.protocol_claim_of_scalar_cap hlist
    (scalar_count h1 h2 h3 h4 h5 h6 h7 hlist)
end
end Front6969

end Merged_R6960Front6969Cases

-- merged module Front6969Rank1
section Merged_Front6969Rank1
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
namespace Front6969_1
noncomputable section
open Polynomial Matrix FrobeniusLocator Front6969
open ProximityPrize.Benchmark
open P1_1 (eval_atSlope commonGCD_of_roots lift_dvd_atSlope)
private theorem twoBlock_atSlope (u : Words) (γ : K) :
    ((twoBlock u).map (evalRingHom γ)) =
      Strata.conjugateHankel (Strata.twoConjugations (frobenius K p))
        node (fun i => u 0 i + γ * u 1 i) L t := by
  rw [twoBlock, Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval]
  have h : (fun b : Fin 2 => iterateFrobenius K p b.val) =
      Strata.twoConjugations (frobenius K p) := by
    funext b
    fin_cases b
    · exact iterateFrobenius_zero K p
    · exact iterateFrobenius_one K p
  rw [h]
private theorem rank_at_normal {u : Words} (T : TwoActive u) {γ : K} (hγ : Normal u γ) :
    ((twoBlock u).map (evalRingHom γ)).rank = L + T.height := by
  change _ = stackRank u at hγ
  rw [hγ, actual_stackRank]
  have h := relation_height_balance T
  omega
private theorem error_rank {u : Words} {γ : K} (M : BadMark u γ)
    (E : Finset I) (hE : E.card ≤ t)
    (hEagree : ∀ i ∉ E, u 0 i + γ * u 1 i = M.decoder.eval (node i)) :
    ((twoBlock u).map (evalRingHom γ)).rank =
      (Strata.errorTwoMatrix (frobenius K p) (fun i : E => node i.val)
        (fun i : E => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)) L).rank := by
  have hfix : ∀ b i, Strata.twoConjugations (frobenius K p) b (node i) = node i := by
    intro b i
    fin_cases b <;> simp [Strata.twoConjugations, frobenius_def, Native.native_domain_fixed]
  have h := Strata.conjugateHankel_error_rank
    (Strata.twoConjugations (frobenius K p)) node (fun i => u 0 i + γ * u 1 i)
    IRSProfile.domain.injective hfix M.decoder k L t M.degree
    (by rw [IRSProfile.card_index]; decide) E (hE.trans (Nat.le_succ t)) hEagree
  rw [Strata.conjugateErrors_two] at h
  rw [twoBlock_atSlope]
  exact h
private theorem valid_of_saturation {u : Words} {T : TwoActive u} (R : Relation T)
    (γ : K) (S : Finset I)
    (hdegree : max (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree = T.height)
    (hG : IsCommonGCD (locator node S) (atSlope (leftU R) γ) (atSlope (leftV R) γ)) :
    ¬ InvalidLeft R := by
  intro hinvalid
  rcases hinvalid with hlow | ⟨G, _, hGU, hGV, hbad⟩
  · have hle : max (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree ≤
        max (leftU R).natDegree (leftV R).natDegree :=
      max_le_max Polynomial.natDegree_map_le Polynomial.natDegree_map_le
    omega
  · have hS : locator node S ∣ locator node Finset.univ :=
      ⟨locator node (Finset.univ \ S),
        (Principal.locator_mul_sdiff node S Finset.univ (Finset.subset_univ S)).symm⟩
    exact hbad ((hG.2.2.2 G (lift_dvd_atSlope γ hGU) (lift_dvd_atSlope γ hGV)).trans hS)
theorem proof : Front6969.c1 := by
  classical
  intro u hfront T R γ hγ M
  let U := atSlope (leftU R) γ
  let V := atSlope (leftV R) γ
  let E : Finset I := Finset.univ.filter (fun i => M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i)
  let e : E → K := fun i => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)
  let x : E → K := fun i => node i.val
  have hEagree (i : I) (hi : i ∉ E) : u 0 i + γ * u 1 i = M.decoder.eval (node i) := by
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm h⟩)
  have hEcard : E.card ≤ t := by
    have hsub : E ⊆ Finset.univ \ M.support := by
      intro i hi
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hs => ?_⟩
      exact (Finset.mem_filter.mp hi).2 (M.hits i hs)
    have h := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      IRSProfile.card_index] at h
    exact h.trans (Nat.sub_le_sub_left M.agreement blockLength)
  have hheight : T.height ≤ heightCap := relation_height_le hfront T
  have hH : T.height < L := hheight.trans_lt (by change 33735 < 48668; decide)
  have hfit : k + T.height ≤ M.support.card :=
    have hcap : k + heightCap ≤ agreement := by
      change 164807 ≤ 179740
      decide
    ((Nat.add_le_add_left hheight k).trans hcap).trans M.agreement
  have hfix (i : I) : frobenius K p (node i) = node i := Native.native_domain_fixed i
  obtain ⟨hpair, hrel⟩ :=
    Strata.certificate_specializes p node (u 0) (u 1) k T.height R γ
  have hUle : U.natDegree ≤ T.height := hrel.degree_U
  have hVle : V.natDegree ≤ T.height := hrel.degree_V
  have hx : Function.Injective x := IRSProfile.domain.injective.comp Subtype.val_injective
  have he (i : E) : e i ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp i.property).2)
  have herror (i : E) : U.eval (x i) * e i + V.eval (x i) * frobenius K p (e i) = 0 :=
    Strata.certificate_error_identity p node (u 0) (u 1) IRSProfile.domain.injective
      Native.native_domain_fixed k T.height R γ M.support hfit M.decoder M.degree M.hits i.val
  have hrank : (Strata.errorTwoMatrix (frobenius K p) x e L).rank = L + T.height :=
    (error_rank M E hEcard hEagree).symm.trans (rank_at_normal T hγ)
  obtain ⟨hU, hV⟩ := Strata.saturated_coefficients_nonzero (frobenius K p) x e hx U V
    T.height L hUle hVle hpair hH he herror hrank
  let G := GCDMonoid.gcd U V
  let C₀ := (Finset.univ : Finset E).filter (fun i => G.eval (x i) = 0)
  let S := C₀.image (fun i : E => i.val)
  obtain ⟨hC, hsum, _⟩ := Strata.normal_error_three_rank (frobenius K p) x e hx
    (fun i => hfix i.val) U V T.height L hUle hVle hpair hH he herror hrank
  have hmax : max U.natDegree V.natDegree = T.height := by
    obtain ⟨hle, hred⟩ := Strata.gcd_reduction_degrees U V hU hV
    change max (U / G).natDegree (V / G).natDegree + G.natDegree = T.height at hsum
    change G.natDegree ≤ max U.natDegree V.natDegree at hle
    change max (U / G).natDegree (V / G).natDegree =
      max U.natDegree V.natDegree - G.natDegree at hred
    omega
  have hS_card : S.card = G.natDegree :=
    (Finset.card_image_of_injective C₀ Subtype.val_injective).trans hC
  have hS_error (i : I) (hi : i ∈ S) : M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp j.property).2
  have hG : IsCommonGCD (locator node S) U V := by
    apply commonGCD_of_roots U V hV S _ hS_card
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp hj).2
  refine ⟨hU, hV, hmax, ⟨S, hS_error, hG⟩, ?_, valid_of_saturation R γ S hmax hG⟩
  intro i hi
  have hzero := (Finset.mem_filter.mp hi).2
  have hu0 : U.eval (node i) = 0 := by
    change (atSlope (leftU R) γ).eval (node i) = 0
    rw [eval_atSlope, hzero.1, eval_zero]
  have hv0 : V.eval (node i) = 0 := by
    change (atSlope (leftV R) γ).eval (node i) = 0
    rw [eval_atSlope, hzero.2, eval_zero]
  have hdiv : (Polynomial.X : (Polynomial K)) - C (node i) ∣ locator node S :=
    hG.2.2.2 _ (dvd_iff_isRoot.mpr hu0) (dvd_iff_isRoot.mpr hv0)
  have hroot : (locator node S).eval (node i) = 0 :=
    eval_eq_zero_of_dvd_of_eval_eq_zero hdiv (by rw [eval_sub, eval_X, eval_C, sub_self])
  exact hS_error i ((Principal.locator_eval_zero_iff node IRSProfile.domain.injective S i).mp hroot)
end
end Front6969_1
end

end Merged_Front6969Rank1

-- merged module Front6969Rank2
section Merged_Front6969Rank2

set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace Front6969_2
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P0 (Words k amplitudeDegree)
open K1_9 (K I node twist pencil fold pencil_degree
  seedCoeff crossValue CoefficientIdentities sixNorm_mul sixNorm_ne_zero)
open K1_9 (seedCoeff_degree)
open P0_5 (coefficientsAt pow_eq_twist threeUAt_native relationOnAt_native)
abbrev heightBound : ℕ := Front6969.heightCap
structure PolarData (u : Words) where
  a : (Polynomial K)
  b : (Polynomial K)
  A : Fin 2 → (Polynomial K)
  Q : K → K → (Polynomial K)
  a_ne : a ≠ 0
  norms_ne : K1.sixNorm a ≠ K1.sixNorm b
  primitive : IsCoprime (A 0) (A 1)
  a_bound : a.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  b_bound : b.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  Q_degree : ∀ r s, (Q r s).degree < (k + heightBound : ℕ)
  nodes : ∀ r s i,
    (Q r s).eval (node i) =
      a.eval (node i) * twist ((pencil (A 0) (A 1) r).eval (node i)) * fold u s i -
      b.eval (node i) * (pencil (A 0) (A 1) s).eval (node i) * twist (fold u r i)
abbrev PolarData.amp {u : Words} (D : PolarData u) := pencil (D.A 0) (D.A 1)
private theorem polarData_of_set {u : Words} (S : Finset I) (height : ℕ)
    (a b : (Polynomial K)) (A : Fin 2 → (Polynomial K)) (output : P0.Bivar)
    (hh : height + S.card ≤ heightBound)
    (hout : output.degree < (k + height : ℕ))
    (hfirst : a.natDegree + amplitudeDegree (A 0) (A 1) ≤ height)
    (hsecond : b.natDegree + amplitudeDegree (A 0) (A 1) ≤ height)
    (hane : a ≠ 0) (hn : K1.sixNorm a ≠ K1.sixNorm b) (hA : IsCoprime (A 0) (A 1))
    (hc : ∀ i ∉ S, CoefficientIdentities u a b A output i) : Nonempty (PolarData u) := by
  classical
  let g := locator node S
  let v (j : ℕ) := g * seedCoeff output j
  have hg : g.natDegree = S.card := locator_natDegree _ _
  have hd (j : ℕ) : (v j).degree < (k + heightBound : ℕ) := by
    have h := Strata.degree_mul_lt_add g (seedCoeff output j) g.natDegree
      (k + height) le_rfl (seedCoeff_degree _ _ _ hout)
    exact h.trans_le (by exact_mod_cast (show k + height + g.natDegree ≤ k + heightBound by omega))
  have ha : (g * a).natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound := by
    have h := natDegree_mul_le (p := g) (q := a)
    omega
  have hb : (g * b).natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound := by
    have h := natDegree_mul_le (p := g) (q := b)
    omega
  have hgn : g ≠ 0 := (locator_monic node S).ne_zero
  refine ⟨⟨g * a, g * b, A,
    fun r s => pencil (pencil (v 0) (v 1) s) (pencil (v K1.p) (v (K1.p + 1)) s) (twist r),
    mul_ne_zero hgn hane, ?_, hA, ha, hb, ?_, ?_⟩⟩
  · intro h
    rw [sixNorm_mul, sixNorm_mul] at h
    exact hn (mul_left_cancel₀ (sixNorm_ne_zero hgn) h)
  · intro r s
    exact pencil_degree (pencil_degree (hd 0) (hd 1) s)
      (pencil_degree (hd K1.p) (hd (K1.p + 1)) s) _
  · intro r s i
    by_cases hi : i ∈ S
    · have hz : g.eval (node i) = 0 := locator_eval_zero node _ i hi
      simp only [pencil, v, eval_mul, eval_add, eval_C, hz, zero_mul, mul_zero, add_zero, sub_zero]
    obtain ⟨h0, h1, h2, h3⟩ := hc i hi
    simp only [pencil, fold, v, eval_add, eval_mul, eval_C, h0, h1, h2, h3,
      crossValue, map_add, map_mul]
    ring
end
end Front6969_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Front6969_2
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open Front6969 (Words k agreement amplitudeDegree)
open K1_9 (K I node twist pencil fold map_eval_node pencil_natDegree pencil_degree
  degree_sub_lt eq_on_nodes sixNorm_mul sixNorm_twist sixNorm_ne_zero)
open K1_9 (all_card affine_zero residual fold_residual)
private theorem amp_natDegree_le {u : Words} (D : PolarData u) (z : K) :
    (D.amp z).natDegree ≤ amplitudeDegree (D.A 0) (D.A 1) :=
  pencil_natDegree ..
private theorem PolarData.amp_nonzero_at {u} (D : PolarData u) {r s : K}
    (hrs : r ≠ s) (i : I) : (D.amp r).eval (node i) ≠ 0 ∨ (D.amp s).eval (node i) ≠ 0 := by
  by_contra! hz
  obtain ⟨hr, hs⟩ := hz
  simp only [PolarData.amp, pencil, eval_add, eval_mul, eval_C] at hr hs
  have hb : (r-s) * (D.A 1).eval (node i) = 0 := by linear_combination hr - hs
  have h1 := (mul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr hrs)
  have h0 : (D.A 0).eval (node i) = 0 := by simpa [h1] using hr
  obtain ⟨P, Q, hPQ⟩ := D.primitive
  have h := congrArg (Polynomial.eval (node i)) hPQ
  simp only [eval_add, eval_mul, h0, h1, mul_zero, add_zero, eval_one, zero_ne_one] at h
private def PolarData.cross {u} (D : PolarData u) (r s : K) (P Q : (Polynomial K)) : (Polynomial K) :=
  D.a * (D.amp r).map twist * Q - D.b * D.amp s * P.map twist
private theorem PolarData.cross_degree {u} (D : PolarData u) (r s : K)
    {P Q : (Polynomial K)} (hP : P.degree < k) (hQ : Q.degree < k) :
    (D.cross r s P Q).degree < (k + heightBound : ℕ) := by
  have hl : (D.a * (D.amp r).map twist).natDegree ≤ heightBound :=
    natDegree_mul_le.trans <|
      (Nat.add_le_add_left (natDegree_map_le.trans (amp_natDegree_le D r)) _).trans D.a_bound
  have hr : (D.b * D.amp s).natDegree ≤ heightBound :=
    natDegree_mul_le.trans <|
      (Nat.add_le_add_left (amp_natDegree_le D s) _).trans D.b_bound
  exact degree_sub_lt
    (Strata.degree_mul_lt_add _ _ heightBound k hl hQ)
    (Strata.degree_mul_lt_add _ _ heightBound k hr (degree_map_le.trans_lt hP))
private theorem PolarData.decoder_identity {u} (D : PolarData u) (z : K)
    (S : Finset I) (P : (Polynomial K)) (hS : agreement ≤ S.card) (hP : P.degree < k)
    (hits : ∀ i ∈ S, P.eval (node i) = fold u z i) : D.cross z z P P = D.Q z z := by
  have hcard := (show k + heightBound ≤ agreement by decide).trans hS
  have hb : ((k + heightBound : ℕ) : WithBot ℕ) ≤ S.card := by exact_mod_cast hcard
  apply eq_on_nodes S _ _ ((D.cross_degree z z hP hP).trans_le hb) ((D.Q_degree z z).trans_le hb)
  intro i hi
  simp only [PolarData.cross, eval_sub, eval_mul, map_eval_node, hits i hi, D.nodes]
private def PolarData.subtract {u} (D : PolarData u) (P Q : (Polynomial K))
    (hP : P.degree < k) (hQ : Q.degree < k) : PolarData (residual u P Q) where
  a := D.a
  b := D.b
  A := D.A
  Q r s := D.Q r s - D.cross r s (pencil P Q r) (pencil P Q s)
  a_ne := D.a_ne
  norms_ne := D.norms_ne
  primitive := D.primitive
  a_bound := D.a_bound
  b_bound := D.b_bound
  Q_degree r s := degree_sub_lt (D.Q_degree r s)
    (D.cross_degree r s (pencil_degree hP hQ r) (pencil_degree hP hQ s))
  nodes r s i := by
    simp only [eval_sub, D.nodes, PolarData.cross, eval_mul, map_eval_node, fold_residual, map_sub]
    ring
private theorem PolarData.offdiag_zero {u} (D : PolarData u) {r s : K}
    (hr : D.amp r ≠ 0) (hs : D.amp s ≠ 0) (hrr : D.Q r r = 0) (hss : D.Q s s = 0) :
    D.Q r s = 0 := by
  let E := D.amp s * (D.amp r).map twist
  let d := amplitudeDegree (D.A 0) (D.A 1)
  have hd : d ≤ heightBound := (Nat.le_add_left _ _).trans D.a_bound
  have hE : E.natDegree ≤ d + d := natDegree_mul_le.trans
    (Nat.add_le_add (amp_natDegree_le D s) (natDegree_map_le.trans (amp_natDegree_le D r)))
  have hl : (D.b * E).natDegree ≤ heightBound + heightBound := by
    have hb : D.b.natDegree + d ≤ heightBound := D.b_bound
    exact natDegree_mul_le.trans (by omega)
  have ht : (D.a.map twist * E.map twist).natDegree ≤ heightBound + heightBound := by
    have ha : D.a.natDegree + d ≤ heightBound := D.a_bound
    exact natDegree_mul_le.trans
      ((Nat.add_le_add natDegree_map_le natDegree_map_le).trans (by omega))
  have hcut : ((k + heightBound + (heightBound + heightBound) : ℕ) : WithBot ℕ) ≤
      (Finset.univ : Finset I).card := by
    rw [all_card]
    exact_mod_cast (show k + heightBound + (heightBound + heightBound) ≤ 262144 by decide)
  have heq : D.b * E * (D.Q r s).map twist = D.a.map twist * E.map twist * D.Q r s := by
    apply eq_on_nodes Finset.univ _ _
      ((Strata.degree_mul_lt_add _ _ _ _ hl (degree_map_le.trans_lt (D.Q_degree r s))).trans_le hcut)
      ((Strata.degree_mul_lt_add _ _ _ _ ht (D.Q_degree r s)).trans_le hcut)
    intro i _
    have h₁ := (D.nodes r r i).symm
    have h₂ := (D.nodes s s i).symm
    rw [hrr, eval_zero] at h₁
    rw [hss, eval_zero] at h₂
    have hσ := congrArg (fun x => twist x) h₁
    simp only [map_sub, map_mul, map_zero] at hσ
    simp only [E, eval_mul, map_eval_node, D.nodes, map_sub, map_mul]
    linear_combination
      -(twist (D.a.eval (node i))) * twist (twist ((D.amp r).eval (node i))) *
        twist ((D.amp r).eval (node i)) * h₂ +
      D.b.eval (node i) * (D.amp s).eval (node i) * twist ((D.amp s).eval (node i)) * hσ
  by_contra hne
  have hn : E ≠ 0 := mul_ne_zero hs ((Polynomial.map_ne_zero_iff twist.injective).mpr hr)
  have hN := congrArg K1.sixNorm heq
  simp only [sixNorm_mul, sixNorm_twist] at hN
  exact D.norms_ne (mul_right_cancel₀ (sixNorm_ne_zero hn)
    (mul_right_cancel₀ (sixNorm_ne_zero hne) hN.symm))
private theorem PolarData.zero_of_diagonal_zeros {u} (D : PolarData u) {r s : K}
    (hrs : r ≠ s) (hr : D.amp r ≠ 0) (hs : D.amp s ≠ 0)
    (hrr : D.Q r r = 0) (hss : D.Q s s = 0) (y z : K) : D.Q y z = 0 := by
  have hrs' := D.offdiag_zero hr hs hrr hss
  have hsr' := D.offdiag_zero hs hr hss hrr
  apply eq_on_nodes Finset.univ _ _ (by rw [all_card]; exact (D.Q_degree y z).trans_le (by exact_mod_cast (show k + heightBound ≤ 262144 by decide)))
    (by rw [all_card, degree_zero]; exact WithBot.bot_lt_coe 262144)
  intro i _
  let f (r s : K) := (D.Q r s).eval (node i)
  have right (x γ : K) : f x γ = f x 0 + id γ * (f x 1 - f x 0) := by
    simp only [f, D.nodes, pencil, fold, eval_add, eval_mul, eval_C, id_eq]
    ring
  have left (x γ : K) : f γ x = f 0 x + twist γ * (f 1 x - f 0 x) := by
    simp only [f, D.nodes, pencil, fold, eval_add, eval_mul, eval_C, map_add, map_mul,
      map_zero, map_one]
    ring
  have h₁ : f r z = 0 := affine_zero (f r) id Function.injective_id hrs (right r)
    (by simp [f, hrr]) (by simp [f, hrs']) z
  have h₂ : f s z = 0 := affine_zero (f s) id Function.injective_id hrs (right s)
    (by simp [f, hsr']) (by simp [f, hss]) z
  simpa only [eval_zero] using affine_zero (fun γ => f γ z) twist twist.injective hrs (left z) h₁ h₂ y
private theorem PolarData.decoder_zero {u} (D : PolarData u) (hQ : ∀ r s, D.Q r s = 0) (z : K)
    (S : Finset I) (P : (Polynomial K)) (hS : agreement ≤ S.card) (hP : P.degree < k)
    (hits : ∀ i ∈ S, P.eval (node i) = fold u z i) : P = 0 := by
  classical
  by_cases hz : D.amp z = 0
  · let S' := S.filter (fun i => D.a.eval (node i) ≠ 0)
    let roots := S.filter (fun i => D.a.eval (node i) = 0)
    have hroots : roots.card ≤ D.a.natDegree := by
      rw [← Finset.card_image_of_injective roots node.injective]
      apply Polynomial.card_le_degree_of_subset_roots
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Polynomial.mem_roots D.a_ne).mpr (Finset.mem_filter.mp hi).2
    have hsum : roots.card + S'.card = S.card := Finset.card_filter_add_card_filter_not ..
    have ha : D.a.natDegree ≤ heightBound := (Nat.le_add_right _ _).trans D.a_bound
    have hmargin : k + heightBound ≤ agreement := by decide
    have hcard : k ≤ S'.card := by omega
    apply eq_on_nodes S' _ _ (hP.trans_le (by exact_mod_cast hcard))
      (by rw [degree_zero]; exact WithBot.bot_lt_coe _)
    intro i hi
    have hi' : i ∈ S ∧ D.a.eval (node i) ≠ 0 := Finset.mem_filter.mp hi
    obtain ⟨hiS, hia⟩ := hi'
    rw [hits i hiS, eval_zero]
    obtain ⟨r, hr⟩ : ∃ r, (D.amp r).eval (node i) ≠ 0 := by
      rcases D.amp_nonzero_at zero_ne_one i with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have he := (D.nodes r z i).symm
    simp only [hQ, hz, eval_zero, mul_zero, zero_mul, sub_zero] at he
    have ht : twist ((D.amp r).eval (node i)) ≠ 0 := by
      intro h
      exact hr (twist.injective (h.trans (map_zero twist).symm))
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hia ht)
  · have he := D.decoder_identity z S P hS hP hits
    rw [hQ, PolarData.cross] at he
    by_contra hne
    have hN := congrArg K1.sixNorm (sub_eq_zero.mp he)
    simp only [sixNorm_mul, sixNorm_twist] at hN
    exact D.norms_ne (mul_right_cancel₀ (sixNorm_ne_zero hz)
      (mul_right_cancel₀ (sixNorm_ne_zero hne) hN))
theorem pencil_of_marks {u : Words} (D : PolarData u) (Γ : Finset K)
    (M : ∀ z ∈ Γ, Front6969.BadMark u z) :
    Γ.card ≤ 2 ∨ ∃ P Q : (Polynomial K), P.degree < k ∧ Q.degree < k ∧
      ∀ z (hz : z ∈ Γ), (M z hz).decoder = pencil P Q z := by
  classical
  let G := Γ.filter (fun z => D.amp z ≠ 0)
  by_cases hsmall : G.card ≤ 1
  · let zeros := Γ.filter (fun z => D.amp z = 0)
    have hZ : zeros.card ≤ 1 := by
      apply Finset.card_le_one_iff.mpr
      intro r s hr hs
      by_contra hrs
      have hr' := (Finset.mem_filter.mp hr).2
      have hs' := (Finset.mem_filter.mp hs).2
      simpa [hr', hs'] using D.amp_nonzero_at hrs (0 : I)
    have hsum : zeros.card + G.card = Γ.card := Finset.card_filter_add_card_filter_not ..
    exact Or.inl (by omega)
  right
  obtain ⟨r, hr, s, hs, hrs⟩ := Finset.one_lt_card.mp (by omega : 1 < G.card)
  obtain ⟨hrΓ, hrA⟩ := Finset.mem_filter.mp hr
  obtain ⟨hsΓ, hsA⟩ := Finset.mem_filter.mp hs
  let Wr := (M r hrΓ).decoder
  let Ws := (M s hsΓ).decoder
  let Q := C ((s-r)⁻¹) * (Ws-Wr)
  let P := Wr - C r * Q
  have hWr : Wr.degree < k := (M r hrΓ).degree
  have hWs : Ws.degree < k := (M s hsΓ).degree
  have scale (c : K) (V : (Polynomial K)) (hV : V.degree < k) : (C c * V).degree < k := by
    by_cases hc : c = 0
    · rw [hc, map_zero, zero_mul, degree_zero]
      exact WithBot.bot_lt_coe k
    · simpa only [degree_C_mul hc] using hV
  have hQ : Q.degree < k := scale _ _ (degree_sub_lt hWs hWr)
  have hP : P.degree < k := degree_sub_lt hWr (scale _ _ hQ)
  have hpr : pencil P Q r = Wr := by simp [pencil, P]
  have hps : pencil P Q s = Ws := by
    have hc : (C s - C r : (Polynomial K)) * C ((s-r)⁻¹) = 1 := by
      rw [← map_sub, ← map_mul, mul_inv_cancel₀ (sub_ne_zero.mpr hrs.symm), map_one]
    calc
      pencil P Q s = Wr + ((C s - C r) * C ((s-r)⁻¹)) * (Ws-Wr) := by
        simp only [pencil, P, Q]
        ring
      _ = Ws := by rw [hc, one_mul, add_comm, sub_add_cancel]
  let D' := D.subtract P Q hP hQ
  have hd (z : K) (hz : z ∈ Γ) (h : pencil P Q z = (M z hz).decoder) : D'.Q z z = 0 := by
    change D.Q z z - D.cross z z (pencil P Q z) (pencil P Q z) = 0
    rw [h, D.decoder_identity z _ _ (M z hz).agreement (M z hz).degree (M z hz).hits, sub_self]
  have hzero := D'.zero_of_diagonal_zeros hrs hrA hsA (hd r hrΓ hpr) (hd s hsΓ hps)
  refine ⟨P, Q, hP, hQ, fun z hz => sub_eq_zero.mp ?_⟩
  let W := M z hz
  change W.decoder - pencil P Q z = 0
  apply D'.decoder_zero hzero z W.support _ W.agreement (degree_sub_lt W.degree (pencil_degree hP hQ z))
  intro i hi
  rw [fold_residual, eval_sub, W.hits i hi]
  rfl
end
end Front6969_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
namespace Front6969_2
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open Front6969 (Words k agreement t amplitudeDegree)
open K1_9 (K I node pencil CoefficientIdentities)
open P0_5 (coefficientsAt pow_eq_twist threeUAt_native relationOnAt_native)
private theorem coefficients {u : Words} {T : Front6969.TwoActive u} {R : Front6969.Relation T}
    {D : Front6969.Reduction u T R} (B : Front6969.RankThree u T R D) (hp : Front6969.Parallel B)
    (i : I) (hi : i ∉ Front6969.fixedNodes R) :
    CoefficientIdentities u B.a B.b B.α B.output i := by
  have hnodes : P0_5.relationOnAt P0.p u (Front6969.fixedNodes R) (P0_5.threeUAt P0.p B.a B.β)
      (P0.threeV B.b B.α) B.output := by
    rw [threeUAt_native, relationOnAt_native]
    exact B.nodes
  exact coefficientsAt P0.p (by decide) pow_eq_twist u (Front6969.fixedNodes R)
    B.a B.b B.α B.β B.output hp hnodes i hi
private theorem polarData_of_parallel {u : Words} {T : Front6969.TwoActive u} {R : Front6969.Relation T}
    {D : Front6969.Reduction u T R} (B : Front6969.RankThree u T R D)
    (hu : Front6969.FrontRemainder u) (hp : Front6969.Parallel B) (hn : ¬ Front6969.UnitNorm B) :
    Nonempty (PolarData u) := by
  have hh : D.height + (Front6969.fixedNodes R).card ≤ heightBound := by
    rw [D.height_eq]
    exact (Front6969.relation_height_le hu T).trans (by decide)
  have hfirst := (congrArg (fun A : Fin 2 → (Polynomial K) =>
    B.a.natDegree + amplitudeDegree (A 0) (A 1) ≤ D.height) hp).mpr B.first_degree
  exact polarData_of_set (Front6969.fixedNodes R) D.height B.a B.b B.α B.output hh
    B.output_degree hfirst B.second_degree B.a_ne hn B.α_primitive (coefficients B hp)
private theorem pencil_count {u : Words} (Γ : Finset K)
    (M : ∀ z ∈ Γ, Front6969.BadMark u z) {P Q : (Polynomial K)} (hP : P.degree < k)
    (hQ : Q.degree < k) (h : ∀ z (hz : z ∈ Γ), (M z hz).decoder = pencil P Q z) :
    Γ.card ≤ t + 1 := by
  classical
  by_cases hΓ : Γ.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hΓ]
  obtain ⟨r, hr⟩ := hΓ
  let S := (M r hr).support
  let nonjoint (i : I) := P.eval (node i) ≠ u 0 i ∨ Q.eval (node i) ≠ u 1 i
  have hits {z : K} (hz : z ∈ Γ) {i : I} (hi : i ∈ (M z hz).support) :
      P.eval (node i) + z * Q.eval (node i) = u 0 i + z * u 1 i := by
    simpa only [h z hz, pencil, eval_add, eval_mul, eval_C] using (M z hz).hits i hi
  have unique {z t : K} (hz : z ∈ Γ) (ht : t ∈ Γ) {i : I}
      (hi : i ∈ (M z hz).support) (hj : i ∈ (M t ht).support) (hn : nonjoint i) : z = t := by
    by_contra hne
    have h₁ := hits hz hi
    have h₂ := hits ht hj
    have hw : (z-t) * (Q.eval (node i) - u 1 i) = 0 := by linear_combination h₁ - h₂
    have he := sub_eq_zero.mp ((mul_eq_zero.mp hw).resolve_left (sub_ne_zero.mpr hne))
    rw [he, add_right_cancel_iff] at h₁
    exact hn.elim (fun hbad => hbad h₁) (fun hbad => hbad he)
  have witness (z : ↥(Γ.erase r)) :
      ∃ i ∈ (M z.val (Finset.mem_erase.mp z.property).2).support, nonjoint i := by
    let W := M z.val (Finset.mem_erase.mp z.property).2
    by_contra hw
    apply W.nonjoint
    refine ⟨⟨P, hP, ?_⟩, ⟨Q, hQ, ?_⟩⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inl hn⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inr hn⟩
  choose f hf hn using witness
  let g : ↥(Γ.erase r) → ↥((Finset.univ : Finset I) \ S) := fun z =>
    ⟨f z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hi =>
      (Finset.mem_erase.mp z.property).1 (unique (Finset.mem_erase.mp z.property).2 hr (hf z) hi (hn z))⟩⟩
  have hg : Function.Injective g := by
    intro z t hzt
    have he : f z = f t := congrArg Subtype.val hzt
    apply Subtype.ext
    have ht := hf t
    rw [← he] at ht
    exact unique (Finset.mem_erase.mp z.property).2 (Finset.mem_erase.mp t.property).2 (hf z) ht (hn z)
  have hcard := Finset.card_le_card_of_injective hg
  have he := Finset.card_erase_add_one hr
  have hS : agreement ≤ S.card := (M r hr).agreement
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, IRSProfile.card_index] at hcard
  change 179740 ≤ S.card at hS
  change Γ.card ≤ 82405
  omega
theorem proof : Front6969.c2 := by
  intro u hu T R D B _ hp hn Γ hΓ _
  classical
  obtain ⟨data⟩ := polarData_of_parallel B hu hp hn
  let M (z : K) (hz : z ∈ Γ) := Classical.choice (Front6969.bad_mark u Γ hΓ z hz)
  rcases pencil_of_marks data Γ M with
    hsmall | ⟨P, Q, hP, hQ, h⟩
  · exact hsmall.trans (by decide)
  · exact pencil_count Γ M hP hQ h
end
end Front6969_2
end

end Merged_Front6969Rank2

end Merged_Front6969Rank2
end Z6969Source2220

-- Source: ProximityPrize.SubmissionLower.ProfileBanks
section Z6969Source2221
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 900000

namespace Research6969.ProfileBanks

open scoped BigOperators

abbrev sourceCutoff := 4 * Profile.agreement - 1
abbrev weightedCutoff := sourceCutoff

namespace RankThree

open P0 (blockLength k)
open P1_3 (Bank jet_quotient cutDegree)
open P0_6 (sum_rows ceil_sq_div_eq)

def quotientSurplus (bank : Bank) (n h : ℕ) : Prop :=
  n * (K1_10.jetDim 4 bank.first bank.second -
      K1_10.jetDim 3 (bank.first - 1) (bank.second - 1)) <
    K1_10.sourceDim sourceCutoff 5 bank.first bank.second -
      K1_10.sourceDim (sourceCutoff - (k - 1) - h) 4
        (bank.first - 1) (bank.second - 1)
private theorem source_st : K1_10.sourceDim sourceCutoff 5 20 17 = 1978211746 := by
  let rows : Fin 6 → ℕ := ![812343315, 547409400, 338756966, 183431124, 77952701, 18318240]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 6, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 1978211746 := by decide
private theorem source_ts : K1_10.sourceDim sourceCutoff 5 17 20 = 1978211746 := by
  let rows : Fin 6 → ℕ := ![823069800, 548363475, 335229632, 179140530, 75044144, 17364165]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 6, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 1978211746 := by decide
private theorem multiple_st : K1_10.sourceDim 563554 4 19 16 = 991135446 := by
  let rows : Fin 5 → ℕ := ![478333700, 290315440, 151894044, 59910550, 10681712]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 5, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 991135446 := by decide
private theorem multiple_ts : K1_10.sourceDim 563554 4 16 19 = 991135446 := by
  let rows : Fin 5 → ℕ := ![483443960, 289764640, 149574540, 58141846, 10210460]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 5, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 991135446 := by decide
private theorem source_corner (bank : Bank) :
    K1_10.sourceDim sourceCutoff 5 bank.first bank.second = 1978211746 := by
  cases bank
  · exact source_st
  · exact source_ts
private theorem multiple_corner (bank : Bank) :
    K1_10.sourceDim 563554 4 (bank.first - 1) (bank.second - 1) = 991135446 := by
  cases bank
  · exact multiple_st
  · exact multiple_ts
theorem minimum_surplus (bank : Bank) :
    K1_10.sourceDim sourceCutoff 5 bank.first bank.second -
      K1_10.sourceDim 563554 4 (bank.first - 1) (bank.second - 1) =
      blockLength * 3765 + 104140 := by
  rw [source_corner, multiple_corner]
  decide
theorem rank_three_bank_surplus (bank : Bank) (n h : ℕ) (hn : n ≤ blockLength) (hh : 24334 ≤ h) :
    quotientSurplus bank n h := by
  let s := bank.first - 1
  let t := bank.second - 1
  have hm : K1_10.sourceDim (sourceCutoff - (k - 1) - h) 4 s t ≤
      K1_10.sourceDim 563554 4 s t := by
    have hcut : sourceCutoff - (k - 1) - 24334 = 563554 := by decide
    rw [← hcut]
    unfold K1_10.sourceDim
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.sub_le_sub_right (Nat.add_le_add_right (Nat.sub_le_sub_left hh _) _) _))
  unfold quotientSurplus
  rw [jet_quotient]
  have hd := minimum_surplus bank
  have hs : n * 3765 ≤ blockLength * 3765 := Nat.mul_le_mul_right _ hn
  calc
    n * 3765 ≤ blockLength * 3765 := hs
    _ < blockLength * 3765 + 104140 := Nat.lt_add_of_pos_right (by decide)
    _ = _ := hd.symm
    _ ≤ _ := Nat.sub_le_sub_left hm _
def incidenceRatio : ℚ :=
  (((blockLength - (k - 1)) * cutDegree : ℕ) : ℚ) / ((Profile.agreement - (k - 1) : ℕ) : ℚ)

def regularPrice : ℕ := ⌈((210 : ℕ) : ℚ) * incidenceRatio ^ 2⌉₊

theorem regularPrice_exact : regularPrice = 175945687340321989 := by
  unfold regularPrice incidenceRatio
  exact ceil_sq_div_eq 0x147ffafff86 48669 210 175945687340321989
    (by decide) (by decide) (by decide) (by decide)

theorem bank_price_le (bank : Bank) :
    regularPrice + bank.graphFee ≤ 250000000000000000 := by
  rw [regularPrice_exact]
  cases bank <;> decide


end RankThree

namespace RankFour

open P0 (blockLength)
open P2_4 (Bank)
abbrev heightCap := Profile.heightCap

def originalFloor : Bank → ℕ
  | .w12 | .w21 | .w22 | .w22Swapped => 24334
  | _ => 32446

open K1_11 (V J)
open P0_7 (countRow gradeRow count grade contactRow V_affine rational_fee)
open P1_4 (dims_5_16_10 dims_4_15_8 jets_4_16_10 jets_3_15_8 dims_5_8_7 dims_4_7_4 jets_4_8_7 jets_3_7_4 dims_5_10_16 dims_4_8_15 jets_4_10_16 jets_3_8_15 dims_5_11_10 dims_4_9_8 jets_4_11_10 jets_3_9_8 dims_5_8_6 dims_4_6_3 jets_4_8_6 jets_3_6_3 dims_5_7_8 dims_4_4_7 jets_4_7_8 jets_3_4_7 dims_5_6_8 dims_4_3_6 jets_4_6_8 jets_3_3_6 dims_4_3_5 jets_3_3_5)
open P2_4 (dims_5_10_11 jets_4_10_11 dims_4_8_9 jets_3_8_9 dims_4_5_3 jets_3_5_3)
private theorem surplus_of_stats (h H e N lo s t ds dt c g c' g' j : ℕ)
    (hlo : lo ≤ h) (hmax : h ≤ 33735) (hH : H + e = h) (hN : N + e = 262144)
    (hc : count 5 s t = c) (hg : grade 5 s t = g)
    (hc' : count 4 (s-ds) (t-dt) = c') (hg' : grade 4 (s-ds) (t-dt) = g')
    (hj : J 4 s t - J 3 (s-ds) (t-dt) = j) (hgain : c' ≤ j)
    (hmargin : 262144 * j + (587889 - lo) * c' + 131071 * g <
      718960 * c + 131071 * g') :
    N * (J 4 s t - J 3 (s-ds) (t-dt)) + V (718959 - 131071 - H) 131071 4 (s-ds) (t-dt)
      < V 718959 131071 5 s t := by
  have hv := V_affine 718959 131071 5 s t (by decide)
  have hv' := V_affine (718959 - 131071 - H) 131071 4 (s-ds) (t-dt) (by omega)
  rw [hc, hg] at hv
  rw [hc', hg'] at hv'
  have hw : 718959 - 131071 - H + 1 ≤ (587889 - lo) + e := by omega
  have hm : N * j + (718959 - 131071 - H + 1) * c' ≤
      262144 * j + (587889 - lo) * c' := by
    calc
      _ ≤ N * j + ((587889 - lo) + e) * c' :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hw) _
      _ = N * j + e * c' + (587889 - lo) * c' := by ring
      _ ≤ N * j + e * j + (587889 - lo) * c' :=
        Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ hgain) _) _
      _ = _ := by rw [← Nat.add_mul, hN]
  rw [hj]
  omega
theorem rank_four_bank_surplus (b : Bank) (h H e N : ℕ) (hlo : originalFloor b ≤ h)
    (hmax : h ≤ heightCap) (hH : H + e = h) (hN : N + e = blockLength) :
    N * (J 4 b.s b.t - J 3 (b.s - b.dS) (b.t - b.dT)) +
      V (weightedCutoff - 131071 - H) 131071 4 (b.s - b.dS) (b.t - b.dT) <
      V weightedCutoff 131071 5 b.s b.t := by
  cases b with
  | w12 =>
    exact surplus_of_stats h H e N 24334 16 10 1 2 2982 9324 1675 4189 2010
      hlo hmax hH hN dims_5_16_10.1 dims_5_16_10.2 dims_4_15_8.1 dims_4_15_8.2
      (by rw [jets_4_16_10, jets_3_15_8]) (by decide) (by decide)
  | w13 =>
    exact surplus_of_stats h H e N 32446 8 7 1 3 952 2814 355 809 855
      hlo hmax hH hN dims_5_8_7.1 dims_5_8_7.2 dims_4_7_4.1 dims_4_7_4.2
      (by rw [jets_4_8_7, jets_3_7_4]) (by decide) (by decide)
  | w21 =>
    exact surplus_of_stats h H e N 24334 10 16 2 1 2982 9324 1675 4189 2010
      hlo hmax hH hN dims_5_10_16.1 dims_5_10_16.2 dims_4_8_15.1 dims_4_8_15.2
      (by rw [jets_4_10_16, jets_3_8_15]) (by decide) (by decide)
  | w22 =>
    exact surplus_of_stats h H e N 24334 11 10 2 2 2002 6174 985 2419 1495
      hlo hmax hH hN dims_5_11_10.1 dims_5_11_10.2 dims_4_9_8.1 dims_4_9_8.2
      (by rw [jets_4_11_10, jets_3_9_8]) (by decide) (by decide)
  | w22Swapped =>
    exact surplus_of_stats h H e N 24334 10 11 2 2 2002 6174 985 2419 1495
      hlo hmax hH hN dims_5_10_11.1 dims_5_10_11.2 dims_4_8_9.1 dims_4_8_9.2
      (by rw [jets_4_10_11, jets_3_8_9]) (by decide) (by decide)
  | w23 =>
    exact surplus_of_stats h H e N 32446 8 6 2 3 798 2324 215 459 800
      hlo hmax hH hN dims_5_8_6.1 dims_5_8_6.2 dims_4_6_3.1 dims_4_6_3.2
      (by rw [jets_4_8_6, jets_3_6_3]) (by decide) (by decide)
  | w31 =>
    exact surplus_of_stats h H e N 32446 7 8 3 1 952 2814 355 809 855
      hlo hmax hH hN dims_5_7_8.1 dims_5_7_8.2 dims_4_4_7.1 dims_4_4_7.2
      (by rw [jets_4_7_8, jets_3_4_7]) (by decide) (by decide)
  | w32 =>
    exact surplus_of_stats h H e N 32446 6 8 3 2 798 2324 215 459 800
      hlo hmax hH hN dims_5_6_8.1 dims_5_6_8.2 dims_4_3_6.1 dims_4_3_6.2
      (by rw [jets_4_6_8, jets_3_3_6]) (by decide) (by decide)
  | w33 =>
    exact surplus_of_stats h H e N 32446 6 8 3 3 798 2324 175 364 835
      hlo hmax hH hN dims_5_6_8.1 dims_5_6_8.2 dims_4_3_5.1 dims_4_3_5.2
      (by rw [jets_4_6_8, jets_3_3_5]) (by decide) (by decide)
  | w33Swapped =>
    exact surplus_of_stats h H e N 32446 8 6 3 3 798 2324 175 364 835
      hlo hmax hH hN dims_5_8_6.1 dims_5_8_6.2 dims_4_5_3.1 dims_4_5_3.2
      (by rw [jets_4_8_6, jets_3_5_3]) (by decide) (by decide)
def chartRate (b : Bank) : ℚ := (131073 / 48669 : ℚ) * b.M
def chartFee (b : Bank) : ℚ := b.E * chartRate b ^ 2
abbrev tariff : ℕ := 250000000000000000
private theorem priced (E M zeroFee cap : ℕ)
    (h : zeroFee * 48669^2 + 5 * E * (131073*M)^2 ≤ cap * 48669^2)
    (hc : cap ≤ tariff) :
    (zeroFee : ℚ) + 5 * ((E : ℚ) * ((131073 / 48669 : ℚ) * M)^2) ≤ tariff :=
  (rational_fee E M zeroFee cap 131073 48669 (by decide) h).trans (by exact_mod_cast hc)
local notation "fee!" e "," m "," z "," c => priced e m z c (by decide) (by decide)
theorem bank_fee (b : Bank) : (b.zeroFee : ℚ) + 5 * chartFee b ≤ tariff := by
  cases b with
  | w12 => exact fee! 36, 9174936, 0x771000024, 250000000000000000
  | w21 => exact fee! 36, 9174936, 0x7f0000024, 250000000000000000
  | w22Swapped => exact fee! 36, 9174936, 0x7f0000024, 250000000000000000
  | w13 => exact fee! 30, 7602090, 0x86f00001e, 250000000000000000
  | w31 => exact fee! 30, 7602090, 0x3f800001e, 250000000000000000
  | w23 => exact fee! 34, 8650654, 0x7f0000022, 250000000000000000
  | w32 => exact fee! 34, 8650654, 0x673000022, 250000000000000000
  | w33 => exact fee! 39, 9961359, 0x8ee000027, 250000000000000000
  | w22 => exact fee! 36, 9174936, 0x771000024, 250000000000000000
  | w33Swapped => exact fee! 39, 9961359, 0x7f0000027, 250000000000000000

theorem bank_rate_ge (b : Bank) : (262144 : ℚ) ≤ chartRate b := by
  have hm : (262144 : ℕ) ≤ b.M := by cases b <;> decide
  have hr : (1 : ℚ) ≤ 131073 / 48669 := by
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 48669)).mpr
    rw [one_mul]
    exact_mod_cast (show (48669 : ℕ) ≤ 131073 by decide)
  exact (by exact_mod_cast hm : (262144 : ℚ) ≤ b.M).trans
    (by simpa only [one_mul, chartRate] using
      mul_le_mul_of_nonneg_right hr (by positivity : (0 : ℚ) ≤ b.M))


end RankFour
end Research6969.ProfileBanks
end Z6969Source2221

-- Source: ProximityPrize.SubmissionLower.ProfileFrontRankThree
section Z6969Source2222
set_option autoImplicit true
set_option Elab.async false
set_option autoImplicit true
section
namespace Front6969_3
noncomputable section
open Front6969 Polynomial
open P1_3 (Bank cutDegree)
def leftCoeff {u T R D} (B : RankThree u T R D) (l : Fin 2) : (Polynomial K) :=
  B.a * (B.β l).map twist
def rightCoeff {u T R D} (B : RankThree u T R D) (j : Fin 2) : (Polynomial K) :=
  -(B.b * B.α j)
abbrev sourceCutoff : ℕ := 4 * agreement - 1
def quotientSurplus (bank : Bank) (n h : ℕ) : Prop :=
  n * (K1_10.jetDim 4 bank.first bank.second -
      K1_10.jetDim 3 (bank.first - 1) (bank.second - 1)) <
    K1_10.sourceDim sourceCutoff 5 bank.first bank.second -
      K1_10.sourceDim (sourceCutoff - (k - 1) - h) 4
        (bank.first - 1) (bank.second - 1)
def incidenceRatio : ℚ :=
  (((blockLength - (k - 1)) * cutDegree : ℕ) : ℚ) / ((agreement - (k - 1) : ℕ) : ℚ)
def regularPrice : ℕ := ⌈((210 : ℕ) : ℚ) * incidenceRatio ^ 2⌉₊
end
end Front6969_3
end
section
namespace Front6969_3
noncomputable section
open Front6969 Polynomial ProximityPrize.Benchmark FrobeniusLocator
open P1_3 (Adjugate Plane)
open P0_6 (amp_le primitive_lift contraction_degree)
theorem adjugate_of_plane {u : Words} {T : TwoActive u} {R : Relation T} {D : Reduction u T R}
    (B : RankThree u T R D) (hnp : Nonparallel B)
    (W : Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B))
    (hroom : k + 3 * D.height + (fixedNodes R).card ≤ blockLength) :
    Nonempty (Adjugate u (fixedNodes R) D.height) := by
  change 131072 + 3 * D.height + (fixedNodes R).card ≤ 262144 at hroom
  let A := B.α
  let V := fun j => (B.β j).map twist
  let s := amplitudeDegree (A 0) (A 1)
  let t := amplitudeDegree (V 0) (V 1)
  have htw (P : (Polynomial K)) : (P.map twist).natDegree = P.natDegree :=
    natDegree_map_eq_of_injective twist.injective _
  have ht : t = amplitudeDegree (B.β 0) (B.β 1) := by simp only [t, V, amplitudeDegree, htw]
  have ha : B.a.natDegree + t ≤ D.height := ht ▸ B.first_degree
  have hb : B.b.natDegree + s ≤ D.height := B.second_degree
  have hv : IsCoprime (V 0) (V 1) := B.β_primitive.map (mapRingHom twist)
  have hout (j l : Fin 2) : (W.output j l).natDegree < 131072 + D.height := by
    by_cases hz : W.output j l = 0
    · simp [hz]
    · exact (natDegree_lt_iff_degree_lt hz).mpr (W.output_degree j l)
  let L := fun l => A 0 * W.output 1 l - A 1 * W.output 0 l
  let N := fun j => V 1 * W.output j 0 - V 0 * W.output j 1
  let w := fun i => B.a.eval (node i) * ((A 0).eval (node i) * u 1 i - (A 1).eval (node i) * u 0 i)
  let z := fun i => B.b.eval (node i) * ((V 0).eval (node i) * (u 1 i)^p - (V 1).eval (node i) * (u 0 i)^p)
  have hn (i : I) (hi : i ∉ fixedNodes R) (j l : Fin 2) :
      (W.output j l).eval (node i) =
        B.a.eval (node i) * (V l).eval (node i) * u j i -
        B.b.eval (node i) * (A j).eval (node i) * (u l i)^p := by
    rw [← W.nodes i hi]
    simp only [leftCoeff, rightCoeff, eval_mul, eval_neg, A, V]
    ring
  obtain ⟨P, hP, heP⟩ := primitive_lift (fixedNodes R) V L w (131072 + D.height + s) hv
    (fun l => contraction_degree (amp_le A 0) (amp_le A 1) (hout 1 l) (hout 0 l))
    (by intro i hi j; simp only [L, w, eval_sub, eval_mul, hn i hi]; ring)
    (by change t < _; omega) (by change _ + t + _ ≤ _; omega)
  obtain ⟨Q, hQ, heQ⟩ := primitive_lift (fixedNodes R) A N z (131072 + D.height + t) B.α_primitive
    (fun j => contraction_degree (amp_le V 1) (amp_le V 0) (hout j 0) (hout j 1))
    (by intro i hi j; simp only [N, z, eval_sub, eval_mul, hn i hi]; ring)
    (by change s < _; omega) (by change _ + s + _ ≤ _; omega)
  change P.natDegree + t < 131072 + D.height + s at hP
  change Q.natDegree + s < 131072 + D.height + t at hQ
  let σ := RingEquiv.ofBijective twist ⟨twist.injective, Finite.surjective_of_injective twist.injective⟩
  let τ := σ.symm.toRingHom
  have hundo (x : K) : τ (twist x) = x := σ.symm_apply_apply x
  have hfixed (i : I) : τ (node i) = node i := by
    have hh : twist (node i) = node i := Native.native_domain_fixed i
    simpa only [hh] using hundo (node i)
  have hmap (F : (Polynomial K)) (i : I) : (F.map τ).eval (node i) = τ (F.eval (node i)) :=
    Strata.eval_coefficient_map τ _ _ (hfixed i)
  have hβ (l : Fin 2) (i : I) : (V l).eval (node i) = twist ((B.β l).eval (node i)) :=
    Strata.eval_coefficient_map twist _ _ (Native.native_domain_fixed i)
  let b := B.b.map τ
  let Q' := Q.map τ
  have heQ' (i : I) (hi : i ∉ fixedNodes R) : Q'.eval (node i) = b.eval (node i) *
      ((B.β 0).eval (node i) * u 1 i - (B.β 1).eval (node i) * u 0 i) := by
    rw [show Q'.eval (node i) = τ (Q.eval (node i)) from hmap Q i, heQ i hi]
    change τ (B.b.eval (node i) * ((V 0).eval (node i) * twist (u 1 i) -
      (V 1).eval (node i) * twist (u 0 i))) = _
    simp only [b, hmap, hβ, map_mul, map_sub, hundo]
  let det := A 0 * B.β 1 - A 1 * B.β 0
  let denom := B.a * b * det
  let num := fun j => b * B.β j * P - B.a * A j * Q'
  have hb' : b.natDegree = B.b.natDegree := natDegree_map_eq_of_injective τ.injective _
  have hQ' : Q'.natDegree = Q.natDegree := natDegree_map_eq_of_injective τ.injective _
  have hvdeg (j : Fin 2) : (B.β j).natDegree ≤ t := ht ▸ amp_le B.β j
  have hadeg (j : Fin 2) : (A j).natDegree ≤ s := amp_le A j
  have ddet : det.natDegree ≤ s + t := (natDegree_sub_le _ _).trans (max_le
    (natDegree_mul_le.trans (Nat.add_le_add (hadeg 0) (hvdeg 1)))
    (natDegree_mul_le.trans (Nat.add_le_add (hadeg 1) (hvdeg 0))))
  refine ⟨⟨denom, mul_ne_zero (mul_ne_zero B.a_ne ((Polynomial.map_ne_zero_iff τ.injective).mpr B.b_ne)) hnp,
    ?_, num, ?_, ?_⟩⟩
  · calc
      denom.natDegree ≤ B.a.natDegree + b.natDegree + det.natDegree :=
        natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)
      _ ≤ 2 * D.height := by omega
  · intro j
    apply degree_le_natDegree.trans_lt
    exact_mod_cast (show (num j).natDegree < 131072 + 2 * D.height from by
      apply (natDegree_sub_le _ _).trans_lt
      apply max_lt
      · have := hvdeg j
        exact (natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)).trans_lt (by omega)
      · have := hadeg j
        exact (natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)).trans_lt (by omega))
  · intro i hi j
    fin_cases j
    · change denom.eval (node i) * u 0 i = (num 0).eval (node i)
      simp only [denom, num, det, eval_mul, eval_sub, heP i hi, heQ' i hi, w]
      ring
    · change denom.eval (node i) * u 1 i = (num 1).eval (node i)
      simp only [denom, num, det, eval_mul, eval_sub, heP i hi, heQ' i hi, w]
      ring
end
end Front6969_3
end
section
namespace Front6969_3
noncomputable section
open Front6969
open P1_3 (Bank)
open scoped BigOperators
open P1_3 (jet_quotient)
open P0_6 (sum_rows ceil_sq_div_eq)
theorem bank_surplus (bank : Bank) (n h : ℕ) (hn : n ≤ blockLength) (hh : 24334 ≤ h) :
    quotientSurplus bank n h :=
  Research6969.ProfileBanks.RankThree.rank_three_bank_surplus bank n h hn hh

theorem bank_price_le (bank : Bank) :
    regularPrice + bank.graphFee ≤ 250000000000000000 :=
  Research6969.ProfileBanks.RankThree.bank_price_le bank
end
end Front6969_3
end
section
namespace Front6969_3
noncomputable section
open Front6969 FrobeniusLocator ProximityPrize.Benchmark Polynomial
open P1_3 (Adjugate)
open P0_6 (natDegree_lt_of_degree_lt_pos)
theorem mark_disjoint {u : Words} {T : TwoActive u} {R : Relation T} (D : Reduction u T R)
    {γ : K} (hn : Normal u γ) (M : BadMark u γ) :
    Disjoint M.support (fixedNodes R) := by
  apply Finset.disjoint_left.mpr
  intro i hi hfix
  exact D.deleted_error γ hn M i hfix (M.hits i hi)
theorem no_small_normal {u : Words} (T : TwoActive u) {R : Relation T}
    (D : Reduction u T R) (J : Adjugate u (fixedNodes R) D.height)
    (hsmall : 2 * D.height < Front6969.L) {γ : K} (hn : Normal u γ) (M : BadMark u γ) : False := by
  classical
  let F := J.numer 0 + C γ * J.numer 1 - J.denom * M.decoder
  have hfit : Front6969.k + 2 * D.height < Front6969.agreement := by
    have hsum : Front6969.k + Front6969.L = Front6969.agreement := by decide
    omega
  have hdeg : F.natDegree < Front6969.agreement := by
    have hj (j : Fin 2) : (J.numer j).natDegree < Front6969.k + 2 * D.height :=
      natDegree_lt_of_degree_lt_pos (by
        have hk : 0 < Front6969.k := by decide
        omega) (J.numer_degree j)
    have hP : M.decoder.natDegree < Front6969.k := natDegree_lt_of_degree_lt_pos (by decide) M.degree
    have hnum := (natDegree_add_le (J.numer 0) (C γ * J.numer 1)).trans
      (max_le_max_left _ (natDegree_C_mul_le γ (J.numer 1)))
    have hprod := natDegree_mul_le (p := J.denom) (q := M.decoder)
    have hsub := natDegree_sub_le (J.numer 0 + C γ * J.numer 1) (J.denom * M.decoder)
    change (J.numer 0 + C γ * J.numer 1 - J.denom * M.decoder).natDegree < Front6969.agreement
    have := J.denom_degree
    apply hsub.trans_lt
    apply max_lt
    · exact hnum.trans_lt (max_lt (by have := hj 0; omega) (by have := hj 1; omega))
    · exact hprod.trans_lt (by omega)
  have hF : F = 0 := by
    by_contra hf
    have hroot := Strata.root_nodes_card_le node IRSProfile.domain.injective F hf M.support
      (by
        intro i hi
        have hd : i ∉ fixedNodes R := fun h => (Finset.disjoint_left.mp (mark_disjoint D hn M)) hi h
        simp only [F, eval_sub, eval_add, eval_mul, eval_C, ← J.nodes i hd, M.hits i hi]
        ring)
    have := M.agreement
    omega
  let zeros := Finset.univ.filter (fun i : I => J.denom.eval (node i) = 0)
  let E := fixedNodes R ∪ zeros
  have hZ : zeros.card ≤ J.denom.natDegree := Strata.root_nodes_card_le node
    IRSProfile.domain.injective _ J.nonzero zeros (fun _ hi => (Finset.mem_filter.mp hi).2)
  have hE : E.card ≤ (fixedNodes R).card + 2 * D.height := (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (hZ.trans J.denom_degree) _)
  have hoff (i : I) (hi : i ∉ E) : u 0 i + γ * u 1 i = M.decoder.eval (node i) := by
    have hd : i ∉ fixedNodes R := fun h => hi (Finset.mem_union_left _ h)
    have hz : J.denom.eval (node i) ≠ 0 :=
      fun h => hi (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have hf : F.eval (node i) = 0 := by rw [hF, eval_zero]
    simp only [F, eval_sub, eval_add, eval_mul, eval_C, ← J.nodes i hd] at hf
    apply mul_left_cancel₀ hz
    linear_combination hf
  have hbal := relation_height_balance T
  have hheight := D.height_eq
  have hs := actual_stackRank u
  have hcard : Front6969.k + Front6969.L + Front6969.t ≤ Fintype.card I := by
    rw [IRSProfile.card_index]
    decide
  have hfix (b : Fin 2) (i : I) : iterateFrobenius K p b.val (node i) = node i := by
    fin_cases b
    · exact iterateFrobenius_zero_apply K p _
    · exact (iterateFrobenius_one_apply K p _).trans (Native.native_domain_fixed i)
  change ((stacked p node (u 0) (u 1) Front6969.L Front6969.t).map (evalRingHom γ)).rank = stackRank u at hn
  rw [Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval,
    Strata.conjugateHankel_error_rank _ node _ IRSProfile.domain.injective hfix M.decoder
      Front6969.k Front6969.L Front6969.t M.degree hcard E (by omega) hoff] at hn
  have hr := Matrix.rank_le_card_width (Strata.conjugateErrors
    (fun b : Fin 2 => iterateFrobenius K p b.val) (fun i : E => node i.val)
    (fun i : E => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)) Front6969.L)
  rw [Fintype.card_coe, hn] at hr
  have hsize : 2 * D.height + (fixedNodes R).card < stackRank u := by
    omega
  omega
end
end Front6969_3
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace Front6969_3
noncomputable section
open Front6969 Polynomial FrobeniusLocator
open P1_3 (Plane)
open P0_6 (column column_ne column_bound column_dvd firstColumn_normal threeU_fun tight_pair outputs slice_bound nodes_of_columns relationOn_fun)
private theorem left_eq {u T R D} (B : RankThree u T R D) :
    threeU B.a B.β = column p (leftCoeff B) := by
  rw [threeU_fun]
  exact (firstColumn_normal p B.a B.β).trans (congrArg (column p)
    (show (fun j => B.a * (B.β j).map twist) = leftCoeff B by rfl))
private theorem right_eq {u T R D} (B : RankThree u T R D) :
    threeV B.b B.α = column 1 (rightCoeff B) := by
  simp only [threeV, rightCoeff, column, liftX, seed, Polynomial.map_mul, Polynomial.map_neg, pow_one]
  ring
theorem plane_of_rankThree {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} (B : RankThree u T R D) :
    Nonempty (Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B)) := by
  let U := leftCoeff B
  let V := rightCoeff B
  have amp_ne (v : Fin 2 → (Polynomial K)) (hv : IsCoprime (v 0) (v 1)) : ∃ j, v j ≠ 0 := by
    by_contra! hz
    obtain ⟨a,b,hab⟩ := hv
    simp [hz] at hab
  obtain ⟨l,hl⟩ := amp_ne B.β B.β_primitive
  obtain ⟨j,hj⟩ := amp_ne B.α B.α_primitive
  have hU : ∃ l, U l ≠ 0 :=
    ⟨l, mul_ne_zero B.a_ne ((Polynomial.map_ne_zero_iff twist.injective).mpr hl)⟩
  have hV : ∃ j, V j ≠ 0 := ⟨j, neg_ne_zero.mpr (mul_ne_zero B.b_ne hj)⟩
  have hu : amplitudeDegree (U 0) (U 1) ≤ D.height := by
    unfold amplitudeDegree
    apply max_le
    all_goals
      apply natDegree_mul_le.trans
      apply le_trans _ B.first_degree
      apply Nat.add_le_add_left
      rw [natDegree_map_eq_of_injective twist.injective]
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hv : amplitudeDegree (V 0) (V 1) ≤ D.height := by
    unfold amplitudeDegree
    apply max_le
    all_goals
      simp only [V, rightCoeff, natDegree_neg]
      apply natDegree_mul_le.trans
      apply le_trans _ B.second_degree
      apply Nat.add_le_add_left
    · exact le_max_left _ _
    · exact le_max_right _ _
  let φ := algebraMap (Polynomial K) Frac
  have hinj : Function.Injective φ := IsFractionRing.injective (Polynomial K) Frac
  have hd (P : Bivar) : (extendSeed P).natDegree = P.natDegree := natDegree_map_eq_of_injective hinj _
  have hn {P : Bivar} (hp : P ≠ 0) : extendSeed P ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hp
  have hdir := B.same_direction
  rw [sameDirection, left_eq, right_eq] at hdir
  have he := congrArg (Polynomial.map φ) hdir
  simp only [Polynomial.map_mul] at he
  have hdom := max_le_max (column_bound p U) (column_bound 1 V)
  obtain ⟨htight,hcp⟩ := tight_pair (extendSeed D.U) (extendSeed D.V)
    (extendSeed (column p U)) (extendSeed (column 1 V))
    (hn D.U_ne) (hn D.V_ne) (hn (column_ne (by decide : p ≠ 0) hU)) D.coprime he
    (by simp only [hd, D.max_degree]; exact hdom.trans (max_le hu hv))
  simp only [hd, D.max_degree] at htight
  refine ⟨⟨outputs p B.output, hU, hV, ?_, ?_, ?_, ?_⟩⟩
  · exact le_antisymm (max_le hu hv) (htight ▸ hdom)
  · intro f hfU hfV
    have hunit := hcp.isUnit_of_dvd'
      ((mapRingHom φ).map_dvd (column_dvd p U f hfU))
      ((mapRingHom φ).map_dvd (column_dvd 1 V f hfV))
    apply isUnit_iff_degree_eq_zero.mpr
    change IsUnit ((f.map Polynomial.C).map φ) at hunit
    simpa only [degree_map_eq_of_injective hinj,
      degree_map_eq_of_injective Polynomial.C_injective] using isUnit_iff_degree_eq_zero.mp hunit
  · intro j l
    apply degree_le_natDegree.trans_lt
    have ht : B.output.natDegree < P0.k + D.height := by
      by_cases hz : B.output = 0
      · simp [hz]
      · exact (natDegree_lt_iff_degree_lt hz).mpr B.output_degree
    exact_mod_cast (slice_bound B.output _).trans_lt ht
  · apply nodes_of_columns p (by decide) u (fixedNodes R) U V B.output
    have h := B.nodes
    rwa [relationOn_fun, left_eq, right_eq] at h
end
end Front6969_3
end
section
namespace Front6969_3
noncomputable section
open Front6969 Polynomial
open P1_3 (Bank Plane ScalarSource)
def c1 : Prop :=
  ∀ bank u deleted h U V, Plane u deleted h U V → 24334 ≤ h →
    h + deleted.card ≤ heightCap → quotientSurplus bank (blockLength - deleted.card) h →
    ∃ A : ScalarSource bank, ∀ γ (M : BadMark u γ), Disjoint M.support deleted →
      A.atDecoder γ M.decoder = 0
def c2 : Prop :=
  ∀ bank u (A : ScalarSource bank) (Γ : Finset K),
    (∀ γ ∈ Γ, A.atLabel γ ≠ 0 ∧ ∃ M : BadMark u γ, A.atDecoder γ M.decoder = 0) →
    Γ.card ≤ regularPrice
private theorem zero_specializations {bank : Bank} (A : ScalarSource bank) (Γ : Finset K)
    (hΓ : ∀ γ ∈ Γ, A.atLabel γ = 0) : Γ.card ≤ bank.graphFee := by
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr A.nonzero
  have hlt : bank.first + 5 < p := by cases bank <;> decide
  apply K1_10.frobenius_coefficient_exception_count p (bank.first + 5) bank.second
    (by decide) (A.poly.coeff e) (MvPolynomial.mem_support_iff.mp he)
    (A.s_degree e he) hlt (A.t_degree e he) Γ
  intro γ hγ
  have hh := congrArg (fun P : MvPolynomial (Fin 2) K => P.coeff e) (hΓ γ hγ)
  simpa only [ScalarSource.atLabel, MvPolynomial.coeff_map,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hh
private theorem count_with_bank (h1 : c1) (h2 : c2) (bank : Bank) : Front6969.c3 := by
  classical
  intro u hu T R D B _hsat hnp Γ hΓ hn
  obtain ⟨W⟩ := plane_of_rankThree B
  have hh : D.height + (fixedNodes R).card ≤ heightCap :=
    D.height_eq ▸ relation_height_le hu T
  by_cases hsmall : 2 * D.height < L
  · have hshort := (shortened_guards D hu).1
    have hcap : heightCap ≤ blockLength := by decide
    have hroom : k + 3 * D.height + (fixedNodes R).card ≤ blockLength := by omega
    obtain ⟨J⟩ := adjugate_of_plane B hnp W hroom
    have hempty : Γ = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro γ hγ
      obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγ
      exact no_small_normal T D J hsmall (hn γ hγ) M)
    simp [hempty]
  have hmin : 24334 ≤ D.height := by
    change ¬ 2 * D.height < 48668 at hsmall
    omega
  obtain ⟨A, hA⟩ := h1 bank u _ D.height _ _ W hmin hh
    (bank_surplus bank _ _ (Nat.sub_le _ _) hmin)
  let good := Γ.filter (fun γ => A.atLabel γ ≠ 0)
  let exc := Γ.filter (fun γ => ¬ A.atLabel γ ≠ 0)
  have hexc : exc.card ≤ bank.graphFee := zero_specializations A exc (by
    intro γ hγ
    exact not_ne_iff.mp (Finset.mem_filter.mp hγ).2)
  have hgood : good.card ≤ regularPrice := h2 bank u A good (by
    intro γ hγ
    obtain ⟨hγΓ, hnonzero⟩ := Finset.mem_filter.mp hγ
    obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγΓ
    exact ⟨hnonzero, M, hA γ M (mark_disjoint D (hn γ hγΓ) M)⟩)
  have hsum : good.card + exc.card = Γ.card :=
    Finset.card_filter_add_card_filter_not (s := Γ) (p := fun γ => A.atLabel γ ≠ 0)
  exact hsum ▸ (Nat.add_le_add hgood hexc).trans (bank_price_le bank)
theorem of_children (h1 : c1) (h2 : c2) : Front6969.c3 :=
  count_with_bank h1 h2 .ts
end
end Front6969_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace Front6969_3_1
noncomputable section
open MvPolynomial K1_11
open K1_10_1 (Contacts relationBounds)
open Front6969_3 (sourceCutoff)
open P1_3_1 (Multipliers)
open P1_3_1 (localMultiply LocalSpace local_finrank)
open P0_6_1 (exists_kernel_outside)
abbrev Source (F : Type*) [Field F] (bank : P1_3.Bank) :=
  filtered (F := F) (sourceWeights 131071) (sourceBounds sourceCutoff 5 bank.first bank.second)
variable {F : Type*} [Field F] {N : ℕ} {L : MvPolynomial (Fin 5) F}
variable (bank : P1_3.Bank) (C : Contacts N L) {h : ℕ}
    (hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = relationBounds h j)
private def nodeMap (i : Fin N) : Source F bank →ₗ[F] LocalSpace bank C hdeg i :=
  (LinearMap.range (localMultiply bank C hdeg i)).mkQ.comp
    (sourceToJet sourceCutoff 131071 5 bank.first bank.second 3 (C.x i) (C.first i) (C.firstSlope i)
      (C.second i) (C.secondSlope i))
include hdeg in
theorem quotientSource (hL : L ≠ 0) (hh : h ≤ 33735) (hs : Front6969_3.quotientSurplus bank N h) :
    ∃ G : Source F bank, ¬ L ∣ G.val ∧ ∀ i, ∃ R : Multipliers F bank,
      C.shifted i G.val - C.shifted i L * R.val ∈ restrictWeightedOrder contactWeight 4 := by
  have hfit : ∀ j, relationBounds h j ≤ sourceBounds sourceCutoff 5 bank.first bank.second j := by
    have hcapacity : 131071 + 33735 ≤ sourceCutoff := by decide
    intro j
    cases bank <;> fin_cases j <;> simp [relationBounds, sourceBounds, P1_3.Bank.first, P1_3.Bank.second] <;> omega
  have hshift : (fun j => sourceBounds sourceCutoff 5 bank.first bank.second j - relationBounds h j) =
      sourceBounds (sourceCutoff - 131071 - h) 4 (bank.first - 1) (bank.second - 1) := by
    funext j
    fin_cases j <;> simp [sourceBounds, relationBounds, Nat.sub_sub]
    omega
  let mult := filteredMul (sourceWeights 131071) (sourceBounds sourceCutoff 5 bank.first bank.second)
    (relationBounds h) L hL hdeg hfit
  have hmult : Module.finrank F (LinearMap.range mult) =
      V (sourceCutoff - 131071 - h) 131071 4 (bank.first - 1) (bank.second - 1) := by
    rw [LinearMap.finrank_range_of_inj (filteredMul_injective _ _ _ L hL hdeg hfit),
      hshift, source_filtered_finrank]
  let (i : Fin N) : Module.Free F (LocalSpace bank C hdeg i) := Module.Free.of_divisionRing F _
  let : Module F (∀ i : Fin N, LocalSpace bank C hdeg i) := Pi.module _ _ _
  have hlocal : Module.finrank F (∀ i : Fin N, LocalSpace bank C hdeg i) =
      N * (J 4 bank.first bank.second - J 3 (bank.first - 1) (bank.second - 1)) := by
    rw [Module.finrank_pi_fintype]
    simp only [local_finrank bank C hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hdim : Module.finrank F (∀ i : Fin N, LocalSpace bank C hdeg i) +
      Module.finrank F (LinearMap.range mult) < Module.finrank F (Source F bank) := by
    rw [hlocal, hmult, source_filtered_finrank]
    change N * (J 4 bank.first bank.second - J 3 (bank.first - 1) (bank.second - 1)) <
      V sourceCutoff 131071 5 bank.first bank.second -
        V (sourceCutoff - 131071 - h) 131071 4 (bank.first - 1) (bank.second - 1) at hs
    omega
  have hk := P0_6_1.exists_kernel_outside (G := ∀ i : Fin N, LocalSpace bank C hdeg i)
    (LinearMap.pi (nodeMap bank C hdeg)) (LinearMap.range mult) hdim
  obtain ⟨G, hG, hnot⟩ := hk
  refine ⟨G, (mem_filteredMul_range_iff _ _ _ L hL hdeg hfit G).not.mp hnot, ?_⟩
  intro i
  have hi : nodeMap bank C hdeg i G = 0 := congrFun hG i
  obtain ⟨R, hR⟩ := (Submodule.Quotient.mk_eq_zero _).mp hi
  refine ⟨R, (weightedTruncation_eq_zero_iff _ _ _).mp ?_⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hR).symm
end
end Front6969_3_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace Front6969_3_1
noncomputable section
open MvPolynomial K1_11
open Front6969 (K I Words node p blockLength agreement twist heightCap BadMark)
open P1_3 (Plane)
open Front6969_3 (sourceCutoff)
open P1_3_1 (toScalarSource toScalarSource_atDecoder)
open K1_10_1 (Contacts denominator numerator planeRelation planeRelation_view relationBounds)
open P0_6_1 (coeff_bounds denominator_ne relation_eval)
open K1_11 (scalar_total_weight_le)
private theorem mark_degree {u : Words} {γ : K} (M : BadMark u γ) :
    M.decoder.natDegree ≤ 131071 := by
  apply Polynomial.natDegree_le_of_degree_le
  exact Order.le_of_lt_succ (show M.decoder.degree < (131072 : ℕ) from M.degree)
private theorem correctOn_mark {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {γ : K} (M : BadMark u γ) :
    correctOn u P M.decoder (M.decoder.map twist) γ (γ ^ p) (indexedSupport P M.support) := by
  intro i hi
  have h := M.hits (P.index i) ((mem_indexedSupport P M.support i).mp hi)
  refine ⟨h, ?_⟩
  change (M.decoder.map twist).eval (node (P.index i)) =
    u 0 (P.index i) ^ p + γ ^ p * u 1 (P.index i) ^ p
  rw [FrobeniusLocator.Strata.eval_coefficient_map twist M.decoder _
    (FrobeniusLocator.Native.native_domain_fixed (P.index i)), h]
  simp only [map_add, map_mul, P0.twist, frobenius_def]
private theorem relation_at_decoder {u : Words} {deleted : Finset I} {h : ℕ}
    {U V : Fin 2 → Polynomial K} (W : Plane u deleted h U V) (P : Puncture deleted)
    (hdeg : (planeRelation U V W.output).weightedTotalDegree (sourceWeights 131071 0) ≤ 131071 + h)
    (hh : h ≤ 33735) (Q Q' : Polynomial K) (hq : Q.natDegree ≤ 131071)
    (hq' : Q'.natDegree ≤ 131071) (s t : K) (S : Finset (Fin P.N)) (hS : agreement ≤ S.card)
    (hc : correctOn u P Q Q' s t S) :
    aeval (decoderImages Q Q' s t) (planeRelation U V W.output) = 0 := by
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 1
  · intro j hj
    rw [pow_one, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, relation_eval]
    have hi : P.index j ∉ deleted := (P.retained _).mp ⟨j, rfl⟩
    have hcj := hc j hj
    change Q.eval (node (P.index j)) = u 0 (P.index j) + s * u 1 (P.index j) ∧
      Q'.eval (node (P.index j)) = u 0 (P.index j) ^ p + t * u 1 (P.index j) ^ p at hcj
    simp only [Puncture.nodes, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, hcj.1, hcj.2]
    linear_combination W.nodes _ hi 0 0 + s * W.nodes _ hi 1 0 +
      t * W.nodes _ hi 0 1 + (s * t) * W.nodes _ hi 1 1
  · have hd := decoder_eval_degree 131071 (131071 + h) _ hdeg Q Q' hq hq' s t
    have hcapacity : 131071 + 33735 < agreement := by decide
    omega
theorem proof : Front6969_3.c1 := by
  intro bank u deleted h U V W _ hh hs
  have hheight : h ≤ 33735 := by
    have hh' : h + deleted.card ≤ heightCap := hh
    change h + deleted.card ≤ 33735 at hh'
    omega
  let P := nativePuncture deleted
  let L := planeRelation U V W.output
  let a := numerator U W.output
  let b := denominator V
  have hb : b ≠ 0 := denominator_ne W.V_ne
  have hview : polynomialView L = Polynomial.C b * Polynomial.X - Polynomial.C a :=
    planeRelation_view U V W.output
  have hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = relationBounds h j :=
    K1_10_1_1.proof u deleted h U V W
  have hl : L ≠ 0 := by
    intro hz
    have hpos := hdeg 1
    simp [hz, relationBounds, weightedTotalDegree] at hpos
  let C : Contacts P.N L :=
    ⟨P.nodes, fun i => u 0 (P.index i), fun i => u 1 (P.index i),
      fun i => u 0 (P.index i) ^ p, fun i => u 1 (P.index i) ^ p,
      fun i => K1_10_1_2.proof u deleted h U V W (P.index i) ((P.retained _).mp ⟨i, rfl⟩)⟩
  have hN : P.N = blockLength - deleted.card := by
    have hsize : P.N + deleted.card = blockLength := P.size
    omega
  obtain ⟨G, hnot, hcontacts⟩ := quotientSource bank C hdeg hl hheight (hN ▸ hs)
  let Q := scalarEliminant 5 G.val a b
  have hne : Q ≠ 0 := scalarEliminant_ne_zero sourceCutoff 131071 5 bank.first bank.second
    G.val L G.property hnot a b hb hview (K1_10_1_3.proof u deleted h U V W)
  have hLsource : L ∈ filtered (sourceWeights 131071) (sourceBounds (131071 + h) 1 1 1) := by
    apply (mem_filtered _ _ _).mpr
    intro j
    rw [hdeg j]
    rfl
  obtain ⟨haY, hbY, haS, hbS, haT, hbT⟩ := coeff_bounds L a b _ hLsource hview hb
  obtain ⟨hY, hS, hT⟩ := polynomialView_source_coefficients
    sourceCutoff 131071 5 bank.first bank.second G.val G.property
  have hy : Q.weightedTotalDegree scalarWeightY ≤ 5 :=
    clearedEval_weight_bound scalarWeightY 5 5 1 1 0 (polynomialView G.val) a b
      (by simpa using hY) haY hbY (by decide)
  have hs' : Q.weightedTotalDegree scalarWeightYS ≤ bank.first + 5 :=
    clearedEval_weight_bound scalarWeightYS 5 bank.first 0 1 1 (polynomialView G.val) a b
      (by simpa using hS) haS hbS (by decide)
  have ht' : Q.weightedTotalDegree scalarWeightT ≤ bank.second :=
    clearedEval_weight_bound scalarWeightT 5 bank.second 1 1 0 (polynomialView G.val) a b
      (by simpa using hT) haT hbT (by decide)
  have htotal : Q.weightedTotalDegree scalarWeightTotal ≤ 42 :=
    (scalar_total_weight_le Q _ _ hs' ht').trans (by cases bank <;> decide)
  refine ⟨toScalarSource Q hne hy hs' ht' htotal, ?_⟩
  intro γ M hdis
  rw [toScalarSource_atDecoder]
  let S := indexedSupport P M.support
  have hS' : agreement ≤ S.card := by
    rw [indexedSupport_card P M.support
      (fun i hi hid => Finset.disjoint_left.mp hdis hi hid)]
    exact M.agreement
  have hd := mark_degree M
  have hd' : (M.decoder.map twist).natDegree ≤ 131071 := Polynomial.natDegree_map_le.trans hd
  have hcorrect := correctOn_mark P M
  have hrel := relation_at_decoder W P (le_of_eq (hdeg 0)) hheight
    _ _ hd hd' γ (γ ^ p) S hS' hcorrect
  apply scalarEliminant_annihilates sourceCutoff 131071 5 bank.first bank.second
    G.val L G.property a b hview M.decoder (M.decoder.map twist) γ (γ ^ p) hrel
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 4
  · intro i hi
    obtain ⟨R, hR⟩ := hcontacts i
    exact decoder_contact_multiplicity 4 _ _ _ _ _ γ (γ ^ p) _ _ G.val L R.val
      (hcorrect i hi).1 (hcorrect i hi).2 hrel hR
  · have hdG := decoder_eval_degree 131071 sourceCutoff G.val
      ((mem_filtered _ _ _).mp G.property 0) _ _ hd hd' γ (γ ^ p)
    have hcut : sourceCutoff < 4 * agreement := by decide
    omega
end
end Front6969_3_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace Front6969_3_2
noncomputable section
open Front6969 Polynomial MvPolynomial ProximityPrize.Benchmark
open P1_3 (cutDegree)
open P1_3_2 (nodeCut_degree)
open Front6969_3 (incidenceRatio)
open K1_10_2 (GenericRow point surface_count_with_terminal RegularRoot
  derivativeOrder toGeneric atTrajectory)
open scoped Polynomial
open P1_3_2 (assign_charts)
open K1_10_2_2 (nodeCut eval_nodeCut)
open K1_10_2 (derivativeOrder_degree eval_toGeneric)
private abbrev Marks (u : Words) (Γ : Finset K) := ∀ γ ∈ Γ, BadMark u γ
private structure TaylorCuts {u : Words} {Γ : Finset K} (F : Marks u Γ) where
  equation : I → GenericRow
  degree : ∀ i, (equation i).totalDegree ≤ cutDegree
  agrees : ∀ γ (hγ : γ ∈ Γ) i,
    MvPolynomial.eval (point γ (F γ hγ).decoder) (equation i) = 0 ↔
      (F γ hγ).decoder.eval (node i) = u 0 i + γ * u 1 i
private theorem pencil_count {u : Words} (Γ : Finset K) (F : Marks u Γ)
    (P Q : (Polynomial K)) (hP : P.degree < 131072) (hQ : Q.degree < 131072)
    (hpencil : ∀ γ (hγ : γ ∈ Γ), (F γ hγ).decoder = P + Polynomial.C γ * Q) :
    Γ.card ≤ 82405 := by
  classical
  rcases Γ.eq_empty_or_nonempty with rfl | ⟨r, hr⟩
  · simp
  let S := (F r hr).support
  let mismatch (i : I) := P.eval (node i) ≠ u 0 i ∨ Q.eval (node i) ≠ u 1 i
  have hits {γ : K} (hγ : γ ∈ Γ) {i : I} (hi : i ∈ (F γ hγ).support) :
      P.eval (node i) + γ * Q.eval (node i) = u 0 i + γ * u 1 i := by
    simpa only [hpencil γ hγ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      using (F γ hγ).hits i hi
  have unique {γ δ : K} (hγ : γ ∈ Γ) (hδ : δ ∈ Γ) {i : I}
      (hi : i ∈ (F γ hγ).support) (hj : i ∈ (F δ hδ).support) (hm : mismatch i) :
      γ = δ := by
    by_contra hne
    have hγi := hits hγ hi
    have hδi := hits hδ hj
    have h := show (γ - δ) * (Q.eval (node i) - u 1 i) = 0 by
      linear_combination hγi - hδi
    have he := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne))
    rw [he, add_right_cancel_iff] at hγi
    exact hm.elim (fun hbad => hbad hγi) (fun hbad => hbad he)
  have witness (γ : ↥(Γ.erase r)) :
      ∃ i ∈ (F γ.val (Finset.mem_erase.mp γ.property).2).support, mismatch i := by
    let M := F γ.val (Finset.mem_erase.mp γ.property).2
    by_contra hw
    apply M.nonjoint
    refine ⟨⟨P, hP, ?_⟩, ⟨Q, hQ, ?_⟩⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inl hn⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inr hn⟩
  choose index hindex hmismatch using witness
  let f : ↥(Γ.erase r) → ↥((Finset.univ : Finset I) \ S) := fun γ =>
    ⟨index γ, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hi =>
      (Finset.mem_erase.mp γ.property).1
        (unique (Finset.mem_erase.mp γ.property).2 hr (hindex γ) hi (hmismatch γ))⟩⟩
  have hf : Function.Injective f := by
    intro γ δ h
    have he : index γ = index δ := congrArg Subtype.val h
    have hδ := hindex δ
    rw [← he] at hδ
    exact Subtype.ext (unique (Finset.mem_erase.mp γ.property).2
      (Finset.mem_erase.mp δ.property).2 (hindex γ) hδ (hmismatch γ))
  have hcard := Finset.card_le_card_of_injective hf
  have he := Finset.card_erase_add_one hr
  have hS : 179740 ≤ S.card := (F r hr).agreement
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    IRSProfile.card_index] at hcard
  omega
private theorem persistent_count {u : Words} {Γ : Finset K} {F : Marks u Γ}
    (C : TaylorCuts F) (J : Ideal GenericRow) (W : Finset K) (hW : W ⊆ Γ)
    (hzero : ∀ γ (hγ : γ ∈ W), point γ (F γ (hW hγ)).decoder ∈ zeroLocus Frac J)
    (hpersistent : 131072 ≤ {i | C.equation i ∈ J}.ncard) :
    W.card ≤ 82405 := by
  classical
  let keep := Finset.univ.filter fun i => C.equation i ∈ J
  have hk : 131072 ≤ keep.card := by
    rw [← Set.ncard_coe_finset]
    exact hpersistent.trans_eq (congrArg Set.ncard (by ext i; simp [keep]))
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hk
  let P := Lagrange.interpolate S node (u 0)
  let Q := Lagrange.interpolate S node (u 1)
  have hinj : Set.InjOn node (S : Set I) := node.injective.injOn
  have hP : P.degree < (131072 : ℕ) := by
    simpa only [P, hcard] using Lagrange.degree_interpolate_lt (u 0) hinj
  have hQ : Q.degree < (131072 : ℕ) := by
    simpa only [Q, hcard] using Lagrange.degree_interpolate_lt (u 1) hinj
  apply pencil_count W (fun γ hγ => F γ (hW hγ)) P Q hP hQ
  intro γ hγ
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hinj
  · rw [hcard]
    exact (F γ (hW hγ)).degree
  · rw [hcard]
    have hm : (Polynomial.C γ * Q).degree ≤ Q.degree := by
      refine (Polynomial.degree_mul_le _ _).trans ?_
      simpa only [zero_add] using add_le_add_left (Polynomial.degree_C_le (a := γ)) Q.degree
    exact (Polynomial.degree_add_le _ _).trans_lt (max_lt hP (hm.trans_lt hQ))
  · intro i hi
    have hcut := (Finset.mem_filter.mp (hS hi)).2
    have hz := hzero γ hγ _ hcut
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    exact (C.agrees γ (hW hγ) i).mp hz |>.trans (by
      rw [Lagrange.eval_interpolate_at_node _ hinj hi, Lagrange.eval_interpolate_at_node _ hinj hi])
private theorem terminal_price_le : (82405 : ℚ) ≤ incidenceRatio := by
  change ((82405 : ℕ) : ℚ) ≤ ((0x147ffafff86 : ℕ) : ℚ) / ((48669 : ℕ) : ℚ)
  apply (le_div_iff₀ (by positivity)).mpr
  exact_mod_cast (show (82405 : ℕ) * 48669 ≤ 0x147ffafff86 by decide)
private theorem node_incidence (m : ℕ) (hm : m < 131072) :
    (((Fintype.card I - m) * cutDegree : ℕ) : ℚ) ≤
      incidenceRatio * ((179740 - m : ℕ) : ℚ) := by
  rw [IRSProfile.card_index, Nat.cast_mul]
  have hn : (262144 - m) * 48669 ≤ 131073 * (179740 - m) := by omega
  have hq : ((262144 - m : ℕ) : ℚ) * 48669 ≤ 131073 * ((179740 - m : ℕ) : ℚ) := by
    exact_mod_cast hn
  change ((262144 - m : ℕ) : ℚ) * (cutDegree : ℚ) ≤
    (((131073 : ℕ) * cutDegree : ℕ) : ℚ) / 48669 * ((179740 - m : ℕ) : ℚ)
  rw [Nat.cast_mul, div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = (((262144 - m : ℕ) : ℚ) * 48669) * (cutDegree : ℚ) := by ring
    _ ≤ (131073 * ((179740 - m : ℕ) : ℚ)) * (cutDegree : ℚ) :=
      mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg _)
    _ = _ := by push_cast; ring
private theorem count_chart {u : Words} {Γ : Finset K} (F : Marks u Γ) (C : TaylorCuts F)
    (g s : GenericRow) (hg : g ≠ 0) (hdeg : g.totalDegree ≤ 42)
    (hroot : ∀ γ (hγ : γ ∈ Γ), MvPolynomial.eval (point γ (F γ hγ).decoder) g = 0 ∧
      MvPolynomial.eval (point γ (F γ hγ).decoder) s ≠ 0) :
    (Γ.card : ℚ) ≤ 42 * incidenceRatio ^ 2 := by
  classical
  let x : Γ → (Fin 3 → Frac) := fun γ => point γ (F γ γ.property).decoder
  have hinj : Function.Injective x := by
    intro γ δ h
    apply Subtype.ext
    apply Polynomial.C_injective
    apply IsFractionRing.injective (Polynomial K) Frac
    exact congrFun h 1
  let S := Γ.attach.image x
  have hcard : S.card = Γ.card := by
    simp only [S, Finset.card_image_of_injective _ hinj, Finset.card_attach]
  rw [← hcard]
  refine surface_count_with_terminal g s hg C.equation (L := 131072) (A := 179740)
    (by decide) hdeg C.degree ((by norm_num : (1 : ℚ) ≤ 82405).trans terminal_price_le)
    node_incidence S
    (fun y hy => ?_) (fun y hy => ?_) (fun J hJ => ?_)
  · obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hy
    exact hroot γ γ.property
  · obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hy
    let M := F γ γ.property
    have hsub : (M.support : Set I) ⊆ {i | aeval (x γ) (C.equation i) = 0} :=
      fun i hi => (C.agrees γ γ.property i).mpr (M.hits i hi)
    exact M.agreement.trans (by simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub)
  · let W := Γ.attach.filter fun γ => x γ ∈ zeroLocus Frac J
    let V := W.image (fun γ : Γ => (γ : K))
    have hV : V ⊆ Γ := fun γ hγ => by
      obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hγ
      exact δ.property
    have hV0 : ∀ γ (hγ : γ ∈ V), point γ (F γ (hV hγ)).decoder ∈ zeroLocus Frac J := by
      intro γ hγ
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hγ
      exact (Finset.mem_filter.mp hδ).2
    have hcount := persistent_count C J V hV hV0 hJ
    have hW : W.card = V.card := (Finset.card_image_of_injective W Subtype.val_injective).symm
    have he : (S : Set (Fin 3 → Frac)) ∩ zeroLocus Frac J = (W.image x : Finset _) := by
      ext y
      simp only [S, W, Set.mem_inter_iff, Finset.mem_coe, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨γ, hγ, rfl⟩, h⟩
        exact ⟨γ, ⟨hγ, h⟩, rfl⟩
      · rintro ⟨γ, ⟨hγ, h⟩, rfl⟩
        exact ⟨⟨γ, hγ, rfl⟩, h⟩
    rw [he, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj, hW]
    exact (by exact_mod_cast hcount : (V.card : ℚ) ≤ 82405).trans terminal_price_le
theorem proof : Front6969_3.c2 := by
  classical
  intro bank u A Γ hΓ
  let F : Marks u Γ := fun γ hγ => Classical.choose (hΓ γ hγ).2
  have hF (γ : K) (hγ : γ ∈ Γ) :
      A.atLabel γ ≠ 0 ∧ A.atDecoder γ (F γ hγ).decoder = 0 :=
    ⟨(hΓ γ hγ).1, Classical.choose_spec (hΓ γ hγ).2⟩
  obtain ⟨g, hg, hassign⟩ := assign_charts A Γ (fun γ hγ => (F γ hγ).decoder) hF
  let charts (j : Fin 5) := Γ.filter fun γ =>
    ∃ hγ : γ ∈ Γ, RegularRoot (derivativeOrder g j) γ (F γ hγ).decoder
  have hsub (j : Fin 5) : charts j ⊆ Γ := Finset.filter_subset _ _
  have hcover : Γ ⊆ Finset.univ.biUnion charts := by
    intro γ hγ
    obtain ⟨j, hj⟩ := hassign γ hγ
    exact Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, hγ, hj⟩⟩
  have hchart (j : Fin 5) : ((charts j).card : ℚ) ≤ 42 * incidenceRatio ^ 2 := by
    rcases (charts j).eq_empty_or_nonempty with hempty | ⟨γ₀, hγ₀⟩
    · simp only [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
    let G := derivativeOrder g j
    let M : Marks u (charts j) := fun γ hγ => F γ (hsub j hγ)
    have hregular (γ : K) (hγ : γ ∈ charts j) : RegularRoot G γ (M γ hγ).decoder := by
      obtain ⟨_, hr⟩ := (Finset.mem_filter.mp hγ).2
      exact hr
    have hG : G.totalDegree ≤ 42 := (derivativeOrder_degree g j).trans hg
    let C : TaylorCuts M :=
      ⟨nodeCut u G, nodeCut_degree u G hG, fun γ hγ i =>
        eval_nodeCut u G γ (M γ hγ).decoder (hregular γ hγ) (M γ hγ).degree i⟩
    have hinj := IsFractionRing.injective (Polynomial K) Frac
    have hGne : G ≠ 0 := by
      intro h
      exact (hregular γ₀ hγ₀).2 (by simp [h, atTrajectory])
    have hgne : toGeneric G ≠ 0 := by
      intro h
      exact hGne (MvPolynomial.map_injective (algebraMap (Polynomial K) Frac) hinj
        (by simpa [toGeneric] using h))
    have hgd : (toGeneric G).totalDegree ≤ 42 := by
      simpa only [toGeneric, totalDegree, support_map_of_injective G hinj] using hG
    apply count_chart M C (toGeneric G) (toGeneric (MvPolynomial.pderiv 0 G)) hgne hgd
    intro γ hγ
    obtain ⟨hr, hs⟩ := hregular γ hγ
    rw [K1_10_2.eval_toGeneric, K1_10_2.eval_toGeneric, hr, map_zero]
    exact ⟨rfl, by simpa only [map_zero] using hinj.ne hs⟩
  have hnat : Γ.card ≤ ∑ j : Fin 5, (charts j).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hrat : (Γ.card : ℚ) ≤ 5 * 42 * incidenceRatio ^ 2 := by
    calc
      (Γ.card : ℚ) ≤ ∑ j : Fin 5, ((charts j).card : ℚ) := by exact_mod_cast hnat
      _ ≤ ∑ _j : Fin 5, (42 * incidenceRatio ^ 2 : ℚ) :=
        Finset.sum_le_sum fun j _ => hchart j
      _ = _ := by simp; ring
  have hrounded : (Γ.card : ℚ) ≤ (Front6969_3.regularPrice : ℚ) := by
    unfold Front6969_3.regularPrice
    apply hrat.trans
    rw [show (5 : ℚ) * 42 = ((210 : ℕ) : ℚ) by norm_num]
    exact Nat.le_ceil _
  exact_mod_cast hrounded
end
end Front6969_3_2
end
end Z6969Source2222

-- Source: ProximityPrize.SubmissionLower.ProfileFrontRankFour
section Z6969Source2223
set_option autoImplicit true
set_option Elab.async false

-- merged module R6960Front6969Charts
section Merged_R6960Front6969Charts

set_option Elab.async false
set_option autoImplicit false

namespace Front6969_4
noncomputable section
open Front6969 MvPolynomial
open P2_4 (Bank Puncture nodeCut)
open K1_11 (scalarWeightY scalarWeightYS scalarWeightT scalarWeightTotal scalarImages)

structure Marks (u : Words) (deleted : Finset I) (Γ : Finset K) where
  mark : ∀ γ ∈ Γ, BadMark u γ
  survives : ∀ γ (hγ : γ ∈ Γ) i, i ∈ (mark γ hγ).support → i ∉ deleted
structure Annihilator {u : Words} {deleted : Finset I} {Γ : Finset K}
    (F : Marks u deleted Γ) (b : Bank) where
  Q : MvPolynomial (Fin 4) K
  nonzero : Q ≠ 0
  degreeY : Q.weightedTotalDegree scalarWeightY ≤ 5
  degreeS : Q.weightedTotalDegree scalarWeightYS ≤ b.a
  degreeT : Q.weightedTotalDegree scalarWeightT ≤ b.b
  degreeTotal : Q.weightedTotalDegree scalarWeightTotal ≤ b.E
  vanishes : ∀ γ (hγ : γ ∈ Γ),
    aeval (scalarImages (F.mark γ hγ).decoder γ (γ ^ p)) Q = 0
structure TaylorChart (u : Words) {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} (F : Marks u deleted Γ) (b : Bank) (Λ : Finset K) where
  subset : Λ ⊆ Γ
  equation : MvPolynomial (Fin 3) Frac
  equation_ne : equation ≠ 0
  equation_degree : equation.totalDegree ≤ b.E
  numerator : Polynomial (MvPolynomial (Fin 3) Frac)
  numerator_degree : numerator.natDegree ≤ 131071
  denominator : MvPolynomial (Fin 3) Frac
  cut_degree : ∀ i, (nodeCut u P numerator denominator i).totalDegree ≤ b.M
  point : K → Fin 3 → Frac
  slope : ∀ γ ∈ Λ, point γ 1 = algebraMap K Frac γ
  on_equation : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) equation = 0
  regular : ∀ γ ∈ Λ, MvPolynomial.eval (point γ) denominator ≠ 0
  reconstruction : ∀ γ (hγ : γ ∈ Λ),
    numerator.map (MvPolynomial.eval (point γ)) =
      Polynomial.C (MvPolynomial.eval (point γ) denominator) *
        (F.mark γ (subset hγ)).decoder.map (algebraMap K Frac)
end
end Front6969_4
section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Front6969_4
noncomputable section
open Front6969 MvPolynomial
open P2_4 (Bank Puncture nodeCut)
open K1_11 (scalarWeightTotal)
open K1_11_3 (SimpleRoot derivativeChart exists_simple_derivative_at_root)
open K1_11_3 (exceptions specializeY yView_degree specializeY_eval specializeY_iterate specializeY_derivative)
open K1_11_3 (centerPoint atCenter atCenter_degree numerator numerator_degree denominator eval_atCenter pderiv_atCenter numerator_eval_degree denominator_degree reconstruct natDegree_le_of_degree_lt_succ derivativeChart_degree)
theorem assign {u : Words} {deleted : Finset I} {Γ : Finset K}
    {F : Marks u deleted Γ} {b : Bank} (A : Annihilator F b) :
    ∃ (exceptional : Finset K) (charts : Fin 5 → Finset K),
      exceptional.card ≤ b.zeroFee ∧
      (∀ γ ∈ Γ, γ ∈ exceptional ∨ ∃ j, γ ∈ charts j) ∧
      ∀ j, ∃ hsub : charts j ⊆ Γ, ∀ γ (hγ : γ ∈ charts j),
        SimpleRoot (derivativeChart A.Q j) (F.mark γ (hsub hγ)).decoder γ (γ ^ p) := by
  classical
  obtain ⟨exceptional, hfee, hex⟩ := exceptions A.Q A.nonzero p b.a b.b (by decide)
    (by cases b <;> decide) A.degreeS A.degreeT Γ
  have hassign (γ : K) (hγ : γ ∈ Γ) (hn : γ ∉ exceptional) :
      ∃ j : Fin 5, SimpleRoot (derivativeChart A.Q j) (F.mark γ hγ).decoder γ (γ ^ p) := by
    let f := specializeY A.Q γ (γ ^ p)
    have hdeg : f.natDegree ≤ 5 :=
      (Polynomial.natDegree_map_le).trans ((yView_degree A.Q).le.trans A.degreeY)
    have hroot : f.IsRoot (F.mark γ hγ).decoder :=
      (specializeY_eval A.Q _ γ (γ ^ p)).trans (A.vanishes γ hγ)
    obtain ⟨j, hj, hz, hnz⟩ := exists_simple_derivative_at_root p 5 f
      (hex γ hγ hn) hdeg (by decide) _ hroot
    refine ⟨⟨j,hj⟩, ?_, ?_⟩
    · rw [← specializeY_eval, specializeY_iterate]
      exact hz
    · rw [← specializeY_eval, specializeY_derivative, specializeY_iterate]
      exact hnz
  let charts (j : Fin 5) := Γ.filter fun γ =>
    ∃ hγ : γ ∈ Γ, SimpleRoot (derivativeChart A.Q j) (F.mark γ hγ).decoder γ (γ ^ p)
  refine ⟨exceptional, charts, hfee, ?_, ?_⟩
  · intro γ hγ
    by_cases he : γ ∈ exceptional
    · exact Or.inl he
    · obtain ⟨j,hj⟩ := hassign γ hγ he
      exact Or.inr ⟨j, Finset.mem_filter.mpr ⟨hγ, hγ, hj⟩⟩
  · intro j
    refine ⟨fun _ hγ => (Finset.mem_filter.mp hγ).1, ?_⟩
    intro γ hγ
    obtain ⟨_, h⟩ := (Finset.mem_filter.mp hγ).2
    exact h
private theorem build_chart
    {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} (F : Marks u deleted Γ) (b : Bank)
    (Λ : Finset K) (hsub : Λ ⊆ Γ) (hne : Λ.Nonempty)
    (G : MvPolynomial (Fin 4) K) (hG : G.weightedTotalDegree scalarWeightTotal ≤ b.E)
    (hroot : ∀ γ (hγ : γ ∈ Λ),
      SimpleRoot G (F.mark γ (hsub hγ)).decoder γ (γ ^ p)) :
    Nonempty (TaylorChart u P F b Λ) := by
  classical
  let point (γ : K) : Fin 3 → Frac := if h : γ ∈ Λ then
    centerPoint (F.mark γ (hsub h)).decoder γ (γ ^ p) else fun _ => 0
  have hpnt (γ : K) (hγ : γ ∈ Λ) :
      point γ = centerPoint (F.mark γ (hsub hγ)).decoder γ (γ ^ p) := by
    simp [point, hγ]
  refine ⟨{
    subset := hsub
    equation := atCenter G
    equation_ne := ?_
    equation_degree := (atCenter_degree G).trans hG
    numerator := K1_11_3.numerator G 131071
    numerator_degree := numerator_degree _ _
    denominator := K1_11_3.denominator G 131071
    cut_degree := ?_
    point := point
    slope := fun γ hγ => by rw [hpnt γ hγ]; rfl
    on_equation := fun γ hγ => by rw [hpnt γ hγ, eval_atCenter, (hroot γ hγ).1, map_zero]
    regular := ?_
    reconstruction := ?_ }⟩
  · obtain ⟨γ, hγ⟩ := hne
    have hn := (hroot γ hγ).2
    intro hz
    apply hn
    apply (IsFractionRing.injective (Polynomial K) Frac)
    rw [map_zero, ← eval_atCenter, ← pderiv_atCenter, hz, map_zero, map_zero]
  · intro i
    unfold nodeCut
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact numerator_eval_degree K1_11_3_1.proof G 131071 b.E (by cases b <;> decide) hG _
    · apply (totalDegree_mul _ _).trans
      have ha : (C (σ := Fin 3) (algebraMap K Frac (u 0 (P.index i))) +
          MvPolynomial.X 1 * C (algebraMap K Frac (u 1 (P.index i)))).totalDegree ≤ 1 := by
        exact (totalDegree_add _ _).trans (max_le (by simp)
          ((totalDegree_mul _ _).trans (by simp)))
      exact Nat.add_le_add (denominator_degree G 131071 b.E hG) ha
  · intro γ hγ
    rw [hpnt γ hγ, K1_11_3.denominator, map_pow, eval_atCenter]
    exact pow_ne_zero _ (fun h => (hroot γ hγ).2
      ((IsFractionRing.injective (Polynomial K) Frac) (h.trans (map_zero _).symm)))
  · intro γ hγ
    rw [hpnt γ hγ]
    apply reconstruct K1_11_3_2.proof
    · exact natDegree_le_of_degree_lt_succ (F.mark γ (hsub hγ)).degree
    · exact (hroot γ hγ).1
    · intro n hn
      have pp := CharP.char_is_prime_of_two_le K p (by decide)
      intro hz
      have hn' := pp.dvd_factorial.mp ((CharP.cast_eq_zero_iff K p _).mp hz)
      exact (not_lt_of_ge (hn'.trans hn)) (by decide)
theorem chart_cover {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {Γ : Finset K} {F : Marks u deleted Γ} {b : Bank} (A : Annihilator F b) :
    ∃ (exceptional : Finset K) (charts : Fin 5 → Finset K),
      exceptional.card ≤ b.zeroFee ∧
      (∀ γ ∈ Γ, γ ∈ exceptional ∨ ∃ j, γ ∈ charts j) ∧
      ∀ j, charts j = ∅ ∨ Nonempty (TaylorChart u P F b (charts j)) := by
  obtain ⟨exceptional, charts, hfee, hcover, hcharts⟩ := assign A
  refine ⟨exceptional, charts, hfee, hcover, fun j => ?_⟩
  rcases (charts j).eq_empty_or_nonempty with he | hn
  · exact Or.inl he
  · obtain ⟨hsub, hroot⟩ := hcharts j
    exact Or.inr (build_chart P F b (charts j) hsub hn (derivativeChart A.Q j)
      ((derivativeChart_degree A.Q j).trans A.degreeTotal) hroot)
end
end Front6969_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Front6969_4
noncomputable section
open Front6969 MvPolynomial
open P2_4 (Bank Puncture nodeCut)
open K1_11 (scalarWeightTotal)
open scoped BigOperators
open K1_11 (indexedSupport mem_indexedSupport indexedSupport_card nodes_injective)
open K1_11 (ncard_inter_filter surface_count_with_terminal)
open K1_11 (seed_eq_of_mismatch)
variable {u : Words} {deleted : Finset I} {P : Puncture deleted}
  {Γ Λ : Finset K} {F : Marks u deleted Γ} {b : Bank}
theorem mark_degree {u : Words} {γ : K} (M : BadMark u γ) :
    M.decoder.natDegree ≤ 131071 := by
  apply Polynomial.natDegree_le_of_degree_le
  exact Order.le_of_lt_succ (show M.decoder.degree < (131072 : ℕ) from M.degree)

theorem correctOn_mark {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {γ : K} (M : BadMark u γ) :
    K1_11.correctOn u P M.decoder (M.decoder.map twist) γ (γ ^ p) (indexedSupport P M.support) := by
  intro i hi
  have h := M.hits (P.index i) ((mem_indexedSupport P M.support i).mp hi)
  refine ⟨h, ?_⟩
  change (M.decoder.map twist).eval (node (P.index i)) =
    u 0 (P.index i) ^ p + γ ^ p * u 1 (P.index i) ^ p
  rw [FrobeniusLocator.Strata.eval_coefficient_map twist M.decoder _
    (FrobeniusLocator.Native.native_domain_fixed (P.index i)), h]
  simp only [map_add, map_mul, P0.twist, frobenius_def]

private theorem pencil_bad_count (hsub : Λ ⊆ Γ) (P₀ P₁ : Polynomial K)
    (h₀ : P₀.degree < (131072 : ℕ)) (h₁ : P₁.degree < (131072 : ℕ))
    (pencil : ∀ γ (hγ : γ ∈ Λ),
      (F.mark γ (hsub hγ)).decoder = P₀ + Polynomial.C γ * P₁) :
    Λ.card ≤ P.N := by
  classical
  have mismatch (γ : Λ) :
      ∃ i : Fin P.N,
        (P₀.eval (P.nodes i) ≠ u 0 (P.index i) ∨ P₁.eval (P.nodes i) ≠ u 1 (P.index i)) ∧
        P₀.eval (P.nodes i) + (γ : K) * P₁.eval (P.nodes i) =
          u 0 (P.index i) + (γ : K) * u 1 (P.index i) := by
    let M := F.mark γ (hsub γ.property)
    obtain ⟨idx, hi, hm⟩ :
        ∃ idx ∈ M.support, P₀.eval (node idx) ≠ u 0 idx ∨ P₁.eval (node idx) ≠ u 1 idx := by
      by_contra hn
      push Not at hn
      exact M.nonjoint ⟨⟨P₀, h₀, fun j hj => (hn j hj).1⟩, ⟨P₁, h₁, fun j hj => (hn j hj).2⟩⟩
    obtain ⟨i, rfl⟩ := (P.retained idx).mpr (F.survives γ (hsub γ.property) idx hi)
    refine ⟨i, hm, ?_⟩
    have hh := M.hits (P.index i) hi
    change (F.mark (γ : K) (hsub γ.property)).decoder.eval (P.nodes i) = _ at hh
    simpa only [pencil _ γ.property, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C] using hh
  let f : Λ → Fin P.N := fun γ => Classical.choose (mismatch γ)
  have hf : Function.Injective f := by
    intro γ δ he
    apply Subtype.ext
    obtain ⟨hm, hγ⟩ := Classical.choose_spec (mismatch γ)
    have hδ := (Classical.choose_spec (mismatch δ)).2
    change f γ = f δ at he
    change
      (P₀.eval (P.nodes (f γ)) ≠ u 0 (P.index (f γ)) ∨
        P₁.eval (P.nodes (f γ)) ≠ u 1 (P.index (f γ))) at hm
    change P₀.eval (P.nodes (f γ)) + (γ : K) * P₁.eval (P.nodes (f γ)) =
      u 0 (P.index (f γ)) + (γ : K) * u 1 (P.index (f γ)) at hγ
    change P₀.eval (P.nodes (f δ)) + (δ : K) * P₁.eval (P.nodes (f δ)) =
      u 0 (P.index (f δ)) + (δ : K) * u 1 (P.index (f δ)) at hδ
    rw [← he] at hδ
    exact seed_eq_of_mismatch (F := K) hγ hδ hm
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf
variable (chart : TaylorChart u P F b Λ)
theorem chart_cut_iff (γ : K) (hγ : γ ∈ Λ) (i : Fin P.N) :
    MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0 ↔
      (F.mark γ (chart.subset hγ)).decoder.eval (P.nodes i) =
        u 0 (P.index i) + γ * u 1 (P.index i) := by
  let val := MvPolynomial.eval (chart.point γ)
  let x := algebraMap K Frac (P.nodes i)
  change val (nodeCut u P chart.numerator chart.denominator i) = 0 ↔ _
  have heval := Polynomial.eval_map_apply val (C x) (p := chart.numerator)
  unfold nodeCut
  change val (chart.numerator.eval (C x) - _) = 0 ↔ _
  rw [map_sub, ← heval]
  change (chart.numerator.map val).eval (val (C x)) - _ = 0 ↔ _
  rw [show val (C x) = x by simp [val], show chart.numerator.map val = _ from chart.reconstruction γ hγ]
  rw [Polynomial.eval_mul, Polynomial.eval_C, show x = algebraMap K Frac (P.nodes i) from rfl,
    Polynomial.eval_map_apply, map_mul, map_add, map_mul]
  simp only [val, eval_C, eval_X, chart.slope γ hγ]
  rw [← map_mul, ← map_add, sub_eq_zero]
  constructor
  · intro h
    exact (algebraMap K Frac).injective (mul_left_cancel₀ (chart.regular γ hγ) h)
  · intro h
    rw [h]
theorem chart_persistent (J : Ideal (MvPolynomial (Fin 3) Frac)) (W : Finset K) (hW : W ⊆ Λ)
    (hzero : ∀ γ ∈ W, chart.point γ ∈ zeroLocus Frac J)
    (hpersist : 131072 ≤ {i | nodeCut u P chart.numerator chart.denominator i ∈ J}.ncard) :
    W.card ≤ P.N := by
  classical
  let keep := Finset.univ.filter fun i => nodeCut u P chart.numerator chart.denominator i ∈ J
  have hk : 131072 ≤ keep.card := by
    rw [← Set.ncard_coe_finset]
    exact hpersist.trans_eq (congrArg Set.ncard (by ext i; simp [keep]))
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hk
  let P₀ := Lagrange.interpolate S P.nodes (fun i => u 0 (P.index i))
  let P₁ := Lagrange.interpolate S P.nodes (fun i => u 1 (P.index i))
  have hinj : Set.InjOn P.nodes (S : Set (Fin P.N)) := nodes_injective.injOn
  have hd₀ : P₀.degree < (131072 : ℕ) := by
    simpa only [P₀, hcard] using Lagrange.degree_interpolate_lt (fun i => u 0 (P.index i)) hinj
  have hd₁ : P₁.degree < (131072 : ℕ) := by
    simpa only [P₁, hcard] using Lagrange.degree_interpolate_lt (fun i => u 1 (P.index i)) hinj
  apply pencil_bad_count (P := P) (F := F) (fun _ hg => chart.subset (hW hg)) P₀ P₁ hd₀ hd₁
  intro γ hγ
  let M := F.mark γ (chart.subset (hW hγ))
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hinj
  · rw [hcard]
    exact Polynomial.degree_le_natDegree.trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le (mark_degree M)))
  · rw [hcard]
    have hm : (Polynomial.C γ * P₁).degree ≤ P₁.degree := by
      refine (Polynomial.degree_mul_le _ _).trans ?_
      simpa only [zero_add] using add_le_add_left (Polynomial.degree_C_le (a := γ)) P₁.degree
    exact (Polynomial.degree_add_le _ _).trans_lt (max_lt hd₀ (hm.trans_lt hd₁))
  · intro i hi
    have hcut : nodeCut u P chart.numerator chart.denominator i ∈ J := (Finset.mem_filter.mp (hS hi)).2
    have hz : MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0 :=
      hzero γ hγ _ hcut
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    exact (chart_cut_iff chart γ (hW hγ) i).mp hz |>.trans (by
      rw [Lagrange.eval_interpolate_at_node _ hinj hi, Lagrange.eval_interpolate_at_node _ hinj hi])
end
end Front6969_4
end

end Merged_R6960Front6969Charts

-- merged module Front6969Rank4
section Merged_Front6969Rank4
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace Front6969_4
noncomputable section
open Front6969 MvPolynomial
def WedgeBounds (h : ℕ) (U V : MvPolynomial (Fin 5) K) : Prop :=
  (L - h) * U.degreeOf 3 ≤ h ∧ (L - h) * U.degreeOf 4 ≤ L ∧
    (L - h) * V.degreeOf 3 ≤ L ∧ (L - h) * V.degreeOf 4 ≤ h
structure IndependentLift {u : Words} {T : TwoActive u} (R : Relation T) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  U_omits : K1_11_2.OmitsMessages U
  V_omits : K1_11_2.OmitsMessages V
  heights : U.degreeOf 0 ≤ T.height ∧ V.degreeOf 0 ≤ T.height
  bounds : WedgeBounds T.height U V
  primitive : ∀ q : MvPolynomial (Fin 2) K,
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ U →
    rename (![3, 4] : Fin 2 → Fin 5) q ∣ V → IsUnit q
  content : Polynomial K
  content_ne : content ≠ 0
  graphU : K1_11_2.graph p U = Polynomial.C content * leftU R
  graphV : K1_11_2.graph p V = Polynomial.C content * leftV R
structure ReducedPair {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (A : IndependentLift R) where
  U : MvPolynomial (Fin 5) K
  V : MvPolynomial (Fin 5) K
  U_omits : K1_11_2.OmitsMessages U
  V_omits : K1_11_2.OmitsMessages V
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  U_dvd : U ∣ A.U
  V_dvd : V ∣ A.V
  relPrime : IsRelPrime U V
  height : max (U.degreeOf 0) (V.degreeOf 0) = D.height
  graphU : K1_11_2.graph p U = Polynomial.C A.content * D.U
  graphV : K1_11_2.graph p V = Polynomial.C A.content * D.V
abbrev weightedCutoff : ℕ := 4 * agreement - 1
def originalFloor : P2_4.Bank → ℕ
  | .w22 | .w22Swapped | .w12 | .w21 => 24334
  | _ => 32446
end
end Front6969_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
namespace Front6969_4
noncomputable section
open Front6969 MvPolynomial
open P2_4 (Bank Puncture ContactInput)
open K1_11 (sourceWeights sourceBounds filtered mem_filtered)
open K1_11_2 (OmitsMessages sWeight tWeight graph PlaneOutput equation equation_degrees
  nodeWordMap decoder_bounds decoderNumerator decoderDenominator decoderDenominator_ne equation_linear
  equation_primitive linear_relation_contact_order_one)
open K1_11_2_2 (interpolant parameterNode nodeValue parameterNode_interpolant
  parameterNode_nodeValue degreeOf_interpolant_le degreeOf_nodeValue_le seedEval
  seedEval_nodeValue eval_graph nodeWord_combination nodeWord_omits)
open K1_11_2_1 (degreeOf_le_of_dvd)
open K1_11_2 (no_pair_one_one_of_graph native_column_rank)
open K1_8 (transfer_at)
private theorem reduced_bounds {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A) :
    WedgeBounds T.height B.U B.V := by
  have loc_ne : liftX (FrobeniusLocator.locator node (fixedNodes R)) ≠ 0 :=
    fun hz => (FrobeniusLocator.locator_monic node (fixedNodes R)).ne_zero
      ((Polynomial.map_injective _ Polynomial.C_injective) (hz.trans (Polynomial.map_zero _).symm))
  have hU : A.U ≠ 0 := by
    intro h
    have hg := A.graphU
    rw [h, map_zero, D.U_factor] at hg
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr A.content_ne) (mul_ne_zero loc_ne D.U_ne) hg.symm
  have hV : A.V ≠ 0 := by
    intro h
    have hg := A.graphV
    rw [h, map_zero, D.V_factor] at hg
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr A.content_ne) (mul_ne_zero loc_ne D.V_ne) hg.symm
  exact ⟨(Nat.mul_le_mul_left _ (degreeOf_le_of_dvd hU B.U_dvd 3)).trans A.bounds.1,
    (Nat.mul_le_mul_left _ (degreeOf_le_of_dvd hU B.U_dvd 4)).trans A.bounds.2.1,
    (Nat.mul_le_mul_left _ (degreeOf_le_of_dvd hV B.V_dvd 3)).trans A.bounds.2.2.1,
    (Nat.mul_le_mul_left _ (degreeOf_le_of_dvd hV B.V_dvd 4)).trans A.bounds.2.2.2⟩
private theorem degree_lt_of_product (s d m b : ℕ) (hd : s * d ≤ b) (hm : b < s * m) :
    d < m := by
  by_contra! h
  exact (not_lt_of_ge ((Nat.mul_le_mul_left s h).trans hd)) hm
private theorem reduced_boxes {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hH : T.height ≤ heightCap) :
    B.U.degreeOf 3 ≤ 2 ∧ B.U.degreeOf 4 ≤ 3 ∧
      B.V.degreeOf 3 ≤ 3 ∧ B.V.degreeOf 4 ≤ 2 := by
  obtain ⟨hUS, hUT, hVS, hVT⟩ := reduced_bounds B
  have hh : T.height ≤ 33735 := hH
  exact ⟨Nat.le_of_lt_succ (degree_lt_of_product _ _ 3 _ hUS (by change _ < (48668 - _) * 3; omega)),
    Nat.le_of_lt_succ (degree_lt_of_product _ _ 4 _ hUT (by change 48668 < (48668 - _) * 4; omega)),
    Nat.le_of_lt_succ (degree_lt_of_product _ _ 4 _ hVS (by change 48668 < (48668 - _) * 4; omega)),
    Nat.le_of_lt_succ (degree_lt_of_product _ _ 3 _ hVT (by change _ < (48668 - _) * 3; omega))⟩
private theorem no_pair_one_one {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hr : columnRank D.U D.V = 4) (hs : sWeight B.U B.V = 1) (ht : tWeight B.U B.V = 1) :
    False := by
  let f : Polynomial K →ₐ[K] Frac := IsScalarTower.toAlgHom K (Polynomial K) Frac
  have hf : Function.Injective f := IsFractionRing.injective (Polynomial K) Frac
  have hold : K1.columnRank D.U D.V = 4 := (P0_4.columnRank_eq D.U D.V).symm.trans hr
  have hr' : K1_8.columnRankAt K1.p D.U D.V = 4 := hold
  rw [native_column_rank] at hr'
  exact no_pair_one_one_of_graph p f hf A.content B.U B.V D.U D.V A.content_ne D.U_ne
    B.U_omits B.V_omits B.graphU B.graphV hr' hs ht
private theorem actual_bank {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hr : columnRank D.U D.V = 4) (hH : T.height ≤ heightCap) :
    ∃ bank : Bank, sWeight B.U B.V = bank.dS ∧ tWeight B.U B.V = bank.dT ∧
      originalFloor bank ≤ T.height := by
  obtain ⟨pUS, pUT, pVS, pVT⟩ := reduced_bounds B
  obtain ⟨bUS, bUT, bVS, bVT⟩ := reduced_boxes B hH
  have hlo : 24334 ≤ T.height := by
    by_contra! h
    have hs₁ : B.U.degreeOf 3 < 1 :=
      degree_lt_of_product _ _ 1 _ pUS (by change _ < (48668 - _) * 1; omega)
    have hs₂ : B.V.degreeOf 3 < 2 :=
      degree_lt_of_product _ _ 2 _ pVS (by change 48668 < (48668 - _) * 2; omega)
    have ht₁ : B.U.degreeOf 4 < 2 :=
      degree_lt_of_product _ _ 2 _ pUT (by change 48668 < (48668 - _) * 2; omega)
    have ht₂ : B.V.degreeOf 4 < 1 :=
      degree_lt_of_product _ _ 1 _ pVT (by change _ < (48668 - _) * 1; omega)
    exact no_pair_one_one B hr (by unfold sWeight; omega) (by unfold tWeight; omega)
  have hhi (hw : sWeight B.U B.V = 3 ∨ tWeight B.U B.V = 3) : 32446 ≤ T.height := by
    by_contra! h
    have hs₁ : B.U.degreeOf 3 < 2 :=
      degree_lt_of_product _ _ 2 _ pUS (by change _ < (48668 - _) * 2; omega)
    have hs₂ : B.V.degreeOf 3 < 3 :=
      degree_lt_of_product _ _ 3 _ pVS (by change 48668 < (48668 - _) * 3; omega)
    have ht₁ : B.U.degreeOf 4 < 3 :=
      degree_lt_of_product _ _ 3 _ pUT (by change 48668 < (48668 - _) * 3; omega)
    have ht₂ : B.V.degreeOf 4 < 2 :=
      degree_lt_of_product _ _ 2 _ pVT (by change _ < (48668 - _) * 2; omega)
    unfold sWeight tWeight at hw
    omega
  have hs : sWeight B.U B.V = 1 ∨ sWeight B.U B.V = 2 ∨ sWeight B.U B.V = 3 := by
    unfold sWeight
    omega
  have ht : tWeight B.U B.V = 1 ∨ tWeight B.U B.V = 2 ∨ tWeight B.U B.V = 3 := by
    unfold tWeight
    omega
  rcases hs with hs | hs | hs <;> rcases ht with ht | ht | ht
  · exact (no_pair_one_one B hr hs ht).elim
  · exact ⟨.w12, hs, ht, hlo⟩
  · exact ⟨.w13, hs, ht, hhi (Or.inr ht)⟩
  · exact ⟨.w21, hs, ht, hlo⟩
  · exact ⟨.w22Swapped, hs, ht, hlo⟩
  · exact ⟨.w23, hs, ht, hhi (Or.inr ht)⟩
  · exact ⟨.w31, hs, ht, hhi (Or.inl hs)⟩
  · exact ⟨.w32, hs, ht, hhi (Or.inl hs)⟩
  · exact ⟨.w33, hs, ht, hhi (Or.inl hs)⟩
private theorem reduced_scaled_relation {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (e : Polynomial K) :
    K1_8.relationOnAt p u (fixedNodes R) (Polynomial.C e * D.U)
      (Polynomial.C e * D.V) (Polynomial.C e * D.output) := by
  let G := liftX (FrobeniusLocator.locator node (fixedNodes R))
  have hG : ∀ i ∉ fixedNodes R, G.eval (Polynomial.C (node i)) ≠ 0 := by
    intro i hi
    rw [show G = K1.liftX _ from rfl, K1_8.eval_liftX, Polynomial.C_ne_zero]
    exact fun hz => hi ((FrobeniusLocator.Principal.locator_eval_zero_iff node
      ProximityPrize.Benchmark.IRSProfile.domain.injective _ i).mp hz)
  exact @transfer_at u p 131072 T.height R (fixedNodes R) G D.U D.V D.output
    hG D.U_factor D.V_factor D.output_factor e
private theorem nodeValue_of_relation (q : ℕ) {u : Words} {deleted : Finset I}
    {P : Puncture deleted} {U V : MvPolynomial (Fin 5) K} {G : Bivar}
    (hrel : K1_8.relationOnAt q u deleted (graph q U) (graph q V) G) (i : Fin P.N) :
    seedEval q (nodeValue (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
      (u 0 (P.index i) ^ q) (u 1 (P.index i) ^ q) U V) = G.eval (Polynomial.C (P.nodes i)) := by
  have hkeep : P.index i ∉ deleted := (P.retained _).mp ⟨i, rfl⟩
  rw [seedEval_nodeValue]
  exact hrel (P.index i) hkeep
private theorem plane_output {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hH : T.height ≤ heightCap) (P : Puncture (fixedNodes R)) :
    Nonempty (PlaneOutput u P D.height B.U B.V) := by
  let x : Fin P.N → K := P.nodes
  let a (i : Fin P.N) : K := u 0 (P.index i)
  let b (i : Fin P.N) : K := u 1 (P.index i)
  let v (i : Fin P.N) := nodeValue (x i) (a i) (b i) (a i ^ p) (b i ^ p) B.U B.V
  let W := interpolant x v
  have hx : Function.Injective x :=
    ProximityPrize.Benchmark.IRSProfile.domain.injective.comp P.index.injective
  have hnodes (i : Fin P.N) : parameterNode (x i) W = v i :=
    parameterNode_interpolant x hx v (fun _ => parameterNode_nodeValue ..) i
  have hdeg (j : Fin 5) : W.degreeOf j ≤
      (P.N - 1) * (MvPolynomial.X 0 : MvPolynomial (Fin 5) K).degreeOf j +
      (if j = 3 then sWeight B.U B.V else if j = 4 then tWeight B.U B.V else 0) :=
    degreeOf_interpolant_le x hx v j _ (fun i => degreeOf_nodeValue_le j
      (x i) (a i) (b i) (a i ^ p) (b i ^ p) B.U B.V)
  have hm : OmitsMessages W := ⟨Nat.eq_zero_of_le_zero (by simpa [degreeOf_X] using hdeg 1),
    Nat.eq_zero_of_le_zero (by simpa [degreeOf_X] using hdeg 2)⟩
  have hs : W.degreeOf 3 ≤ sWeight B.U B.V := by simpa [degreeOf_X] using hdeg 3
  have ht : W.degreeOf 4 ≤ tWeight B.U B.V := by simpa [degreeOf_X] using hdeg 4
  have hbound : 131072 + D.height ≤ P.N := by
    have hh : T.height ≤ 33735 := hH
    have hD := D.height_eq
    have hP := P.size
    omega
  have hsmall : W.degreeOf 3 < p := by
    obtain ⟨huS, _, hvS, _⟩ := reduced_boxes B hH
    unfold sWeight at hs
    change W.degreeOf 3 < 2130706433
    omega
  have hdegree := K1_11_2_1.graph_natDegree p (by decide) W hm hsmall
  have hWdeg : (graph p W).natDegree < P.N := by
    rw [hdegree]
    have hh : W.degreeOf 0 ≤ P.N - 1 := by simpa [degreeOf_X] using hdeg 0
    omega
  let G := Polynomial.C A.content * D.output
  have hDdeg : D.output.natDegree ≤ 131071 + D.height := by
    by_cases hz : D.output = 0
    · simp [hz]
    have hd := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr D.output_degree
    change D.output.natDegree < 131072 + D.height at hd
    omega
  have hGdeg : G.natDegree ≤ 131071 + D.height :=
    (Polynomial.natDegree_C_mul_le A.content D.output).trans hDdeg
  have hrel : K1_8.relationOnAt p u (fixedNodes R) (graph p B.U) (graph p B.V) G := by
    rw [B.graphU, B.graphV]
    exact reduced_scaled_relation D A.content
  have heval (i : Fin P.N) : (graph p W).eval (Polynomial.C (x i)) = G.eval (Polynomial.C (x i)) := by
    rw [eval_graph, hnodes]
    exact nodeValue_of_relation p (P := P) hrel i
  have hgraph : graph p W = G := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (Polynomial.C_injective.comp hx) heval
    rw [Fintype.card_fin]
    exact max_lt hWdeg (by omega)
  have hheight : W.degreeOf 0 ≤ 131071 + D.height := by
    rw [← hdegree, hgraph]
    exact hGdeg
  refine ⟨⟨W, hm, hheight, hs, ht, ?_⟩⟩
  intro i
  change nodeWordMap (x i) (a i) (b i) (a i ^ p) (b i ^ p) (B.U * MvPolynomial.X 1 + B.V * MvPolynomial.X 2 - W) = 0
  rw [map_sub, nodeWord_combination _ _ _ _ _ _ _ B.U_omits B.V_omits,
    nodeWord_omits _ _ _ _ _ W hm, hnodes]
  exact sub_self _
theorem contact_input {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} {A : IndependentLift R} (B : ReducedPair D A)
    (hr : columnRank D.U D.V = 4) (hH : T.height ≤ heightCap) (P : Puncture (fixedNodes R)) :
    ∃ b : Bank, originalFloor b ≤ T.height ∧ Nonempty (ContactInput u P b D.height) := by
  obtain ⟨W⟩ := plane_output B hH P
  obtain ⟨bank, hs, ht, hfloor⟩ := actual_bank B hr hH
  let L := equation B.U B.V W.W
  have hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) =
      sourceBounds (131071 + D.height) 1 bank.dS bank.dT j := by
    simpa only [L, equation, hs, ht] using equation_degrees 131071 D.height B.U B.V W.W
      B.U_ne B.V_ne B.U_omits B.V_omits W.omits B.height W.height W.degreeS W.degreeT
  have hL : L ≠ 0 := by
    intro hz
    have he := hdeg 1
    simp [hz, sourceBounds, weightedTotalDegree] at he
  have hf : L ∈ filtered (sourceWeights 131071)
      (sourceBounds (131071 + D.height) 1 bank.dS bank.dT) :=
    (mem_filtered _ _ _).mpr fun j => (hdeg j).le
  obtain ⟨hy, hdy, hns, hds, hnt, hdt⟩ := decoder_bounds 131071 D.height bank.dS bank.dT
    B.U B.V W.W B.U_omits B.V_omits W.omits B.V_ne hf
  refine ⟨bank, hfloor, ⟨{
    L := L
    L_ne := hL
    degrees := hdeg
    order_one := ?_
    numerator := decoderNumerator B.U W.W
    denominator := decoderDenominator B.V
    denominator_ne := decoderDenominator_ne B.V B.V_omits B.V_ne
    linear := equation_linear B.U B.V W.W B.U_omits B.V_omits W.omits
    primitive := equation_primitive B.U B.V W.W B.U_omits B.V_omits W.omits B.V_ne B.relPrime
    numerator_Y := hy
    denominator_Y := hdy
    numerator_S := hns
    denominator_S := hds
    numerator_T := hnt
    denominator_T := hdt
  }⟩⟩
  intro i
  exact linear_relation_contact_order_one _ _ _ _ _ B.U B.V W.W B.relPrime
    B.U_omits B.V_omits W.omits (W.node i)
end
end Front6969_4
end
section
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 900000
namespace Front6969_4
open Front6969 Finset
open P2_4 (Bank)
open K1_11 (V J)
open P0_7 (countRow gradeRow count grade contactRow V_affine rational_fee)
open P1_4 (dims_5_16_10 dims_4_15_8 jets_4_16_10 jets_3_15_8 dims_5_8_7 dims_4_7_4 jets_4_8_7 jets_3_7_4 dims_5_10_16 dims_4_8_15 jets_4_10_16 jets_3_8_15 dims_5_11_10 dims_4_9_8 jets_4_11_10 jets_3_9_8 dims_5_8_6 dims_4_6_3 jets_4_8_6 jets_3_6_3 dims_5_7_8 dims_4_4_7 jets_4_7_8 jets_3_4_7 dims_5_6_8 dims_4_3_6 jets_4_6_8 jets_3_3_6 dims_4_3_5 jets_3_3_5)
open P2_4 (dims_5_10_11 jets_4_10_11 dims_4_8_9 jets_3_8_9 dims_4_5_3 jets_3_5_3)
theorem bank_surplus (b : Bank) (h H e N : ℕ) (hlo : originalFloor b ≤ h)
    (hmax : h ≤ heightCap) (hH : H + e = h) (hN : N + e = blockLength) :
    N * (J 4 b.s b.t - J 3 (b.s - b.dS) (b.t - b.dT)) +
      V (weightedCutoff - 131071 - H) 131071 4 (b.s - b.dS) (b.t - b.dT) <
      V weightedCutoff 131071 5 b.s b.t := by
  apply Research6969.ProfileBanks.RankFour.rank_four_bank_surplus b h H e N _ hmax hH hN
  cases b <;> exact hlo

def chartRate (b : Bank) : ℚ := (131073 / 48669 : ℚ) * b.M
def chartFee (b : Bank) : ℚ := b.E * chartRate b ^ 2
abbrev tariff := Research6969.ProfileBanks.RankFour.tariff
theorem bank_fee (b : Bank) : (b.zeroFee : ℚ) + 5 * chartFee b ≤ tariff :=
  Research6969.ProfileBanks.RankFour.bank_fee b
theorem bank_rate_ge (b : Bank) : (262144 : ℚ) ≤ chartRate b :=
  Research6969.ProfileBanks.RankFour.bank_rate_ge b
end Front6969_4
end
section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
namespace Front6969_4
noncomputable section
open MvPolynomial
open Front6969 (heightCap)
open P2_4 (Bank ContactData Multipliers)
open K1_11 (V J filtered filteredMul filteredMul_injective mem_filteredMul_range_iff
  sourceWeights sourceBounds source_filtered_finrank sourceToJet contactWeight)
open K1_11 (exists_kernel_outside)
open P2_4 (LocalSpace localMultiply local_finrank)
abbrev Source (F : Type*) [Field F] (b : Bank) :=
  filtered (F := F) (sourceWeights 131071) (sourceBounds weightedCutoff 5 b.s b.t)
variable {F : Type*} [Field F]
  {N : ℕ} {L : MvPolynomial (Fin 5) F} {b : Bank} {H : ℕ} (D : ContactData N L b)
private def nodeMap (i : Fin N) : Source F b →ₗ[F] LocalSpace D i :=
  (LinearMap.range (localMultiply D i)).mkQ.comp
    (sourceToJet weightedCutoff 131071 5 b.s b.t 3 (D.x i) (D.first i) (D.firstSlope i) (D.second i) (D.secondSlope i))
private theorem localContact (Q : Source F b) (i : Fin N) (hi : nodeMap D i Q = 0) :
    ∃ R : Multipliers F b, D.shifted i Q.val - D.shifted i L * R.val ∈
      restrictWeightedOrder contactWeight 4 := by
  have hmem : sourceToJet weightedCutoff 131071 5 b.s b.t 3 (D.x i)
      (D.first i) (D.firstSlope i) (D.second i) (D.secondSlope i) Q ∈
      LinearMap.range (localMultiply D i) :=
    (Submodule.Quotient.mk_eq_zero _).mp hi
  obtain ⟨R, hR⟩ := hmem
  refine ⟨R, (weightedTruncation_eq_zero_iff _ _ _).mp ?_⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hR).symm
theorem exists_quotient_source (h e : ℕ) (hmin : originalFloor b ≤ h) (hmax : h ≤ heightCap)
    (hH : H + e = h) (hN : N + e = 262144)
    (hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = b.relationBounds H j) :
    ∃ Q : Source F b, ¬ L ∣ Q.val ∧ ∀ i, ∃ R : Multipliers F b,
      D.shifted i Q.val - D.shifted i L * R.val ∈ restrictWeightedOrder contactWeight 4 := by
  have hupper : H ≤ 33735 := by
    have hh : h ≤ 33735 := hmax
    omega
  have hD : weightedCutoff = 718959 := rfl
  have hfit : ∀ i, b.relationBounds H i ≤ sourceBounds weightedCutoff 5 b.s b.t i := by
    intro i
    cases b <;> fin_cases i <;>
      simp [Bank.relationBounds, Bank.s, Bank.t, Bank.dS, Bank.dT, sourceBounds, hD] <;> omega
  have hshift : (fun i => sourceBounds weightedCutoff 5 b.s b.t i - b.relationBounds H i) =
      sourceBounds (weightedCutoff - 131071 - H) 4 (b.s-b.dS) (b.t-b.dT) := by
    funext i
    fin_cases i <;> simp [sourceBounds, Bank.relationBounds, hD]
    omega
  let mult := filteredMul (sourceWeights 131071) (sourceBounds weightedCutoff 5 b.s b.t)
    (b.relationBounds H) L D.nonzero hdeg hfit
  have hdimMult : Module.finrank F (LinearMap.range mult) =
      V (weightedCutoff - 131071 - H) 131071 4 (b.s-b.dS) (b.t-b.dT) := by
    rw [LinearMap.finrank_range_of_inj
      (filteredMul_injective _ _ _ L D.nonzero hdeg hfit), hshift, source_filtered_finrank]
  have hdimLocal : Module.finrank F (∀ i : Fin N, LocalSpace D i) =
      N * (J 4 b.s b.t - J 3 (b.s-b.dS) (b.t-b.dT)) := by
    let (i : Fin N) : Module.Free F (LocalSpace D i) := Module.Free.of_divisionRing F _
    rw [Module.finrank_pi_fintype]
    simp only [local_finrank D, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hdim : Module.finrank F (∀ i : Fin N, LocalSpace D i) +
      Module.finrank F (LinearMap.range mult) < Module.finrank F (Source F b) := by
    rw [hdimLocal, hdimMult, source_filtered_finrank]
    exact bank_surplus b h H e N hmin hmax hH hN
  let : Module F (∀ i : Fin N, LocalSpace D i) := Pi.module _ _ _
  have hk := exists_kernel_outside (G := ∀ i : Fin N, LocalSpace D i)
    (LinearMap.pi (nodeMap D)) (LinearMap.range mult) hdim
  obtain ⟨Q, hQ, hnot⟩ := hk
  exact ⟨Q, (mem_filteredMul_range_iff _ _ _ L D.nonzero hdeg hfit Q).not.mp hnot,
    fun i => localContact D Q i (congrFun hQ i)⟩
end
end Front6969_4
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Front6969_4
noncomputable section
open Front6969 FrobeniusLocator MvPolynomial
open P2_4 (Bank Puncture ContactInput)
open K1_11 (contactWeight contactDecoderImages decoder_contact_composition contactDecoderImages_vanish
  decoder_eval_degree eq_zero_of_many_contacts decoder_contact_multiplicity decoderImages
  sourceWeights mem_filtered correctOn nodes_injective indexedSupport indexedSupport_card
  scalarWeightY scalarWeightYS scalarWeightT scalarEliminant
  scalarEliminant_ne_zero polynomialView_source_coefficients clearedEval_weight_bound
  polynomialView scalarEliminant_annihilates)
open K1_11 (scalar_total_weight_le)
open P2_4 (asContactData bank_cancel contact_order_one_mem)
variable {u : Words} {deleted : Finset I} {P : Puncture deleted} {b : Bank} {H : ℕ}
    (D : ContactInput u P b H)
private theorem relation_on_support (hH : H ≤ 33735) (Q Q' : Polynomial K)
    (hQ : Q.natDegree ≤ 131071) (hQ' : Q'.natDegree ≤ 131071)
    (s t : K) (S : Finset (Fin P.N)) (hS : agreement ≤ S.card) (hc : correctOn u P Q Q' s t S) :
    aeval (decoderImages Q Q' s t) D.L = 0 := by
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 1
  · intro i hi
    have ho := contact_order_one_mem contactWeight (D.shifted i D.L) (D.order_one i)
    have hd := pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder Polynomial.C ho
      (contactDecoderImages_vanish _ _ _ _ _ s t Q Q' (hc i hi).1 (hc i hi).2)
    change (Polynomial.X-Polynomial.C (P.nodes i))^1 ∣
      aeval (contactDecoderImages (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
        (u 0 (P.index i)^p) (u 1 (P.index i)^p) s t Q Q') (D.shifted i D.L) at hd
    rwa [ContactInput.shifted, decoder_contact_composition] at hd
  · have hdeg : D.L.weightedTotalDegree (sourceWeights 131071 0) ≤ 131071+H :=
      le_of_eq (D.degrees 0)
    have hd := decoder_eval_degree 131071 (131071+H) D.L hdeg Q Q' hQ hQ' s t
    change 179740 ≤ S.card at hS
    omega
theorem exists_two_decoder_source (h : ℕ) (hmin : originalFloor b ≤ h) (hmax : h ≤ heightCap)
    (hH : H + deleted.card = h) :
    ∃ G : Source K b, ¬ D.L ∣ G.val ∧
      ∀ (Q Q' : Polynomial K), Q.natDegree ≤ 131071 → Q'.natDegree ≤ 131071 →
        ∀ (s t : K) (S : Finset (Fin P.N)), agreement ≤ S.card → correctOn u P Q Q' s t S →
          aeval (decoderImages Q Q' s t) G.val = 0 := by
  obtain ⟨G, hnot, hnode⟩ := exists_quotient_source (asContactData D) h deleted.card hmin hmax hH P.size D.degrees
  refine ⟨G, hnot, ?_⟩
  intro Q Q' hQ hQ' s t S hS hc
  have hmax' : h ≤ 33735 := hmax
  have hrel := relation_on_support D (by omega) Q Q' hQ hQ' s t S hS hc
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 4
  · intro i hi
    obtain ⟨R, hR⟩ := hnode i
    exact decoder_contact_multiplicity 4 _ _ _ _ _ s t Q Q' G.val D.L R.val
      (hc i hi).1 (hc i hi).2 hrel hR
  · have hd := decoder_eval_degree 131071 weightedCutoff G.val
      ((mem_filtered _ _ _).mp G.property 0) Q Q' hQ hQ' s t
    change _ ≤ 718959 at hd
    change 179740 ≤ S.card at hS
    omega
def SupportAt {u : Words} {deleted : Finset I} {Γ : Finset K} (F : Marks u deleted Γ) : Prop :=
  ∀ γ (hγ : γ ∈ Γ), agreement ≤ (F.mark γ hγ).support.card
def selectMarks {u : Words} {T : TwoActive u} {R : Relation T} (D : Reduction u T R)
    {Γ : Finset K} (hΓ : BadFamily u Γ) (hn : ∀ γ ∈ Γ, Normal u γ) :
    { F : Marks u (fixedNodes R) Γ // SupportAt F } := by
  let M := fun γ hγ => Classical.choice (Front6969.bad_mark u Γ hΓ γ hγ)
  refine ⟨{
    mark := M
    survives := fun γ hγ i hi hid => D.deleted_error γ (hn γ hγ) (M γ hγ) i hid
      ((M γ hγ).hits i hi)
  }, fun γ hγ => (M γ hγ).agreement⟩
theorem exists_annihilator {u : Words} {deleted : Finset I} {P : Puncture deleted}
    {b : Bank} {H : ℕ} (C : ContactInput u P b H) (h : ℕ)
    (hmin : originalFloor b ≤ h) (hmax : h ≤ heightCap) (hH : H + deleted.card = h)
    {Γ : Finset K} (F : Marks u deleted Γ) (hF : SupportAt F) : Nonempty (Annihilator F b) := by
  obtain ⟨G, hG, hgAnn⟩ := exists_two_decoder_source C h hmin hmax hH
  let Q := scalarEliminant 5 G.val C.numerator C.denominator
  have hne : Q ≠ 0 := scalarEliminant_ne_zero weightedCutoff 131071 5 b.s b.t
    G.val C.L G.property hG C.numerator C.denominator C.denominator_ne C.linear C.primitive
  obtain ⟨hY, hS, hT⟩ := polynomialView_source_coefficients weightedCutoff 131071 5 b.s b.t G.val G.property
  have hy : Q.weightedTotalDegree scalarWeightY ≤ 5 := by
    simpa [Q, scalarEliminant] using
      clearedEval_weight_bound scalarWeightY 5 5 1 1 0 (polynomialView G.val)
        C.numerator C.denominator (by simpa using hY) C.numerator_Y C.denominator_Y (by omega)
  have hs : Q.weightedTotalDegree scalarWeightYS ≤ b.a := by
    simpa [Q, scalarEliminant, Bank.a] using
      clearedEval_weight_bound scalarWeightYS 5 b.s 0 b.dS b.dS (polynomialView G.val)
        C.numerator C.denominator (by simpa using hS) C.numerator_S C.denominator_S (by omega)
  have ht : Q.weightedTotalDegree scalarWeightT ≤ b.b := by
    simpa [Q, scalarEliminant, Bank.b] using
      clearedEval_weight_bound scalarWeightT 5 b.t 1 b.dT (b.dT-1) (polynomialView G.val)
        C.numerator C.denominator (by simpa using hT) C.numerator_T C.denominator_T (bank_cancel b).ge
  refine ⟨⟨Q, hne, hy, hs, ht, scalar_total_weight_le Q b.a b.b hs ht, ?_⟩⟩
  intro γ hγ
  let M := F.mark γ hγ
  let S := indexedSupport P M.support
  have hS : agreement ≤ S.card := by
    rw [indexedSupport_card P M.support (F.survives γ hγ)]
    exact hF γ hγ
  have hd := mark_degree M
  have hd' : (M.decoder.map twist).natDegree ≤ 131071 :=
    Polynomial.natDegree_map_le.trans hd
  have hcorrect := correctOn_mark P M
  have hmax' : h ≤ 33735 := hmax
  have hrel := relation_on_support C (by omega) _ _ hd hd' γ (γ ^ p) S hS hcorrect
  exact scalarEliminant_annihilates weightedCutoff 131071 5 b.s b.t G.val C.L G.property
    C.numerator C.denominator C.linear _ _ γ (γ^p) hrel
    (hgAnn _ _ hd hd' γ (γ^p) S hS hcorrect)
end
end Front6969_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Front6969_4
noncomputable section
open Front6969 MvPolynomial
open P2_4 (Bank Puncture nodeCut)
open scoped BigOperators
open K1_11 (indexedSupport mem_indexedSupport indexedSupport_card)
open K1_11 (ncard_inter_filter surface_count_with_terminal)
variable {u : Words} {deleted : Finset I} {P : Puncture deleted}
  {Γ Λ : Finset K} {F : Marks u deleted Γ} {b : Bank}
private theorem chart_agreements (chart : TaylorChart u P F b Λ) (hF : SupportAt F) (γ : K) (hγ : γ ∈ Λ) :
    179740 ≤ {i | MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0}.ncard := by
  let M := F.mark γ (chart.subset hγ)
  have hsub : (indexedSupport P M.support : Set (Fin P.N)) ⊆
      {i | MvPolynomial.eval (chart.point γ) (nodeCut u P chart.numerator chart.denominator i) = 0} := by
    intro i hi
    exact (chart_cut_iff chart γ hγ i).mpr (M.hits _ ((mem_indexedSupport P M.support i).mp hi))
  have h := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, indexedSupport_card P M.support (F.survives γ (chart.subset hγ))] at h
  exact (hF γ (chart.subset hγ)).trans h
theorem chart_count {u : Words} {deleted : Finset I} {P : Puncture deleted}
    {Γ Λ : Finset K} {F : Marks u deleted Γ} {b : Bank}
    (chart : TaylorChart u P F b Λ) (hF : SupportAt F) : (Λ.card : ℚ) ≤ chartFee b := by
  classical
  let S := Λ.image chart.point
  let R : ℚ := chartRate b
  have hRbig : (262144 : ℚ) ≤ R := bank_rate_ge b
  have hone : (1 : ℚ) ≤ 262144 := by
    exact_mod_cast (show (1 : ℕ) ≤ 262144 by decide)
  have hR : 1 ≤ R := hone.trans hRbig
  have hN : P.N ≤ 262144 := by have := P.size; omega
  have hinj : Set.InjOn chart.point (Λ : Set K) := by
    intro γ hγ δ hδ he
    apply (algebraMap K Frac).injective
    exact (chart.slope γ hγ).symm.trans ((congrFun he 1).trans (chart.slope δ hδ))
  have hcard : S.card = Λ.card := Finset.card_image_of_injOn hinj
  let cuts := nodeCut u P chart.numerator chart.denominator
  have hratio (m : ℕ) (hm : m < 131072) :
      (((Fintype.card (Fin P.N) - m) * b.M : ℕ) : ℚ) ≤ R * ((179740 - m : ℕ) : ℚ) := by
    have hnat : (P.N - m) * 48669 ≤ 131073 * (179740 - m) := by omega
    have hrat : ((P.N - m : ℕ) : ℚ) * 48669 ≤ 131073 * ((179740 - m : ℕ) : ℚ) := by
      exact_mod_cast hnat
    have hh : ((P.N - m : ℕ) : ℚ) ≤ (131073/48669 : ℚ) * ((179740 - m : ℕ) : ℚ) := by
      linarith
    rw [Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (b.M : ℚ))).trans_eq (by dsimp [R, chartRate]; ring)
  rw [← hcard]
  refine surface_count_with_terminal chart.equation chart.denominator chart.equation_ne cuts
    (L := 131072) (A := 179740) (by decide) chart.equation_degree chart.cut_degree hR hratio S
    (fun x hx => ?_) (fun x hx => ?_) (fun J hJ => ?_)
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨chart.on_equation γ hγ, chart.regular γ hγ⟩
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact chart_agreements chart hF γ hγ
  · let W := Λ.filter fun γ => chart.point γ ∈ zeroLocus Frac J
    have hW : W ⊆ Λ := Finset.filter_subset _ _
    have hWimage : W.image chart.point = S.filter (· ∈ zeroLocus Frac J) := by
      ext x
      simp only [W, S, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨γ, ⟨hγ, hJγ⟩, rfl⟩
        exact ⟨⟨γ, hγ, rfl⟩, hJγ⟩
      · rintro ⟨⟨γ, hγ, rfl⟩, hJγ⟩
        exact ⟨γ, ⟨hγ, hJγ⟩, rfl⟩
    have hbound := chart_persistent chart J W hW (fun γ hγ => (Finset.mem_filter.mp hγ).2) hJ
    rw [ncard_inter_filter, ← hWimage, Finset.card_image_of_injOn (hinj.mono hW)]
    exact (by exact_mod_cast hbound.trans hN : (W.card : ℚ) ≤ 262144).trans hRbig
end
end Front6969_4
end
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Front6969_4
open Front6969
open P2_4 (Bank)
def c1 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T),
    Nonempty (IndependentLift R)
def c2 : Prop :=
  ∀ (u : Words) (T : TwoActive u) (R : Relation T) (D : Reduction u T R),
    T.height ≤ heightCap → ∀ (A : IndependentLift R),
      Nonempty (ReducedPair D A)
private theorem card_from_cover (b : Bank) (Γ exceptional : Finset K)
    (charts : Fin 5 → Finset K) (hfee : exceptional.card ≤ b.zeroFee)
    (hcover : ∀ γ ∈ Γ, γ ∈ exceptional ∨ ∃ j, γ ∈ charts j)
    (hcharts : ∀ j, ((charts j).card : ℚ) ≤ chartFee b) :
    Γ.card ≤ tariff := by
  classical
  have hsub : Γ ⊆ exceptional ∪ Finset.univ.biUnion charts := by
    intro γ hγ
    exact Finset.mem_union.mpr ((hcover γ hγ).imp id (fun ⟨j, hj⟩ =>
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩))
  have hcount := (Finset.card_le_card hsub).trans
    (Finset.card_union_le _ _ |>.trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hbound : (Γ.card : ℚ) ≤ b.zeroFee + 5 * chartFee b := by
    calc
      (Γ.card : ℚ) ≤ (exceptional.card : ℚ) + ∑ j : Fin 5, ((charts j).card : ℚ) := by
        exact_mod_cast hcount
      _ ≤ (b.zeroFee : ℚ) + ∑ _j : Fin 5, chartFee b := by
        exact add_le_add (by exact_mod_cast hfee) (Finset.sum_le_sum fun j _ => hcharts j)
      _ = _ := by simp
  have hcap := hbound.trans (bank_fee b)
  exact_mod_cast hcap
theorem of_children (h1 : c1) (h2 : c2) : Front6969.c4 := by
  intro u hu T R D _ hr Γ hΓ hn
  classical
  have hmax := relation_height_le hu T
  obtain ⟨A⟩ := h1 u hu T R
  obtain ⟨B⟩ := h2 u T R D hmax A
  let P := K1_11.nativePuncture (fixedNodes R)
  let F := selectMarks D hΓ hn
  obtain ⟨b, hfloor, ⟨C⟩⟩ := contact_input B hr hmax P
  obtain ⟨Q⟩ := exists_annihilator C T.height hfloor hmax D.height_eq F.val F.property
  obtain ⟨exceptional, charts, hfee, hcover, hcharts⟩ := chart_cover P Q
  refine card_from_cover b Γ exceptional charts hfee hcover fun j => ?_
  rcases hcharts j with he | chart
  · simp only [he, Finset.card_empty, Nat.cast_zero]
    unfold chartFee
    positivity
  · exact chart_count (Classical.choice chart) F.property
end Front6969_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000
namespace Front6969_4_1
noncomputable section
open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark Front6969
open K1_11_1 (Seeds PlaneField planeSlice planeStack graph rank_graph mulVec_map)
open K1_11_1 (syndrome_degree graph_slice_map graph_stack_map certificate_kernel)
private theorem first_slice_nullity (u : Words) (T : TwoActive u) :
    GenericLayer.genericNullity
      (Strata.parameterRelation p node (u 0) (u 1) k T.height) = 1 :=
  Strata.generic_relation_line_of_level p node (u 0) (u 1)
    k T.a T.b T.c T.top T.degreeSum T.ab (T.active.trans_lt T.inactive)
    ((show 1 ≤ t by decide).trans_lt T.inactive) T.level
theorem plane_first_slice_nullity (u : Words) (T : TwoActive u)
    (hh : T.height ≤ heightCap) :
    Module.finrank (PlaneField K) (LinearMap.ker
      ((planeSlice p node (u 0) (u 1) k T.height).map
        (algebraMap (Seeds K) (PlaneField K))).mulVecLin) = 1 := by
  let A := planeSlice p node (u 0) (u 1) k T.height
  have hdeg (j : Fin (k - T.height)) (b : Fin 2 × Fin (T.height + 1)) :
      (A j b).degreeOf 0 ≤ if b.1 = 0 then 1 else 0 :=
    syndrome_degree p node (u 0) (u 1) b.1 0 _
  have hsize : T.height + 1 < p :=
    (Nat.add_le_add_right hh 1).trans_lt (by decide)
  have he := rank_graph p (by decide) hsize A hdeg
  change (A.map (algebraMap (Seeds K) (PlaneField K))).rank =
    ((planeSlice p node (u 0) (u 1) k T.height).map _).rank at he
  rw [graph_slice_map] at he
  have hn := GenericLayer.rank_add_nullity
    (Strata.parameterRelation p node (u 0) (u 1) k T.height)
  rw [first_slice_nullity u T] at hn
  apply GenericRank.nullity_one_of_rank
  change (A.map (algebraMap (Seeds K) (PlaneField K))).rank + 1 = _
  rw [he]
  exact hn
theorem plane_stack_degree (u : Words) (b : Fin 2 × Fin L) (j : Fin (t + 1))
    (i : Fin 2) :
    (planeStack p node (u 0) (u 1) L t b j).degreeOf i ≤
      if b.1 = i then 1 else 0 :=
  syndrome_degree p node (u 0) (u 1) b.1 i _
theorem plane_stack_rank (u : Words) :
    ((planeStack p node (u 0) (u 1) L t).map
      (algebraMap (Seeds K) (PlaneField K))).rank = stackRank u := by
  let A := planeStack p node (u 0) (u 1) L t
  have hdeg (j : Fin (t + 1)) (b : Fin 2 × Fin L) :
      (A.transpose j b).degreeOf 0 ≤ if b.1 = 0 then 1 else 0 :=
    plane_stack_degree u b j 0
  have he := rank_graph p (by decide) (by decide) A.transpose hdeg
  rw [Matrix.transpose_map, Matrix.transpose_map, Matrix.rank_transpose, Matrix.rank_transpose] at he
  change ((planeStack p node (u 0) (u 1) L t).map _).rank =
    ((planeStack p node (u 0) (u 1) L t).map _).rank at he
  rw [graph_stack_map] at he
  exact he
theorem graph_content (u : Words) (T : TwoActive u) (R : Relation T)
    (Q : Fin 2 × Fin (T.height + 1) → Seeds K)
    (hQ : (planeSlice p node (u 0) (u 1) k T.height).mulVec Q = 0)
    (hgraph : (fun j => graph p (Q j)) ≠ 0) :
    ∃ c : (Polynomial K), c ≠ 0 ∧ ∀ j, graph p (Q j) = c * R.coefficients j := by
  classical
  let f := algebraMap (Polynomial K) Frac
  let M := (Strata.parameterRelation p node (u 0) (u 1) k T.height).map f
  let E := fun j => f (R.coefficients j)
  let V := fun j => f (graph p (Q j))
  obtain ⟨a, ha⟩ := (PrimitiveVector.primitive_iff_bezout R.coefficients).mp R.primitive
  have hinj := IsFractionRing.injective (Polynomial K) Frac
  have hE : E ≠ 0 := by
    intro he
    have hzero (j : Fin 2 × Fin (T.height + 1)) : R.coefficients j = 0 :=
      hinj ((congrFun he j).trans (map_zero f).symm)
    simp only [hzero, mul_zero, Finset.sum_const_zero, zero_ne_one] at ha
  have hME : M.mulVec E = 0 :=
    certificate_kernel p node (u 0) (u 1) IRSProfile.domain.injective
      Native.native_domain_fixed k k T.height
      (by rw [IRSProfile.card_index]; decide) R
  have hMV : M.mulVec V = 0 := by
    change ((Strata.parameterRelation p node (u 0) (u 1) k T.height).map f).mulVec V = 0
    rw [← graph_slice_map]
    change ((planeSlice p node (u 0) (u 1) k T.height).map
      (f.comp (graph p).toRingHom)).mulVec
      (fun j => (f.comp (graph p).toRingHom) (Q j)) = 0
    rw [mulVec_map, hQ]
    funext j
    rw [Pi.zero_apply, map_zero, Pi.zero_apply]
  obtain ⟨b, hb⟩ := GenericRank.kernel_line_of_finrank M
    (first_slice_nullity u T) E hE hME V hMV
  let c := ∑ j, a j * graph p (Q j)
  have hc : f c = b := by
    have hbe := congrArg f ha
    simp only [map_sum, map_mul, map_one] at hbe
    simp only [c, map_sum, map_mul]
    have he (j : Fin 2 × Fin (T.height + 1)) : f (graph p (Q j)) = b * f (R.coefficients j) :=
      congrFun hb j
    simp_rw [he, mul_left_comm (f (a _)) b, ← Finset.mul_sum, hbe, mul_one]
  have he (j : Fin 2 × Fin (T.height + 1)) : graph p (Q j) = c * R.coefficients j := by
    apply hinj
    rw [map_mul, hc]
    exact congrFun hb j
  refine ⟨c, ?_, he⟩
  intro hzero
  apply hgraph
  funext j
  rw [he, hzero, zero_mul, Pi.zero_apply]
end
end Front6969_4_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace Front6969_4_1
noncomputable section
open Polynomial Matrix FrobeniusLocator Front6969
open K1_11_1 (Seeds PlaneField planePair planeStack plane_generator shifts_annihilate
  blockDegree degreeOf_coordinate graph graph_ne_zero seedPositions intoFive intoFive_omitted
  intoFive_height intoFive_seed_degree intoFive_primitive graph_intoFive)
private theorem graph_pair {F : Type} [Field F] {h : ℕ} (q : ℕ)
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (a : Fin 2 × Fin (h + 1) → (Polynomial F))
    (c : (Polynomial F)) (hQ : ∀ j, graph q (Q j) = c * a j) (b : Fin 2) :
    (planePair Q b).map (graph q).toRingHom =
      Polynomial.C c * Principal.assemble (fun j => a (b, j)) := by
  rw [planePair, Principal.map_assemble]
  change Principal.assemble (fun j => graph q (Q (b, j))) = _
  simp only [hQ, Principal.assemble, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.C_mul_monomial]
theorem proof : Front6969_4.c1 := by
  intro u front T R
  classical
  let h := T.height
  let s := L - h
  have hbal : L + h + nullity u = t + 1 := relation_height_balance T
  have hhi : h ≤ heightCap := relation_height_le front T
  have hL : h < L := hhi.trans_lt (by decide)
  have hsum : h + s = L := by omega
  have hs : 0 < s := by omega
  have hsL : s ≤ L := Nat.sub_le _ _
  have hSlice := plane_first_slice_nullity u T hhi
  obtain ⟨Q, hQne, hQ, hPrim⟩ := plane_generator _ (by rw [hSlice]; decide)
  let M := planeStack p node (u 0) (u 1) L t
  let W := K1_6.shifts (planePair Q) L s
  have hRank : (M.map (algebraMap (Seeds K) (PlaneField K))).rank + s = 2 * L := by
    rw [plane_stack_rank u, actual_stackRank u]
    omega
  have hker : W.transpose * M = 0 :=
    shifts_annihilate p node (u 0) (u 1) h L s t hsum Q hQ
  obtain ⟨hMP, hattain⟩ := K1_11_1_1.proof K h L s Q hsum hs hQne hPrim
  have hprod (b i : Fin 2) : s * blockDegree Q b i ≤ if b = i then h else L := by
    by_cases hd : blockDegree Q b i = 0
    · simp only [hd, Nat.mul_zero, Nat.zero_le]
    obtain ⟨rows, hdet⟩ := hattain b i (Nat.pos_of_ne_zero hd)
    have hb := K1_11_1_2.proof K L (t + 1) s M W hs hsL hRank hker
      (plane_stack_degree u) hMP b i rows
    rw [hdet] at hb
    simpa only [show L - s = h by omega] using hb
  have hgraph : (fun j => graph p (Q j)) ≠ 0 := by
    intro hz
    apply hQne
    funext j
    change Q j = 0
    by_contra hne
    obtain ⟨b, i⟩ := j
    have hbound : s * blockDegree Q b 0 ≤ L := by
      apply (hprod b 0).trans
      split_ifs
      · exact hL.le
      · exact le_rfl
    have hone : 1 ≤ s := hs
    have hdeg : (Q (b, i)).degreeOf 0 ≤ L :=
      (degreeOf_coordinate Q b 0 i).trans
        ((by simpa only [one_mul] using Nat.mul_le_mul_right (blockDegree Q b 0) hone :
          blockDegree Q b 0 ≤ s * blockDegree Q b 0).trans hbound)
    exact graph_ne_zero p (by decide) _ hne (hdeg.trans_lt (by decide)) (congrFun hz (b, i))
  obtain ⟨c, hc, hgraphQ⟩ := graph_content u T R Q hQ hgraph
  have hdegree (b i : Fin 2) :
      s * (intoFive (planePair Q b)).degreeOf (seedPositions i) ≤
        if b = i then h else L :=
    (Nat.mul_le_mul_left s (intoFive_seed_degree Q b i)).trans (hprod b i)
  refine ⟨{
    U := intoFive (planePair Q 0)
    V := intoFive (planePair Q 1)
    U_omits := ⟨intoFive_omitted Q 0 1 (Or.inl rfl), intoFive_omitted Q 0 2 (Or.inr rfl)⟩
    V_omits := ⟨intoFive_omitted Q 1 1 (Or.inl rfl), intoFive_omitted Q 1 2 (Or.inr rfl)⟩
    heights := ⟨intoFive_height Q 0, intoFive_height Q 1⟩
    bounds := ?_
    primitive := intoFive_primitive Q hPrim
    content := c
    content_ne := hc
    graphU := (graph_intoFive p (planePair Q 0)).trans (graph_pair p Q R.coefficients c hgraphQ 0)
    graphV := (graph_intoFive p (planePair Q 1)).trans (graph_pair p Q R.coefficients c hgraphQ 1)
  }⟩
  have hseedS : seedPositions 0 = 3 := rfl
  have hseedT : seedPositions 1 = 4 := rfl
  exact ⟨by simpa only [hseedS, ite_true] using hdegree 0 0,
    by simpa only [hseedT, ite_eq_right (show (0 : Fin 2) ≠ 1 by decide)] using hdegree 0 1,
    by simpa only [hseedS, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)] using hdegree 1 0,
    by simpa only [hseedT, ite_true] using hdegree 1 1⟩
end
end Front6969_4_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
namespace Front6969_4_2
noncomputable section
open Front6969 MvPolynomial
open FrobeniusLocator (locator locator_monic)
open K1_11_2 (graph OmitsMessages)
open K1_11_2_1 (graph_natDegree)
open K1_11_2_1 (divide_plane planeLocator degreeOf_le_of_dvd omits_of_dvd native_p_pos seedRelPrime parameter_only)
open Front6969_4 (degree_lt_of_product)
private theorem seed_degree_lt {h d : ℕ} (hmax : h ≤ heightCap)
    (hd : (L - h) * d ≤ L) : d < p := by
  have hh : h ≤ 33735 := hmax
  have hd' : d < 4 := degree_lt_of_product _ _ 4 _ hd (by
    change 48668 < (48668 - h) * 4
    omega)
  exact hd'.trans_le (by change 4 ≤ 2130706433; decide)
private theorem reduced_relPrime {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (A : Front6969_4.IndependentLift R)
    {U V : MvPolynomial (Fin 5) K} (hU : U ≠ 0) (hUo : OmitsMessages U)
    (hS : U.degreeOf 3 < p) (hAdU : U ∣ A.U) (hAdV : V ∣ A.V)
    (hgU : graph p U = Polynomial.C A.content * D.U)
    (hgV : graph p V = Polynomial.C A.content * D.V) :
    IsRelPrime U V := by
  intro d hdU hdV
  let f := (Polynomial.mapRingHom K1_8.seedInclusion).comp (graph (F := K) p).toRingHom
  have hfdU : f d ∣ extendSeed (Polynomial.C A.content * D.U) := by
    rw [← hgU]
    exact _root_.map_dvd f hdU
  have hfdV : f d ∣ extendSeed (Polynomial.C A.content * D.V) := by
    rw [← hgV]
    exact _root_.map_dvd f hdV
  have hu := seedRelPrime D.coprime A.content_ne hfdU hfdV
  have hx := Polynomial.natDegree_eq_zero_of_isUnit hu
  change ((graph p d).map K1_8.seedInclusion).natDegree = 0 at hx
  have hdo := omits_of_dvd hU hUo hdU
  rw [Polynomial.natDegree_map_eq_of_injective K1_8.seedInclusion_injective,
    graph_natDegree p native_p_pos d hdo
      ((degreeOf_le_of_dvd hU hdU 3).trans_lt hS)] at hx
  obtain ⟨q, rfl⟩ := parameter_only hdo hx
  exact (A.primitive q (hdU.trans hAdU) (hdV.trans hAdV)).map
    (rename (![3, 4] : Fin 2 → Fin 5))
theorem proof : Front6969_4.c2 := by
  intro u T R D hmax A
  have hhcap : T.height ≤ 33735 := hmax
  have hh : T.height ≤ L := hhcap.trans (by decide : 33735 ≤ 48668)
  have hASU := seed_degree_lt hmax (A.bounds.1.trans hh)
  have hASV := seed_degree_lt hmax A.bounds.2.2.1
  obtain ⟨U, hfU, hU, hgU⟩ := divide_plane (fixedNodes R) A.U D.U A.content D.U_ne
    A.content_ne A.U_omits hASU (A.graphU.trans (by simp only [D.U_factor, P0.liftX, K1.liftX]))
  obtain ⟨V, hfV, hV, hgV⟩ := divide_plane (fixedNodes R) A.V D.V A.content D.V_ne
    A.content_ne A.V_omits hASV (A.graphV.trans (by simp only [D.V_factor, P0.liftX, K1.liftX]))
  have hAdU : U ∣ A.U := hfU.symm ▸ dvd_mul_left U (planeLocator (fixedNodes R))
  have hAdV : V ∣ A.V := hfV.symm ▸ dvd_mul_left V (planeLocator (fixedNodes R))
  have hl : planeLocator (fixedNodes R) ≠ 0 := by
    simpa only [planeLocator, EmbeddingLike.map_ne_zero_iff] using
      ((locator_monic node (fixedNodes R)).map
        (MvPolynomial.C : K →+* MvPolynomial (Fin 4) K)).ne_zero
  have hAu : A.U ≠ 0 := hfU.symm ▸ mul_ne_zero hl hU
  have hAv : A.V ≠ 0 := hfV.symm ▸ mul_ne_zero hl hV
  have hUo := omits_of_dvd hAu A.U_omits hAdU
  have hVo := omits_of_dvd hAv A.V_omits hAdV
  have hUS := (degreeOf_le_of_dvd hAu hAdU 3).trans_lt hASU
  have hVS := (degreeOf_le_of_dvd hAv hAdV 3).trans_lt hASV
  refine ⟨⟨U, V, hUo, hVo, hU, hV, hAdU, hAdV,
    reduced_relPrime D A hU hUo hUS hAdU hAdV hgU hgV, ?_, hgU, hgV⟩⟩
  rw [← graph_natDegree p native_p_pos U hUo hUS,
    ← graph_natDegree p native_p_pos V hVo hVS, hgU, hgV,
    Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr A.content_ne) D.U_ne,
    Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr A.content_ne) D.V_ne,
    Polynomial.natDegree_C, zero_add, zero_add, D.max_degree]
end
end Front6969_4_2
end

end Merged_Front6969Rank4
end Z6969Source2223
