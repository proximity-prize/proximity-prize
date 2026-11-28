import ProximityPrize.SubmissionLower.Z6970ExpandedCappedArithmetic
import ProximityPrize.SubmissionLower.Z6970H2307BankBase
import ProximityPrize.SubmissionLower.Z6969Pack0838
import ProximityPrize.SubmissionLower.FrontBranch3
import ProximityPrize.SubmissionLower.Shared50ShapeRankBase
import ProximityPrize.SubmissionLower.Z6970ExpandedOrderH2307
import ProximityPrize.SubmissionLower.Z6970H2307SlopeShape
import ProximityPrize.SubmissionLower.Z6970H2307SlopeArithmetic
import Mathlib.RingTheory.Localization.Integer

-- Source: ProximityPrize.SubmissionLower.Low6969RetainedCount
section Z6969Source2398
set_option autoImplicit true
set_option Elab.async false

-- merged module R6960Low6969RetainedBank
section Merged_R6960Low6969RetainedBank
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Low6969RetainedCut
noncomputable section
open P3 (I K node)
open K1_13 (Row Geom Shape shape InBox atJet extend OrderAt embed indexDegree)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open Low6969Prices (Messages SmallFactor ActiveFits primaryBox primaryCutoff layerWidth layerNeed
  TrueWeightLE LayerBudget)
open scoped Polynomial BigOperators
open P0_9_3 (exists_fresh specialization_bounds sum_by_layer)
variable {Γ : Finset K} {s : K → (Polynomial K)}
theorem Bank.proper_cut (D : Bank Γ s) {f : Row 4} (hf : SmallFactor f)
    (hchar : f.degreeOf 3 < K1.p) {l : ℕ} (hp : 0 < l) (hl : l ≤ D.availability f) :
    Low6969Prices.ProperCut f Γ s l := by
  obtain ⟨T,hT,P,hrow,hk,divF,exactF⟩ := D.extremal f (hp.trans_le hl)
  obtain ⟨hb,hw,ht⟩ := D.bounds T hT P hrow
  have hP : P ≠ 0 := fun he => exactF (he ▸ dvd_zero _)
  obtain ⟨Q,hproper,hbQ,hwQ,haQ,hord⟩ := exists_divided_cut (H := 1) (k := levelOrder T) (l := l) hP one_ne_zero
    hf.1 hf.2.1 hchar isRelPrime_one_right (by omega) hb hw ht (by simp) divF exactF
  refine ⟨Q,hproper,⟨hbQ.1.trans (Nat.sub_le _ _),hbQ.2.1.trans (Nat.sub_le _ _),
    hbQ.2.2.trans (Nat.sub_le _ _)⟩,hwQ,haQ,?_⟩
  intro γ hγ
  exact hord _ (by simp [atJet]) (D.order T hT _ hrow γ hγ)
def sumShape {ι : Type*} (z : Finset ι) (x : ι → Shape) : Shape :=
  ⟨∑ i∈z, (x i).b, ∑ i∈z, (x i).j, ∑ i∈z, (x i).t⟩
theorem shape_of_product {ι : Type*} (z : Finset ι) (f : ι → Row 4) (hn : ∀ i∈z, f i ≠ 0) :
    shape (∏ i∈z, f i) = sumShape z (fun i => shape (f i)) := by
  have hb := MvPolynomial.weightedTotalDegree_prod (1 : Fin 4 → ℕ) z f hn
  have hj := MvPolynomial.weightedTotalDegree_prod Fin.val z f hn
  have ht := MvPolynomial.weightedTotalDegree_prod (Pi.single (3 : Fin 4) 1) z f hn
  simp only [MvPolynomial.weightedTotalDegree_one] at hb
  simp only [← K1_13_1.indexDegree_eq] at hj
  simp only [MvPolynomial.weightedTotalDegree_piSingle] at ht
  change Shape.mk _ _ _ = Shape.mk _ _ _
  rw [hb,hj,ht]
  rfl
theorem Bank.companion_price_floor {w : I → K} {n : ℕ} (D : Bank Γ s) (hm : Messages w Γ s)
    (f : Fin n → Row 4) (hf : ∀ i, SmallFactor (f i))
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) (z : Finset (Fin n))
    (hz : ∀ j∈z, D.availability (f j)=0) {i : Fin n} (hi : i∉z)
    {l active : ℕ} (hpos : 0 < l) (hl : l ≤ D.availability (f i))
    (ha : ActiveFits (f i) active) (hchar : (f i).degreeOf 3 < K1.p)
    (Δ : Finset K) (hsub : Δ ⊆ Γ) (hon : ∀ γ∈Δ, K1_13.OnFactor (f i) (extend (s γ)))
    (hoff : ∀ γ∈Δ, atJet (∏ j∈z, f j) (extend (s γ)) ≠ 0) :
    ∀ h : Shape, InBox h (shape (∏ j∈z, f j)) → Δ.card ≤ contractedPrice (shape (f i)) h l active := by
  classical
  obtain ⟨T,hT,P,hrow,hk,divF,exactF⟩ := D.extremal (f i) (hpos.trans_le hl)
  obtain ⟨hb,hw,ht⟩ := D.bounds T hT P hrow
  have hP : P ≠ 0 := fun he => exactF (he ▸ dvd_zero _)
  have hH : (∏ j∈z, f j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (hf j).1.ne_zero
  have divH := retained_power_dvd z f (fun j => (hf j).1) hdiff (k := levelOrder T) (P := P) (by
    intro j hj
    have hd := D.available (f j) T hT P hrow
    simpa only [hz j hj,Nat.sub_zero] using hd)
  exact price_of_witness_floor (hm.mono hsub) (hf i) ha hchar hon hoff hP hH
    (prime_off_product z f (fun j => (hf j).1) hdiff hi) hpos (by omega) hb hw ht
    (fun γ hγ => D.order T hT P hrow γ (hsub hγ)) divH divF exactF
theorem Bank.companion_price {w : I → K} {n : ℕ} (D : Bank Γ s) (hm : Messages w Γ s)
    (f : Fin n → Row 4) (hf : ∀ i, SmallFactor (f i))
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) (z : Finset (Fin n))
    (hz : ∀ j∈z, D.availability (f j)=0) {i : Fin n} (hi : i∉z)
    {l active : ℕ} (hpos : 0 < l) (hl : l ≤ D.availability (f i))
    (ha : ActiveFits (f i) active) (hchar : (f i).degreeOf 3 < K1.p)
    (Δ : Finset K) (hsub : Δ ⊆ Γ) (hon : ∀ γ∈Δ, K1_13.OnFactor (f i) (extend (s γ)))
    (hoff : ∀ γ∈Δ, atJet (∏ j∈z, f j) (extend (s γ)) ≠ 0) :
    Δ.card ≤ contractedPrice (shape (f i)) (shape (∏ j∈z, f j)) l active :=
  D.companion_price_floor hm f hf hdiff z hz hi hpos hl ha hchar Δ hsub hon hoff
    _ ⟨le_rfl,le_rfl,le_rfl⟩
end
end Low6969RetainedCut

end Merged_R6960Low6969RetainedBank

end Z6969Source2398

-- Source: ProximityPrize.SubmissionLower.Low6969SharedRational
section Z6969Source2400
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 800000
namespace Low6969SharedRational
noncomputable section

open K1_13 (Geom Row)
open K1_13_3 (symbolAt)
open K1_13_6 (GenericField GeoField genericCoeffs toGeneric)
open Polynomial MvPolynomial
open scoped BigOperators nonZeroDivisors

abbrev FractionJet := MvPolynomial (Fin 4) GenericField

def toFraction (P : Row 4) : FractionJet :=
  MvPolynomial.map (algebraMap (Polynomial Geom) GenericField) P

def toGeometric : FractionJet →+* K1_13_6.GeoJets :=
  MvPolynomial.map (algebraMap GenericField GeoField)

theorem fraction_geometric (P : Row 4) :
    toGeometric (toFraction P) = toGeneric P := by
  simp [toGeometric,toFraction,toGeneric,genericCoeffs,MvPolynomial.map_map]

theorem fraction_injective : Function.Injective toFraction :=
  MvPolynomial.map_injective _ (IsFractionRing.injective (Polynomial Geom) _)

theorem support_fraction (P : Row 4) : (toFraction P).support = P.support :=
  MvPolynomial.support_map_of_injective P (IsFractionRing.injective (Polynomial Geom) GenericField)

private theorem primitive_relation {ι : Type*} (s : Finset ι) (c : ι → (Polynomial Geom))
    (e : ι → Row 4) (h : ∑ i ∈ s, c i • e i = 0)
    (hne : ∃ i ∈ s, c i ≠ 0) (x : Geom) :
    ∃ b : ι → (Polynomial Geom), (∑ i ∈ s, b i • e i = 0) ∧ ∃ i ∈ s, (b i).eval x ≠ 0 := by
  classical
  let S := s.filter fun i => c i ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi, hc⟩ := hne
    exact ⟨i,Finset.mem_filter.mpr ⟨hi,hc⟩⟩
  obtain ⟨i,hi,hmin⟩ := S.exists_min_image (fun i => (c i).rootMultiplicity x) hS
  let k := (c i).rootMultiplicity x
  let D : (Polynomial Geom) := (Polynomial.X - Polynomial.C x)^k
  have hd : D ≠ 0 := pow_ne_zero _ (Polynomial.X_sub_C_ne_zero x)
  have hdiv (j : ι) : D ∣ c j ∨ j ∉ s := by
    by_cases hzero : c j = 0
    · exact Or.inl (hzero.symm ▸ dvd_zero D)
    · by_cases hs : j ∈ s
      · exact Or.inl ((pow_dvd_pow _ (hmin j (Finset.mem_filter.mpr ⟨hs,hzero⟩))).trans
          (Polynomial.pow_rootMultiplicity_dvd _ _))
      · exact Or.inr hs
  have hclear (j : ι) : ∃ b : (Polynomial Geom), j ∈ s → c j = D*b := by
    rcases hdiv j with ⟨b,hb⟩ | hno
    · exact ⟨b,fun _ => hb⟩
    · exact ⟨0,fun hyes => (hno hyes).elim⟩
  choose b hb using hclear
  have hii := Finset.mem_filter.mp hi
  have hsum : D • (∑ j ∈ s, b j • e j) = 0 := by
    rw [Finset.smul_sum]
    refine (Finset.sum_congr rfl fun j hj => ?_).trans h
    rw [smul_smul,← hb j hj]
  have hz : ∑ j ∈ s, b j • e j = 0 := (smul_eq_zero.mp hsum).resolve_left hd
  refine ⟨b,hz,i,hii.1,?_⟩
  intro he
  obtain ⟨P,hP⟩ := (Polynomial.dvd_iff_isRoot).mpr he
  have hnot : ¬ (Polynomial.X - Polynomial.C x)^(k+1) ∣ c i :=
    Polynomial.pow_rootMultiplicity_not_dvd hii.2 x
  apply hnot
  refine ⟨P, ?_⟩
  calc
    c i = D * b i := hb i hii.1
    _ = _ := by rw [hP]; dsimp only [D]; rw [pow_succ,mul_assoc]


/-- Specialization independence implies function-field independence. -/
theorem independent_fraction {ι : Type*} (x : Geom) (e : ι → Row 4)
    (he : LinearIndependent Geom (fun i => symbolAt x (e i))) :
    LinearIndependent GenericField (fun i => toFraction (e i)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s a ha i hi
  let R := (Polynomial Geom)
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples (R⁰) s a
  have hd0 : (d : R) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have hc (j : ι) : ∃ c : R, j ∈ s →
      algebraMap R GenericField c = algebraMap R GenericField d * a j := by
    by_cases hm : j ∈ s
    · obtain ⟨c,hc⟩ := hd j hm
      exact ⟨c,fun _ => hc.trans (Algebra.smul_def _ _)⟩
    · exact ⟨0,fun hj => (hm hj).elim⟩
  choose c hc using hc
  have hcleared : ∑ j ∈ s, c j • e j = 0 := by
    apply fraction_injective
    unfold toFraction
    simp only [map_sum,map_zero]
    calc
      _ = ∑ j ∈ s, (algebraMap R GenericField d * a j) •
          MvPolynomial.map (algebraMap R GenericField) (e j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have heq := hc j hj
        change algebraMap (Polynomial Geom) GenericField (c j) = _ at heq
        simp only [← MvPolynomial.C_mul', map_mul,MvPolynomial.map_C,heq]
        rw [mul_assoc]
      _ = (algebraMap R GenericField d) • ∑ j ∈ s, a j • toFraction (e j) := by
        rw [Finset.smul_sum]
        simp only [smul_smul, toFraction]
        rfl
      _ = 0 := by rw [ha,smul_zero]
  by_contra ha0
  have hc0 : c i ≠ 0 := by
    intro hz
    have heC := hc i hi
    rw [hz,map_zero] at heC
    have hNZ : algebraMap R GenericField d ≠ 0 := fun hz =>
      hd0 (IsFractionRing.injective R GenericField (hz.trans (map_zero _).symm))
    exact (mul_ne_zero hNZ ha0) heC.symm
  obtain ⟨b,hb,j,hj,hjx⟩ := primitive_relation s c e hcleared ⟨i,hi,hc0⟩ x
  have hx : ∑ j ∈ s, (b j).eval x • symbolAt x (e j) = 0 := by
    have hs := congrArg (symbolAt x) hb
    simp only [map_sum,map_zero,← MvPolynomial.C_mul',map_mul] at hs
    change (∑ j ∈ s, (evalRingHom x) (b j) • symbolAt x (e j)) = 0
    simpa only [symbolAt, MvPolynomial.map_C, MvPolynomial.C_mul'] using hs
  exact hjx (linearIndependent_iff'.mp he s (fun j => (b j).eval x) hx j hj)

theorem clear_denominators (R : FractionJet) :
    ∃ (d : (Polynomial Geom)) (Q : Row 4), d ≠ 0 ∧ Q.support = R.support ∧
      toFraction Q = MvPolynomial.C (algebraMap (Polynomial Geom) GenericField d) * R := by
  classical
  let M := nonZeroDivisors ((Polynomial Geom))
  let d := IsLocalization.commonDenom M R.support R.coeff
  let num := IsLocalization.integerMultiple M R.support R.coeff
  let Q : Row 4 := ∑ a : ↥R.support, MvPolynomial.monomial a.val (num a)
  have hd : (d : (Polynomial Geom)) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hi : algebraMap (Polynomial Geom) GenericField (d : (Polynomial Geom)) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericField)).mpr hd
  have hQ : toFraction Q = MvPolynomial.C (algebraMap (Polynomial Geom) GenericField d) * R := by
    unfold toFraction
    ext m
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, Q, MvPolynomial.coeff_sum]
    by_cases hm : m ∈ R.support
    · let a : ↥R.support := ⟨m, hm⟩
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
      · have hn := IsLocalization.map_integerMultiple M R.support R.coeff a
        change algebraMap (Polynomial Geom) GenericField (num a) = (d : (Polynomial Geom)) • R.coeff a.val at hn
        rw [Algebra.smul_def] at hn
        simpa [a] using hn
      · intro b _ hba
        have hb : b.val ≠ m := fun h => hba (Subtype.ext h)
        simp [MvPolynomial.coeff_monomial, hb]
    · have hz : R.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
      have hz' : (∑ a : ↥R.support,
          (MvPolynomial.monomial a.val (num a) : Row 4).coeff m) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        have ha : a.val ≠ m := fun h => hm (h ▸ a.property)
        simp [MvPolynomial.coeff_monomial, ha]
      rw [hz', hz, map_zero, mul_zero]
  refine ⟨d, Q, hd, ?_, hQ⟩
  rw [← support_fraction Q, hQ]
  ext m
  simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, hi]

end
end Low6969SharedRational
end Z6969Source2400

-- Source: ProximityPrize.SubmissionLower.Low6969SharedPersistent
section Z6969Source2401
set_option autoImplicit true
set_option Elab.async false

namespace Low6969SharedPersistent
noncomputable section

open P3 (K)
open K1_13 (Geom Row extend atJet shape InBox OrderAt)
open K1_13_6 (GeoJets toGeneric)
open K1_13_6_1_2 (hassePartial multiOrder VanishesTo hasse_inBox hasse_atJet_eq_zero map_hassePartial)
open MvPolynomial Polynomial

/-- Include every admissible-width row that vanishes at the marked messages. -/
def vanishing (Γ : Finset K) (s : K → (Polynomial K)) : Submodule Geom (Row 4) where
  carrier := {P | P.totalDegree ≤ 4024 ∧ ∀ γ ∈ Γ, atJet P (extend (s γ)) = 0}
  zero_mem' := ⟨by simp,fun _ _ => by simp [atJet]⟩
  add_mem' := by
    intro p q hp hq
    exact ⟨(totalDegree_add p q).trans (max_le hp.1 hq.1),fun γ hγ => by
      simp only [atJet, map_add]
      change atJet p (extend (s γ)) + atJet q (extend (s γ)) = 0
      rw [hp.2 γ hγ,hq.2 γ hγ,add_zero]⟩
  smul_mem' := by
    intro a p hp
    refine ⟨(totalDegree_smul_le a p).trans hp.1,fun γ hγ => ?_⟩
    change (MvPolynomial.eval _) (a • p) = 0
    rw [Algebra.smul_def, map_mul]
    change _ * atJet p (extend (s γ)) = 0
    rw [hp.2 γ hγ,mul_zero]

def Persistent (Γ : Finset K) (s : K → (Polynomial K)) (P : Ideal GeoJets) : Prop :=
  ∀ R ∈ vanishing Γ s, toGeneric R ∈ P

/-- Select one row for a finite set of nonpersistent surfaces. -/
theorem common_avoider (Γ : Finset K) (s : K → (Polynomial K)) (surfaces : Finset (Ideal GeoJets))
    (hZ : ∀ P ∈ surfaces, ¬ Persistent Γ s P) :
    ∃ R ∈ vanishing Γ s, ∀ P ∈ surfaces, toGeneric R ∉ P := by
  classical
  let M := vanishing Γ s
  let forbidden (P : surfaces) : Submodule Geom M :=
    ((P.val.comap (MvPolynomial.map K1_13_6.genericCoeffs) : Ideal (Row 4)).restrictScalars Geom).comap M.subtype
  have hproper (P : surfaces) : forbidden P ≠ ⊤ := by
    intro h
    apply hZ P.val P.property
    intro R hR
    have hmem : (⟨R,hR⟩ : M) ∈ forbidden P := h ▸ Submodule.mem_top
    exact hmem
  obtain ⟨R,hR⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (ι := ↥surfaces) (K := Geom) (M := M) forbidden hproper
  exact ⟨R.val,R.property,fun P hP => hR ⟨P,hP⟩⟩

theorem derivative_mem {Γ s P R n} (hp : Persistent Γ s P)
    (hb : InBox (shape R) Low6969Prices.primaryBox)
    (ho : ∀ γ ∈ Γ, OrderAt R (extend (s γ)) n)
    (a : Fin 4 →₀ ℕ) (ha : multiOrder a < n) :
    hassePartial a (toGeneric R) ∈ P := by
  unfold toGeneric
  rw [← map_hassePartial]
  exact hp _ ⟨(hasse_inBox a hb).1,fun γ hγ => hasse_atJet_eq_zero ha (ho γ hγ)⟩

theorem local_order {Γ s R n} {P : Ideal GeoJets} [P.IsPrime] (hp : Persistent Γ s P)
    (hb : InBox (shape R) Low6969Prices.primaryBox)
    (ho : ∀ γ ∈ Γ, OrderAt R (extend (s γ)) n) : VanishesTo P (toGeneric R) n :=
  K1_13_6_1_2_2.vanishesTo_of_hasse _ P n (fun a ha => derivative_mem hp hb ho a ha)

end
end Low6969SharedPersistent
end Z6969Source2401

-- Source: ProximityPrize.SubmissionLower.Low6969ShapeGate
section Z6969Source2402
set_option autoImplicit true
set_option Elab.async false
set_option autoImplicit false

namespace Low6969ShapeGate

open K1_13_2 (cappedCount)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeExponents mem_cumulativeColumns)
open ExpandedColumns6970 (jetColumns jetExponents)
open ExpandedColumns6970 (gradeCap)
open scoped BigOperators
open Finset
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open ExpandedColumns6970 (sumGrade sumOld)

def fits (r : ℕ) (m : JetExp) : Prop :=
  m.weight gradeWeight ≤ r*62 ∧ m.weight oldWeight ≤ r*28 ∧ m 3 ≤ r*7

noncomputable instance (r : ℕ) (m : JetExp) : Decidable (fits r m) := by unfold fits; infer_instance

noncomputable def width (r : ℕ) : ℕ := (jetColumns.filter (fits r)).card

def bound (r : ℕ) : ℕ := min 4025 (r*62+1)
def start (k : ℕ) : ℕ := 16*k
def stop (r k : ℕ) : ℕ := min (bound r) (start (k+1))
def chunks (r : ℕ) : ℕ := (bound r + 15) / 16

def padGrade (r k : ℕ) : ℕ :=
  min (gradeCap (start k)) (gradeCap (stop r k-1))

def index (r : ℕ) : ℕ := min 1679 (r*28)
def top (r : ℕ) : ℕ := min 500 (r*7)

private theorem grade_le {r k q : ℕ} (hlo : start k ≤ q) (hhi : q < stop r k) :
    padGrade r k ≤ gradeCap q := by
  unfold padGrade gradeCap
  have hcap := ExpandedShape6970.cap_antitone (show q ≤ stop r k-1 by omega)
  exact le_min ((min_le_left _ _).trans ((min_le_left _ _).trans hlo))
    ((min_le_right _ _).trans ((min_le_right _ _).trans hcap))

private noncomputable def grid (r : ℕ) : Finset (Σ _ : ℕ, ℕ × JetExp) :=
  (range (chunks r)).sigma fun k => (Ico (start k) (stop r k)).product
    (cappedColumns (padGrade r k) (index r) (top r))

private noncomputable def pad (r : ℕ) (x : Σ _ : ℕ, ℕ × JetExp) : JetExp :=
  x.2.2 + Finsupp.single 0 (x.2.1 - padGrade r x.1)

private theorem pad_spec {r : ℕ} {x : Σ _ : ℕ, ℕ × JetExp} (hx : x ∈ grid r) :
    (pad r x).weight gradeWeight = x.2.1 ∧
    (pad r x).weight oldWeight = x.2.2.weight oldWeight ∧
    (∀ i : Fin 4, i ≠ 0 → pad r x i = x.2.2 i) := by
  obtain ⟨k,q,m⟩ := x
  have hm := (mem_cappedColumns.mp (mem_product.mp (mem_sigma.mp hx).2).2).1
  have hm' := (mem_cumulativeColumns.mp hm).1
  have hg : m.weight gradeWeight = padGrade r k := by exact_mod_cast hm'
  obtain ⟨hl,hh⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hx).2).1
  change start k ≤ q at hl
  change q < stop r k at hh
  have hq := (grade_le hl hh).trans (min_le_left _ _ : gradeCap q ≤ q)
  have h0 : pad r ⟨k,q,m⟩ 0 = m 0 + (q-padGrade r k) := by simp [pad]
  have hsucc (i : Fin 4) (hi : i ≠ 0) : pad r ⟨k,q,m⟩ i = m i := by
    simp [pad,Finsupp.single_eq_of_ne hi]
  refine ⟨?_, ?_, hsucc⟩
  · change (pad r ⟨k,q,m⟩).weight gradeWeight = q
    rw [sumGrade, h0, hsucc 1 (by decide), hsucc 2 (by decide), hsucc 3 (by decide)]
    rw [sumGrade] at hg
    omega
  · rw [sumOld,sumOld,hsucc 1 (by decide),hsucc 2 (by decide),hsucc 3 (by decide)]

private theorem map_mem {r : ℕ} {x : Σ _ : ℕ, ℕ × JetExp} (hx : x ∈ grid r) :
    pad r x ∈ jetColumns.filter (fits r) := by
  obtain ⟨k,q,m⟩ := x
  obtain ⟨hl,hh⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hx).2).1
  obtain ⟨hj,ht⟩ := mem_cappedColumns.mp (mem_product.mp (mem_sigma.mp hx).2).2
  obtain ⟨hg,hi⟩ := mem_cumulativeColumns.mp hj
  obtain ⟨eB,eJ,eOther⟩ := pad_spec hx
  dsimp only at eB eJ eOther hl hh
  have hgrade : m.weight gradeWeight = padGrade r k := by exact_mod_cast hg
  have hindex : m.weight oldWeight ≤ index r := by exact_mod_cast hi
  have htop : m 3 ≤ top r := by exact_mod_cast ht
  have hD := (grade_le hl hh).trans (min_le_right _ _ : gradeCap q ≤ ExpandedTaper6970.cap q)
  have hb : q ≤ 4024 ∧ q ≤ r*62 := by
    unfold stop bound at hh
    omega
  apply Finset.mem_filter.mpr
  refine ⟨?_,⟨eB.trans_le hb.2,eJ.trans_le (hindex.trans (min_le_right _ _)),?_⟩⟩
  · apply ExpandedColumns6970.jetExponents_finite.mem_toFinset.mpr
    change (pad r ⟨k,q,m⟩).weight gradeWeight ≤ 4024 ∧
      (pad r ⟨k,q,m⟩).weight oldWeight ≤ 1679 ∧ _
    refine ⟨eB.trans_le hb.1,eJ.trans_le (hindex.trans (min_le_left _ _)),?_,?_⟩
    · rw [eOther 3 (by decide)]
      exact htop.trans (min_le_left _ _)
    rw [eB,eOther 1 (by decide),eOther 2 (by decide),eOther 3 (by decide)]
    rw [sumGrade] at hgrade
    omega
  · rw [eOther 3 (by decide)]
    exact htop.trans (min_le_right _ _)

private theorem pad_injective (r : ℕ) : Set.InjOn (pad r) (grid r : Set (Σ _ : ℕ, ℕ × JetExp)) := by
  intro x hx y hy hxy
  obtain ⟨k,q,m⟩ := x
  obtain ⟨k',q',m'⟩ := y
  obtain ⟨hlo,hhi⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hx).2).1
  obtain ⟨hlo',hhi'⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hy).2).1
  have eQ : q = q' := (pad_spec hx).1.symm.trans ((congrArg (fun e : JetExp => e.weight gradeWeight) hxy).trans (pad_spec hy).1)
  subst q'
  have eK : k = k' := by
    change q < stop r k at hhi
    change q < stop r k' at hhi'
    change start k ≤ q at hlo
    change start k' ≤ q at hlo'
    simp only [stop, start] at hhi hhi' hlo hlo'
    omega
  subst k'
  have em : m = m' := by
    apply add_right_cancel (b := Finsupp.single (0 : Fin 4) (q-padGrade r k))
    exact hxy
  subst m'
  rfl

def block (r k : ℕ) : ℤ :=
  ((stop r k-start k : ℕ) : ℤ) * cappedCount (padGrade r k) (index r) (top r)

def compute (r : ℕ) : ℤ := ∑ k ∈ range (chunks r), block r k

private theorem grid_eq (r : ℕ) : ((grid r).card : ℤ) = compute r := by
  unfold grid compute
  rw [card_sigma,Nat.cast_sum]
  apply sum_congr rfl
  intro k _
  change (((Ico (start k) (stop r k)).product
    (cappedColumns (padGrade r k) (index r) (top r))).card : ℤ) = block r k
  have hcard := Finset.card_product (Ico (start k) (stop r k))
    (cappedColumns (padGrade r k) (index r) (top r))
  change ((Ico (start k) (stop r k)).product
    (cappedColumns (padGrade r k) (index r) (top r))).card = _ at hcard
  rw [hcard, Nat.card_Ico, Nat.cast_mul, capped_card K1_13_2_2_2.proof]
  rfl

theorem width_ge (r : ℕ) : compute r ≤ (width r : ℤ) := by
  rw [← grid_eq]
  exact_mod_cast Finset.card_le_card_of_injOn (pad r) (fun _ h => map_mem h) (pad_injective r)

private theorem jet_count : jetColumns.card = Low6969Prices.symbolCount := by
  exact ExpandedShape6970.jet_count

private theorem width_le (r : ℕ) : width r ≤ Low6969Prices.symbolCount := by
  rw [← jet_count]
  exact card_le_card (filter_subset _ _)

private theorem width_full (r : ℕ) (hr : 72 ≤ r) : width r = Low6969Prices.symbolCount := by
  unfold width
  rw [filter_true_of_mem, jet_count]
  intro m hm
  have h : m ∈ jetExponents := ExpandedColumns6970.jetExponents_finite.mem_toFinset.mp hm
  unfold fits
  have ht : 3*m 3 ≤ m.weight oldWeight := by rw [sumOld]; omega
  exact ⟨h.1.trans (by omega), h.2.1.trans (by omega), by have hT := h.2.2.1; omega⟩

def intPrefix (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n+1 => intPrefix f n + f n

theorem intPrefix_eq (f : ℕ → ℤ) (n : ℕ) :
    intPrefix f n = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp [intPrefix]
  | succ n ih => rw [intPrefix,sum_range_succ,ih]

def fastRow (r : ℕ) : ℤ := intPrefix (block r) (chunks r)

theorem fastRow_eq (r : ℕ) : fastRow r = compute r := intPrefix_eq _ _

def rowLoss (i : ℕ) : ℤ := (Low6969Prices.symbolCount : ℤ) - fastRow (i+1)


def slopeCap : ℕ := 20942143446291

theorem rowLoss_eq (i : ℕ) : rowLoss i = ExpandedGate6970.H2307Slope.rowLoss i := by
  unfold rowLoss fastRow ExpandedGate6970.H2307Slope.rowLoss ExpandedGate6970.H2307Slope.dimLower
  congr 1
  rw [intPrefix_eq, Gate6966Cell.sumUpTo_eq]
  apply Finset.sum_congr rfl
  intro k _
  unfold block stop start padGrade index top ExpandedGate6970.H2307Slope.gradeCap
    ExpandedColumns6970.gradeCap ExpandedTaper6970.cap
  dsimp only [bound,start,stop]
  have capEq (d u c : ℕ) : K1_13_2.cappedCount (d : ℤ) (u : ℤ) (c : ℤ) =
      Gate6966Cell.cappedN d u c := Low6969GateCell.capped_eq d u c
  rw [capEq] <;> rfl

theorem computed_loss : intPrefix rowLoss 71 = slopeCap := by
  change intPrefix rowLoss 71 = (20942143446291 : ℤ)
  rw [intPrefix_eq, ← ExpandedGate6970.H2307Slope.exactMass, ExpandedGate6970.H2307Slope.mass,
    Gate6966Cell.sumUpTo_eq]
  apply Finset.sum_congr rfl
  intro i _
  simpa using rowLoss_eq i

theorem loss_bound (N : ℕ) :
    (∑ i ∈ range N, (Low6969Prices.symbolCount - width (i+1))) ≤ slopeCap := by
  let f : ℕ → ℕ := fun i => Low6969Prices.symbolCount - width (i+1)
  change (∑ i ∈ range N, f i) ≤ _
  have hzero (i : ℕ) (hi : 71 ≤ i) : f i = 0 := by
    dsimp [f]
    rw [width_full (i+1) (by omega),Nat.sub_self]
  rw [K1_13_8.sum_range_min N 71 hzero]
  refine (sum_le_sum_of_subset (range_mono (min_le_right N 71))).trans ?_
  have row (i : ℕ) : (f i : ℤ) ≤ rowLoss i := by
    unfold f rowLoss
    rw [Int.ofNat_sub (width_le _),fastRow_eq]
    exact sub_le_sub_left (width_ge (i+1)) _
  apply Int.ofNat_le.mp
  rw [Nat.cast_sum, ← computed_loss, intPrefix_eq]
  exact sum_le_sum fun i _ => row i


end Low6969ShapeGate
end Z6969Source2402

-- Source: ProximityPrize.SubmissionLower.Low6969VariableSelect
section Z6969Source2403
set_option autoImplicit true
set_option Elab.async false

-- merged module R6960Low6969SharedShapeRank
section Merged_R6960Low6969SharedShapeRank

set_option Elab.async false
set_option maxRecDepth 40000
set_option linter.style.haveILetI false
set_option maxHeartbeats 1500000
namespace Low6969SharedShapeRank
noncomputable section

open K1_13 (Geom Row extend shape InBox OrderAt)
open K1_13_6 (GenericField GeoField GeoJets toGeneric)
open K1_13_6_1_2 (hassePartial multiOrder taylorHom taylor_coeff)
open Low6969SharedRational
open Low6969SharedPersistent (Persistent derivative_mem)
open ExpandedColumns6970 (jetExponents jetColumns jet_card_eq)
open MvPolynomial Finset

def ambient : Submodule GenericField FractionJet :=
  restrictSupport GenericField jetExponents

instance : Module.Finite GenericField ambient :=
  restrictSupport_finite ExpandedColumns6970.jetExponents_finite

theorem ambient_dim : Module.finrank GenericField ambient = Low6969Prices.symbolCount := by
  have h : (jetColumns : Set _) = jetExponents := Set.Finite.coe_toFinset _
  rw [ambient,← h,finrank_restrictSupport_finset]
  exact ExpandedShape6970.jet_count

def cutoff (r : ℕ) : Submodule GenericField ambient :=
  (restrictSupport GenericField (↑(jetColumns.filter (Low6969ShapeGate.fits r)))).comap ambient.subtype

theorem cutoff_dim (r : ℕ) : Module.finrank GenericField (cutoff r) = Low6969ShapeGate.width r := by
  have hle : restrictSupport GenericField (↑(jetColumns.filter (Low6969ShapeGate.fits r))) ≤ ambient := by
    intro Q hQ m hm
    have hw := Finset.mem_filter.mp ((mem_restrictSupport_iff GenericField).mp hQ hm)
    exact ExpandedColumns6970.jetExponents_finite.mem_toFinset.mp hw.1
  change Module.finrank GenericField
    ((restrictSupport GenericField (↑(jetColumns.filter (Low6969ShapeGate.fits r)))).comap ambient.subtype) = _
  rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq,finrank_restrictSupport_finset]
  rfl

private theorem hasse_add (a : Fin 4 →₀ ℕ) (P Q : GeoJets) :
    hassePartial a (P+Q) = hassePartial a P + hassePartial a Q := by
  rw [← taylor_coeff, map_add, MvPolynomial.coeff_add, taylor_coeff,taylor_coeff]

private theorem hasse_zero (a : Fin 4 →₀ ℕ) :
    hassePartial a (0 : GeoJets) = 0 := by
  rw [← taylor_coeff, map_zero]
  simp

theorem hasse_C_mul (a : Fin 4 →₀ ℕ) (c : GeoField) (P : GeoJets) :
    hassePartial a (MvPolynomial.C c * P) = MvPolynomial.C c * hassePartial a P := by
  rw [← taylor_coeff, map_mul]
  have h : taylorHom (MvPolynomial.C c : GeoJets) = MvPolynomial.C (MvPolynomial.C c) := by
    simp [taylorHom]
  rw [h,coeff_C_mul,taylor_coeff]

def contactSpace (surfaces : Finset (Ideal GeoJets)) (r : ℕ) :
    Submodule GenericField ambient where
  carrier := {Q | ∀ P ∈ surfaces, ∀ a : Fin 4 →₀ ℕ, multiOrder a < r →
    hassePartial a (toGeometric Q.val) ∈ P}
  zero_mem' := by
    intro P _ a _
    change hassePartial a (toGeometric 0) ∈ P
    rw [map_zero,hasse_zero]
    exact P.zero_mem
  add_mem' := by
    intro a b ha hb P hP j hj
    change hassePartial j (toGeometric (a.val+b.val)) ∈ P
    rw [map_add,hasse_add]
    exact P.add_mem (ha P hP j hj) (hb P hP j hj)
  smul_mem' := by
    intro c a ha P hP j hj
    change hassePartial j (toGeometric (c • a.val)) ∈ P
    rw [← MvPolynomial.C_mul', map_mul, toGeometric, MvPolynomial.map_C, hasse_C_mul]
    exact P.mul_mem_left _ (ha P hP j hj)

open P3 (I K node)
open K1_13 (embed)
open ExpandedOrderH2307 (primaryCutoff layerWidth sourceRank requiredOrder)
open Low6969Prices (layerNeed)
open scoped BigOperators
open P0_9_3 (exists_fresh sum_by_layer)

theorem bank_layers {w Γ s} (hm : Low6969Prices.Messages w Γ s)
    (hceil : layerWidth * (layerNeed-1) < sourceRank)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P) :
    layerNeed ≤ ∑ i ∈ range (1+primaryCutoff/layerWidth),
      Module.finrank GenericField (contactSpace surfaces (i+1)) := by
  obtain ⟨x,hx,_⟩ := exists_fresh (fun _ : Fin 0 => (0 : Row 4))
  obtain ⟨r,hr,hbank⟩ := ExpandedOrderH2307.symbol_families w x (ExpandedOrderH2307.primary_rank w) hx
  let cost (i : ℕ) := Module.finrank GenericField (contactSpace surfaces (i+1))
  have hcost : ∀ T ≤ primaryCutoff, r T ≤ cost ((primaryCutoff-T)/layerWidth) := by
    intro T hT
    obtain ⟨e,he,hli⟩ := hbank T hT
    let V := contactSpace surfaces (requiredOrder T)
    letI : Module.Finite GenericField V :=
      @FiniteDimensional.finiteDimensional_submodule GenericField ↥ambient
        inferInstance inferInstance inferInstance inferInstance V
    let u (i : Fin (r T)) : V := ⟨
      ⟨toFraction (e i),fun m hm => (he i).2.2.1 m (support_fraction (e i) ▸ hm)⟩,
      fun P hP a ha => by
        rw [fraction_geometric]
        apply derivative_mem (hp P hP) (he i).1 _ a ha
        intro γ hγ
        obtain ⟨H,hH,hhits⟩ := hm.hits γ hγ
        exact ExpandedOrderH2307.order_of_contact w (e i) hT (he i).2.1 (he i).2.2.2
          (Polynomial.natDegree_map_le.trans (hm.degree γ hγ)) hH
          (fun i hi => by rw [Polynomial.eval_map,Polynomial.eval₂_hom,hhits i hi])⟩
    have hu : LinearIndependent GenericField u :=
      (independent_fraction x e hli).of_comp (ambient.subtype.comp V.subtype)
    have hcard := hu.fintype_card_le_finrank
    rw [Fintype.card_fin] at hcard
    exact hcard
  have hsum : sourceRank ≤ layerWidth * ∑ i ∈ range (1+primaryCutoff/layerWidth),cost i :=
    hr.trans ((sum_le_sum fun i hi => hcost i (Nat.le_of_lt_succ (mem_range.mp hi))).trans
      (sum_by_layer primaryCutoff layerWidth (by decide) cost))
  by_contra! hsmall
  exact (not_le_of_gt hceil) (hsum.trans (Nat.mul_le_mul_left _ (by
    dsimp only [cost]
    omega)))

/-- Select a small rational-function row of positive order on every persistent surface. -/
theorem exists_small {w Γ s} (hm : Low6969Prices.Messages w Γ s)
    (hceil : layerWidth * (layerNeed-1) < sourceRank)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P) :
    ∃ r : ℕ, 0<r ∧ ∃ Q : FractionJet, Q ≠ 0 ∧
      (∀ m ∈ Q.support, Low6969ShapeGate.fits r m) ∧
      ∀ P ∈ surfaces,∀ a : Fin 4 →₀ ℕ, multiOrder a < r → hassePartial a (toGeometric Q) ∈ P := by
  have hbank := bank_layers hm hceil surfaces hp
  let N := 1+primaryCutoff/layerWidth
  have hgate := Low6969ShapeGate.loss_bound N
  have h : (∑ i ∈ range N, (Module.finrank GenericField ambient -
      Module.finrank GenericField (cutoff (i+1)))) <
      ∑ i ∈ range N, Module.finrank GenericField (contactSpace surfaces (i+1)) := by
    simp only [ambient_dim,cutoff_dim]
    exact hgate.trans_lt ((by decide : Low6969ShapeGate.slopeCap < layerNeed).trans_le hbank)
  obtain ⟨i,_,Q,hQ,hm,ht⟩ :=
    @Shared50ShapeRankBase.exists_nonzero_overlap GenericField ↥ambient ℕ
      inferInstance inferInstance inferInstance inferInstance (range N)
      (fun i => contactSpace surfaces (i+1)) (fun i => cutoff (i+1)) h
  refine ⟨i+1,by omega,Q.val,fun hz => hQ (Subtype.ext hz),?_,hm⟩
  intro m hmem
  exact (Finset.mem_filter.mp ((mem_restrictSupport_iff GenericField).mp ht hmem)).2

theorem exists_polynomial {w Γ s} (hm : Low6969Prices.Messages w Γ s)
    (hceil : layerWidth * (layerNeed-1) < sourceRank)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P) :
    ∃ r : ℕ, 0<r ∧ ∃ Q : Row 4, Q ≠ 0 ∧
      (∀ m ∈ Q.support, Low6969ShapeGate.fits r m) ∧
      ∀ P ∈ surfaces,∀ a : Fin 4 →₀ ℕ, multiOrder a < r → hassePartial a (toGeneric Q) ∈ P := by
  obtain ⟨r,hr,U,hU,hs,ho⟩ := exists_small hm hceil surfaces hp
  obtain ⟨d,Q,_,hS,hQ⟩ := clear_denominators U
  refine ⟨r,hr,Q,?_,fun m hm => hs m (hS ▸ hm),?_⟩
  · intro hz
    apply hU
    rw [hz,MvPolynomial.support_zero] at hS
    exact MvPolynomial.support_eq_empty.mp hS.symm
  · intro P hP a ha
    rw [← fraction_geometric,hQ,map_mul,toGeometric,MvPolynomial.map_C,hasse_C_mul]
    exact P.mul_mem_left _ (ho P hP a ha)

end
end Low6969SharedShapeRank

end Merged_R6960Low6969SharedShapeRank

end Z6969Source2403

-- Source: ProximityPrize.SubmissionLower.Low6969SharedTallyOld
section Z6969Source2404
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
namespace Low6969SharedTallyOld
noncomputable section

open P3 (K)
open K1_13 (Row Shape shape InBox ceilDiv mixed32 chart)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength)
open K1_13_6_2_4 (oldEmbedding)
open Low6969GeometryCut (CutInput auxCurves32 auxPoints32 membershipDegree)
open Low6969GeometryCut_2 (Branch budget4 budget5)
open Low6969Prices (primaryBox taylorLength physicalPrice physicalPriceOld physicalPriceTilted
  physicalPriceActive surfaceNumerator32 tiltedSurface tiltedSurfaceActive)
open Low6969ActiveCycle (caps caps_chamber caps_active ordinary_doubled active_doubled ordinary_chart
  active_chart ordinary_budget active_budget activeRaw activeFamily old_section_active
  clip_bounds baseClip)
open Low48BentLattice (Chamber)
open Low48BentCycle (rawFamily capFamily mixedDegree)
open Low6969SharedTally (Data)
open scoped BigOperators Polynomial

open Low6969GeometryCut (le_ceil chargedPrice price_formula_old price_formula_tilted price_formula_active)

variable {Γ : Finset K} {s : K→(Polynomial K)} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}

def orderCost (D : Data Γ s f Q l S) (weight : Ideal GeoJets → ℕ) : ℕ :=
  ∑ b∈D.branches, weight b.surface * (b.weight*(D.points b).card)

private theorem eq_surface :
    surfaceNumerator32 (shape f).chamber primaryBox =
      min (budget4 (shape f).chamber) (budget5 (shape f).chamber) := rfl

private theorem four_budget (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime) :
    32*orderCost D weight ≤ budget4 (shape f).chamber := by
  have h := Low6969SharedCycleFour.bound_with_cut K1_13_6_2_3_1.proof
    (K1_13_6_2_3_2.of_children
      K1_13_6_2_3_2_1.proof K1_13_6_2_3_2_2.proof K1_13_6_2_3_2_3.proof
      K1_13_6_2_3_2_4.proof K1_13_6_2_3_2_5.proof K1_13_6_2_3_2_6.proof)
    (K1_13_6_2_3_3.of_children K1_13_6_2_3_3_1.proof
      (K1_13_6_2_3_3_2.of_children K1_13_6_2_3_3_2_1.proof K1_13_6_2_3_3_2_2.proof))
    f Q Q l input.small input.proper primaryBox ⟨by decide,by decide,by decide⟩ input.box weight
    D.branches D.points (D.four input) (fun b hb => ⟨b.base,hcut b hb⟩)
  have hh := (le_div_iff₀ (by norm_num : (0:ℚ)<32)).mp h
  apply (Nat.cast_le (α := ℚ)).mp
  simp only [orderCost,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat,mul_comm (32:ℚ)]
  simpa only [Nat.cast_mul,budget4] using hh

private theorem legacy_budget (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime) :
    32*orderCost D weight ≤ budget5 (shape f).chamber := by
  have h := Low6969SharedCycleLegacy.bound_with_weights f Q l input.small input.proper input.box
    weight D.branches D.points (D.five input) hcut
  apply (Nat.cast_le (α := ℚ)).mp
  simpa only [orderCost,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] using h

private theorem bent_budget (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime)
    (hguard : Low6969Prices.tiltedFits (shape f)) :
    (60*32)*orderCost D weight ≤ tiltedSurface (shape f).chamber primaryBox := by
  let p := (shape f).chamber
  have ht : 1 ≤ p.t := input.small.2.1
  have hC : ∀ i, Chamber (caps p i) :=
    caps_chamber (K1_13_7_1.shape_chamber f).1 ht hguard.1
  have h := Low6969SharedCycleBound.bound_with_cut (R := rawFamily (caps p)) (B := capFamily (caps p)) (ordinary_doubled (p := p)) f Q Q l input.small input.proper weight
    (Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩)
    (Low48BentCycle.old_section input.box)
    D.branches D.points (D.bent input (ordinary_chart ht)) (fun b hb => ⟨b.base,hcut b hb⟩)
  have hh := (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℚ) ≤ 60*32)).trans (ordinary_budget hC)
  apply (Nat.cast_le (α := ℚ)).mp
  simpa only [orderCost,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] using hh

private theorem active_charge (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime)
    (K : ℕ) (hK : Low6969Prices.ActiveFits f K) (hQ : Low6969Prices.ActiveFits Q 5192)
    (hguard : Low6969Prices.tiltedFits (shape f))
    (hactive : Low6969Prices.activeFitsPrice (shape f) K) :
    (60*32)*orderCost D weight ≤ tiltedSurfaceActive (shape f).chamber primaryBox K := by
  let p := (shape f).chamber
  have hfits := caps_active hguard hactive
  have hK' : baseClip p K ≤ p.b+p.j-K := (clip_bounds _ _ _).1
  have hsum : K+baseClip p K ≤ p.b+p.j := by
    have hc : 4 ≤ baseClip p K := hactive.2.1
    omega
  have h := Low6969SharedCycleBound.bound_with_cut (active_doubled hfits)
    f Q Q l input.small input.proper weight
    (old_section_active ⟨le_max_left _ _,le_rfl,le_rfl⟩ hK hsum)
    (old_section_active input.box hQ (by decide : 5192+498≤4024+1679))
    D.branches D.points (D.bent input (active_chart hK hactive))
    (fun b hb => ⟨b.base,hcut b hb⟩)
  have hh := (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℚ)≤60*32)).trans
    (active_budget (show 3≤p.t from hactive.1) hfits)
  apply (Nat.cast_le (α := ℚ)).mp
  simpa only [orderCost,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] using hh

def auxiliaryCap (x : Shape) : ℕ :=
  ceilDiv (82414*auxCurves32 x + 2*46352*auxPoints32 x) (32*46352)
def continuedCap (x : Shape) : ℕ :=
  ceilDiv ((82414+2*46352)*membershipDegree x) 46352
def surfaceCap (x : Shape) : ℕ :=
  2*(133378*x.b*primaryBox.b)

private theorem charge_le {x : Shape} {l a c d n scale budget O : ℕ}
    (hl : 0<l) (hs : 0<scale)
    (ha : a ≤ auxiliaryCap x) (hc : l*c ≤ continuedCap x)
    (hd : d ≤ surfaceCap x) (hn : l*n≤O) (hO : scale*O≤budget) :
    a+c+d+n ≤ chargedPrice x l scale budget := by
  have H : l*n ≤ ceilDiv budget scale :=
    hn.trans (le_ceil hs (by simpa [Nat.mul_comm] using hO))
  have hmain : c+n ≤ ceilDiv (ceilDiv budget scale+continuedCap x) l := by
    apply le_ceil hl
    rw [Nat.add_mul,Nat.mul_comm c l,Nat.mul_comm n l]
    omega
  unfold chargedPrice auxiliaryCap continuedCap surfaceCap at *
  omega

theorem physical_bound (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (K : ℕ) (hK : Low6969Prices.ActiveFits f K) (hQ : Low6969Prices.ActiveFits Q 5192)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime)
    {a c d n : ℕ} (ha : a ≤ auxiliaryCap (shape f))
    (hc : l*c ≤ continuedCap (shape f)) (hd : d ≤ surfaceCap (shape f))
    (hn : l*n≤orderCost D weight) : a+c+d+n ≤ physicalPrice (shape f) l K := by
  have hraw : 32*orderCost D weight ≤ surfaceNumerator32 (shape f).chamber primaryBox := by
    rw [eq_surface]
    exact le_min (four_budget D input weight hcut) (legacy_budget D input weight hcut)
  have hold : a+c+d+n ≤ physicalPriceOld (shape f) l := by
    rw [price_formula_old]
    exact charge_le input.positive (by decide) ha hc hd hn hraw
  by_cases ht : Low6969Prices.tiltedFits (shape f)
  · have hbent : a+c+d+n ≤ physicalPriceTilted (shape f) l := by
      rw [price_formula_tilted]
      exact charge_le input.positive (by decide) ha hc hd hn (bent_budget D input weight hcut ht)
    rw [physicalPrice,ite_eq_left ht]
    split_ifs with haa
    · refine le_min (le_min hold hbent) ?_
      rw [price_formula_active]
      exact charge_le input.positive (by decide) ha hc hd hn (active_charge D input weight hcut K hK hQ ht haa)
    · exact le_min hold hbent
  · simpa only [physicalPrice,ite_eq_right ht] using hold

theorem additive_le {x : Shape} {l a c d : ℕ} (hl : 0<l)
    (ha : a≤auxiliaryCap x) (hc : l*c≤continuedCap x) (hd : d≤surfaceCap x) :
    a+c+d ≤ Low6969SharedPrice.additiveBase x l := by
  have hc' : c≤ceilDiv (continuedCap x) l :=
    le_ceil hl (by simpa only [Nat.mul_comm] using hc)
  calc
    a+c+d ≤ auxiliaryCap x+ceilDiv (continuedCap x) l+surfaceCap x :=
      Nat.add_le_add (Nat.add_le_add ha hc') hd
    _ = _ := by
      unfold Low6969SharedPrice.additiveBase auxiliaryCap continuedCap surfaceCap
        auxCurves32 auxPoints32 membershipDegree
      simp only [show Low6969Prices.errors = 82414 by decide, show Low6969Prices.incidenceGap = 46352 by decide, show Low6969Prices.physicalDegree = 133378 by decide,
        Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      omega

end
end Low6969SharedTallyOld
end Z6969Source2404
