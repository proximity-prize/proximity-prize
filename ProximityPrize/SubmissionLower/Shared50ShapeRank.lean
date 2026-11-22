import ProximityPrize.SubmissionLower.Final50Order
import Mathlib.RingTheory.Localization.Integer
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import ProximityPrize.SubmissionLower.Final50ShapeGate

-- merged module Shared50Rational
section Merged_Shared50Rational
set_option Elab.async false
set_option maxHeartbeats 800000
namespace Shared50Rational
noncomputable section

open K1_13 (Geom Row)
open K1_13_3 (symbolAt)
open K1_13_6 (GenericField GeoField genericCoeffs toGeneric)
open Polynomial MvPolynomial
open scoped BigOperators nonZeroDivisors

abbrev FractionJet := MvPolynomial (Fin 4) GenericField

def toFraction (P : Row 4) : FractionJet :=
  MvPolynomial.map (algebraMap Geom[X] GenericField) P

def toGeometric : FractionJet →+* K1_13_6.GeoJets :=
  MvPolynomial.map (algebraMap GenericField GeoField)

theorem fraction_geometric (P : Row 4) :
    toGeometric (toFraction P) = toGeneric P := by
  simp [toGeometric,toFraction,toGeneric,genericCoeffs,MvPolynomial.map_map]

theorem fraction_injective : Function.Injective toFraction :=
  MvPolynomial.map_injective _ (IsFractionRing.injective Geom[X] _)

theorem support_fraction (P : Row 4) : (toFraction P).support = P.support :=
  MvPolynomial.support_map_of_injective P (IsFractionRing.injective Geom[X] GenericField)

private theorem primitive_relation {ι : Type*} (s : Finset ι) (c : ι → Geom[X])
    (e : ι → Row 4) (h : ∑ i ∈ s, c i • e i = 0)
    (hne : ∃ i ∈ s, c i ≠ 0) (x : Geom) :
    ∃ b : ι → Geom[X], (∑ i ∈ s, b i • e i = 0) ∧ ∃ i ∈ s, (b i).eval x ≠ 0 := by
  classical
  let S := s.filter fun i => c i ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi, hc⟩ := hne
    exact ⟨i,Finset.mem_filter.mpr ⟨hi,hc⟩⟩
  obtain ⟨i,hi,hmin⟩ := S.exists_min_image (fun i => (c i).rootMultiplicity x) hS
  let k := (c i).rootMultiplicity x
  let D : Geom[X] := (Polynomial.X - Polynomial.C x)^k
  have hd : D ≠ 0 := pow_ne_zero _ (Polynomial.X_sub_C_ne_zero x)
  have hdiv (j : ι) : D ∣ c j ∨ j ∉ s := by
    by_cases hzero : c j = 0
    · exact Or.inl (hzero.symm ▸ dvd_zero D)
    · by_cases hs : j ∈ s
      · exact Or.inl ((pow_dvd_pow _ (hmin j (Finset.mem_filter.mpr ⟨hs,hzero⟩))).trans
          (Polynomial.pow_rootMultiplicity_dvd _ _))
      · exact Or.inr hs
  have hclear (j : ι) : ∃ b : Geom[X], j ∈ s → c j = D*b := by
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
  let R := Geom[X]
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
        change algebraMap Geom[X] GenericField (c j) = _ at heq
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
    ∃ (d : Geom[X]) (Q : Row 4), d ≠ 0 ∧ Q.support = R.support ∧
      toFraction Q = MvPolynomial.C (algebraMap Geom[X] GenericField d) * R := by
  classical
  let M := nonZeroDivisors (Geom[X])
  let d := IsLocalization.commonDenom M R.support R.coeff
  let num := IsLocalization.integerMultiple M R.support R.coeff
  let Q : Row 4 := ∑ a : ↥R.support, MvPolynomial.monomial a.val (num a)
  have hd : (d : Geom[X]) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hi : algebraMap Geom[X] GenericField (d : Geom[X]) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective Geom[X] GenericField)).mpr hd
  have hQ : toFraction Q = MvPolynomial.C (algebraMap Geom[X] GenericField d) * R := by
    unfold toFraction
    ext m
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, Q, MvPolynomial.coeff_sum]
    by_cases hm : m ∈ R.support
    · let a : ↥R.support := ⟨m, hm⟩
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
      · have hn := IsLocalization.map_integerMultiple M R.support R.coeff a
        change algebraMap Geom[X] GenericField (num a) = (d : Geom[X]) • R.coeff a.val at hn
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

#print axioms clear_denominators
#print axioms independent_fraction
end
end Shared50Rational
end Merged_Shared50Rational

-- merged module Shared50Persistent
section Merged_Shared50Persistent
set_option Elab.async false

namespace Shared50Persistent
noncomputable section

open P3 (K)
open K1_13 (Geom Row extend atJet shape InBox OrderAt)
open K1_13_6 (GeoJets toGeneric)
open K1_13_6_1_2 (hassePartial multiOrder VanishesTo hasse_inBox hasse_atJet_eq_zero map_hassePartial)
open MvPolynomial Polynomial

/-- Include every admissible-width row that vanishes at the marked messages. -/
def vanishing (Γ : Finset K) (s : K → K[X]) : Submodule Geom (Row 4) where
  carrier := {P | P.totalDegree ≤ 4012 ∧ ∀ γ ∈ Γ, atJet P (extend (s γ)) = 0}
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

def Persistent (Γ : Finset K) (s : K → K[X]) (P : Ideal GeoJets) : Prop :=
  ∀ R ∈ vanishing Γ s, toGeneric R ∈ P

/-- Select one row for a finite set of nonpersistent surfaces. -/
theorem common_avoider (Γ : Finset K) (s : K → K[X]) (surfaces : Finset (Ideal GeoJets))
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
    (hb : InBox (shape R) Final50Price.primaryBox)
    (ho : ∀ γ ∈ Γ, OrderAt R (extend (s γ)) n)
    (a : Fin 4 →₀ ℕ) (ha : multiOrder a < n) :
    hassePartial a (toGeneric R) ∈ P := by
  unfold toGeneric
  rw [← map_hassePartial]
  exact hp _ ⟨(hasse_inBox a hb).1,fun γ hγ => hasse_atJet_eq_zero ha (ho γ hγ)⟩

theorem local_order {Γ s R n} {P : Ideal GeoJets} [P.IsPrime] (hp : Persistent Γ s P)
    (hb : InBox (shape R) Final50Price.primaryBox)
    (ho : ∀ γ ∈ Γ, OrderAt R (extend (s γ)) n) : VanishesTo P (toGeneric R) n :=
  K1_13_6_1_2_2.vanishesTo_of_hasse _ P n (fun a ha => derivative_mem hp hb ho a ha)

#print axioms common_avoider
#print axioms local_order
end
end Shared50Persistent
end Merged_Shared50Persistent

-- merged module Shared50ShapeRankBase
section Merged_Shared50ShapeRankBase
open scoped BigOperators

namespace Shared50ShapeRankBase

variable {𝕜 E ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A rank balance forces an element in one of the small support spaces. -/
theorem exists_nonzero_overlap (s : Finset ι) (V M : ι → Submodule 𝕜 E)
    (h : (∑ i ∈ s, (Module.finrank 𝕜 E - Module.finrank 𝕜 (M i))) <
      ∑ i ∈ s, Module.finrank 𝕜 (V i)) :
    ∃ i ∈ s, ∃ v : E, v ≠ 0 ∧ v ∈ V i ∧ v ∈ M i := by
  classical
  by_contra! hn
  apply (Nat.not_lt_of_ge ?_) h
  change (∑ i ∈ s, Module.finrank 𝕜 (V i)) ≤
    (∑ i ∈ s, (Module.finrank 𝕜 E - Module.finrank 𝕜 (M i)))
  refine Finset.sum_le_sum (s := s) (f := fun i => Module.finrank 𝕜 (V i))
    (g := fun i => Module.finrank 𝕜 E - Module.finrank 𝕜 (M i)) fun i hi => ?_
  have hmeet : V i ⊓ M i = ⊥ := by
    apply bot_unique
    intro v hv
    have hz : v = 0 := by
      by_contra hzero
      exact (hn i hi v hzero hv.1) hv.2
    rw [hz]
    exact Submodule.zero_mem _
  have he := (V i).finrank_sup_add_finrank_inf_eq (M i)
  rw [hmeet, finrank_bot, add_zero] at he
  have hsup := (V i ⊔ M i).finrank_le
  omega

/-- The second budget counts the high multiplicity part at a higher rate. -/
theorem blended {low high old replacement : ℚ} {k : ℕ}
    (hlow : low ≤ replacement)
    (hold : low + (1 + (k : ℚ)) * high ≤ old) :
    (1 + (k : ℚ)) * (low + high) ≤ old + (k : ℚ) * replacement := by
  have hk : (0 : ℚ) ≤ k := by positivity
  linarith only [hold, mul_le_mul_of_nonneg_left hlow hk]

/-- Strict dominance in one support coordinate survives division by the largest factor power. -/
theorem residual_slope {b f g r k s : ℕ}
    (hf : s * b ≤ f) (hG : k * f + g ≤ r * b) :
    g ≤ (r - s*k) * b := by
  calc
    g ≤ r*b - k*f := by omega
    _ ≤ r*b - k*(s*b) := Nat.sub_le_sub_left (Nat.mul_le_mul_left _ hf) _
    _ = (r-s*k)*b := by rw [Nat.sub_mul]; congr 1; ac_rfl

theorem residual_order_pos {b f r k s : ℕ}
    (hr : 0 < r) (hf : s * b < f) (hG : k * f ≤ r * b) :
    0 < r - s*k := by
  by_contra! hs
  have hsr : r ≤ s*k := by omega
  have hk : 0 < k := by
    by_contra! hn
    interval_cases k
    simp at hsr
    omega
  have hprod := Nat.mul_lt_mul_of_pos_left hf hk
  have he : (s * k) * b = k * (s * b) := by ac_rfl
  rw [← he] at hprod
  exact (not_lt_of_ge hG) ((Nat.mul_le_mul_right b hsr).trans_lt hprod)

#print axioms exists_nonzero_overlap
#print axioms blended
#print axioms residual_slope
#print axioms residual_order_pos
end Shared50ShapeRankBase
end Merged_Shared50ShapeRankBase

set_option Elab.async false
set_option maxRecDepth 40000
set_option linter.style.haveILetI false
set_option maxHeartbeats 1500000
namespace Shared50ShapeRank
noncomputable section

open K1_13 (Geom Row extend shape InBox OrderAt)
open K1_13_6 (GenericField GeoField GeoJets toGeneric)
open K1_13_6_1_2 (hassePartial multiOrder taylorHom taylor_coeff)
open Shared50Rational
open Shared50Persistent (Persistent derivative_mem)
open TaperColumns (jetExponents jetColumns jet_card_eq)
open MvPolynomial Finset

def ambient : Submodule GenericField FractionJet :=
  restrictSupport GenericField jetExponents

instance : Module.Finite GenericField ambient :=
  restrictSupport_finite TaperColumns.jetExponents_finite

theorem ambient_dim : Module.finrank GenericField ambient = Final50Price.symbolCount := by
  have h : (jetColumns : Set _) = jetExponents := Set.Finite.coe_toFinset _
  rw [ambient,← h,finrank_restrictSupport_finset]
  have hc := jet_card_eq
  rw [TaperColumns.sourceCount_eq] at hc
  exact_mod_cast hc

def cutoff (r : ℕ) : Submodule GenericField ambient :=
  (restrictSupport GenericField (↑(jetColumns.filter (Final50ShapeGate.fits r)))).comap ambient.subtype

theorem cutoff_dim (r : ℕ) : Module.finrank GenericField (cutoff r) = Final50ShapeGate.width r := by
  have hle : restrictSupport GenericField (↑(jetColumns.filter (Final50ShapeGate.fits r))) ≤ ambient := by
    intro Q hQ m hm
    have hw := Finset.mem_filter.mp ((mem_restrictSupport_iff GenericField).mp hQ hm)
    exact TaperColumns.jetExponents_finite.mem_toFinset.mp hw.1
  change Module.finrank GenericField
    ((restrictSupport GenericField (↑(jetColumns.filter (Final50ShapeGate.fits r)))).comap ambient.subtype) = _
  rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq,finrank_restrictSupport_finset]
  rfl

private theorem hasse_add (a : Fin 4 →₀ ℕ) (P Q : GeoJets) :
    hassePartial a (P+Q) = hassePartial a P + hassePartial a Q := by
  rw [← taylor_coeff, map_add, MvPolynomial.coeff_add, taylor_coeff,taylor_coeff]

private theorem hasse_zero (a : Fin 4 →₀ ℕ) :
    hassePartial a (0 : GeoJets) = 0 := by
  rw [← taylor_coeff, map_zero]
  simp

private theorem hasse_C_mul (a : Fin 4 →₀ ℕ) (c : GeoField) (P : GeoJets) :
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
open Final50Order (primaryCutoff layerWidth sourceRank layerNeed requiredOrder)
open scoped BigOperators
open private exists_fresh sum_by_layer from ProximityPrize.SubmissionLower.PortLowBase

theorem bank_layers {w Γ s} (hm : Final50Price.Messages w Γ s)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P) :
    layerNeed ≤ ∑ i ∈ range (1+primaryCutoff/layerWidth),
      Module.finrank GenericField (contactSpace surfaces (i+1)) := by
  obtain ⟨x,hx,_⟩ := exists_fresh (fun _ : Fin 0 => (0 : Row 4))
  obtain ⟨r,hr,hbank⟩ := Final50Order.symbol_families w x (Final50Order.primary_rank w) hx
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
        exact Final50Order.order_of_contact w (e i) hT (he i).2.1 (he i).2.2.2
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
  have hceil : layerWidth * (layerNeed-1) < sourceRank := by decide
  by_contra! hsmall
  exact (not_le_of_gt hceil) (hsum.trans (Nat.mul_le_mul_left _ (by
    dsimp only [cost]
    omega)))

/-- Select a small rational-function row of positive order on every persistent surface. -/
theorem exists_small {w Γ s} (hm : Final50Price.Messages w Γ s)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P) :
    ∃ r : ℕ, 0<r ∧ ∃ Q : FractionJet, Q ≠ 0 ∧
      (∀ m ∈ Q.support, Final50ShapeGate.fits r m) ∧
      ∀ P ∈ surfaces,∀ a : Fin 4 →₀ ℕ, multiOrder a < r → hassePartial a (toGeometric Q) ∈ P := by
  have hbank := bank_layers hm surfaces hp
  let N := 1+primaryCutoff/layerWidth
  have hgate := Final50ShapeGate.loss_bound N
  have h : (∑ i ∈ range N, (Module.finrank GenericField ambient -
      Module.finrank GenericField (cutoff (i+1)))) <
      ∑ i ∈ range N, Module.finrank GenericField (contactSpace surfaces (i+1)) := by
    simp only [ambient_dim,cutoff_dim]
    exact hgate.trans_lt ((by decide : Final50SharedPrice.slopeLoss < layerNeed).trans_le hbank)
  obtain ⟨i,_,Q,hQ,hm,ht⟩ :=
    @Shared50ShapeRankBase.exists_nonzero_overlap GenericField ↥ambient ℕ
      inferInstance inferInstance inferInstance inferInstance (range N)
      (fun i => contactSpace surfaces (i+1)) (fun i => cutoff (i+1)) h
  refine ⟨i+1,by omega,Q.val,fun hz => hQ (Subtype.ext hz),?_,hm⟩
  intro m hmem
  exact (Finset.mem_filter.mp ((mem_restrictSupport_iff GenericField).mp ht hmem)).2

theorem exists_polynomial {w Γ s} (hm : Final50Price.Messages w Γ s)
    (surfaces : Finset (Ideal GeoJets)) (hp : ∀ P ∈ surfaces, Persistent Γ s P) :
    ∃ r : ℕ, 0<r ∧ ∃ Q : Row 4, Q ≠ 0 ∧
      (∀ m ∈ Q.support, Final50ShapeGate.fits r m) ∧
      ∀ P ∈ surfaces,∀ a : Fin 4 →₀ ℕ, multiOrder a < r → hassePartial a (toGeneric Q) ∈ P := by
  obtain ⟨r,hr,U,hU,hs,ho⟩ := exists_small hm surfaces hp
  obtain ⟨d,Q,_,hS,hQ⟩ := clear_denominators U
  refine ⟨r,hr,Q,?_,fun m hm => hs m (hS ▸ hm),?_⟩
  · intro hz
    apply hU
    rw [hz,MvPolynomial.support_zero] at hS
    exact MvPolynomial.support_eq_empty.mp hS.symm
  · intro P hP a ha
    rw [← fraction_geometric,hQ,map_mul,toGeometric,MvPolynomial.map_C,hasse_C_mul]
    exact P.mul_mem_left _ (ho P hP a ha)

#print axioms bank_layers
#print axioms exists_polynomial
end
end Shared50ShapeRank