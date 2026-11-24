import ProximityPrize.SubmissionLower.Zgvu91a
import Mathlib.FieldTheory.PurelyInseparable.Tower
import ProximityPrize.SubmissionLower.ZPKTqyb
import ProximityPrize.SubmissionLower.ZQTNHBe
import ProximityPrize.SubmissionLower.Z4EMMWa
import ProximityPrize.SubmissionLower.Zpj8DDa
import ProximityPrize.SubmissionLower.Z8duOVc
import ProximityPrize.SubmissionLower.ZpWrDCd
import ProximityPrize.SubmissionLower.AU
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.CH
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.Z5h1PTd
import ProximityPrize.SubmissionLower.ZO2xefe
import ProximityPrize.SubmissionLower.ZS2Jire
import ProximityPrize.SubmissionLower.ZS4VEna
import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.CI
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.Z2fdgla
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.Z409zke
import ProximityPrize.SubmissionLower.ZBRA0Kc
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.ZSWmOqa
import ProximityPrize.SubmissionLower.ZV6zyia
import ProximityPrize.SubmissionLower.ZZMyKHc
import ProximityPrize.SubmissionLower.ZaQt7ib
set_option Elab.async false
open _root_ renaming Field → zrb, Finset.mem_univ → zTc, Finset.sum_eq_single → zi6, Finset.univ → zdB, Function.Injective → zq4, Ideal.span → zye, IsFractionRing.injective → zxb, IsFractionRing.map → zJ1, Module.Finite → zAa, Nat.mul_le_mul_right → ztf, Polynomial.coe_mapRingHom → zKC, Polynomial.mapRingHom → zhd, Polynomial.mapRingHom_comp → zPl, Polynomial.map_injective → zTo, Polynomial.map_map → zoi, Polynomial.map_mul → zNl, Polynomial.resultant → zSp, Set.range → zxp, Submodule.sum_mem → zo3
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace q6CrDDe
noncomputable section
open Polynomial
open quN7Z4a (physicalWeight)

open gT (kM)
open Cu
open P5 (p)
open qBajpRb
variable {C₀ : sQ} [Fact (Irreducible C₀)] {J : Ideal kM} {g n : ℕ}
  {R : wJ C₀ J g} (A : yI R n)
private theorem mul_coeff_mem {P Q : (CurveRing A)[X]} {j k : ℕ}
    (hP : ∀ a, P.coeff a ∈ tuple A j) (hQ : ∀ a, Q.coeff a ∈ tuple A k) (a : ℕ) :
    (P*Q).coeff a ∈ tuple A (j+k) := by
  rw [coeff_mul]
  exact zo3 _ fun x _ => tuple_mul A j k (Submodule.mul_mem_mul (hP x.1) (hQ x.2))
private theorem prod_coeff_mem {ι : Type} (U : Finset ι) (P : ι → (CurveRing A)[X]) {j : ℕ}
    (h : ∀ i ∈ U, ∀ a, (P i).coeff a ∈ tuple A j) (a : ℕ) :
    (∏ i ∈ U, P i).coeff a ∈ tuple A (U.card*j) := by
  classical
  induction U using Finset.induction_on generalizing a with
  | empty =>
      have h1 : (1 : CurveRing A) ∈ tuple A 0 :=
        ⟨1, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr (by simp), map_one (tupleMap A)⟩
      by_cases ha : a = 0 <;> simp [Polynomial.coeff_one, ha, h1]
  | @insert i U hi ih =>
      rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul, Nat.one_mul,
        add_comm (U.card*j)]
      exact mul_coeff_mem A (h i (Finset.mem_insert_self ..))
        (fun a => ih (fun l hl => h l (Finset.mem_insert_of_mem hl)) a) a
private theorem resultant_coeff {F G : (CurveRing A)[X][X]} {j k : ℕ}
    (hF : ∀ i a, (F.coeff i).coeff a ∈ tuple A j)
    (hG : ∀ i a, (G.coeff i).coeff a ∈ tuple A k) (a : ℕ) :
    (zSp (R := (CurveRing A)[X]) F G g G.natDegree).coeff a ∈
      tuple A (g*k+G.natDegree*j) := by
  classical
  let m := G.natDegree
  let B := F.sylvester G g m
  change B.det.coeff a ∈ _
  rw [Matrix.det_apply', finsetSum_coeff]
  apply zo3
  intro σ _
  rw [← zsmul_eq_mul, coeff_smul]
  apply zsmul_mem
  rw [Fin.prod_univ_add]
  have hl (i : Fin g) (a : ℕ) : (B (σ (Fin.castAdd m i)) (Fin.castAdd m i)).coeff a ∈ tuple A k := by
    simp only [B, sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact hG _ _
    · simp
  have hr (i : Fin m) (a : ℕ) : (B (σ (Fin.natAdd g i)) (Fin.natAdd g i)).coeff a ∈ tuple A j := by
    simp only [B, sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact hF _ _
    · simp
  exact mul_coeff_mem A
    (fun b => by simpa using prod_coeff_mem A zdB _ (fun i _ => hl i) b)
    (fun b => by simpa using prod_coeff_mem A zdB _ (fun i _ => hr i) b) a
private theorem coprime_of_weight {D M : ℕ} {F : ((oO C₀)[X])[X]}
    (hFd : F.natDegree = g) (hprim : F.IsPrimitive)
    (hirr : Irreducible (F.map (F5 C₀)))
    (hM : 0 < M) (hlarge : M ≤ physicalWeight D F)
    {G : (CurveRing A)[X][X]} (hG0 : G ≠ 0) (hGdeg : G.natDegree ≤ g)
    (hsmall : ∀ i a, (G.coeff i).coeff a ≠ 0 → a+i*D < M) :
    IsCoprime (F.map (F5 C₀))
      (G.map ((F5 C₀).comp (zhd (incl A)))) := by
  let E := oO C₀
  let ι := zhd (incl A)
  let G' := G.map ι
  have hi : zq4 ι := zTo _ (incl_injective A)
  have hG' : G' ≠ 0 := (Polynomial.map_ne_zero_iff (f := ι) hi).mpr hG0
  have hf : F ≠ 0 := fun h => hirr.ne_zero (by rw [h, Polynomial.map_zero])
  have hsmall' : physicalWeight D G' < M := by
    apply Nat.lt_of_le_pred hM
    apply Finset.sup_le
    intro i hi
    let a := (G'.coeff i).natDegree
    have hn : (G'.coeff i).coeff a ≠ 0 :=
      leadingCoeff_ne_zero.mpr (Polynomial.mem_support_iff.mp hi)
    have hn' : (G.coeff i).coeff a ≠ 0 := by
      intro h
      exact hn (by simp [G', ι, coeff_map, h])
    exact Nat.le_pred_of_lt (hsmall i a hn')
  rw [← zoi]
  change IsCoprime (F.map (F5 C₀)) (G'.map (F5 C₀))
  refine (hirr.isCoprime_or_dvd _).resolve_right ?_
  intro hd
  obtain ⟨q, hq⟩ := hprim.dvd_of_fraction_map_dvd_fraction_map hd
  have hq0 : q ≠ 0 := fun h => hG' (by rw [hq, h, mul_zero])
  have hqd : q.natDegree = 0 := by
    have hb : G'.natDegree ≤ g := (natDegree_map_le (p := G)).trans hGdeg
    rw [hq, natDegree_mul hf hq0, hFd] at hb
    omega
  let a := q.coeff 0
  have ha : a ≠ 0 := by
    intro h
    exact hq0 ((eq_C_of_natDegree_eq_zero hqd).trans (by rw [show q.coeff 0 = 0 from h, C_0]))
  have he : G' = C a * F := by
    rw [hq, eq_C_of_natDegree_eq_zero hqd, mul_comm]
  have hw : physicalWeight D F ≤ physicalWeight D G' := by
    apply Finset.sup_le
    intro j hj
    have hj0 := Polynomial.mem_support_iff.mp hj
    have hc : G'.coeff j = a * F.coeff j := by rw [he, coeff_C_mul]
    have hj' := Polynomial.mem_support_iff.mpr (show G'.coeff j ≠ 0 from hc ▸ mul_ne_zero ha hj0)
    refine le_trans ?_ (Finset.le_sup hj')
    rw [hc, natDegree_mul ha hj0]
    omega
  exact (not_le_of_gt hsmall') (hlarge.trans hw)
variable [CharP (CurveRing A) p] [CharP (oO C₀) p]
theorem frob_degree {B : Type} [CommRing B] [IsDomain B] [CharP B p]
    (r : ℕ) (F : B[X][X]) : ((frobEquation B r) F).natDegree = F.natDegree :=
  natDegree_map_eq_of_injective (zTo _ (iterateFrobenius_inj B p r)) F
private theorem frob_weight (r D : ℕ) :
    physicalWeight D ((frobEquation (oO C₀) r) R.equation) =
      physicalWeight D R.equation := by
  let E := oO C₀
  have hi := iterateFrobenius_inj E p r
  unfold physicalWeight frobEquation
  rw [zKC, Polynomial.support_map_of_injective _ (zTo _ hi)]
  simp only [coeff_map, frobPoly, zKC,
    natDegree_map_eq_of_injective (iterateFrobenius_inj (oO C₀) p r)]
private theorem frob_generic (r : ℕ) :
    (((frobEquation (CurveRing A) r) (equation A)).map (zhd (incl A))) =
      C (frobPoly (oO C₀) r (C (A.scale : oO C₀))) *
        ((frobEquation (oO C₀) r) R.equation) := by
  have hc : (zhd (incl A)).comp (frobPoly (CurveRing A) r) =
      (frobPoly (oO C₀) r).comp (zhd (incl A)) := by
    unfold frobPoly
    rw [zPl, zPl, (incl A).iterateFrobenius_comm]
  simp only [frobEquation, zKC, zoi, hc]
  rw [← zoi, equation_generic, zNl, map_C]
theorem frob_resultant {D M k r : ℕ} (hg : 0 < g) (hM : 0 < M)
    (hlarge : M ≤ physicalWeight D R.equation)
    (hprim : ((frobEquation (oO C₀) r) R.equation).IsPrimitive)
    (hirr : Irreducible (((frobEquation (oO C₀) r) R.equation).map (F5 C₀)))
    {G : (CurveRing A)[X][X]} (hG0 : G ≠ 0) (hGd : G.natDegree ≤ g)
    (hs : ∀ i a, (G.coeff i).coeff a ≠ 0 → a+i*D < M)
    (hG : ∀ i a, (G.coeff i).coeff a ∈ tuple A k) :
    ∃ f ∈ tuple A (g*k+G.natDegree*(p^r)), f ≠ 0 ∧
      ∀ (Q : Type) [CommRing Q] (φ : CurveRing A →+* Q) (u : Q[X]),
        (((frobEquation (CurveRing A) r) (equation A)).map (zhd φ)).eval u = 0 →
        (G.map (zhd φ)).eval u = 0 → φ f = 0 := by
  let F := (frobEquation (CurveRing A) r) (equation A)
  let F' := (frobEquation (oO C₀) r) R.equation
  let ev := (F5 C₀).comp (zhd (incl A))
  have hei : zq4 ev :=
    (zxb (oO C₀)[X] (y7 C₀)).comp
      (zTo _ (incl_injective A))
  have hF'd : F'.natDegree = g := (frob_degree r R.equation).trans R.degree
  have hW : M ≤ physicalWeight D F' := (frob_weight (R := R) r D).symm ▸ hlarge
  have hcop := coprime_of_weight A hF'd hprim hirr hM hW hG0 hGd hs
  have hu : IsUnit (C (F5 C₀ (frobPoly (oO C₀) r (C (A.scale : oO C₀))))) :=
    A.scale.isUnit.map (C.comp ((F5 C₀).comp ((frobPoly (oO C₀) r).comp C)))
  have hcop' : IsCoprime (F.map ev) (G.map ev) := by
    rw [show ev = (F5 C₀).comp (zhd (incl A)) from rfl,
      ← zoi, frob_generic A r, zNl, map_C]
    exact (isCoprime_mul_unit_left_left hu _ _).mpr hcop
  have hR := Polynomial.resultant_ne_zero (R := y7 C₀) (F.map ev) (G.map ev) hcop'
  have hdF : F.natDegree = g := (frob_degree r (equation A)).trans (equation_degree A)
  rw [natDegree_map_eq_of_injective hei F, hdF, natDegree_map_eq_of_injective hei G] at hR
  let f := zSp F G g G.natDegree
  have hmap : ev f = zSp (F.map ev) (G.map ev) g G.natDegree :=
    (Polynomial.resultant_map_map F G g G.natDegree ev).symm
  have hf : f ≠ 0 := fun h => hR (hmap.symm.trans (by rw [h, map_zero]))
  let a := f.natDegree
  have hF (i b : ℕ) : (F.coeff i).coeff b ∈ tuple A (p^r) :=
    frob_coeff A r i b (equation A) (equation_coeff A)
  refine ⟨f.coeff a, resultant_coeff A hF hG a, leadingCoeff_ne_zero.mpr hf, ?_⟩
  intro Q _ φ u hx hy
  have hc := Polynomial.map_resultant_eq_zero_of_common_root (zhd φ)
    F G hdF.le le_rfl (Or.inl hg.ne') u hx hy
  have ha := congrArg (fun P : Q[X] => P.coeff a) hc
  simpa only [← show zSp F G g G.natDegree = f from rfl,
    zKC, coeff_map, coeff_zero] using ha
end
end q6CrDDe
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q6CrDDe
noncomputable section
open Polynomial
open P5 (p)
private theorem primitive_iff_span {E : Type} [zrb E] (F : E[X][X]) :
    F.IsPrimitive ↔ zye (zxp F.coeff) = ⊤ := by
  let I := zye (zxp F.coeff)
  rw [isPrimitive_iff_isUnit_of_C_dvd]
  constructor
  · intro h
    let a := Submodule.IsPrincipal.generator I
    exact Ideal.eq_top_of_isUnit_mem I (Submodule.IsPrincipal.generator_mem I)
      (h a ((C_dvd_iff_dvd_coeff a F).mpr (fun i =>
        (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp (Ideal.subset_span ⟨i, rfl⟩))))
  · intro h a ha
    have hle : I ≤ zye {a} := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_span_singleton.mpr ((C_dvd_iff_dvd_coeff a F).mp ha i)
    have ho : (1 : E[X]) ∈ I := by
      change 1 ∈ zye (zxp F.coeff)
      rw [h]
      exact Submodule.mem_top
    exact isUnit_iff_dvd_one.mpr (Ideal.mem_span_singleton.mp (hle ho))
theorem frob_preserves {E : Type} [zrb E] [CharP E p] (F : E[X][X])
    (hF : F.natDegree = 2) (hprim : F.IsPrimitive)
    (hirr : Irreducible (F.map (algebraMap E[X] (FractionRing E[X])))) (r : ℕ) :
    ((frobEquation E r) F).IsPrimitive ∧
      Irreducible (((frobEquation E r) F).map (algebraMap E[X] (FractionRing E[X]))) := by
  let σ := frobPoly E r
  have hm : (frobEquation E r) F = F.map σ := rfl
  constructor
  · rw [hm, primitive_iff_span, show zxp (F.map σ).coeff = σ '' zxp F.coeff by
      rw [← Set.range_comp]
      congr 1
      funext j
      exact coeff_map σ j]
    rw [← Ideal.map_span, (primitive_iff_span F).mp hprim, Ideal.map_top]
  let K := FractionRing E[X]
  let i := algebraMap E[X] K
  let hi := zTo _ (iterateFrobenius_inj E p r)
  let φ : K →+* K := zJ1 (j := σ) hi
  let M := φ.fieldRange
  let e := φ.rangeRestrictFieldEquiv
  have hc : φ.comp i = i.comp σ := by
    apply RingHom.ext
    intro f
    change φ (i f) = i (σ f)
    unfold φ zJ1
    rw [IsLocalization.map_eq]
  let : CharP K p := charP_of_injective_ringHom
    (i.comp ((Polynomial.C : E →+* E[X]))).injective p
  let : CharP M p := Subfield.charP M p
  have hp : ∀ f : E[X], i f ^ (p^r) = φ (i (expand E (p^r) f)) := by
    intro f
    rw [← map_pow, ← map_iterateFrobenius_expand (p := p) f r]
    exact (DFunLike.congr_fun hc (expand E (p^r) f)).symm
  let : IsPurelyInseparable M K := (isPurelyInseparable_iff_pow_mem M (E := K) p).mpr (by
    intro x
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective E[X] x
    refine ⟨r, e (i (expand E (p^r) a) / i (expand E (p^r) b)), ?_⟩
    change φ _ = (i a / i b)^(p^r)
    rw [map_div₀, div_pow, hp a, hp b])
  let f := F.map i
  have hd : f.natDegree = 2 := (natDegree_map_eq_of_injective (zxb E[X] K) F).trans hF
  have hs : f.Separable := by
    apply (separable_iff_derivative_ne_zero hirr).mpr
    intro hzero
    have h := congrArg (fun P : K[X] => P.coeff 1) hzero
    rw [coeff_derivative, coeff_zero] at h
    have ha : f.coeff 2 ≠ 0 := by
      rw [← hd]
      exact leadingCoeff_ne_zero.mpr hirr.ne_zero
    have htwo : (2 : K) ≠ 0 := by
      exact mt ((CharP.cast_eq_zero_iff K p 2).mp) (by decide : ¬p ∣ 2)
    exact (mul_ne_zero ha htwo) h
  let fM := f.map e.toRingHom
  have hI : Irreducible fM := (MulEquiv.irreducible_iff (f := (Polynomial.mapEquiv e).toMulEquiv)).mpr hirr
  have hS : fM.Separable := hs.map
  have hr : Irreducible (fM.map (algebraMap M K)) :=
    hS.map_irreducible_of_isPurelyInseparable K hI
  change Irreducible ((F.map i).map e.toRingHom |>.map (algebraMap M K)) at hr
  rw [zoi, show (algebraMap M K).comp e.toRingHom = φ from rfl,
    zoi, hc, ← zoi] at hr
  exact hm ▸ hr
end
end q6CrDDe
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q6CrDDe
noncomputable section
open Polynomial
open P5 (K p)
open cu (L)

open Cu
open quN7Z4a (compressionWidth)
open qBajpRb
theorem of_children (h1 : c1) (h2 : c2) :
    qrsE1ie.c1 := by
  classical
  intro C₀ hC J T z s D H S hD hlarge hz hdeg
  let A := S.bY
  let B := CurveRing A
  let E := oO C₀
  let : CharP B p :=
    charP_of_injective_ringHom
      ((algebraMap L B).comp (algebraMap K L)).injective p
  let : CharP E p :=
    charP_of_injective_ringHom ((zT C₀).comp (algebraMap K L)).injective p
  obtain ⟨r, k, hk, hrank⟩ := choose_rank A
  let q := p^r
  let F := (frobEquation B r) (equation A)
  have hq : 0 < q := pow_pos (by decide : 0 < p) _
  have hF : F.natDegree = 2 := (frob_degree r (equation A)).trans (equation_degree A)
  have hF0 : F ≠ 0 := by
    intro hn
    rw [hn, natDegree_zero] at hF
    omega
  obtain ⟨G, hG0, hGd, hc, hw, htransfer⟩ := h2 B (tuple A k) (tuple A q) D F hD
    hF0 hF.le (fun i a => frob_coeff A r i a _ (equation_coeff A)) hrank
  obtain ⟨hprim, hirr⟩ := frob_preserves S.root.equation S.root.degree S.root.primitive S.root.irreducible r
  have hM : 0 < compressionWidth D 2 := by unfold compressionWidth; positivity
  obtain ⟨f, hf, hf0, hcut⟩ := frob_resultant A (r := r) (by decide : 0 < 2) hM hlarge
    hprim hirr hG0 hGd hw (fun i a => tuple_mul A k q (hc i a))
  let I := thickMarks A T z S.parameter S.onBase q
  have hfI : f ∈ I := by
    refine Ideal.mem_iInf.mpr fun γ => ?_
    let φ := yq A (z γ) (S.parameter γ) (S.onBase γ γ.property)
    let Q := B ⧸ (RingHom.ker φ.toRingHom ^ q)
    let φq : B →+* Q := Ideal.Quotient.mk _
    obtain ⟨u, hu, hFu⟩ := thick_root S r γ.property (hdeg γ γ.property)
    have hzero : φq f = 0 := @hcut Q inferInstance φq u hFu
      (@htransfer Q inferInstance φq u hu hFu)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  obtain ⟨_, hcount⟩ := marks_length A T z S.parameter S.onBase hz q hq
  obtain ⟨hfin, hbound⟩ := h1 C₀ J 2 S.n H S.root A S.height _ f hf hf0
  let : zAa L (B ⧸ zye {f}) := hfin
  have hfI' : zye {f} ≤ I := Ideal.span_le.mpr (by simpa using hfI)
  let π := (Ideal.Quotient.factorₐ L hfI').toLinearMap
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective hfI'
  have hdeg' : 2*(k+q)+G.natDegree*q ≤ 5*q := by
    have h := ztf q hGd
    omega
  have hp := hcount.trans ((LinearMap.finrank_le_finrank_of_surjective hπ).trans
    (hbound.trans (ztf H hdeg')))
  exact Nat.le_of_mul_le_mul_left (hp.trans_eq (by ring)) hq
end
end q6CrDDe
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace q516YUa
noncomputable section

open cu (L)
open qps5rle (SeedSeries vPhysical)
open qymFiQe
open WithZero
open scoped WithZero
theorem seed_powers_ne {q:ℕ} [CharP L q]
   (a :Fin q→SeedSeries) (ha : ∀ i,LaurentSeries.derivative L (a i)=0)
   (k :Fin q) (hk :a k≠0) :
   (∑ i,a i*(HahnSeries.single 1 1 :SeedSeries)^(i:ℕ))≠0:= by
 classical
 have hs : ∀ i n,(a i).coeff n≠0→(q:ℤ)∣n:= by
   intro i n hn
   have h:=congrArg (fun z :SeedSeries=>z.coeff (n-1)) (ha i)
   rw [LaurentSeries.derivative_apply,LaurentSeries.hasseDeriv_coeff,HahnSeries.coeff_zero,
     Ring.choose_one_right,zsmul_eq_mul] at h
   change ((n-1+1 :ℤ) :L)*(a i).coeff (n-1+1)=0 at h
   rw [sub_add_cancel] at h
   exact (CharP.intCast_eq_zero_iff L q n).mp ((mul_eq_zero.mp h).resolve_right hn)
 obtain ⟨n,hn⟩ : ∃ n:ℤ,(a k).coeff n≠0:= by
   by_contra! h
   exact hk (HahnSeries.ext (funext fun j=>(h j).trans (HahnSeries.coeff_zero (a :=j)).symm))
 intro h
 have hz :=congrArg (fun z :SeedSeries=>z.coeff (n+(k :ℕ))) h
 simp only [HahnSeries.coeff_sum,HahnSeries.single_pow,one_pow,nsmul_eq_mul,
   mul_one,HahnSeries.coeff_mul_single,HahnSeries.coeff_zero] at hz
 rw [zi6 k] at hz
 · exact hn (by simpa only [add_sub_cancel_right] using hz)
 · intro i _ hik
   by_contra hc
   have hd:=Int.dvd_sub (hs i _ hc) (hs k n hn)
   rw [show n+(k :ℕ)-(i:ℕ) - n=(k :ℕ)-(i:ℕ) by ring] at hd
   have he :=Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp hd)
   have hkq: ((k :ℕ) :ℤ)<q:= by exact_mod_cast k.isLt
   have hiq: ((i:ℕ) :ℤ)<q:= by exact_mod_cast i.isLt
   rw [Int.emod_eq_of_lt (by omega) hkq,Int.emod_eq_of_lt (by omega) hiq] at he
   exact hik (Fin.ext (Int.ofNat_inj.mp he.symm))
 · simp
variable {E :Type} [zrb E] (V:ValuationSubring E)
def residueIn (S:Subfield E) :V.comap S.subtype →+* V where
 toFun a :=⟨((a :S) :E),a.property⟩
 map_one' := rfl
 map_zero' := rfl
 map_mul' _ _:=rfl
 map_add' _ _:=rfl
def residueConstants (S:Subfield E) :Subfield (IsLocalRing.ResidueField V) := by
  let r :=(IsLocalRing.residue V).comp (residueIn V S)
  refine r.range.toSubfield ?_
  intro x hx
  obtain ⟨a,rfl⟩:=hx
  by_cases h:r a=0
  · rw [h,inv_zero]
    exact r.range.zero_mem
  have ha :V.valuation ((a :S) :E)=1 :=
    (V.valuation_eq_one_iff (residueIn V S a)).mp
      ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h)
  let b:V.comap S.subtype :=⟨(a :S)⁻¹,by
    apply V.mem_of_valuation_le_one
    change V.valuation (((a :S) :E)⁻¹)≤1
    rw [map_inv₀,ha,inv_one]⟩
  have hab:a*b=1 := by
    apply Subtype.ext
    exact mul_inv_cancel₀ (fun h0=>h (by rw [show a=0 from Subtype.ext h0,map_zero]))
  exact ⟨b,eq_inv_of_mul_eq_one_left (by rw [← map_mul,mul_comm b a,hab,map_one])⟩
section Physical
variable [Algebra F E]
theorem restriction (alg : ∀ a :E,IsIntegral F a)
   (hV : ∀ x :IntegerRing,algebraMap F E (x :F)∈V) :
   V = ⊤ ∨ V.comap (algebraMap F E)=IntegerRing:= by
 let:vPhysical.IsNontrivial:=⟨by
   obtain ⟨a,ha⟩:=LaurentSeries.valuation_surjective SeedSeries (exp (-1 :ℤ))
   exact ⟨a,ha.trans_ne exp_ne_zero,ha.trans_ne (exp_lt_one_iff.mpr (by decide)).ne⟩⟩
 have hle :IntegerRing≤V.comap (algebraMap F E) := fun x hx=>hV ⟨x,hx⟩
 rcases ValuationSubring.eq_self_or_eq_top_of_le hle with h | h
 · exact Or.inr h.symm
 · left
   apply top_unique
   intro a _
   exact integral_mem V (fun b=>show b∈V.comap (algebraMap F E) by rw [h]; trivial)
     (alg a)
def overBase (hV : ∀ x :IntegerRing,algebraMap F E (x :F)∈V) :
    IntegerRing →+* V where
  toFun x :=⟨algebraMap F E (x :F),hV x⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_mul' _ _:=Subtype.ext (map_mul _ _ _)
  map_add' _ _:=Subtype.ext (map_add _ _ _)
def a8p:SeedSeries →+* IntegerRing where
  toFun a :=⟨algebraMap SeedSeries F a,by
    apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero SeedSeries (D:=0)).mpr
    intro i hi
    rw [LaurentSeries.algebraMap_apply,HahnSeries.C_apply,HahnSeries.coeff_single_of_ne hi.ne]⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_mul' _ _:=Subtype.ext (map_mul _ _ _)
  map_add' _ _:=Subtype.ext (map_add _ _ _)
def seedResidue (hV : ∀ x :IntegerRing,algebraMap F E (x :F)∈V) :
    SeedSeries →+* IsLocalRing.ResidueField V :=
  (IsLocalRing.residue V).comp ((overBase V hV).comp a8p)
theorem residue_base (hV : ∀ x :IntegerRing,algebraMap F E (x :F)∈V)
    (hr :V.comap (algebraMap F E)=IntegerRing) (x :IntegerRing) :
    IsLocalRing.residue V (overBase V hV x)=seedResidue V hV ((x :F).coeff 0) := by
  let y :=x-a8p ((x :F).coeff 0)
  have hy :vPhysical (y :F)<1 := by
    refine lt_of_le_of_lt ((LaurentSeries.valuation_le_iff_coeff_lt_eq_zero
      SeedSeries (D:=1)).mpr ?_) (exp_lt_one_iff.mpr (by decide))
    intro n hn
    change ((x :F)-algebraMap SeedSeries F ((x :F).coeff 0)).coeff n=0
    rw [HahnSeries.coeff_sub,LaurentSeries.algebraMap_apply,HahnSeries.C_apply]
    by_cases hn0:n=0
    · rw [hn0,HahnSeries.coeff_single_same,sub_self]
    · rw [HahnSeries.coeff_single_of_ne hn0,sub_zero]
      exact (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero SeedSeries (D:=0)).mp
        x.property n (by omega)
  have hzero :IsLocalRing.residue V (overBase V hV y)=0:= by
    by_cases hy0: (y :F)=0
    · rw [show y=0 from Subtype.ext hy0,map_zero,map_zero]
    by_contra hn
    have hu:=(IsLocalRing.residue_ne_zero_iff_isUnit _).mp hn
    have hv :=(V.valuation_eq_one_iff _).mp hu
    have hi: (y :F)⁻¹∈V.comap (algebraMap F E) := by
      apply V.mem_of_valuation_le_one
      rw [map_inv₀,map_inv₀]
      change (V.valuation (algebraMap F E (y :F)))⁻¹≤1
      rw [show V.valuation (algebraMap F E (y :F))=1 from hv,inv_one]
    rw [hr] at hi
    change vPhysical ((y :F)⁻¹)≤1 at hi
    rw [map_inv₀,inv_le_one₀ (vPhysical.pos_iff.mpr hy0)] at hi
    exact (not_le_of_gt hy) hi
  rw [show (overBase V hV y)=overBase V hV x - overBase V hV (a8p ((x :F).coeff 0))
    from map_sub _ _ _,map_sub] at hzero
  exact sub_eq_zero.mp hzero
end Physical
end
end q516YUa
end
section
set_option backward.isDefEq.respectTransparency false
namespace q516YUa
noncomputable section
open Polynomial qymFiQe
open P5 (K p)
open cu (L)
open qps5rle (SeedSeries)
open scoped WithZero
private theorem aoF {A E :Type} {n:ℕ} [zrb A] [zrb E] (j:A →+* E)
   (V:ValuationSubring E) (a :Fin n→A) (i:Fin n) (hi:a i≠0) :
   ∃ k,a k≠0∧(∀ l,j (a l/a k)∈V) ∧
     V.valuation (j (a i))≤V.valuation (j (a k)) := by
 obtain ⟨k,_,hk⟩:=Finset.exists_max_image zdB (fun l=>V.valuation (j (a l)))
   ⟨i,zTc i⟩
 have hk0:a k≠0:= fun h=>(ne_of_gt
   ((V.valuation.pos_iff.mpr ((_root_.map_ne_zero j).2 hi)).trans_le (hk i (zTc i))))
     (by rw [h,map_zero,map_zero])
 refine ⟨k,hk0,fun l=>V.mem_of_valuation_le_one _ ?_,hk i (zTc i)⟩
 rw [map_div₀,map_div₀,div_le_one₀ (V.valuation.pos_iff.mpr ((_root_.map_ne_zero j).2 hk0))]
 exact hk l (zTc l)
private theorem scale {A E :Type} {n:ℕ} [zrb A] [zrb E] (j:A →+* E)
  (a :Fin n→A) (b:A) (x :E) :
  (∑ i,j (a i/b)*x^(i:ℕ))=(j b)⁻¹ * ∑ i,j (a i)*x^(i:ℕ) := by
 rw [Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro i _
 rw [map_div₀,div_eq_mul_inv]
 ac_rfl
private theorem simple_finite (w:Roots) :zAa F (Simple w) :=
 IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R:=F) w)
private theorem constant_minpoly (D:Derivation ℤ F F) (w:Roots)
   (D' : Derivation ℤ (Simple w) (Simple w))
   (hD' : ∀ x,D' (algebraMap F (Simple w) x)=algebraMap F (Simple w) (D x))
   (b:Simple w) (hb:D' b=0) : ∀ i,D ((minpoly F b).coeff i)=0:= by
 let:zAa F (Simple w) :=simple_finite w
 let f :=minpoly F b
 have hbI:IsIntegral F b:=IsIntegral.of_finite F b
 let g:=f.sum fun i a=>monomial i (D a)
 have hc (i:ℕ) :g.coeff i=D (f.coeff i) := by
   dsimp only [g]
   rw [coeff_sum,Polynomial.sum,zi6 i,coeff_monomial]
   · simp
   · intro j _ hj
     simp [coeff_monomial,hj]
   · intro hi
     simp [notMem_support_iff.mp hi]
 have hg:g.eval₂ (algebraMap F (Simple w)) b=0:= by
   have h:=aNu D' (algebraMap F (Simple w)) b f g (fun i=> by rw [hc,hD'])
   rw [hb,mul_zero,add_zero,← aeval_def,minpoly.aeval,map_zero] at h
   exact h.symm
 have hg0:g=0:= by
   by_contra hn
   have hd:=natDegree_le_of_dvd (minpoly.dvd F b (by simpa only [aeval_def] using hg)) hn
   have he :=leadingCoeff_ne_zero.mpr hn
   rw [leadingCoeff,hc] at he
   rcases hd.eq_or_lt with h | h
   · rw [← h,← leadingCoeff,(minpoly.monic hbI).leadingCoeff,D.map_one_eq_zero] at he
     exact he rfl
   · rw [coeff_eq_zero_of_natDegree_lt h,map_zero] at he
     exact he rfl
 intro i
 rw [← hc,hg0,coeff_zero]
private theorem seed_outside {q:ℕ} [CharP L q] (D:Derivation ℤ F F) (hD:coefficientwise D)
   (w:Roots) (hs :IsSeparable F w) (hd:Module.finrank F (Simple w)<q)
   (V:ValuationSubring (Simple w))
   (hV : ∀ x :IntegerRing,algebraMap F (Simple w) (x :F)∈V)
   (hr :V.comap (algebraMap F (Simple w))=IntegerRing) :
   seedResidue V hV (HahnSeries.single 1 1)∉residueConstants V (smallConstants D w) := by
 classical
 let E :=Simple w
 let:zAa F E :=simple_finite w
 let j:=algebraMap F E
 intro h
 obtain ⟨b,hb⟩:=h
 let b' : V:=residueIn V (smallConstants D w) b
 change IsLocalRing.residue V b' = _ at hb
 let x :E :=b'
 let f :=minpoly F x
 have hxI:IsIntegral F x :=IsIntegral.of_finite F x
 have hf :f.natDegree<q:=(minpoly.natDegree_le (A:=F) x).trans_lt hd
 obtain ⟨D',hD'⟩:=extendSimple D w hs
 have hc:=constant_minpoly D w D' hD' x (killConstants D w D' hD' (b:smallConstants D w))
 let a (i:Fin q) :=f.coeff i
 let i:Fin q:=⟨f.natDegree,hf⟩
 have hi:a i≠0:=(minpoly.monic hxI).leadingCoeff.trans_ne one_ne_zero
 obtain ⟨k,hk,hnorm,_⟩:=aoF j V a i hi
 let c (l:Fin q) :IntegerRing:=⟨a l/a k,by
   rw [← hr]
   exact hnorm l⟩
 have he : (∑ l,j (a l)*x^(l:ℕ))=0:= by
   change (∑ l:Fin q,j (f.coeff (l:ℕ))*x^(l:ℕ))=0
   rw [Fin.sum_univ_eq_sum_range (fun m=>j (f.coeff m)*x^m),← eval₂_eq_sum_range' j hf]
   exact minpoly.aeval F x
 have hz : (∑ l,overBase V hV (c l)*b' ^ (l:ℕ))=0:= by
   apply V.subtype_injective
   simp only [map_sum,map_mul,map_pow,map_zero]
   change (∑ l,j (a l/a k)*x^(l:ℕ))=0
   rw [scale,he,mul_zero]
 have hres :=congrArg (IsLocalRing.residue V) hz
 simp only [map_sum,map_mul,map_pow,map_zero,residue_base V hV hr,hb] at hres
 let M (l:Fin q) :SeedSeries :=(c l:F).coeff 0
 have hM : ∀ l,LaurentSeries.derivative L (M l)=0:= by
   intro l
   have hC: (a l/a k)∈constants D :=
     (constants D).div_mem (hc l) (hc k)
   have hh:=hD (a l/a k) 0
   rw [show D (a l/a k)=0 from hC,HahnSeries.coeff_zero] at hh
   exact hh.symm
 have hMk :M k≠0:= by
   change (a k/a k).coeff 0≠0
   rw [div_self hk,HahnSeries.coeff_one]
   simp
 apply seed_powers_ne M hM k hMk
 apply (seedResidue V hV).injective
 simpa only [map_sum,map_mul,map_pow,map_zero,M] using hres
private theorem power_minpoly {E :Type} [zrb E] {q:ℕ} [ExpChar E q]
  (hq:q.Prime) (S:Subfield E) {u:E} (hu:u∉S) (ht:u^q∈S) :
  minpoly S u=(Polynomial.X ^q-Polynomial.C ⟨u^q,ht⟩:S[X]) := by
 let t:S:=⟨u^q,ht⟩
 have hn (x :S) :x^q≠t:= by
  intro h
  have he : (x :E)=u:=frobenius_inj E q (congrArg Subtype.val h)
  exact hu (he ▸ x.property)
 refine (minpoly.eq_of_irreducible_of_monic (x :=u)
  (X_pow_sub_C_irreducible_of_prime hq hn) ?_
  (Polynomial.monic_X_pow_sub_C t hq.ne_zero)).symm
 simp only [map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C]
 exact sub_self _
private theorem residue_independent {E :Type} [zrb E] {q:ℕ} [ExpChar E q]
  (hq:q.Prime) (S:Subfield E) {u:E} (hu:u∉S) (ht:u^q∈S)
  (a :Fin q→S) (k :Fin q) (hk :a k≠0) :
  (∑ i,(a i:E)*u^(i:ℕ))≠0:= by
 classical
 intro h
 let f :=ofFn q a
 have hf :aeval u f=0:= by
  rw [show f = ∑ i:Fin q,monomial (i:ℕ) (a i) from ofFn_eq_sum_monomial a]
  simpa only [map_sum,aeval_monomial,Subfield.algebraMap_ofSubfield,Subfield.coe_subtype] using h
 have hn:f≠0:= fun h0=>hk (by
  have hc:=congrArg (fun g:S[X]=>g.coeff (k :ℕ)) h0
  simpa only [f,ofFn_coeff_eq_val_of_lt a k.isLt,coeff_zero] using hc)
 have hd:=natDegree_le_of_dvd (minpoly.dvd S u hf) hn
 rw [power_minpoly hq S hu ht,natDegree_X_pow_sub_C] at hd
 exact (not_le_of_gt (ofFn_natDegree_lt hq.pos a)) hd
private theorem valuation_coeffs {E :Type} [zrb E] {q:ℕ} [CharP E q] (hq:q.Prime)
   (V:ValuationSubring E) (S:Subfield E) (u:V)
   (hu:IsLocalRing.residue V u∉residueConstants V S) (hpow: (u:E)^q∈S)
   (c:Fin q→S) (hc: (∑ l,(c l:E)*(u:E)^(l:ℕ))∈V)
   (i:Fin q) : (c i:E)∈V:= by
 classical
 let R:=IsLocalRing.ResidueField V
 let ρ:=IsLocalRing.residue V
 let T:=residueConstants V S
 let v :=V.valuation
 by_contra hi
 have hci:c i≠0:= fun h=>hi (by rw [h]; exact V.zero_mem)
 obtain ⟨k,hk,hn,hle⟩:=aoF S.subtype V c i hci
 let b (l:Fin q) :V.comap S.subtype :=⟨c l/ c k,hn l⟩
 have hup: (ρ u)^q∈T:=⟨⟨⟨_,hpow⟩,(u^q).property⟩,map_pow ρ u q⟩
 let a (l:Fin q) :T:=⟨ρ (residueIn V S (b l)),⟨b l,rfl⟩⟩
 have ha :a k≠0:= by
   have hb:b k=1 :=Subtype.ext (div_self hk)
   intro hz
   have he :=congrArg (T.subtype :T→R) hz
   change ρ (residueIn V S (b k))=0 at he
   rw [hb,map_one,map_one] at he
   exact one_ne_zero he
 let:CharP V q:=⟨fun n=> by
   rw [← CharP.cast_eq_zero_iff E q n,← map_natCast V.subtype,
     map_eq_zero_iff V.subtype V.subtype_injective]⟩
 let:CharP R q:=CharP.of_ringHom_of_ne_zero ρ q hq.ne_zero
 let:ExpChar R q := .prime hq
 have hbig:1<v (c k :E) :=
   (lt_of_not_ge fun h=>hi (V.mem_of_valuation_le_one _ h)).trans_le hle
 let b0:V:=⟨(c k :E)⁻¹,V.mem_of_valuation_le_one _ (by
   change v ((c k :E)⁻¹)≤1
   rw [map_inv₀]
   exact inv_le_one_of_one_le₀ hbig.le)⟩
 have hb0:ρ b0=0:=(IsLocalRing.residue_eq_zero_iff b0).mpr
   ((V.valuation_lt_one_iff b0).mpr (by
     change v ((c k :E)⁻¹)<1
     rw [map_inv₀]
     exact inv_lt_one_of_one_lt₀ hbig))
 have hsum: (∑ l,residueIn V S (b l)*u^(l:ℕ)) =
     b0*(⟨(∑ l,(c l:E)*(u:E)^(l:ℕ)),hc⟩:V) := by
   apply V.subtype_injective
   simp only [map_sum,map_mul,map_pow]
   exact scale S.subtype c (c k) (u:E)
 apply residue_independent hq T hu hup a k ha
 have h:=congrArg ρ hsum
 simpa only [map_sum,map_mul,map_pow,hb0,zero_mul] using h
theorem coeffs :qymFiQe.c2 := by
 intro D hD w hs hd V hV c hc i
 let E :=Simple w
 let:zAa F E :=simple_finite w
 let S:=smallConstants D w
 have hV' (a :IntegerRing) :algebraMap F E (a :F)∈V:=hV a
 rcases restriction V (fun a=>IsIntegral.of_finite F a) hV' with ht | hr
 · rw [ht]
   trivial
 let u:V:=overBase V hV' (a8p (HahnSeries.single 1 1))
 have hpw: (u:E)^p∈S :=
   (le_sup_right:_≤S) (Subfield.subset_closure ⟨(u:E),rfl⟩)
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let:CharP SeedSeries p:=charP_of_injective_ringHom (algebraMap L SeedSeries).injective p
 let:CharP F p:=charP_of_injective_ringHom (algebraMap SeedSeries F).injective p
 let:CharP E p:=charP_of_injective_ringHom (algebraMap F E).injective p
 have hp:p.Prime :=CharP.char_prime_of_ne_zero K (by decide)
 exact valuation_coeffs hp V S u (seed_outside D hD w hs hd V hV' hr) hpw c hc i
end
end q516YUa
end
section
set_option autoImplicit true
namespace q516YUa
theorem proof :q0mTRkc.c3 :=
 qb1WXKc.of_children qPfoxUd.proof coeffs
end q516YUa
end
end
section
section
set_option autoImplicit true
namespace qvlURsa
theorem proof :qb1WXKc.c2 :=q516YUa.coeffs
end qvlURsa
end
section
namespace qJh2f6d
def c1 :Prop :=q9uVqha.c1
def c2 :Prop :=q9uVqha.c2
def c3:Prop :=q9uVqha.c3
def c4 :Prop :=q9uVqha.c4
def c5:Prop :=q9uVqha.c5
def c6:Prop :=q9uVqha.c6
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6) :
  q0mTRkc.c4 :=
 q9uVqha.of_children h1 h2 h3 h4 h5 h6
end qJh2f6d
end
end
