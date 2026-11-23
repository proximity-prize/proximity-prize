import Mathlib.RingTheory.Valuation.Extension
import ProximityPrize.SubmissionLower.ZwLbCYa
import ProximityPrize.SubmissionLower.Z3R7Dac
set_option Elab.async false
open _root_ renaming Algebra.IsSeparable → zw7, Function.Surjective → zpX, Ideal.Quotient.field → zxv, Ideal.Quotient.mk → zVv, IsFractionRing → z0o, IsScalarTower.algebraMap_apply → zG3, Module.Finite → zAa, Module.IsTorsionFree → zYo, Module.finrank → zsE
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace qwQWGra
noncomputable section
open Polynomial IsDedekindDomain IsLocalRing WithZero
open scoped WithZero
open P5 (p)
open private nontrivial_val RG center center_mem center_val from ProximityPrize.SubmissionLower.ZwLbCYa
open private adicResidue adicResidue_mk local_degree_bounds from ProximityPrize.SubmissionLower.ZR3mCBd
open private separable_of_small_root from ProximityPrize.SubmissionLower.Z3R7Dac
variable {K M:Type} [Field K] [Field M] [Algebra K M]
variable (v :Valuation K ℤᵐ⁰) (w:Valuation M ℤᵐ⁰)
local notation "O" => v.valuationSubring
local notation "V" => w.valuationSubring
local notation "N" => integralClosure O M
theorem extension (e :ℕ) (he :0<e)
    (h : ∀ z,w (algebraMap K M z)=v z^e) :v.HasExtension w :=
  ⟨fun x y=> by
    simp only [Valuation.comap_apply,h]
    exact (pow_le_pow_iff_left₀ zero_le zero_le he.ne').symm⟩
private theorem separable_of_degree {F E :Type} [Field F] [Field E] [Algebra F E]
    [zAa F E] [CharP F p] (h:zsE F E<p) :
    Algebra.IsSeparable F E :=
  ⟨fun x=>separable_of_small_root (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x))
    ((minpoly.natDegree_le (A:=F) x).trans_lt h) (minpoly.aeval F x)⟩
private theorem bounded [zAa O N] (reg : ∀ a :O,w (algebraMap O M a)≤1)
    [IsDedekindDomain N] [z0o N M] (q:HeightOneSpectrum N)
    (hq:q.valuation M=w)
    (D:Derivation ℤ M M) (hD : ∀ a :O,w (D (algebraMap O M a))≤1) :
    ∃ B:ℤᵐ⁰,1≤B ∧ ∀ x :M,w x≤1→w (D x)≤B:= by
  classical
  obtain ⟨s,hs⟩:=Module.Finite.fg_top (R:=O) (M:=N)
  let B:=1 ⊔ s.sup (fun a=>w (D (algebraMap N M a)))
  have hB:1≤B:=le_sup_left
  have hn (a :N) :w (D (algebraMap N M a))≤B:= by
    have hm:a∈Submodule.span O (↑s :Set N) :=hs.symm ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem a ha=>exact (Finset.le_sup (f := fun a=>w (D (algebraMap N M a))) ha).trans le_sup_right
    | zero=>simpa only [map_zero] using (zero_le.trans hB)
    | add a b _ _ ha hb =>
      rw [map_add,map_add]
      exact (w.map_add _ _).trans (max_le ha hb)
    | smul c a _ ha =>
      rw [Algebra.smul_def,map_mul,← zG3 O N M,
        D.leibniz,smul_eq_mul,smul_eq_mul]
      apply (w.map_add _ _).trans
      apply max_le <;> rw [map_mul]
      · exact (mul_le_mul' (reg c) ha).trans_eq (one_mul B)
      · exact (mul_le_one' (RG v w reg a).property (hD c)).trans hB
  refine ⟨B,hB,fun x hx => ?_⟩
  obtain ⟨a,b,hb⟩:=q.exists_primeCompl_mul_eq_of_integer x (hq.symm ▸ hx)
  have hunit :w (algebraMap N M (b:N))=1 := by
    rw [← hq,q.valuation_of_algebraMap,q.intValuation_eq_one_iff_mem_primeCompl]
    exact b.property
  have hdiff :algebraMap N M (b:N)*D x =
      D (algebraMap N M a) - x*D (algebraMap N M (b:N)) := by
    have h:=congrArg D hb
    rw [D.leibniz,smul_eq_mul,smul_eq_mul] at h
    exact eq_sub_of_add_eq (by simpa only [add_comm] using h)
  have hh:=w.map_sub_le (hn a) (show w (x*D (algebraMap N M (b:N)))≤B by
    rw [map_mul]
    exact (mul_le_mul' hx (hn b)).trans_eq (one_mul B))
  rwa [← hdiff,map_mul,hunit,one_mul] at hh
private theorem adic_separable [IsDedekindDomain N] [z0o N M]
    (q:HeightOneSpectrum N) [q.asIdeal.LiesOver (maximalIdeal O)] [q.asIdeal.IsMaximal]
    [v.HasExtension w] (hq:q.valuation M=w)
    (h:letI:=zxv (maximalIdeal O)
       letI:=zxv q.asIdeal
       zw7 (O ⧸ maximalIdeal O) (N ⧸ q.asIdeal)) :
    zw7 (ResidueField O) (ResidueField V) := by
  subst w
  let:=zxv (maximalIdeal O)
  let:=zxv q.asIdeal
  let:zw7 (O ⧸ maximalIdeal O) (N ⧸ q.asIdeal) :=h
  let i: (O ⧸ maximalIdeal O) ≃+* ResidueField O:=RingEquiv.refl _
  refine Algebra.IsSeparable.of_equiv_equiv (A₁:=O ⧸ maximalIdeal O)
    (A₂:=ResidueField O) i (adicResidue q) ?_
  apply RingHom.ext
  intro a
  obtain ⟨z,rfl⟩:=Ideal.Quotient.mk_surjective a
  have hz :q.valuation M (algebraMap N M (algebraMap O N z))≤1 := by
    rw [← zG3 O N M,zG3 O K M]
    exact (Valuation.HasExtension.val_map_le_one_iff v _ (z :K)).mpr z.property
  change residue _ (algebraMap O (q.valuation M).valuationSubring z) =
    adicResidue q (algebraMap (O ⧸ maximalIdeal O) (N ⧸ q.asIdeal) (zVv _ z))
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
  refine (congrArg (residue _) (Subtype.ext ?_)).trans (adicResidue_mk q _ hz).symm
  change algebraMap K M (z :K)=algebraMap N M (algebraMap O N z)
  rw [← zG3 O N M,zG3 O K M]
  rfl
theorem local_data [zAa K M] [CharP K p] (e :ℕ) (he :0<e)
    (hv :zpX v) (hw:zpX w)
    (h : ∀ z,w (algebraMap K M z)=v z^e) (hd:zsE K M<p)
    (D:Derivation ℤ M M) (hD : ∀ z,v z≤1→w (D (algebraMap K M z))≤1) :
    letI:=extension v w e he h
    e<p∧zw7 (ResidueField O) (ResidueField V) ∧
      ∃ B:ℤᵐ⁰,1≤B ∧ ∀ x :M,w x≤1→w (D x)≤B:= by
  classical
  let:=extension v w e he h
  let:v.IsNontrivial:=nontrivial_val v hv
  let:v.IsRankOneDiscrete :=Valuation.IsRankOneDiscrete.mk' v
  let:zw7 K M:=separable_of_degree hd
  let:IsDedekindDomain N :=integralClosure.isDedekindDomain O K M
  let:z0o N M:=IsIntegralClosure.isFractionRing_of_finite_extension O K M N
  let:zAa O N :=IsIntegralClosure.finite O K M N
  let:zYo O M := .of_smul_eq_zero fun a x hzero=> by
    rw [Algebra.smul_def,zG3 O K M] at hzero
    apply (mul_eq_zero.mp hzero).imp_left
    intro hz
    apply Subtype.ext
    change (a :K)=0
    apply (algebraMap K M).injective
    rwa [map_zero]
  let:zYo O N :=IsIntegralClosure.isTorsionFree O M
  let:Module.Free O N :=IsIntegralClosure.module_free O K M N
  let π:=Classical.choice (inferInstance :Nonempty (Valuation.Uniformizer v))
  have hπ:v (π.1 :K)=exp (-1 :ℤ) := by
    rw [π.2.val,Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective hv]
    rfl
  have reg (a :O) :w (algebraMap O M a)≤1 :=
    (Valuation.HasExtension.val_map_le_one_iff v w _).mpr a.property
  have hπw:w (algebraMap O M π.1)=exp (-(e :ℤ)) := by
    change w (algebraMap K M (π.1 :K))= _
    rw [h,hπ,← exp_nsmul]
    simp
  have hπlt:w (algebraMap O M π.1)<1 := by
    rw [hπw,← exp_zero,exp_lt_exp]
    omega
  let q:=center v w reg π.ne_zero hπlt
  have hq:q.valuation M=w:=center_val v w hw reg π.ne_zero hπlt
  let m:=maximalIdeal O
  have hunder :q.asIdeal.under O=m:= by
    ext a
    change algebraMap O N a∈q.asIdeal↔a∈maximalIdeal O
    rw [center_mem v w reg π.ne_zero hπlt,← zG3 O N M,
      v.mem_maximalIdeal_iff]
    exact Valuation.HasExtension.val_map_lt_one_iff v w (a :K)
  let:q.asIdeal.LiesOver m:=⟨hunder.symm⟩
  let:q.asIdeal.IsMaximal:=q.isMaximal
  have hrank :zsE O N=zsE K M:=IsIntegralClosure.rank O K M N
  have ⟨_,he',hf'⟩:=local_degree_bounds (A:=O) q
  have hspan:Ideal.map (algebraMap O N) m=Ideal.span {algebraMap O N π.1} := by
    rw [show m= _ from π.2.is_generator,Ideal.map_span,Set.image_singleton]
  have hinj:Function.Injective (algebraMap O N) :=
    fun a b hab=>(IsFractionRing.injective O K) ((algebraMap K M).injective (by
      simpa only [← zG3 O K M,zG3 O N M] using
        congrArg (algebraMap N M) hab))
  have hn:algebraMap O N π.1≠0 :=
    (map_ne_zero_iff _ hinj).mpr (fun hz=>π.ne_zero (congrArg Subtype.val hz))
  have hne :Ideal.map (algebraMap O N) m ≠ ⊥ := by
    rwa [hspan,ne_eq,Ideal.span_singleton_eq_bot]
  have hram:q.asIdeal.ramificationIdx O=e := by
    have heq :=q.intValuation_eq_exp_neg_multiplicity hn
    rw [← q.valuation_of_algebraMap (K:=M),hq] at heq
    change w (algebraMap N M (algebraMap O N π.1))= _ at heq
    rw [← zG3 O N M,hπw,← hspan,
      ← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity m q.asIdeal hne,
      WithZero.exp_inj] at heq
    omega
  have hel:e<p:=hram ▸ he'.trans_lt (hrank.symm ▸ hd)
  refine ⟨hel,?_,
    bounded v w reg q hq D (fun a=>hD a a.property)⟩
  let:Field (O ⧸ m) :=zxv m
  let:Field (N ⧸ q.asIdeal) :=zxv q.asIdeal
  let:zAa (O ⧸ m) (N ⧸ q.asIdeal) :=inferInstance
  have hres :zsE (O ⧸ m) (N ⧸ q.asIdeal)<p:= by
    rw [← Ideal.inertiaDeg_eq_of_isMaximal m q.asIdeal]
    exact hf'.trans_lt (hrank.symm ▸ hd)
  let:CharP O p:=(ValuationSubring.subtype O).charP Subtype.val_injective p
  let:CharP (O ⧸ m) p :=
    CharP.of_ringHom_of_ne_zero (zVv m) p (he.trans hel).ne'
  exact adic_separable v w q hq (separable_of_degree hres)
end
end qwQWGra
