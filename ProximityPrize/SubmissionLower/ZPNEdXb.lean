import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import ProximityPrize.SubmissionLower.ZGSvmVd
import ProximityPrize.SubmissionLower.Zn6yRJc
import ProximityPrize.SubmissionLower.ZzOuVbd
set_option Elab.async false
open _root_ renaming LinearMap.range → zWl, Matrix.det_diagonal → zCi, Matrix.rank_eq_finrank_span_cols → z0e, Module.Finite → zAa, Module.Finite.span_of_finite → z3g, Module.finrank → zsE, Module.finrank_fintype_fun_eq_card → zvt
set_option autoImplicit true
namespace q1US8Va
open aR (ao)
open qK9H6va
open fP (Form GS Jx m9 avQ avP)
open xE (Flag U1 oldCount)
open akL (ahV KP BU aDd)
open P6_6_2 (oppositeBound latticeAllowance)
open qnnEPee
open MvPolynomial
open scoped BigOperators
open private dgL from ProximityPrize.SubmissionLower.ZV1UoEe
open private bpX from ProximityPrize.SubmissionLower.ZLIH4nd
open private ker_embed tail_card rank_le_of_ker_le lower_zero full_count from ProximityPrize.SubmissionLower.ZUihISc
open private fTs from ProximityPrize.SubmissionLower.AR
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
local instance :CharP ao P1.p :=
  charP_of_injective_algebraMap (algebraMap K1.K ao).injective P1.p
private theorem rank_le_map {K L m n:Type*} [Field K] [Field L] [Algebra K L]
    [Finite m] [Fintype n] (A:Matrix m n K) :A.rank≤(A.map (algebraMap K L)).rank := by
  let S:=Submodule.span K (Set.range A.col)
  let T:=Submodule.span L (Set.range (A.map (algebraMap K L)).col)
  have :zAa K S:=z3g _ (Set.finite_range _)
  have :zAa L T:=z3g _ (Set.finite_range _)
  let f : (m→K) →ₗ[K] (m→L) :=
    LinearMap.pi fun i=>(Algebra.linearMap K L).comp (LinearMap.proj i)
  have hf :S≤(T.restrictScalars K).comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact Submodule.subset_span (Set.mem_range_self (f :=(A.map (algebraMap K L)).col) j)
  let b:=Module.finBasis K S
  let v (i:Fin (zsE K S)) :T:=⟨f (b i),hf (b i).property⟩
  have hK:=b.linearIndependent.map' S.subtype S.ker_subtype
  have hL:LinearIndependent L (T.subtype ∘ v) :=
    linearIndependent_algebraMap_comp_iff.mpr hK
  rw [z0e,z0e]
  change zsE K S≤zsE L T
  simpa only [Fintype.card_fin] using
    (LinearIndependent.of_comp T.subtype hL).fintype_card_le_finrank
private theorem rank_le_block (q:ℕ) (g:ℤ) :
    (Gy q g).rank≤zsE ao (zWl (auo q g)) := by
  classical
  let VY:=(dgL q g).comp (auo q g)
  let b:Module.Basis (XN q g) ao (GS (iO q) (-g) 56 16) :=
    basisRestrictSupport ao _
  let E :Matrix (ait q g) (XN q g) ao :=
    Matrix.of fun e m=>VY (b m) e
  let φ:=ZMod.castHom (dvd_refl P1.p) ao
  let M:=(Gy q g).map φ
  let R:=Matrix.diagonal fun e :ait q g=>avQ e.val
  let C:=Matrix.diagonal fun m:XN q g=>avP m.val
  have hd:iO q≤56:=(min_le_right _ _).trans (gAv q)
  have hE :E=R*M*C:= by
    ext e m
    rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
    have hm: (b m:Form)=monomial m.val 1 :=
      coe_basisRestrictSupport_apply (R:=ao) _ m
    change (weightedTruncation m9 (Vm q g).toNat (Jx (b m))).coeff e.val =
      avQ e.val*φ (Gy q g e m)*avP m.val
    rw [coeff_weightedTruncation,ite_eq_left e.property.2,hm]
    rw [c3K _ _ (m.property.1.trans e.property.1.symm) (m.property.1.trans_le hd)]
    simp only [Gy,prefixMatrix,map_mul,map_natCast]
    ac_rfl
  have hr :R.det≠0:= by
    rw [zCi]
    exact Finset.prod_ne_zero_iff.mpr fun e _ =>
      div_ne_zero (by simp) (bpX _ (e.property.1.trans_le hd))
  have hc:C.det≠0:= by
    rw [zCi]
    exact Finset.prod_ne_zero_iff.mpr fun m _ =>
      mul_ne_zero (by simp) (bpX _ (m.property.1.trans_le hd))
  calc
    _≤M.rank := by
      let:Algebra (ZMod P1.p) ao:=φ.toAlgebra
      exact rank_le_map (L:=ao) _
    _=E.rank := by
      rw [hE,Matrix.rank_mul_eq_left_of_det_ne_zero C _ hc,
        Matrix.rank_mul_eq_right_of_det_ne_zero R _ hr]
    _=zsE ao (zWl VY) :=Matrix.rank_of_basis b VY
    _≤_:= by
      have :zAa ao (GS (iO q) (-g) 56 16) :=
        fP.bandSpace_finite _ _ _ _
      rw [LinearMap.range_comp]
      exact Submodule.finrank_map_le _ _
def flag (r :ℕ) :Flag:=⟨55, 56-(r :ℤ),56,16,100-(r :ℤ)⟩
private theorem space_eq (r :ℕ) :
    GS (iO 55) (-offset r) 56 16=ahV (flag r) := by
  unfold GS ahV
  apply congrArg (restrictSupport ao)
  ext m
  change (m.degree=iO 55 ∧ -offset r≤(m.weight fP.lP:ℤ) ∧
    (m.weight fP.lP:ℤ)≤56∧m 3≤16) ↔
    ((m.weight BU:ℤ)=55∧56-(r :ℤ)≤(m.weight fP.lP:ℤ) ∧
      (m.weight fP.lP:ℤ)≤56∧(m 3:ℤ)≤16)
  have hg:m.weight BU=m.degree := by
    change m.weight (fun _:Fin 4=>1)=m.degree
    rw [← Finsupp.degree_eq_weight_one]
  rw [hg,show iO 55=55 by rfl]
  unfold offset
  constructor <;> rintro ⟨a,b,c,d⟩ <;> exact ⟨by omega,by omega,c,by omega⟩
private theorem range_eq (r :ℕ) :
    zWl (auo 55 (offset r))=zWl (KP (flag r)) := by
  have ho:Vm 55 (offset r)=(flag r).order := by
    change (99:ℤ) - 55-((r :ℤ) - 56)=100-(r :ℤ)
    omega
  ext Q
  constructor
  · rintro ⟨x,rfl⟩
    refine ⟨⟨x.val,space_eq r ▸ x.property⟩,?_⟩
    change weightedTruncation m9 (flag r).order.toNat (Jx x.val) =
      weightedTruncation m9 (Vm 55 (offset r)).toNat (Jx x.val)
    rw [ho]
  · rintro ⟨x,rfl⟩
    refine ⟨⟨x.val,(space_eq r).symm ▸ x.property⟩,?_⟩
    change weightedTruncation m9 (Vm 55 (offset r)).toNat (Jx x.val) =
      weightedTruncation m9 (flag r).order.toNat (Jx x.val)
    rw [ho]
private theorem opposite (F:Flag) (hguard :F.lower≤1710) :
    zsE ao (zWl (KP F))≤oppositeBound F:= by
  by_cases ho:F.order≤0
  · simpa [oppositeBound,ho] using le_of_eq (fTs F ho)
  have hker :=ker_embed F
  have hn:=(KP F).finrank_range_add_finrank_ker
  rw [aDd] at hn
  have hc:=bjv.proof aw7.proof F
  let D:=zsE ao (zWl (debitMap F))
  have hd:=(debitMap F).finrank_range_add_finrank_ker
  rw [zvt,Fintype.card_coe] at hd
  have ht:=tail_card F
  let below:=U1 F.degree (min F.upper (F.order - 1)) F.cap
  let tail:=U1 F.degree F.upper F.cap - below
  change ((tailColumns F).card:ℤ)=tail at ht
  have hr : (zsE ao (zWl (KP F)) :ℤ) ≤
      oldCount F - tail+D:= by dsimp [D]; omega
  unfold oppositeBound
  rw [ite_eq_right ho]
  change _≤(if F.lower≤0 then below.toNat else
    (oldCount F - tail+min (latticeAllowance F) tail).toNat)
  by_cases hl:F.lower≤0
  · rw [ite_eq_left hl]
    have hz :D =0:= by simp [D,lower_zero F hl]
    have he :oldCount F - tail=below:= by rw [full_count F hl]; dsimp [tail]; omega
    omega
  · rw [ite_eq_right hl]
    have hv :D ≤(reducedColumns F).card:= calc
      _≤zsE ao (zWl (momentMap F (momentColumns F))) :=
        rank_le_of_ker_le (qajFMeb.proof F (by omega) hguard)
      _≤zsE ao (zWl (momentMap F (reducedColumns F))) :=
        rank_le_of_ker_le (qO9urca.proof F (by omega) (by omega))
      _≤_:= by
        simpa only [zvt,Fintype.card_coe] using
          Submodule.finrank_le (zWl (momentMap F (reducedColumns F)))
    have hy : (D:ℤ)≤latticeAllowance F:= by rw [← reduced_card F]; exact_mod_cast hv
    have hz : (D:ℤ)≤tail:= by rw [← ht]; dsimp [D]; omega
    have hm:=le_min hy hz
    omega
theorem rank_le_opposite (r :ℕ) :KC r (oppositeBound (flag r)) := by
  refine (rank_le_block 55 (offset r)).trans ?_
  rw [range_eq]
  exact opposite _ (by dsimp [flag]; omega)
end
end q1US8Va
