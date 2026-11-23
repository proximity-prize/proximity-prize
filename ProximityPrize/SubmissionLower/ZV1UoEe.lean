import ProximityPrize.SubmissionLower.ZITfVad
import ProximityPrize.SubmissionLower.ZLIH4nd
set_option Elab.async false
set_option autoImplicit true
namespace qK9H6va
noncomputable section
open aR (ao)
open fP (Form GS Jx m9 aMe avQ
  avP)
open MvPolynomial
open scoped BigOperators
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private instance :CharP ao P1.p :=
  charP_of_injective_algebraMap (algebraMap K1.K ao).injective P1.p
private def dgL (q:ℕ) (g:ℤ) :Form →ₗ[ao] (ait q g→ao) :=
  LinearMap.pi fun e=>lcoeff ao e.val
private theorem dgW {q:ℕ} {g:ℤ} (Q:GS (iO q) (-g) 56 16)
    {e :Fin 4 →₀ ℕ} (he : (auo q g Q).coeff e≠0) :
    e.degree=iO q∧e.weight m9<(Vm q g).toNat := by
  have hQ: (Q:Form).IsWeightedHomogeneous (fun _=>(1 :ℕ)) (iO q) := by
    intro m hm
    rw [← Finsupp.degree_eq_weight_one]
    exact (Q.property (mem_support_iff.mpr hm)).1
  change (weightedTruncation m9 (Vm q g).toNat (Jx Q)).coeff e≠0 at he
  rw [coeff_weightedTruncation] at he
  by_cases ht:e.weight m9<(Vm q g).toNat
  · have hc: (Jx Q).coeff e≠0:= by simpa only [ite_eq_left ht] using he
    exact ⟨by simpa only [Finsupp.degree_eq_weight_one] using aMe hQ hc,ht⟩
  · simp only [ite_eq_right ht,ne_self_iff_false] at he
private theorem gAw (q:ℕ) (g:ℤ) :
    Set.InjOn (dgL q g) (LinearMap.range (auo q g)) := by
  rintro _ ⟨Q,rfl⟩ _ ⟨R,rfl⟩ h
  ext e
  by_cases he :e.degree=iO q∧e.weight m9<(Vm q g).toNat
  · exact congrFun h ⟨e,he⟩
  · rw [not_ne_iff.mp (fun hQ=>he (dgW Q hQ)),
      not_ne_iff.mp (fun hR=>he (dgW R hR))]
theorem fS4 (q:ℕ) (g:ℤ) :
    Module.finrank ao (LinearMap.range (auo q g))≤(Gy q g).rank := by
  classical
  let A:=dgL q g
  let VY:=A.comp (auo q g)
  let coord:LinearMap.range (auo q g) →ₗ[ao] LinearMap.range VY :=
    (A.domRestrict _).codRestrict _ (by
      rintro ⟨_,⟨Q,rfl⟩⟩
      exact ⟨Q,rfl⟩)
  have hinj:Function.Injective coord:= fun Q R h =>
    Subtype.ext (gAw q g Q.property R.property (congrArg Subtype.val h))
  let basis :Module.Basis (XN q g) ao (GS (iO q) (-g) 56 16) :=
    basisRestrictSupport ao _
  let E :Matrix (ait q g) (XN q g) ao :=
    Matrix.of fun e m=>VY (basis m) e
  let φ:=ZMod.castHom (dvd_refl P1.p) ao
  let M:=(Gy q g).map φ
  let R:=Matrix.diagonal fun e :ait q g=>avQ e.val
  let C:=Matrix.diagonal fun m:XN q g=>avP m.val
  have hdegree :iO q≤56:=(min_le_right _ _).trans (gAv q)
  have hE :E=R*M*C:= by
    ext e m
    rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
    change (auo q g (basis m)).coeff e.val =
      avQ e.val*φ (Gy q g e m)*avP m.val
    have hm: (basis m:Form)=monomial m.val 1 :=
      coe_basisRestrictSupport_apply (R:=ao) _ m
    change (weightedTruncation m9 (Vm q g).toNat
      (Jx (basis m))).coeff e.val= _
    rw [coeff_weightedTruncation,ite_eq_left e.property.2,hm]
    rw [c3K _ _ (m.property.1.trans e.property.1.symm)
      (m.property.1.trans_le hdegree)]
    simp only [Gy,prefixMatrix,map_mul,map_natCast]
    ac_rfl
  calc
    _≤Module.finrank ao (LinearMap.range VY) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    _=E.rank :=(Matrix.rank_of_basis basis VY).symm
    _=(R*M*C).rank :=congrArg Matrix.rank hE
    _≤M.rank :=(Matrix.rank_mul_le_left (R*M) C).trans (Matrix.rank_mul_le_right R M)
    _≤_:=Matrix.rank_map_le φ _
theorem eiE (q:ℕ) :b5w q≤Oi q :=
  Finset.sum_le_sum fun r _=>fS4 q (offset r)
end
end qK9H6va
