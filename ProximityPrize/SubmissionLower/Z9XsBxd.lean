import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.ZqZuDUb
set_option Elab.async false
set_option autoImplicit true
namespace P1_6_4_1_2
set_option backward.isDefEq.respectTransparency false
noncomputable section
open aR jA NR aFN
open scoped Polynomial BigOperators
open private aJI bXk cV b5x bcu BA cEy cZl from ProximityPrize.SubmissionLower.S
open private aCD bCI cFU from ProximityPrize.SubmissionLower.S
private theorem dLK {a :Shape} {α:ao} {N D:ao[X]} {U:ℕ}
    (hN :N.natDegree≤1) (hD:D.natDegree≤1) {F:jK} (hF:Jn a F)
    (hseed :gY F≤U) (q:Fin (a.b+1)) (c:abE a q.val) :
    (BA a α N D q F c).natDegree≤U + (a.b - q.val) := by
  classical
  rw [bXk]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  split
  next he =>
    apply (Polynomial.natDegree_smul_le _ _).trans
    have hB:=(aJI hF hm).1
    have hU:m none≤U:=(MvPolynomial.monomial_le_degreeOf _ hm).trans hseed
    have hq:=b5x hB (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) he
    have hn: (N^(m (some 0) - k)).natDegree≤ m (some 0) - k :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left _ hN)
    have hd: (D^(a.b - cV m)).natDegree≤a.b - cV m :=
      Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left _ hD)
    calc
      _≤(m none+(m (some 0) - k))+(a.b - cV m) := by
        unfold bcu
        apply Polynomial.natDegree_mul_le.trans
        apply Nat.add_le_add _ hd
        apply Polynomial.natDegree_mul_le.trans
        apply Nat.add_le_add _ hn
        exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le _)
      _≤_:= by omega
  next=>simp
private theorem cGo {a :Shape} {q U:ℕ} {α:ao}
    {F:jK} {G:Lq} {D:ao[X]} (hD:D ≠0)
    (w:abE a q→ao) (p:jK →ₗ[ao] (abE a q→ao[X]))
    (hp : ∀ c,(p F c).natDegree≤U + (a.b - q) ∧
      algebraMap ao[X] kS (p F c) =
        (algebraMap ao[X] kS D)^(a.b - q)*bfj a α q c G) :
    (∀ k :Fin (U + 1+(a.b - q)),(aCD w p F).coeff k.val=0) ↔
      dot a α q w G=0:= by
  have hdeg: (aCD w p F).natDegree≤U + (a.b - q) := by
    rw [bCI]
    exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun c _ =>
      (Polynomial.natDegree_smul_le _ _).trans (hp c).1
  have hz : (∀ k :Fin (U + 1+(a.b - q)),(aCD w p F).coeff k.val=0) ↔
      aCD w p F=0:= by
    refine ⟨fun h=>Polynomial.ext fun n => ?_,by intro h k; rw [h,Polynomial.coeff_zero]⟩
    rw [Polynomial.coeff_zero]
    by_cases hn:n<U + 1+(a.b - q)
    · exact h ⟨n,hn⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hmap :algebraMap ao[X] kS (aCD w p F) =
      (algebraMap ao[X] kS D)^(a.b - q)*dot a α q w G:= by
    rw [bCI,dot,Finset.mul_sum,map_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Algebra.smul_def,map_mul,(hp c).2,IsScalarTower.algebraMap_apply ao ao[X] kS]
    ring
  rw [hz,← (map_eq_zero_iff _ (IsFractionRing.injective ao[X] kS)),hmap]
  have hne :algebraMap ao[X] kS D ≠0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ao[X] kS)).2 hD
  simp [pow_ne_zero _ hne]
private theorem rank_le (a :Shape) (U:ℕ) {Γ s} (P:jF Γ s)
    (L:kH P) (α:ao) (V:Submodule ao jK) [Module.Finite ao V]
    (hcap : ∀ F∈V,Jn a F∧gY F≤U)
    (hroot :P.H.IsRoot α) (hsimple :P.H.derivative.eval α≠0) :
    TT V (amn P L a (O8 α)) ≤
      ∑ q∈Finset.range (a.b+1),(a.b+a.j - q)*ay8 a q*(U + 1+(a.b - q)) := by
  classical
  obtain ⟨N,D,hD,hNdeg,hDdeg,hnorm⟩:=eFi P L α hroot hsimple
  obtain ⟨w,hw⟩:=Sy.proof a α
  have hD' : algebraMap ao[X] kS D ≠0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ao[X] kS)).2 hD
  let p:=BA a α N D
  let E := ∀ q:Fin (a.b+1),(Test a q.val×Fin (U + 1+(a.b - q.val)))→ao
  let f :V →ₗ[ao] E :=
    LinearMap.pi fun q=>LinearMap.pi fun ij =>
      (Polynomial.lcoeff ao ij.2.val).comp ((aCD (w q ij.1) (p q)).comp V.subtype)
  have hker :LinearMap.ker f=(amn P L a (O8 α)).comap V.subtype := by
    ext F
    obtain ⟨hF,hseed⟩:=hcap F.val F.property
    have hsupport :=cEy
      (algebraMap ao[X] kS N/algebraMap ao[X] kS D) hF
    have hp (q:Fin (a.b+1)) (c:abE a q.val) :=
      And.intro (dLK (α:= α) hNdeg hDdeg hF hseed q c)
        (cZl (α:= α) (N :=N) hD' hF q c)
    rw [LinearMap.mem_ker,Submodule.mem_comap]
    simp only [Submodule.subtype_apply,hnorm,hw _ hsupport]
    constructor
    · intro hf q i
      apply (cGo hD (w q i) (p q) (hp q)).mp
      intro k
      exact congrFun (congrFun hf q) (i,k)
    · intro hf
      funext q ij
      exact (cGo hD (w q ij.1) (p q) (hp q)).mpr (hf q ij.1) ij.2
  have hdim:Module.finrank ao E =
      ∑ q∈Finset.range (a.b+1),(a.b+a.j - q)*ay8 a q*(U + 1+(a.b - q)) := by
    unfold E
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_pi,Fintype.card_prod,Fintype.card_fin]
    exact Fin.sum_univ_eq_sum_range
      (fun q=>(a.b+a.j - q)*ay8 a q*(U + 1+(a.b - q))) (a.b+1)
  exact (cFU _ _ f hker).trans hdim.le
end
end P1_6_4_1_2
