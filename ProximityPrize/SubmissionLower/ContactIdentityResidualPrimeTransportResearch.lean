import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagAffineResidualAutomorphismResearch
namespace ProximityPrize.SubmissionLower.ContactIdentityResidualPrimeTransportResearch
open scoped Classical
open ContactFlagAffineResidualAutomorphismResearch
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def forwardResidualPoint
    (aY v bY aS bS cS:K) (q:Fin 3 → K):Fin 3 → K:=
  ![aY+v*q 0+bY*q 2,
    aS+v*q 1+bS*q 0+cS*q 2,
    q 2]
theorem eval_residualEquiv
    (aY v bY aS bS cS:K) (hv:v≠0)
    (q:Fin 3 → K) (F:Poly3 K):
    MvPolynomial.eval q
        (residualEquiv aY v bY aS bS cS hv F)=
      MvPolynomial.eval (forwardResidualPoint aY v bY aS bS cS q) F:=by
  change MvPolynomial.eval₂Hom (RingHom.id K) q
      (residualAlgHom aY v bY aS bS cS F)=
    MvPolynomial.eval₂Hom (RingHom.id K)
      (forwardResidualPoint aY v bY aS bS cS q) F
  have hq:q=![q 0,q 1,q 2]:=by
    funext i
    fin_cases i <;> rfl
  have hforward:
      forwardResidualPoint aY v bY aS bS cS q=
        ![aY+v*q 0+bY*q 2,
          aS+v*q 1+bS*q 0+cS*q 2,
          q 2]:=by
    funext i
    fin_cases i <;> simp [forwardResidualPoint]
  calc
    _=MvPolynomial.eval₂Hom (RingHom.id K) ![q 0,q 1,q 2]
          (residualAlgHom aY v bY aS bS cS F):=by rw [←hq]
    _=MvPolynomial.eval₂Hom (RingHom.id K)
          ![aY+v*q 0+bY*q 2,
            aS+v*q 1+bS*q 0+cS*q 2,
            q 2] F:=by
      simpa only [Algebra.algebraMap_self,RingHom.id_apply] using
        (eval₂Hom_residual F (q 0) (q 1) (q 2) aY v bY aS bS cS)
    _=_:=by rw [hforward]
theorem comap_pointKernel_residualEquiv
    (aY v bY aS bS cS:K) (hv:v≠0)
    (q:Fin 3 → K):
    (RingHom.ker (MvPolynomial.aeval q).toRingHom).comap
        (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom=
      RingHom.ker
        (MvPolynomial.aeval
          (forwardResidualPoint aY v bY aS bS cS q)).toRingHom:=by
  ext F
  simp only [Ideal.mem_comap,RingHom.mem_ker]
  change MvPolynomial.eval q
      (residualEquiv aY v bY aS bS cS hv F)=0 ↔
    MvPolynomial.eval (forwardResidualPoint aY v bY aS bS cS q) F=0
  rw [eval_residualEquiv]
theorem map_le_pointKernel_iff
    (aY v bY aS bS cS:K) (hv:v≠0)
    (P:Ideal (Poly3 K)) (q:Fin 3 → K):
    P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom ≤
        RingHom.ker (MvPolynomial.aeval q).toRingHom ↔
      P ≤ RingHom.ker
        (MvPolynomial.aeval
          (forwardResidualPoint aY v bY aS bS cS q)).toRingHom:=by
  rw [Ideal.map_le_iff_le_comap,
    comap_pointKernel_residualEquiv aY v bY aS bS cS hv q]
theorem map_le_pointKernel_of_forward_eq
    (aY v bY aS bS cS:K) (hv:v≠0)
    (P:Ideal (Poly3 K)) (q qOld:Fin 3 → K)
    (hforward:forwardResidualPoint aY v bY aS bS cS q=qOld)
    (hold:P ≤ RingHom.ker (MvPolynomial.aeval qOld).toRingHom):
    P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom ≤
      RingHom.ker (MvPolynomial.aeval q).toRingHom:=by
  rw [map_le_pointKernel_iff,hforward]
  exact hold
structure RegularPrimeData (G T H:Poly3 K) where
  ideal:Ideal (Poly3 K)
  isPrime:ideal.IsPrime
  G_mem:G∈ideal
  T_mem:T∈ideal
  H_not_mem:H∉ideal
  ne_point:∀ q:Fin 3 → K,
    ideal≠RingHom.ker (MvPolynomial.aeval q).toRingHom
def RegularPrimeData.mulRegularityUnit
    {G T H:Poly3 K} (D:RegularPrimeData G T H)
    (c:K) (hc:c≠0):
    RegularPrimeData G T (MvPolynomial.C c*H):=by
  have hu:IsUnit (MvPolynomial.C c:Poly3 K):=
    (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
  refine {
    ideal:=D.ideal
    isPrime:=D.isPrime
    G_mem:=D.G_mem
    T_mem:=D.T_mem
    H_not_mem:=?_
    ne_point:=D.ne_point
  }
  intro hmem
  exact D.H_not_mem ((D.ideal.unit_mul_mem_iff_mem hu).mp hmem)
@[simp] theorem RegularPrimeData.mulRegularityUnit_ideal
    {G T H:Poly3 K} (D:RegularPrimeData G T H)
    (c:K) (hc:c≠0):
    (D.mulRegularityUnit c hc).ideal=D.ideal:=rfl
def RegularPrimeData.mapResidual
    {G T H:Poly3 K} (D:RegularPrimeData G T H)
    (aY v bY aS bS cS:K) (hv:v≠0):
    RegularPrimeData
      (residualAlgHom aY v bY aS bS cS G)
      (residualAlgHom aY v bY aS bS cS T)
      (residualAlgHom aY v bY aS bS cS H):=by
  let E:=residualEquiv aY v bY aS bS cS hv
  let Pnext:Ideal (Poly3 K):=D.ideal.map E.toRingEquiv.toRingHom
  letI:D.ideal.IsPrime:=D.isPrime
  haveI:Pnext.IsPrime:=Ideal.map_isPrime_of_equiv E.toRingEquiv
  refine {
    ideal:=Pnext
    isPrime:=inferInstance
    G_mem:=?_
    T_mem:=?_
    H_not_mem:=?_
    ne_point:=?_
  }
  · exact Ideal.mem_map_of_mem E.toRingEquiv.toRingHom D.G_mem
  · exact Ideal.mem_map_of_mem E.toRingEquiv.toRingHom D.T_mem
  · intro hmem
    exact D.H_not_mem
      ((Ideal.apply_mem_of_equiv_iff (f:=E.toRingEquiv)
        (I:=D.ideal) (x:=H)).mp hmem)
  · intro q heq
    apply D.ne_point (forwardResidualPoint aY v bY aS bS cS q)
    have hback:Pnext.comap E.toRingEquiv.toRingHom=D.ideal:=by
      ext F
      exact Ideal.apply_mem_of_equiv_iff (f:=E.toRingEquiv)
        (I:=D.ideal) (x:=F)
    rw [←hback,heq,
      comap_pointKernel_residualEquiv aY v bY aS bS cS hv q]
@[simp] theorem RegularPrimeData.mapResidual_ideal
    {G T H:Poly3 K} (D:RegularPrimeData G T H)
    (aY v bY aS bS cS:K) (hv:v≠0):
    (D.mapResidual aY v bY aS bS cS hv).ideal=
      D.ideal.map
        (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom:=rfl
theorem mem_mapResidual_iff
    {G T H:Poly3 K} (D:RegularPrimeData G T H)
    (aY v bY aS bS cS:K) (hv:v≠0) (F:Poly3 K):
    residualAlgHom aY v bY aS bS cS F∈
        (D.mapResidual aY v bY aS bS cS hv).ideal ↔
      F∈D.ideal:=by
  exact Ideal.apply_mem_of_equiv_iff
    (f:=(residualEquiv aY v bY aS bS cS hv).toRingEquiv)
      (I:=D.ideal) (x:=F)
end
end ProximityPrize.SubmissionLower.ContactIdentityResidualPrimeTransportResearch
