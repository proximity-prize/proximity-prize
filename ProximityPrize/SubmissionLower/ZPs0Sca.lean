import ProximityPrize.SubmissionLower.ZjZ6ihd
import ProximityPrize.SubmissionLower.ZLITaXd
set_option Elab.async false
open _root_ renaming Finset.sum_add_distrib → zfW, MvPolynomial.C → znf, MvPolynomial.X → z9v, Polynomial.sum_def → zBJ
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace qh06gse
noncomputable section
open Polynomial Finset
open P5 (K)
open qaySLPd (RS)
open cu (FX aZ Equation Jet kr qD)
open vq (Dx aYD bzc apZ)
open ak0 (aTH adg)
open Qv (lX S4)
open private coeffDx_mul from ProximityPrize.SubmissionLower.ZjNfeqc
open private bXz bXA from ProximityPrize.SubmissionLower.DB
open private aMW from ProximityPrize.SubmissionLower.DB
open private dmT from ProximityPrize.SubmissionLower.ZFFuWqa
private theorem aNu {A:Type} [CommRing A] (g:A →+* aZ) (q:A[X]) (t:FX) :
    aTH (q.eval₂ g (znf t)) =
      (∑ j∈q.support,aTH (g (q.coeff j))*(znf t)^j) +
        znf (Dx t)*q.derivative.eval₂ g (znf t) := by
  classical
  have hp (j:ℕ) :aTH ((znf t:aZ)^j) =
      (j:aZ)*(znf t)^(j-1)*znf (Dx t) := by
    rw [← map_pow,bXz,bzc,map_mul,map_mul,map_natCast,map_pow]
  conv_lhs=>rw [eval₂_eq_sum]
  rw [derivative_apply,eval₂_sum]
  simp only [zBJ,map_sum,coeffDx_mul,hp,eval₂_mul,eval₂_C,
    eval₂_X_pow,eval₂_natCast,map_mul,map_natCast,Finset.mul_sum,← zfW]
  apply Finset.sum_congr rfl
  intro j _
  ring
private theorem ordinate_chain (q:Equation) (S:K[X]) :
    let ev :=evalRingHom (znf (kr S))
    aTH (ev q)=ev (lX q) +
      znf (kr S.derivative)*ev q.derivative := by
  classical
  have he :lX q=q.sum (fun j a=>monomial j (aTH a)) := by
    apply Polynomial.ext
    intro n
    rw [zBJ,finsetSum_coeff,sum_eq_single n]
    · exact MvPolynomial.ext _ _ (fun m=>(aMW q n m).trans
        (by rw [coeff_monomial_same,adg]))
    · exact fun j _ hj=>coeff_monomial_of_ne _ hj.symm
    · intro hn
      simp [Polynomial.notMem_support_iff.mp hn]
  change aTH (q.eval₂ (RingHom.id aZ) (znf (kr S)))= _
  rw [aNu,aYD,he]
  simp only [coe_evalRingHom,zBJ,eval_finsetSum,eval_monomial,RingHom.id_apply]
  rfl
private theorem ctV (f :Jet) (S:K[X]) :
    numerator f S-MvPolynomial.C (kr (hasseDeriv 2 S))*denominator f S =
      -aTH (RS f S) := by
  have hsecond:kr S.derivative.derivative=2*kr (hasseDeriv 2 S) := by
    have h:S.derivative.derivative=2*hasseDeriv 2 S:= by
      simpa [hasseDeriv_one',Nat.choose_one_right,nsmul_eq_mul] using
        LinearMap.congr_fun (hasseDeriv_comp (R:=K) 1 1) S
    simp only [h,kr,cu.j9,Polynomial.map_mul,Polynomial.map_ofNat,
      map_mul,map_ofNat]
  have h:=aNu (A:=Equation) (evalRingHom (znf (kr S) :aZ))
    f (kr S.derivative)
  change aTH (fibreMap S f)= _ at h
  rw [aYD,hsecond,map_mul,map_ofNat] at h
  change _ = -aTH (fibreMap S f)
  rw [h]
  simp only [ordinate_chain,add_mul,zfW,mul_assoc,← Finset.mul_sum,
    numerator,denominator,fibreMap,S4,coe_eval₂RingHom,eval₂_finsetSum,
    eval₂_monomial,zBJ]
  ring
private theorem graph_C (z :K) (a :FX) :
    qD z (znf a)=a :=MvPolynomial.eval_C _
private theorem marked_derivative (E :aZ) (z :K) :
    qD z (aTH E)=Dx (qD z E) := by
  classical
  have hX (i:Fin 2) :aTH (z9v i)=0:= by
    simpa [uk.wZ] using bXA (z9v i)
  have h0 (i:Fin 2) :Dx (qD z (z9v i))=0:= by
    fin_cases i <;> simp [qD,dmT,bzc]
  induction E using MvPolynomial.induction_on with
  | C a=>simp only [bXz,graph_C]
  | add P Q hp hq=>simp [map_add,hp,hq]
  | mul_X P i hp=>simp [map_mul,coeffDx_mul,apZ,hp,h0,hX,mul_comm]
end
end qh06gse
