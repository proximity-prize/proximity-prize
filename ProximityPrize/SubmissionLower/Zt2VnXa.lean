import ProximityPrize.SubmissionLower.ZFO2WXb
import ProximityPrize.SubmissionLower.Z7B8rOc
set_option Elab.async false
open _root_ renaming Fin.castSucc → z1o, Function.comp_apply → z3s, IsFractionRing.injective → zxb, MvPolynomial.eval → zY9, MvPolynomial.eval_rename → zCp, MvPolynomial.pderiv → zWe, MvPolynomial.rename → zHw, Polynomial.C → z1z
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qwWTALb
noncomputable section
open Polynomial
open P5 (K p twist)
open P5_7_1
open qaySLPd
open qlc9qed (duQ)
open cu (L FX)
open private values from ProximityPrize.SubmissionLower.ZFO2WXb
private theorem conjugate_at_zero {B:TopRow} {z :K} {S:K[X]}
    (hS:S.map twist=S) (h:atTop (topConjugate B) (twist z) S=0) :
    atTop B z S=0:= by
  let σ:=Polynomial.mapRingHom (frobenius L p)
  have hf (T:K[X]) (hT:T.map twist=T) :
      σ (cu.j9 T)=cu.j9 T :=
    (cu.dio T).symm.trans (congrArg cu.j9 hT)
  have hv :σ ∘ values z S=values (twist z) S:= by
    funext j
    fin_cases j
    · change (z1z (aR.embed z)).map (frobenius L p) =
        z1z (aR.embed (twist z))
      rw [Polynomial.map_C]
      exact congrArg z1z (((algebraMap K L).map_frobenius p z).symm)
    · exact hf S hS
    · exact hf S.derivative ((Polynomial.derivative_map S twist).symm.trans (congrArg derivative hS))
    · exact hf (hasseDeriv 2 S)
        ((Polynomial.hasseDeriv_map twist 2 S).symm.trans (congrArg (hasseDeriv 2) hS))
  rw [duQ,topConjugate,MvPolynomial.eval_map,← hv,← MvPolynomial.eval₂_comp] at h
  have hσ:Function.Injective σ:=Polynomial.map_injective _ (frobenius L p).injective
  have hi:=zxb L[X] FX
  have hz :zY9 (values z S) B=0 :=
    hσ (by simpa only [map_zero] using hi (by simpa only [map_zero] using h))
  rw [duQ]
  rw [hz,map_zero]
private theorem cvh (B:TopRow) (v :Fin 4→ L[X]) :
    zY9 v B =
      ((YN L[X] B).map (zY9 (v ∘ z1o))).eval (v 3) := by
  change zY9 v B =
    ((MvPolynomial.optionEquivLeft _ _ (zHw finSuccEquivLast B)).map
      (zY9 (v ∘ z1o))).eval (v 3)
  rw [← MvPolynomial.optionEquivLeft_elim_eval,zCp]
  apply congrArg (fun a :Fin 4→ L[X]=>zY9 a B)
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [z3s,finSuccEquivLast_last]
    rfl
  · rw [z3s,finSuccEquivLast_castSucc]
    rfl
private theorem cut_at_zero {B:TopRow} {z :K} {S:K[X]}
    (hB:atTop B z S=0) (hd:atTop (zWe 3 B) z S=0) :
    atTop (up (cut B)) z S=0:= by
  let v :=values z S
  let ev :=zY9 (v ∘ z1o)
  let f :=YN L[X] B
  let c:=f.natDegree
  have hroot (Q:TopRow) (hQ:atTop Q z S=0) :
      ((YN L[X] Q).map ev).eval (v 3)=0:= by
    rw [← cvh]
    apply zxb L[X] FX
    simpa only [v,← duQ,map_zero] using hQ
  have h0:=hroot B hB
  change (f.map ev).eval (v 3)=0 at h0
  have h1 :=hroot (zWe 3 B) hd
  have hview:YN L[X] (zWe 3 B)=f.derivative :=
    aeA.gLd B
  rw [hview] at h1
  have hz :ev (cut B)=0:= by
    change ev (if c=0 then f.coeff 0 else f.resultant f.derivative c (c-1))=0
    by_cases hc:c=0
    · rw [ite_eq_left hc]
      rw [show f=C (f.coeff 0) from eq_C_of_natDegree_eq_zero hc,Polynomial.map_C,eval_C] at h0
      exact h0
    · rw [ite_eq_right hc]
      exact map_resultant_eq_zero_of_common_root ev f f.derivative le_rfl
        (natDegree_derivative_le _) (Or.inl hc) (v 3) h0 h1
  rw [duQ]
  change jA.qV (zY9 v (zHw z1o (cut B)))=0
  rw [zCp]
  change jA.qV (ev (cut B))=0
  rw [hz,map_zero]
end
end qwWTALb
