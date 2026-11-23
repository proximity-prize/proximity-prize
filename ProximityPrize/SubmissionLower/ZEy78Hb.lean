import ProximityPrize.SubmissionLower.ZK8GpQb
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace qERExMc
noncomputable section
open Polynomial Finset qwGrtCa
open scoped Classical
open P5 (K p)
open cu (L)




open qFD8jve (polarResultant)

variable {E :Type} [Field E]
variable [Algebra L E]
private theorem result_nonzero (G:E[X][X]) (hd:0<G.natDegree) (hp:G.natDegree<p)
   (hi:Irreducible (G.map (algebraMap E[X] (FractionRing E[X])))) :polarResultant G≠0:= by
 let j:E[X] →+* FractionRing E[X] :=algebraMap _ _
 let P:=G.map j
 let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let _:CharP E p:=charP_of_injective_ringHom (algebraMap L E).injective p
 let _:CharP (FractionRing E[X]) p:=charP_of_injective_ringHom
   (IsFractionRing.injective E[X] (FractionRing E[X])) p
 have he :P.natDegree=G.natDegree :=natDegree_map_eq_of_injective
   (IsFractionRing.injective E[X] (FractionRing E[X])) G
 have hp' : 0<P.natDegree :=he ▸ hd
 have hder :=qrezXJe.bD9 hp' (he ▸ hp)
 have hsep:P.Separable :=(separable_iff_derivative_ne_zero hi).mpr (fun hz=> by
   have h:=coeff_derivative P (P.natDegree-1)
   rw [hz,coeff_zero,← Nat.cast_succ,Nat.succ_eq_add_one,
     Nat.sub_add_cancel hp',← leadingCoeff] at h
   exact qrezXJe.cast_ne_zero hp' (he ▸ hp)
     ((mul_eq_zero.mp h.symm).resolve_left (leadingCoeff_ne_zero.mpr hi.ne_zero)))
 have hn:=resultant_ne_zero _ _ hsep
 rw [he,hder,he] at hn
 dsimp only [P] at hn
 rw [derivative_map,resultant_map_map] at hn
 exact fun h=>hn (by rw [show G.resultant G.derivative G.natDegree (G.natDegree-1) =
   polarResultant G from rfl,h,map_zero])
end
end qERExMc
