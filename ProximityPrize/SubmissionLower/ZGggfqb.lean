import ProximityPrize.SubmissionLower.Zgvu91a
import ProximityPrize.SubmissionLower.Z6B1Brd
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace qISdf9a
noncomputable section
open Finset MvPolynomial


open qL2osVa
open cu (FX)

open Cu akS
open scoped BigOperators


set_option backward.isDefEq.respectTransparency true in
private theorem growth_count {n H :ℕ} (B:Ideal (Gc n)) (hB:B.IsPrime)
    (hH :a9K B H) (q:N4 n) {ι:Type} [Fintype ι]
    (r :ι→tu B)
    (hr : ∀ k,LinearIndependent FX (fun ij:Fin (k+1)×ι =>
      (Ideal.Quotient.mk B (aa4 n q))^(ij.1 :ℕ)*r ij.2)) :
    Fintype.card ι≤q.totalDegree*H := by
  classical
  obtain ⟨D,hD⟩:=bz2.proof n B hB hH.dimension
  let mulMark (j:ι) :=LinearMap.mulLeft (e7 n) (ajy B (r j))
  let pieces (j:ι) :=(aIU B D).map (mulMark j)
  let W:=iSup pieces
  have c32 (j:ι) :Module.Finite (e7 n) (pieces j) := by
    dsimp only [pieces]
    infer_instance
  let : ∀ j,Module.Finite (e7 n) (pieces j) :=c32
  obtain ⟨C,hC⟩:=aR1.proof n H B hB hH W (Submodule.finite_iSup pieces)
  have hcount (k :ℕ) : (k+1)*Fintype.card ι≤C+(k*q.totalDegree)*H := by
    let S:=abb (F:=e7 n) (A:=Mb B) (aoe B) W (k*q.totalDegree)
    let v (ij:Fin (k+1)×ι) :=
      ajy B ((Ideal.Quotient.mk B (aa4 n q))^(ij.1 :ℕ)*r ij.2)
    have hmem (ij:Fin (k+1)×ι) :v ij∈S:= by
      obtain ⟨i,j⟩:=ij
      have hdeg: (q^(i:ℕ)).totalDegree≤D + k*q.totalDegree :=
        ((totalDegree_pow q (i:ℕ)).trans
          (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ i.isLt))).trans (Nat.le_add_left _ _)
      have hp:=hD _ (eJS B _ hdeg)
      have hj:pieces j≤W:=le_iSup pieces j
      have hm: (abb (F:=e7 n) (aoe B) (aIU B D)
          (k*q.totalDegree)).map (mulMark j)≤S :=
        ey8 (F:=e7 n) (A:=Mb B) (aoe B)
          (ajy B (r j)) (W:=aIU B D) (U:=W) hj (k*q.totalDegree)
      apply hm
      refine Submodule.mem_map.mpr ⟨_,hp,?_⟩
      simp only [mulMark,v,LinearMap.mulLeft_apply,map_mul,map_pow]
      exact mul_comm _ _
    let w:Fin (k+1)×ι→S:= fun ij=>⟨v ij,hmem ij⟩
    have hw:LinearIndependent (e7 n) w :=
      LinearIndependent.of_comp S.subtype
        (Module.Flat.linearIndependent_one_tmul (S:=e7 n) (hr k))
    exact (by simpa [S,Fintype.card_prod] using hw.fintype_card_le_finrank.trans (hC _))
  by_contra! hn
  have ht:=(Nat.mul_le_mul_left (C+1) (Nat.succ_le_of_lt hn)).trans (hcount C)
  rw [Nat.mul_succ,Nat.mul_assoc,Nat.succ_mul C (q.totalDegree*H)] at ht
  omega
variable {C₀:sQ} [Fact (Irreducible C₀)]
end
end qISdf9a
