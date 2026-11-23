import ProximityPrize.SubmissionLower.J
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.DG
set_option Elab.async false
open _root_ renaming MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval → zY9, MvPolynomial.eval₂Hom → zOD, MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.map → zDK, RingHom.comp_apply → zQb
section
set_option autoImplicit true
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
namespace as9
noncomputable section
open Polynomial K1 aR dN rW wH Rl
private theorem cGd {R:Type} [CommRing R] {M:ℕ} (a :Fin M→R) (n:ℕ) :
   (∑ i:Fin M,monomial i.val (a i)).coeff n =
     if hn:n<M then a ⟨n,hn⟩ else 0:= by
 classical
 rw [Polynomial.finsetSum_coeff]
 split_ifs with hn
 · rw [Finset.sum_eq_single (⟨n,hn⟩:Fin M)]
   · exact coeff_monomial_same _ _
   · intro i _ hi
     exact coeff_monomial_of_ne _ (fun he=>hi (Fin.ext he.symm))
   · simp
 · exact Finset.sum_eq_zero fun i _=>coeff_monomial_of_ne _ (fun he=>hn (he.symm ▸ i.isLt))
private theorem crL {R:Type} [CommRing R] {M:ℕ}
   (a :Fin M→R) (U:R[X]) (hdegree :U.natDegree<M)
   (hcoeff : ∀ i,a i=U.coeff i.val) : (∑ i:Fin M,monomial i.val (a i))=U:= by
 ext n
 rw [cGd]
 split_ifs with hn
 · exact hcoeff ⟨n,hn⟩
 · exact (coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (Nat.not_lt.mp hn))).symm
theorem map_universalEval {L:Type} [Field L] (k :ao →+* L) (U:L[X])
   (hd:U.natDegree<bf) (Q:af 4) :
   (aip Q).map (zOD k
     (fun i:Fin bf=>U.coeff i.val))=jW k Q U:= by
 let e :=zOD k (fun i:Fin bf=>U.coeff i.val)
 have hU:Sp.map e=U:= by
   rw [Sp,Polynomial.map_sum]
   simp only [C_mul_X_pow_eq_monomial,map_monomial,e,MvPolynomial.eval₂Hom_X']
   exact crL _ U hd (fun _=>rfl)
 have hk :e.comp znf=k :=RingHom.ext fun a=>zTv _ _ a
 change (mapRingHom e) (MvPolynomial.eval₂ (mapRingHom znf)
   (fun i:Fin 4=>hasseDeriv i.val Sp) Q)=jW k Q U
 rw [MvPolynomial.hom_eval₂,Polynomial.mapRingHom_comp,hk]
 simp only [Polynomial.coe_mapRingHom,← hasseDeriv_map,hU,jW]
end
end as9
end
section
set_option autoImplicit true
namespace ap9
noncomputable section
open Polynomial K1 aR dN rW wH Rl MvPolynomial
open scoped BigOperators
private theorem cHa {f :af 4} (T:Li f) (g:mK) :
    ∃ (u:GeoJets) (n:ℕ),∀ A:kT,XP f T A →
      g*mS (bC T.denom)^n - mS u∈gN A:= by
  let D:=bC T.denom
  let d:=mS D
  induction g using MvPolynomial.induction_on with
  | C c =>
    refine ⟨znf c,0,?_⟩
    intro A _
    simp only [pow_zero,mul_one,mS,zTv,sub_self,Ideal.zero_mem]
  | add p q hp hq =>
    obtain ⟨u,n,hu⟩:=hp
    obtain ⟨v,m,hv⟩:=hq
    refine ⟨u*D^m+v*D^n,n+m,?_⟩
    intro A hA
    let J:=gN A
    have hpu:=J.mul_mem_right (d^m) (hu A hA)
    have hqv :=J.mul_mem_right (d^n) (hv A hA)
    have he : (p+q)*d^(n+m) - mS (u*D^m+v*D^n) =
        (p*d^n - mS u)*d^m+(q*d^m - mS v)*d^n:= by
      have hd:mS D =d:=rfl
      simp only [map_add,map_mul,map_pow,hd,pow_add]
      ring
    change (p+q)*d^(n+m) - mS (u*D^m+v*D^n)∈J
    rw [he]
    exact J.add_mem hpu hqv
  | mul_X p i hp =>
    obtain ⟨u,n,hu⟩:=hp
    let v :=bC (T.Fr i)
    refine ⟨u*v,n+1,?_⟩
    intro A hA
    let J:=gN A
    have hpu:=J.mul_mem_right (z9v i*d) (hu A hA)
    have hiv :=J.mul_mem_left (mS u) (hA.ar5 i)
    have he :p*z9v i*d^(n+1) - mS (u*v) =
        (p*d^n - mS u)*(z9v i*d) +
          mS u*(z9v i*d - mS v) := by
      rw [map_mul,pow_succ]
      ring
    change p*z9v i*d^(n+1) - mS (u*v)∈J
    rw [he]
    exact J.add_mem hpu hiv
theorem bGZ {f :af 4} {T:Li f} {A:kT}
   (h:XP f T A) :asY A:= by
 intro g
 obtain ⟨u,n,hu⟩:=cHa T g
 refine ⟨u,bC T.denom^n,?_,?_⟩
 · rw [map_pow]
   exact fun hz=>h.denom (h.extended_prime.mem_of_pow_mem _ hz)
 · rw [map_pow]
   exact hu A h
private theorem eIj {B:kT} (hB:B.IsPrime) {g:rW.jo}
  (hg:zDK ni g∈gN B) :g∈B:= by
 rw [← hB.radical,← vanishingIdeal_zeroLocus_eq_radical (K:=ao)]
 intro x hx
 let ψ:=zY9 (ni ∘ x)
 have hψ:ψ.comp (zDK ni)=ni.comp (zY9 x) := by
  apply RingHom.ext
  intro q
  exact (eval_map _ _ _).trans (eval₂_comp _ _ _).symm
 have hker :gN B≤RingHom.ker ψ:= by
  apply Ideal.map_le_iff_le_comap.mpr
  intro q hq
  change ψ (zDK ni q)=0
  rw [← zQb,hψ,zQb]
  have hq0:zY9 x q=0:=hx q hq
  rw [hq0,map_zero]
 have hv :=RingHom.mem_ker.mp (hker hg)
 change (ψ.comp (zDK ni)) g=0 at hv
 rw [hψ,zQb,← map_zero ni] at hv
 exact ni.injective hv
theorem b7l {f :af 4} {T:Li f} {A B:kT}
  (hA:XP f T A) (hB:XP f T B) (hp:B.IsPrime)
  (hle :lA A≤lA B) :A≤B:= by
 intro g hg
 apply eIj hp
 let q:=zDK ni g
 have hq:q∈gN A:=Ideal.mem_map_of_mem _ hg
 obtain ⟨u,n,hu⟩:=cHa T q
 let d:=mS (bC T.denom)
 have huA:u∈lA A:= by
  change mS u∈gN A
  have hm:=(gN A).mul_mem_right (d^n) hq
  simpa only [d,sub_sub_cancel] using (gN A).sub_mem hm (hu A hA)
 have hm:q*d^n∈gN B:= by
  have huB:mS u∈gN B:=hle huA
  simpa only [sub_add_cancel] using (gN B).add_mem (hu B hB) huB
 exact (hB.extended_prime.mem_or_mem hm).resolve_right
  (fun hz=>hB.denom (hB.extended_prime.mem_of_pow_mem _ hz))
end
end ap9
end
