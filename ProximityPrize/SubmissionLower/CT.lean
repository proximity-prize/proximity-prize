import ProximityPrize.SubmissionLower.A1
import ProximityPrize.SubmissionLower.C
import ProximityPrize.SubmissionLower.A2
import ProximityPrize.SubmissionLower.A3
import ProximityPrize.SubmissionLower.AB
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option autoImplicit true
section
namespace bR4
noncomputable section




open aeB (rest)


open scoped BigOperators

private theorem cBc (F:Finset (Fin 4)→ℝ) :
    (∑ S∈rest.powerset,(-1 :ℝ)^(3 - S.card)*F S) =
      F (insert 1 (insert 2 (insert 3 ∅))) -
        F (insert 1 (insert 2 ∅))-F (insert 1 (insert 3 ∅))-F (insert 2 (insert 3 ∅)) +
        F (insert 1 ∅)+F (insert 2 ∅)+F (insert 3 ∅)-F ∅ := by
  unfold rest
  simp only [
    Finset.sum_powerset_insert (a :=(1 :Fin 4)) (s :=insert 2 (insert 3 ∅)) (by decide),
    Finset.sum_powerset_insert (a :=(2 :Fin 4)) (s :=insert 3 ∅) (by decide),
    Finset.sum_powerset_insert (a :=(3:Fin 4)) (s := ∅) (by decide),
    Finset.powerset_empty,Finset.sum_singleton]
  norm_num [Finset.card_insert_of_notMem,Finset.mem_insert]
  ring
end
end bR4
end
section
namespace dnJ
noncomputable section
open aR (af)
open oR (AR separant Ev)
open we (eT fW qY)





open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem b9V (f :af 3) (P:Ideal (eT 3)) (j:ℕ)
    (hj:fW (AR f j)∈P) :
    fW (AR f (j+1))∈P ↔
      fW (separant f)*fW (Ev f (AR f j))∈P:= by
  have hterm :
      fW (((2*j+1 :ℕ) :af 3)*AR f j *
        Ev f (separant f))∈P:= by
    simp only [fW,map_mul]
    exact P.mul_mem_right _ (P.mul_mem_left _ hj)
  change (MvPolynomial.map qY) (_-_)∈P↔_
  unfold fW at hterm ⊢
  rw [map_sub,P.sub_mem_iff_left hterm,map_mul]
end
end dnJ
end
section
set_option backward.isDefEq.respectTransparency false
namespace bR5
noncomputable section
open aR (ao embed af)
open oR (separant AR)
open B7 ac1


open scoped Polynomial
open private Lz aG5 acj cNv boZ aUa
 b1O b6B from ProximityPrize.SubmissionLower.AH
open private Uj cZe cMy
 from ProximityPrize.SubmissionLower.AH
private theorem fUs {F:Type} [Field F] [CharP F K1.p]
  (D:Derivation ℕ F F) (L:ℕ) (hL:3≤L) (hchar :L<K1.p)
  (f :af 3) (k :ao →+* F) (x :F) (y :Fin 3→F)
  (hx :D x=1) (hk : ∀ a,D (k a)=0)
  (hy₀:D (y 0)=y 1) (hy₁:D (y 1)=2*y 2)
  (hcut: ((D:F→F)^[L]) (y 0)=0) (hzero :ee k x y f=0)
  (hweight : ∀ U:F[X],U.natDegree<L→(jW k U f).natDegree<K1.p) :
  ∃ U:F[X],U.natDegree<L∧jW k U f=0∧rD x U=y := by
 let _:Differential F :=
  ⟨Derivation.mk' D.toLinearMap.toAddMonoidHom.toIntLinearMap (fun a b=>D.leibniz a b)⟩
 obtain ⟨U,hU,hc,hinit⟩:=Uj hL hchar x y hx hy₀ hy₁ hcut
 have hroot : (jW k U f).eval x=0:= by
  rwa [bdt,hinit]
 exact ⟨U,hU,cMy _ hx _ (hweight U hU)
  (cZe _ hk hc f) hroot,hinit⟩
private theorem cFt (f :af 3) [(Jy f).IsPrime]
   (L:ℕ) (hL:3≤L) (hchar :L<K1.p)
   (hs :GZ (separant f)∉Jy f)
   (hweight : ∀ U: (WE f)[X],U.natDegree<L →
     (jW (Jb f) U f).natDegree<K1.p)
   (hwhole :f∣AR f (L-3)) :
   ∃ U: (WE f)[X],U.natDegree<L ∧
     jW (Jb f) U f=0∧rD (CW f) U=a2l f := by
 let e :=y3 f
 let π:nW →+* ChartRing f :=Ideal.Quotient.mk (Jy f)
 have hsurj:Function.Surjective π:=Ideal.Quotient.mk_surjective
 have hker :RingHom.ker π=Jy f :=Ideal.mk_ker
 have hregular :Lz e (separant f)≠0 :=
   fun h=>hs ((aO5 f _).mp h)
 let qr :CommRing (ChartRing f) :=Ideal.Quotient.commRing (Jy f)
 let qd:IsDomain (ChartRing f) :=Ideal.Quotient.isDomain (Jy f)
 let kf :Field (WE f) :=FractionRing.field (ChartRing f)
 let ka :Algebra (ChartRing f) (WE f) :=inferInstance
 let kl:IsFractionRing (ChartRing f) (WE f) :=inferInstance
 obtain ⟨D,hD⟩ := @cNv (ChartRing f) (WE f) qr kf ka qd kl π f
   hsurj hker hregular
 have hnum :Lz e (AR f (L-3))=0:= by
   obtain ⟨q,hq⟩:=hwhole
   have hzero :Lz e f=0 :=
     (aO5 f _).mpr (Ideal.mem_span_singleton_self _)
   rw [hq,map_mul,hzero,zero_mul]
 rw [b1O e f D hD hregular] at hnum
 have hjet:=(mul_eq_zero.mp hnum).resolve_left (pow_ne_zero _ hregular)
 have hcut: ((D:WE f→WE f)^[L]) (a2l f 0)=0:= by
   change ((D:WE f→WE f)^[L]) (acj e 0)=0
   rw [show L=(L-3+1)+2 by omega,
     b6B e f D hD,hjet,mul_zero]
 let _:CharP (WE f) K1.p :=
   charP_of_injective_ringHom ((Jb f).comp embed).injective K1.p
 have hx :D (CW f)=1 := by
   change D (aG5 e Polynomial.X)=1
   rw [boZ e f D hD,Polynomial.derivative_X,map_one]
 have hk (a :ao) :D (Jb f a)=0:= by
   change D (aG5 e (Polynomial.C a))=0
   rw [boZ e f D hD,Polynomial.derivative_C,map_zero]
 have hzero :ee (Jb f) (CW f) (a2l f) f=0:= by
   rw [bvd]
   exact (aO5 f _).mpr (Ideal.mem_span_singleton_self _)
 exact fUs D L hL hchar f (Jb f) (CW f) (a2l f)
   hx hk (aUa e f D hD 0) (aUa e f D hD 1) hcut hzero hweight
end
end bR5
end
section
set_option backward.isDefEq.respectTransparency false
namespace bR5
noncomputable section

open B7 Ey Pw

open MvPolynomial
open scoped BigOperators Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
open private dh4 from ProximityPrize.SubmissionLower.I
private theorem guo {A:Type} [CommRing A] [IsDomain A]
    {f :A[X]} (s :Factorization f) {d:ℕ} (hf :f.natDegree≤d) (hd:2≤d) :
    f^2∣(aFm s)^d:= by
  classical
  have hdegree : (∑ i,s.multiplicity i*(s.factor i).natDegree)=f.natDegree := by
    conv_rhs=>rw [s.product_eq]
    rw [Polynomial.natDegree_prod_of_monic Finset.univ _ (fun i _=>(s.monic i).pow _)]
    simp only [Polynomial.natDegree_pow]
  refine (dvd_of_eq (congrArg (fun g:A[X]=>g^2) s.product_eq)).trans ?_
  rw [aFm,← Finset.prod_pow,← Finset.prod_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  by_cases hconstant: (s.factor i).natDegree=0
  · simp [Polynomial.eq_one_of_monic_natDegree_zero (s.monic i) hconstant]
  have hmi:s.multiplicity i≤d:= calc
    _=s.multiplicity i*1 :=(mul_one _).symm
    _≤ s.multiplicity i*(s.factor i).natDegree :=
      Nat.mul_le_mul_left _ (Nat.pos_of_ne_zero hconstant)
    _ ≤ ∑ j,s.multiplicity j*(s.factor j).natDegree :=
      Finset.single_le_sum (f := fun j=>s.multiplicity j*(s.factor j).natDegree)
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    _=f.natDegree :=hdegree
    _≤d:=hf
  rw [← pow_mul,← pow_mul]
  apply pow_dvd_pow
  by_cases h:s.multiplicity i≤2
  · rw [min_eq_left h]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (s.multiplicity i) hd
  · rw [min_eq_right (by omega)]
    exact (Nat.mul_le_mul_right 2 hmi).trans_eq (Nat.mul_comm d 2)
private theorem cMU {A B:Type} [CommRing A] [IsDomain A] [CommRing B]
   (e :A[X] →+* B) {f :A[X]} (s :Factorization f) {d:ℕ}
   (hf :f.natDegree≤d) (hd:2≤d) :
   e (aFm s)∣e f∧e f^2∣e (aFm s)^d :=
 ⟨map_dvd e (dh4 s),
   by simpa only [map_pow] using map_dvd e (guo s hf hd)⟩
end
end bR5
end
