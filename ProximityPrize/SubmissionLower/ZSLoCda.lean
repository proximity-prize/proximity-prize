import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertBidegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComap
import ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedBidegree
import Mathlib.RingTheory.Polynomial.Resultant.Basic
set_option Elab.async false
section
set_option autoImplicit true
namespace qckEfrc
noncomputable section
open Filter Polynomial MvPolynomial
open scoped BigOperators
variable {k σ:Type*} [Field k]
private theorem hilbert_bound [Finite σ] {i:σ}
    {a b c h j r N :ℕ} {g:MvPolynomial (Option σ) k} (hg0:g≠0)
    (hg:g∈restrictCappedBidegree σ k i h j r) (hh:h≤a*N) (hj:j≤b*N)
    (hr :r≤ c*N) :
    affineHilbertFunction
        ((Ideal.span {g}).comap (monomialMap k (cappedBidegreeExponents σ i a b c))) N +
        (a*N - h+1)*(cappedDegreeExponents σ i (b*N - j) (c*N - r)).ncard ≤
      (a*N+1)*(cappedDegreeExponents σ i (b*N) (c*N)).ncard:= by
  have hH :=affineHilbertFunction_comap_span_singleton_add_finrank_le
    (monomialMap k (cappedBidegreeExponents σ i a b c)) hg0
    (M:=restrictCappedBidegree σ k i (a*N) (b*N) (c*N))
    (M' := restrictCappedBidegree σ k i (a*N - h) (b*N - j) (c*N - r))
    (fun _ hP ↦ monomialMap_mem_restrictCappedBidegree hP) fun p hp ↦ by
      have hgp:=mul_mem_restrictCappedBidegree hg hp
      rwa [Nat.add_sub_cancel' hh,Nat.add_sub_cancel' hj,Nat.add_sub_cancel' hr] at hgp
  rwa [finrank_restrictCappedBidegree,finrank_restrictCappedBidegree] at hH
private theorem two_mul_ncard_cast (B C:ℕ) (hCB:C≤B) :
  (2 :ℚ)*(cappedDegreeExponents (Fin 2) 1 B C).ncard=(C+1)*(2*B+2 - C) := by
 have h:=congrArg (Nat.cast:ℕ→ℚ) (two_mul_ncard_cappedDegreeExponents_fin_two B C hCB)
 push_cast [Nat.cast_sub (show C≤2*B+2 by omega)] at h
 exact h
theorem box_degree {a b c h j r :ℕ}
    (ha :0<a) (hb:0<b) (hc:0<c) (hcb:c≤b) {g:MvPolynomial (Option (Fin 2)) k}
    (hg0:g≠0) (hg:g∈restrictCappedBidegree (Fin 2) k 1 h j r) :
    affineDegree
        ((Ideal.span {g}).comap (monomialMap k (cappedBidegreeExponents (Fin 2) 1 a b c))) ≤
      (h*c*(2*b - c)+2*a*(j*c+r*(b - c)) :ℕ) := by
  rcases hcb.lt_or_eq with hcb | rfl
  swap
  ·
    have key : ∀ (S:Set (Option (Fin 2) →₀ ℕ)) [Finite S],S=bidegreeExponents (Fin 2) a c →
        affineDegree ((Ideal.span {g}).comap (monomialMap k S)) ≤
          (h*c*(2*c - c)+2*a*(j*c+r*(c - c)) :ℕ) := by
      rintro S _ rfl
      rw [← bidegreeMap_eq_monomialMap]
      refine (affineDegree_comap_bidegreeMap_span_singleton_le ha hb hg0
        (restrictCappedBidegree_le_restrictBidegree hg)).trans_eq ?_
      rw [Nat.card_eq_fintype_card,Fintype.card_fin,Nat.sub_self,mul_zero,add_zero,
        show 2*c - c=c by omega]
      push_cast
      ring
    exact key _ (cappedBidegreeExponents_eq_bidegreeExponents le_rfl)
  by_cases hproper :Ideal.span {g} = ⊤
  · rw [hproper,Ideal.comap_top,affineDegree_top]
    exact Nat.cast_nonneg _
  have hdim: (affineHilbertPolynomial
      ((Ideal.span {g}).comap (monomialMap k (cappedBidegreeExponents (Fin 2) 1 a b c)))).natDegree
      = 2 := by
    have h:=natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective
      (monomialMap k (cappedBidegreeExponents (Fin 2) 1 a b c))
      (monomialMap_cappedBidegreeExponents_surjective ha hb hc) hg0 hproper
    rw [Finite.card_option,Nat.card_eq_fintype_card,Fintype.card_fin] at h
    omega
  set a' : ℚ:=(a :ℚ)
  set b' : ℚ:=(b:ℚ)
  set c' : ℚ:=(c:ℚ)
  set h' : ℚ:=(h:ℚ)
  set j' : ℚ:=(j:ℚ)
  set r' : ℚ:=(r :ℚ)
  let q₂:ℚ:=(h' * c' * (2*b' - c')+2*a' * (j' * c' + r' * (b' - c')))/2
  let q₁:ℚ:=(2*a' + 2*c' + (2*b' - c')-(a' * (1 - r')*(2 - 2*j' + r') +
    (1 - h')*c' * (2 - 2*j' + r')+(1 - h')*(1 - r')*(2*b' - c')))/2
  let q₀:ℚ:=(2 - (1 - h')*(1 - r')*(2 - 2*j' + r'))/2
  let R:ℚ[X] :=Polynomial.C q₂*Polynomial.X ^2+Polynomial.C q₁*Polynomial.X +
    Polynomial.C q₀
  refine (affineDegree_le_of_eventually_affineHilbertFunction_le hdim
    (R:=R) natDegree_quadratic_le ?_).trans_eq ?_
  · filter_upwards [eventually_ge_atTop (h+j+r)] with N hN
    have hhN :h≤a*N :=(show h≤N by omega).trans (Nat.le_mul_of_pos_left N ha)
    have hjN :j≤b*N :=(show j≤N by omega).trans (Nat.le_mul_of_pos_left N hb)
    have hrN :r≤ c*N :=(show r≤N by omega).trans (Nat.le_mul_of_pos_left N hc)
    have hgap:c*N+N≤b*N := by
      have :=Nat.mul_le_mul_right N hcb
      rwa [Nat.succ_mul] at this
    have hshift:c*N - r≤b*N - j:= by omega
    have hbound:=hilbert_bound hg0 hg
      hhN hjN hrN (a :=a) (b:=b) (c:=c)
    have hT:=two_mul_ncard_cast (b*N) (c*N) (by omega)
    have hT' := two_mul_ncard_cast (b*N - j) (c*N - r) hshift
    have hboundq: ((_:ℕ) :ℚ)≤((_:ℕ) :ℚ) :=Nat.cast_le.mpr hbound
    push_cast [Nat.cast_sub hhN,Nat.cast_sub hjN,Nat.cast_sub hrN] at hboundq hT hT'
    have hR:2*R.eval (N :ℚ)=(a' * N+1)*((c' * N+1)*(2*(b' * N)+2 - c' * N)) -
        (a' * N - h' + 1) *
          ((c' * N - r' + 1)*(2*(b' * N - j')+2 - (c' * N - r'))) := by
      simp only [R,q₂,q₁,q₀,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
        Polynomial.eval_pow,Polynomial.eval_X]
      ring
    rw [← hT,← hT'] at hR
    linarith
  · simp only [R,coeff_add,Polynomial.coeff_C]
    push_cast [Nat.cast_sub (show c≤2*b by omega),Nat.cast_sub hcb.le]
    norm_num [Nat.factorial,q₂]
    ring
end
end qckEfrc
end
section
set_option autoImplicit true
namespace qtQA4Je
open Polynomial
open scoped BigOperators
noncomputable section
private theorem det_order {F:Type*} [Field F] {N d:ℕ}
   (M:Matrix (Fin N) (Fin N) F[X]) (B:Matrix (Fin N) (Fin N) F)
   (a :F) (hd:d≤N) (hB:B.det=1)
   (hz : ∀ i j:Fin N,(i:ℕ)<d→(B*(evalRingHom a).mapMatrix M) i j=0) :
   (X - C a)^d∣M.det:= by
 classical
 let A:=C.mapMatrix B*M
 have hA:A.det=M.det:= by
   rw [show A= _ from rfl,Matrix.det_mul,← RingHom.map_det,hB,map_one,one_mul]
 have hAB: (evalRingHom a).mapMatrix A=B*(evalRingHom a).mapMatrix M:= by
   change (evalRingHom a).mapMatrix (C.mapMatrix B*M)= _
   rw [map_mul]
   congr 1
   ext i j
   change (C (B i j)).eval a= _
   simp
 let v (i:Fin N) :F[X] :=if (i:ℕ)<d then X - C a else 1
 have hv (i j:Fin N) :v i∣A i j:= by
   by_cases hi: (i:ℕ)<d
   · simp only [v,hi,ite_true,dvd_iff_isRoot]
     exact (congrArg (fun M:Matrix (Fin N) (Fin N) F=>M i j) hAB).trans (hz i j hi)
   · simp [v,hi]
 choose b hb using hv
 let B' : Matrix (Fin N) (Fin N) F[X] :=Matrix.of b
 have hfactor :A=Matrix.of fun i j=>v i*B' i j:=Matrix.ext hb
 have hprod: (∏ i,v i)=(X - C a)^d:= by
   change (∏ i:Fin N,if (i:ℕ)<d then (X - C a :F[X]) else 1)= _
   rw [Fin.prod_univ_eq_prod_range (fun i=>if i<d then (X - C a :F[X]) else 1) N,
     Finset.prod_ite,Finset.prod_const_one,mul_one]
   have hr : ((Finset.range N).filter fun i=>i<d)=Finset.range d:= by
     ext i
     simp only [Finset.mem_filter,Finset.mem_range]
     omega
   rw [hr,Finset.prod_const,Finset.card_range]
 rw [← hA,hfactor,Matrix.det_mul_column,hprod]
 exact dvd_mul_right _ _
theorem cfp {F:Type*} [Field F] (P Q:F[X][X]) {m n:ℕ}
   (a :F) {D:F[X]} (hm:P.natDegree≤ m) (hn:Q.natDegree≤n)
   (hD:D.Monic) (hd:D.natDegree≤ m+n)
   (hp:D ∣P.map (evalRingHom a)) (hq:D ∣Q.map (evalRingHom a)) :
   (X - C a)^D.natDegree∣resultant P Q m n:= by
 classical
 let d:=D.natDegree
 let B:Matrix (Fin (m+n)) (Fin (m+n)) F:=Matrix.of fun i j =>
   if (i:ℕ)<d then ((X ^(j:ℕ)) %ₘ D).coeff i else if i=j then 1 else 0
 have hrem (j:Fin (m+n)) (hj: (j:ℕ)<d) :
     (X ^(j:ℕ) :F[X]) %ₘ D =X ^(j:ℕ) := by
   apply (modByMonic_eq_self_iff hD).mpr
   rw [degree_X_pow,degree_eq_natDegree hD.ne_zero]
   exact Nat.cast_lt.mpr hj
 have htri:B.IsUpperTriangular := by
   intro i j hij
   change j< i at hij
   have hne :i≠j:=ne_of_gt hij
   by_cases hi: (i:ℕ)<d
   · have hj: (j:ℕ)<d:=(show (j:ℕ)< i from hij).trans hi
     simpa [B,hi,hrem j hj,coeff_X_pow,← Fin.ext_iff] using hne
   · simp [B,hi,hne]
 have hdet:B.det=1 := by
   rw [Matrix.det_of_isUpperTriangular htri]
   apply Finset.prod_eq_one
   intro i _
   by_cases hi: (i:ℕ)<d
   · simp [B,hi,hrem i hi]
   · simp [B,hi]
 apply det_order _ B a hd hdet
 rw [← sylvester_map_map]
 intro i j hi
 change (i:ℕ)<d at hi
 let f :=P.map (evalRingHom a)
 let g:= Q.map (evalRingHom a)
 let S:=degreeLT.basis F (m+n)
 let T:=degreeLT.basisProd F m n
 let E :=sylvesterMap f g (natDegree_map_le.trans hm) (natDegree_map_le.trans hn)
 let u:=E (T j)
 have hcoeff (k :Fin (m+n)) :sylvester f g m n k j=(u:F[X]).coeff k := by
   rw [← toMatrix_sylvesterMap' f g (natDegree_map_le.trans hm) (natDegree_map_le.trans hn)]
   exact LinearMap.toMatrix_apply _ _ _ _ _
 have hu:D ∣(u:F[X]) := by
   change D ∣f*((T j).2 :F[X])+g*((T j).1 :F[X])
   exact (hp.mul_right _).add (hq.mul_right _)
 have hsum: (∑ k :Fin (m+n),(u:F[X]).coeff k•(X:F[X])^(k :ℕ))=(u:F[X]) := by
   simpa only [S,Submodule.coe_sum,Submodule.coe_smul,degreeLT.basis_repr,degreeLT.basis_val]
     using congrArg (fun v :degreeLT F (m+n)=>(v :F[X])) (S.sum_repr u)
 have hzero :modByMonicHom D (u:F[X])=0:=(modByMonic_eq_zero_iff_dvd hD).mpr hu
 have hsum' := congrArg (fun v :F[X]=>(modByMonicHom D v).coeff i) hsum
 change (B*sylvester f g m n) i j=0
 simp only [Matrix.mul_apply,hcoeff,B,Matrix.of_apply,hi,ite_true]
 simp only [map_sum,map_smul,finsetSum_coeff,coeff_smul,smul_eq_mul,
   modByMonicHom_apply,hzero,coeff_zero] at hsum'
 simpa only [mul_comm] using hsum'
end
end qtQA4Je
end
