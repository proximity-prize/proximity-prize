import ProximityPrize.SubmissionLower.M
import ProximityPrize.SubmissionLower.O
set_option Elab.async false
open _root_ renaming IsCoprime→lI,MvPolynomial→lz,Nat.add_lt_add_of_le_of_lt→mD,Polynomial→cy,Polynomial.C→lJ,Polynomial.X→aU,Polynomial.coeff_C_mul_X_pow→lV,Polynomial.coeff_sub→nX,Polynomial.mapRingHom→nI,Polynomial.natDegree→nq,congrArg→c9
set_option autoImplicit true
section
namespace axD
noncomputable section
open P0 Polynomial ProximityPrize.Benchmark gR
private theorem aSU (v :Fin 2→K[X]) (j:Fin 2) :
   (v j).natDegree≤uO (v 0) (v 1) := by
 fin_cases j
 · exact le_max_left _ _
 · exact le_max_right _ _
private theorem dtb (v :Fin 2→K[X]) (hc:lI (v 0) (v 1)) :
   ∃ j,v j≠0∧(v j).natDegree=uO (v 0) (v 1) := by
 by_cases hv :v 0=0
 · have h1 :v 1≠0:= by
     intro h
     obtain ⟨a,b,hab⟩:=hc
     simp [hv,h] at hab
   exact ⟨1,h1,by simp [uO,hv]⟩
 by_cases hd: (v 1).natDegree≤(v 0).natDegree
 · exact ⟨0,hv,(max_eq_left hd).symm⟩
 · refine ⟨1,?_,(max_eq_right (by omega)).symm⟩
   intro hz
   simp [hz] at hd
private theorem ccE (del:Finset I) (v L:Fin 2→K[X]) (w:I→K)
    (t:ℕ) (hc:lI (v 0) (v 1)) (hL : ∀ j,(L j).natDegree<t)
    (he : ∀ i∉del,∀ j,(L j).eval (node i)=(v j).eval (node i)*w i)
    (hpos :uO (v 0) (v 1)<t)
    (hroom:t+uO (v 0) (v 1)+del.card≤262144) :
    ∃ P:K[X],P.natDegree+uO (v 0) (v 1)<t ∧
      ∀ i∉del,P.eval (node i)=w i:= by
  classical
  have hcross :v 0*L 1 - v 1*L 0=0:= by
    by_contra hn
    have hb:=kL.agd node IRSProfile.domain.injective _ hn (Finset.univ \ del)
      (by
        intro i hi
        simp only [eval_sub,eval_mul,he i (Finset.mem_sdiff.mp hi).2]
        ring)
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,IRSProfile.card_index] at hb
    have hprod (i j:Fin 2) : (v i*L j).natDegree< uO (v 0) (v 1)+t :=
      natDegree_mul_le.trans_lt (mD (aSU v i) (hL j))
    have hlt:=(natDegree_sub_le (v 0*L 1) (v 1*L 0)).trans_lt
      (max_lt (hprod 0 1) (hprod 1 0))
    omega
  obtain ⟨a,b,hab⟩:=hc
  let P:=a*L 0+b*L 1
  have hdiv (j:Fin 2) :v j*P=L j:= by
    dsimp [P]
    fin_cases j
    · change v 0*(a*L 0+b*L 1)=L 0
      linear_combination L 0*hab+b*hcross
    · change v 1*(a*L 0+b*L 1)=L 1
      linear_combination L 1*hab-a*hcross
  refine ⟨P,?_,?_⟩
  · by_cases hz :P=0
    · simpa [hz] using hpos
    obtain ⟨j,hv,hd⟩:=dtb v ⟨a,b,hab⟩
    have hh:=hL j
    rw [← hdiv j,natDegree_mul hv hz,hd,add_comm] at hh
    exact hh
  · intro i hi
    have hh:=c9 (Polynomial.eval (node i)) hab
    simp only [eval_add,eval_mul,eval_one] at hh
    simp only [P,eval_add,eval_mul,he i hi]
    linear_combination w i*hh
private theorem bYK {U V P Q:K[X]} {s t:ℕ}
  (hU:U.natDegree≤ s) (hV:V.natDegree≤ s)
  (hP:P.natDegree<t) (hQ:Q.natDegree<t) :
  (U*P-V*Q).natDegree<t+s := by
 apply (natDegree_sub_le _ _).trans_lt
 rw [add_comm t s]
 exact max_lt (natDegree_mul_le.trans_lt (mD hU hP))
  (natDegree_mul_le.trans_lt (mD hV hQ))
end
end axD
end
section
namespace axD
noncomputable section
open P0
open scoped BigOperators
private theorem aJH {n:ℕ} (f :ℕ→ℕ) (rows :Fin n→ℕ)
  (h : ∀ i:Fin n,f i.val=rows i) :
  (∑ i∈Finset.range n,f i) = ∑ i:Fin n,rows i:= by
 rw [← Fin.sum_univ_eq_sum_range f n]
 exact Finset.sum_congr rfl (fun i _=>h i)
private theorem cEs (a b c v :ℕ) (hb:0<b) (hv :v≠0)
   (hl: (v - 1)*b^2<c*a^2) (hu:c*a^2≤v*b^2) :
   ⌈(c:ℚ)*((a :ℚ)/(b:ℚ))^2⌉₊ = v := by
 rw [Nat.ceil_eq_iff hv,div_pow,← mul_div_assoc]
 have hpos :0<(b:ℚ)^2 :=pow_pos (Nat.cast_pos.mpr hb) 2
 constructor
 · apply (lt_div_iff₀ hpos).mpr
   exact_mod_cast hl
 · apply (div_le_iff₀ hpos).mpr
   exact_mod_cast hu
end
end axD
end
section
namespace axD
noncomputable section
open P0 gR ProximityPrize.Benchmark Polynomial
private theorem aDT {P:K[X]} {m:ℕ} (hm:0< m)
   (h:P.degree< m) :P.natDegree< m:= by
 by_cases hP:P=0
 · simpa [hP] using hm
 · exact (natDegree_lt_iff_degree_lt hP).mpr h
end
end axD
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace axD
noncomputable section
open P0 Polynomial gR
attribute [local instance 2500] i4.Vv._proof_1 P0.iy._proof_1
local notation "KS" => @CommSemiring.toSemiring K
  (@Semifield.toCommSemiring K (@Field.toSemifield K
    (@CompPoly.Extension.Ext.instField KoalaBear.Field KoalaBear.instFieldField KoalaBear.ext6Params
      i4.Vv._proof_1 KoalaBear.instFactEqNatCardFieldQExt6Params
      KoalaBear.instFactIrreduciblePolynomialFieldPolyExt6Params)))
private def column (n:ℕ) (f :Fin 2→K[X]) :nC :=
 jH (f 0)+jH (f 1)*C (aU ^n)
private theorem bC7 {n:ℕ} (hn:n≠0) {f :Fin 2→K[X]}
   (hf : ∃ j,f j≠0) :column n f≠0:= by
 intro hz
 have h:=c9 Polynomial.Bivariate.swap hz
 simp only [column,jH,map_add,map_mul,Bivariate.swap_map_C,Bivariate.swap_C,
   Polynomial.map_pow,Polynomial.map_X,map_zero] at h
 have hcoeff (i:ℕ) :=c9 (fun q:nC=>q.coeff i) h
 have h0:f 0=0:= by simpa [lV,Ne.symm hn] using hcoeff 0
 have h1 :f 1=0:= by simpa [lV,coeff_C,hn] using hcoeff n
 obtain ⟨j,hj⟩:=hf
 fin_cases j
 · exact hj h0
 · exact hj h1
private theorem bcH (n:ℕ) (f :Fin 2→K[X]) :
   (column n f).natDegree≤uO (f 0) (f 1) :=
 (natDegree_add_le _ _).trans (max_le_max natDegree_map_le
   ((natDegree_mul_C_le _ _).trans natDegree_map_le))
private theorem bcI (n:ℕ) (f :Fin 2→K[X]) (q:K[X])
  (hd : ∀ j,q∣f j) :jH q∣column n f :=
 dvd_add ((nI lJ).map_dvd (hd 0))
  ((((nI lJ).map_dvd (hd 1))).mul_right _)
private theorem dNM (a :K[X]) (n:ℕ) (f :Fin 2→K[X]) :
  jH a*(jH (f 0)+seed^n*jH (f 1)) =
   column n (fun j=>a*f j) := by
 simp only [column,jH,seed,Polynomial.map_mul,← C_pow]
 ring
private def cSi (d:ℕ) (a :K[X]) (β:Fin 2→K[X]) :nC :=
 jH a*(jH (@Polynomial.map K K KS KS twist (β 0)) +
  seed^d*jH (@Polynomial.map K K KS KS twist (β 1)))
private theorem bOU:JO=cSi p:=rfl
private theorem bGK (d:ℕ) (a :K[X]) (β:Fin 2→K[X]) :
  cSi d a β=column d (fun j=>a*(β j).map twist) :=
 dNM a d (fun j=>(β j).map twist)
private theorem bOV {F:Type*} [Field F] (U V U' V' : F[X])
  (hneU:U≠0) (hneV:V≠0) (hne' : U' ≠ 0) (hc:lI U V)
  (he :U*V' = V*U') (hmax :max U'.natDegree V'.natDegree≤ max U.natDegree V.natDegree) :
  max U'.natDegree V'.natDegree=max U.natDegree V.natDegree∧lI U' V' := by
 obtain ⟨a,b,hab⟩:=hc
 let m:=a*U' + b*V'
 have hu:U' = m*U:= by dsimp [m]; linear_combination -U' * hab - b*he
 have hv :V' = m*V:= by dsimp [m]; linear_combination -V' * hab+a*he
 have hm:m≠0:= by intro h; exact hne' (hu.trans (by simp [h]))
 have huD:=c9 nq hu
 have hvD:=c9 nq hv
 rw [natDegree_mul hm hneU] at huD
 rw [natDegree_mul hm hneV] at hvD
 have hdeg:m.natDegree=0:= by omega
 have hunit :IsUnit m:=isUnit_iff_degree_eq_zero.mpr (by rw [degree_eq_natDegree hm,hdeg]; rfl)
 obtain ⟨k,hk⟩:=isUnit_iff_dvd_one.mp hunit
 refine ⟨by omega,a*k,b*k,?_⟩
 calc
  a*k*U' + b*k*V' = (m*k)*(a*U + b*V) := by rw [hu,hv]; ring
  _=1 := by rw [← hk,hab,one_mul]
private def slice (P:nC) (n:ℕ) :K[X] :=
 ∑ j∈Finset.range (P.natDegree+1),monomial j ((P.coeff j).coeff n)
private theorem gr9 (P:nC) (n:ℕ) (x :K) :
  (slice P n).eval x=(P.eval (C x)).coeff n:= by
 rw [eval_eq_sum_range (C x)]
 simp only [slice,eval_finsetSum,eval_monomial,finsetSum_coeff,← C_pow,coeff_mul_C]
private theorem bN1 (P:nC) (n:ℕ) : (slice P n).natDegree≤P.natDegree := by
 apply natDegree_sum_le_of_forall_le
 intro i hi
 exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
private theorem gpi (d:ℕ) (hd:1<d) (r :Fin 2→Fin 2→K) (j l:Fin 2) :
  ((C (r 0 0)+C (r 1 0)*aU +C (r 0 1)*aU^d +
    C (r 1 1)*aU^(d+1)) :K[X]).coeff (j.val+d*l.val)=r j l:= by
 fin_cases j <;> fin_cases l <;>
  simp only [coeff_add,coeff_C_mul_X,lV,coeff_C,Nat.mul_zero,
    Nat.mul_one,Nat.zero_add,Nat.add_zero] <;>
  split_ifs <;> first | omega | simp_all
private theorem edG (d:ℕ) (hd:1<d) (u v w z :Fin 2→K) (j l:Fin 2) :
   (((C (u 0)+C (u 1)*aU ^d)*(C (w 0)+Polynomial.X*C (w 1)) +
     (C (v 0)+C (v 1)*aU)*(C (z 0)+Polynomial.X^d*C (z 1)) :K[X]).coeff
     (j.val+d*l.val))=u l*w j+v j*z l:= by
 let r := fun j l=>u l*w j+v j*z l
 have hex : (C (u 0)+C (u 1)*aU ^d)*(C (w 0)+Polynomial.X*C (w 1)) +
     (C (v 0)+C (v 1)*aU)*(C (z 0)+Polynomial.X^d*C (z 1)) =
     C (r 0 0)+C (r 1 0)*aU +C (r 0 1)*aU^d +
     C (r 1 1)*aU^(d+1) := by
   simp only [r,map_add,map_mul,pow_succ]
   ring
 rw [hex]
 exact gpi d hd r j l
private theorem cGX (d:ℕ) (f :Fin 2→K[X]) (x :K) :
  (column d f).eval (C x)=C ((f 0).eval x)+C ((f 1).eval x)*aU^d:= by
 simp only [column,jH,eval_add,eval_mul,eval_C,eval_map_apply]
private theorem gM1 (d:ℕ) (hd:1<d) (U V:Fin 2→K[X]) (u:e9)
    (i:I) (j l:Fin 2) :
    (U l).eval (node i)*u j i+(V j).eval (node i)*(u l i)^d =
    (((C ((U 0).eval (node i))+C ((U 1).eval (node i))*aU^d) *
          (C (u 0 i)+Polynomial.X*C (u 1 i)) +
        (C ((V 0).eval (node i))+C ((V 1).eval (node i))*aU) *
          (C ((u 0 i)^d)+Polynomial.X^d*C ((u 1 i)^d))) :K[X]).coeff
        (j.val+d*l.val) :=
  (edG d hd (fun l=>(U l).eval (node i)) (fun j=>(V j).eval (node i))
    (fun j=>u j i) (fun l=>(u l i)^d) j l).symm
private def c71 (d:ℕ) (u:e9) (deleted:Finset I) (U V output :nC) :Prop :=
 ∀ i∉deleted,
   U.eval (C (node i))*(C (u 0 i)+Polynomial.X (R:=K)*C (u 1 i)) +
   V.eval (C (node i))*(C (u 0 i^d)+Polynomial.X (R:=K)^d*C (u 1 i^d)) =
     output.eval (C (node i))
private theorem bLh:ake=c71 p:=rfl
private def outputs (d:ℕ) (P:nC) (j l:Fin 2) :=slice P (j.val+d*l.val)
private theorem bJJ (d:ℕ) (hd:1<d) (u:e9) (deleted:Finset I)
  (U V:Fin 2→K[X]) (P:nC)
  (h:c71 d u deleted (column d U) (column 1 V) P) :
  BN.c4b d u deleted U V (outputs d P) := by
 intro i hi j l
 rw [outputs,gr9,← h i hi,cGX,cGX,pow_one]
 exact gM1 d hd U V u i j l
end
end axD
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace bR1
noncomputable section
open MvPolynomial wT
open aez (awZ GA)

private theorem aHJ {F E G:Type*} [Field F]
  [AddCommGroup E] [Module F E] [Module.Finite F E]
  [AddCommGroup G] [Module F G] [Module.Finite F G]
  (f :E →ₗ[F] G) (R:Submodule F E)
  (hdim:Module.finrank F G+Module.finrank F R<Module.finrank F E) :
  ∃ q:E,f q=0∧q∉R:= by
 by_contra hn
 have hle :LinearMap.ker f≤R:= by
  intro q hq
  by_contra hnot
  exact hn ⟨q,LinearMap.mem_ker.mp hq,hnot⟩
 have hk :=Submodule.finrank_mono hle
 have hf :=LinearMap.finrank_range_add_finrank_ker f
 have hr :=(LinearMap.range f).finrank_le
 omega
variable {F:Type*} [Field F] {N :ℕ} {L:lz (Fin 5) F}
variable (C:awZ N L) {h:ℕ}
 (hdeg : ∀ j,L.weightedTotalDegree (vO 131071 j)=GA h j)
end
end bR1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace bR1
noncomputable section
open K1 BN wT MvPolynomial
open aez (denominator Om numerator qW aEc bgd)

private theorem cM2 (Q P:cy K) (s t:K) :
   aeval (D9 P s t) (Om Q)= Q:= by
 let φ:lz (Fin 4) K →+* cy K:=(aeval (D9 P s t)).toRingHom
 have hh:φ.comp Om=RingHom.id (cy K) := by
   apply Polynomial.ringHom_ext
   · intro a
     simp [φ,Om]
   · simp [φ,Om,D9]
 exact RingHom.congr_fun hh Q
private theorem a3G (V:Fin 2→cy K) (P:cy K) (s t:K) :
  aeval (D9 P s t) (denominator V)=V 0+Polynomial.C s*V 1 := by
 simp only [denominator,qW,map_add,map_mul,aeval_X,cM2]
 rfl
private theorem ayD {V:Fin 2→cy K} (hV : ∃ j,V j≠0) :
   denominator V≠0:= by
 intro hz
 have h (s :K) :=a3G V 0 s 0
 simp only [hz,map_zero] at h
 have h0:V 0=0:= by simpa using (h 0).symm
 have h1 :V 1=0:= by simpa [h0] using (h 1).symm
 obtain ⟨j,hj⟩:=hV
 fin_cases j
 · exact hj h0
 · exact hj h1
private theorem c77 (U V:Fin 2→cy K) (O:Fin 2→Fin 2→cy K)
    (Q Q' : cy K) (s t:K) :
    aeval (aju Q Q' s t) (aEc U V O) =
      (V 0+Polynomial.C s*V 1)*Q' -
      ((O 0 0+Polynomial.C s*O 1 0)+Polynomial.C t*(O 0 1+Polynomial.C s*O 1 1) -
        (U 0+Polynomial.C t*U 1)*Q) := by
  rw [aju,← ccf,bgd]
  simp [a3G,numerator,qW,cM2]
  rfl
private theorem cF7 (L:lz (Fin 5) K) (a b:lz (Fin 4) K)
   (d:ℕ) (hL:L∈filtered (vO 131071) (A6 d 1 1 1))
   (hview:xx L=lJ b*aU-Polynomial.C a)
   (hb:b≠0) :
   a.weightedTotalDegree Qb≤1∧b.weightedTotalDegree Qb≤0 ∧
   a.weightedTotalDegree ME≤1∧b.weightedTotalDegree ME≤1 ∧
   a.weightedTotalDegree MD ≤1∧b.weightedTotalDegree MD ≤0:= by
 have hz : (xx L).coeff 0 = -a := by
   rw [hview]
   simp [nX ,Polynomial.coeff_X]
 have hone : (xx L).coeff 1=b:= by
   rw [hview]
   simp [nX ,Polynomial.coeff_C]
 obtain ⟨hy,hs,ht⟩:=bgg d 131071 1 1 1 L hL
 have hs1 :=hs 1 (by decide) (hone ▸ hb)
 have hy1 :=hy 1 (by decide) (hone ▸ hb)
 have ht1 :=ht 1 (by decide) (hone ▸ hb)
 rw [hone] at hs1 hy1 ht1
 have ha (v :Fin 4→ℕ) : (-a).weightedTotalDegree v=a.weightedTotalDegree v := by
   simp [weightedTotalDegree]
 have ha0:a.weightedTotalDegree Qb≤1 ∧
     a.weightedTotalDegree ME≤1∧a.weightedTotalDegree MD ≤1 := by
   by_cases ha' : a=0
   · simp [ha',weightedTotalDegree]
   · have h0: (xx L).coeff 0≠0:=hz ▸ neg_ne_zero.mpr ha'
     have hy0:=hy 0 (by decide) h0
     have hs0:=hs 0 (by decide) h0
     have ht0:=ht 0 (by decide) h0
     simp only [hz,ha,Nat.add_zero] at hy0 hs0 ht0
     exact ⟨hy0,hs0,ht0⟩
 exact ⟨ha0.1,by omega,ha0.2.1,hs1,ha0.2.2,by omega⟩
end
end bR1
end
