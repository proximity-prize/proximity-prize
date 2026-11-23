import ProximityPrize.SubmissionLower.ZSLoCda
import ProximityPrize.SubmissionLower.ZFdiUYb
import ProximityPrize.SubmissionLower.Z4uF8Nb
import ProximityPrize.SubmissionLower.Zay1XCa
import ProximityPrize.SubmissionLower.ZfNZDra
set_option Elab.async false
open _root_ renaming CommRing → za6, Finset.range → z4x, Function.Surjective → zpX, Ideal.mem_span_singleton → zxV, Ideal.span → zye, IsFractionRing.injective → zxb, Matrix.of_apply → zN9, Nat.lt_succ_of_le → zB1, Polynomial.X → z7y, Polynomial.map_add → zS4, Polynomial.map_map → zoi, Polynomial.map_mul → zNl, PowerSeries.X → zWv, PowerSeries.constantCoeff → zbO, RingHom.ker → zdq
section
set_option backward.isDefEq.respectTransparency false
namespace qvWbALd
noncomputable section
open Polynomial
open scoped BigOperators WithZero
private theorem det_order {A B:Type} [za6 A] [za6 B] (ρ:A →+* B)
   (π:A) (hπ:zdq ρ=zye {π}) {N d:ℕ}
   (M W:Matrix (Fin N) (Fin N) A) (hd:d≤N) (hW:W.det=1)
   (hz : ∀ i j:Fin N,(i:ℕ)<d→ρ ((W*M) i j)=0) :
   π^d∣M.det:= by
 classical
 let v (i:Fin N) :A:=if (i:ℕ)<d then π else 1
 have hv (i j:Fin N) :v i∣(W*M) i j:= by
   by_cases hi: (i:ℕ)<d
   · simp only [v,hi,ite_true,← zxV,← hπ,RingHom.mem_ker]
     exact hz i j hi
   · simp [v,hi]
 choose b hb using hv
 have hfactor :W*M=Matrix.of fun i j=>v i*b i j:=Matrix.ext hb
 have hprod: (∏ i,v i)=π^d:= by
   change (∏ i:Fin N,if (i:ℕ)<d then π else 1)= _
   rw [Fin.prod_univ_eq_prod_range (fun i=>if i<d then π else 1) N,
     Finset.prod_ite,Finset.prod_const_one,mul_one]
   have hr : ((z4x N).filter fun i=>i<d)=z4x d:= by
     ext i
     simp only [Finset.mem_filter,Finset.mem_range]
     omega
   rw [hr,Finset.prod_const,Finset.card_range]
 have he :=congrArg Matrix.det hfactor
 rw [Matrix.det_mul,hW,one_mul,Matrix.det_mul_column,hprod] at he
 exact ⟨_,he⟩
theorem cfp {A F:Type} [za6 A] [Nontrivial A] [Field F]
   (ρ:A →+* F) (π:A) (hρ:zpX ρ)
   (hπ:zdq ρ=zye {π}) (P Q:A[X]) {m n:ℕ}
   {D:F[X]} (hm:P.natDegree≤ m) (hn:Q.natDegree≤n)
   (hD:D.Monic) (hd:D.natDegree≤ m+n) (hp:D ∣P.map ρ) (hq:D ∣Q.map ρ) :
   π^D.natDegree∣P.resultant Q m n:= by
 classical
 have hl:D∈lifts ρ:= by
   rw [lifts_iff_coeff_lifts]
   intro i
   exact hρ (D.coeff i)
 obtain ⟨D',hmap,hdeg,hD'⟩:=lifts_and_natDegree_eq_and_monic hl hD
 let d:=D.natDegree
 let W:Matrix (Fin (m+n)) (Fin (m+n)) A:=Matrix.of fun i j =>
   if (i:ℕ)<d then ((z7y (R:=A)^(j:ℕ)) %ₘ D').coeff i else if i=j then 1 else 0
 have hrem (j:Fin (m+n)) (hj: (j:ℕ)<d) :
     (z7y ^(j:ℕ) :A[X]) %ₘ D' = z7y ^(j:ℕ) := by
   apply (modByMonic_eq_self_iff hD').mpr
   rw [degree_X_pow,degree_eq_natDegree hD'.ne_zero,hdeg]
   exact Nat.cast_lt.mpr hj
 have htri:W.IsUpperTriangular := by
   intro i j hij
   change j< i at hij
   have hne :i≠j:=ne_of_gt hij
   by_cases hi: (i:ℕ)<d
   · have hj: (j:ℕ)<d:=(show (j:ℕ)< i from hij).trans hi
     simpa [W,hi,hrem j hj,coeff_X_pow,← Fin.ext_iff] using hne
   · simp [W,hi,hne]
 have hdet:W.det=1 := by
   rw [Matrix.det_of_isUpperTriangular htri]
   apply Finset.prod_eq_one
   intro i _
   by_cases hi: (i:ℕ)<d
   · simp [W,hi,hrem i hi]
   · simp [W,hi]
 apply det_order ρ π hπ _ W hd hdet
 intro i j hi
 change (i:ℕ)<d at hi
 let f :=P.map ρ
 let g:= Q.map ρ
 let U:=degreeLT.basis F (m+n)
 let T:=degreeLT.basisProd F m n
 let E :=sylvesterMap f g (natDegree_map_le.trans hm) (natDegree_map_le.trans hn)
 let u:=E (T j)
 have hcoeff (k :Fin (m+n)) :sylvester f g m n k j=(u:F[X]).coeff k := by
   rw [← toMatrix_sylvesterMap' f g (natDegree_map_le.trans hm) (natDegree_map_le.trans hn)]
   exact LinearMap.toMatrix_apply _ _ _ _ _
 have hu:D ∣(u:F[X]) := by
   change D ∣f*((T j).2 :F[X])+g*((T j).1 :F[X])
   exact (hp.mul_right _).add (hq.mul_right _)
 have hsum: (∑ k :Fin (m+n),(u:F[X]).coeff k•(z7y:F[X])^(k :ℕ))=(u:F[X]) := by
   simpa only [U,Submodule.coe_sum,Submodule.coe_smul,degreeLT.basis_repr,degreeLT.basis_val]
     using congrArg (fun v :degreeLT F (m+n)=>(v :F[X])) (U.sum_repr u)
 have hzero :modByMonicHom D (u:F[X])=0:=(modByMonic_eq_zero_iff_dvd hD).mpr hu
 have hsum' := congrArg (fun v :F[X]=>(modByMonicHom D v).coeff i) hsum
 have hw (k :Fin (m+n)) :ρ (W i k)=((z7y (R:=F)^(k :ℕ)) %ₘ D).coeff i:= by
   simp only [W,zN9,hi,ite_true,← coeff_map,map_modByMonic ρ hD',
     hmap,Polynomial.map_pow,Polynomial.map_X]
 have hM (k :Fin (m+n)) :ρ (sylvester P Q m n k j)=sylvester f g m n k j :=
   (congrArg (fun M:Matrix (Fin (m+n)) (Fin (m+n)) F=>M k j)
     (sylvester_map_map P Q m n ρ)).symm
 simp only [Matrix.mul_apply,map_sum,map_mul,hw,hM,hcoeff]
 simp only [map_sum,map_smul,finsetSum_coeff,coeff_smul,smul_eq_mul,
   modByMonicHom_apply,hzero,coeff_zero] at hsum'
 simpa only [mul_comm] using hsum'
variable {F:Type} [Field F]
private theorem cast_le_one (v :Valuation F ℤᵐ⁰) (n:ℕ) :v (n:F)≤1 := by
 induction n with
 | zero=>simp
 | succ n ih=>rw [Nat.cast_succ]; exact v.map_add_le ih (by simp)
theorem cfo (v :Valuation F ℤᵐ⁰) (G:F[X]) (B:ℤᵐ⁰)
    (h : ∀ i,v (G.coeff i)≤B) (m n:ℕ) :
    v (G.resultant G.derivative m n)≤B^(m+n) := by
  classical
  let M:=sylvester G G.derivative m n
  have he (i j:Fin (m+n)) :v (M i j)≤B:= by
    refine Fin.addCases ?_ ?_ j
    · intro a
      simp only [M,sylvester,zN9,Fin.addCases_left]
      split
      · rw [coeff_derivative,← Nat.cast_succ,map_mul]
        exact (mul_le_mul' (h _) (cast_le_one v _)).trans_eq (mul_one _)
      · simp
    · intro a
      simp only [M,sylvester,zN9,Fin.addCases_right]
      split
      · exact h _
      · simp
  change v M.det≤_
  rw [Matrix.det_apply]
  apply v.map_sum_le
  intro σ _
  have hp:v (∏ j,M (σ j) j)≤B^(m+n) := by
    rw [map_prod]
    calc
      _ ≤ ∏ _j:Fin (m+n),B:=Finset.prod_le_prod fun j _=>he _ _
      _ = _:= by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simpa [hs] using hp
end
end qvWbALd
end
section
set_option autoImplicit true
namespace qJ69aaa
theorem proof :qziIa4d.c2 :=qJai0ob.transport
end qJ69aaa
end
section
namespace qC1dA5c
noncomputable section
open Polynomial
open scoped Classical WithZero
open cu (L)
open E7 (KB)
open qxPDCsa (reduce)
open qgbTAnb (liftSeries degree_lift map_lift fWX coeff_extract)
private theorem ceS {E :Type} [Field E] [Algebra L E]
  (a :E →ₐ[L] LaurentSeries L) (f :E[X]) :
  (liftSeries a f).map zbO=reduce a f := by
 rw [fWX]
 ext j
 rw [qgbTAnb.slice,coeff_extract (by simp),reduce,
  q1kuFjb.expansion_coeff,coeff_C_zero]
private theorem residue_kernel :
   zdq (zbO (R:=L)) =
     zye {(zWv:PowerSeries L)} := by
 ext x
 rw [RingHom.mem_ker,zxV,PowerSeries.X_dvd_iff]
theorem proof :qxPDCsa.c6:= by
  intro q Cq z S F u v hr γ hγ hu hv
  let ι:=F.atPlace γ hγ
  let a :=reduce ι u
  let b:=reduce ι v
  let G:=GCDMonoid.gcd a b
  change G.natDegree≤_
  by_cases hG:G=0
  · simp [hG]
  let U:=liftSeries ι u
  let V:=liftSeries ι v
  have hU:U.map zbO=a :=ceS ι u
  have hV:V.map zbO=b:=ceS ι v
  have ha :a.natDegree≤u.natDegree :=hU ▸ natDegree_map_le.trans (degree_lift ι u)
  have hb:b.natDegree≤v.natDegree :=hV ▸ natDegree_map_le.trans (degree_lift ι v)
  have hd:G.natDegree≤u.natDegree+v.natDegree := by
    by_cases hz :a=0
    · have hb₀:b≠0:= fun h=>hG (by simp [G,hz,h])
      exact ((natDegree_le_of_dvd (gcd_dvd_right a b) hb₀).trans hb).trans (Nat.le_add_left ..)
    · exact ((natDegree_le_of_dvd (gcd_dvd_left a b) hz).trans ha).trans (Nat.le_add_right ..)
  let R:=U.resultant V u.natDegree v.natDegree
  have hdiv :zWv ^G.natDegree∣R:= by
    simpa only [natDegree_normalize] using
      qvWbALd.cfp zbO zWv
        (fun r=>⟨PowerSeries.C r,PowerSeries.constantCoeff_C r⟩) residue_kernel U V
        (degree_lift ι u) (degree_lift ι v) (monic_normalize hG)
        (by rwa [natDegree_normalize])
        (by rw [hU]; exact normalize_dvd_iff.mpr (gcd_dvd_left a b))
        (by rw [hV]; exact normalize_dvd_iff.mpr (gcd_dvd_right a b))
  have hR:algebraMap (PowerSeries L) (LaurentSeries L) R=ι (u.resultant v) := by
    rw [show R= _ from rfl,← resultant_map_map,
      map_lift ι u (fun j=>(F.value γ hγ _).symm.trans_le (hu j)),
      map_lift ι v (fun j=>(F.value γ hγ _).symm.trans_le (hv j)),resultant_map_map]
    rfl
  have hval : (F.place γ).value (u.resultant v)≤WithZero.exp (-(G.natDegree :ℤ)) := by
    rw [F.value γ hγ,← hR]
    exact (LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero L R).mpr
      (PowerSeries.X_pow_dvd_iff.mp hdiv)
  have hlog:=(WithZero.log_le_iff_le_exp ((F.place γ).value.ne_zero_iff.mpr hr)).mpr hval
  unfold KB
  omega
end
end qC1dA5c
end
section
set_option backward.isDefEq.respectTransparency false
namespace qnyP9Da
noncomputable section
open Polynomial
open qziIa4d (SeedSeries)
theorem seed_derivation {q:ℕ} (hq:q.Prime) {M:Type} [Field M] [CharP M q]
   (F:Subfield M) (s :M) (hs :s∉F) (hp:s^q∈F) :
   ∃ D:Derivation F (seedField F s) (seedField F s),D (a8p F s)=1 := by
 let E :=seedField F s
 let b:F:=⟨s^q,hp⟩
 let f :F[X] :=(z7y:F[X])^q - C b
 let z :E :=a8p F s
 let e :F[X] →ₐ[F] E :=aeval z
 let i:E →ₐ[F] M:=E.val
 let:Fact q.Prime :=⟨hq⟩
 have hi:Irreducible f :=X_pow_sub_C_irreducible_of_prime hq (fun c h=> by
   have h' : (c:M)^q=s^q:=congrArg Subtype.val h
   exact hs ((frobenius_inj M q h') ▸ c.property))
 have hf :f.Monic:=monic_X_pow_sub_C b hq.ne_zero
 have hcomp (g:F[X]) :i (e g)=aeval s g:= by
   change i (aeval z g)= _
   rw [← AlgHom.comp_apply,← aeval_algHom]
   rfl
 have hfs :aeval s f=0:= by
   simp only [f,map_sub,map_pow,aeval_X,aeval_C]
   exact sub_self _
 have hz :e f=0:=i.injective (show i (e f)=i 0 by rw [hcomp,hfs,map_zero])
 have hm:f=minpoly F z :=minpoly.eq_of_irreducible_of_monic hi hz hf
 have ha :IsAlgebraic F s :=⟨f,hf.ne_zero,hfs⟩
 have he :zpX e := by
   intro a
   have hmem: (a :M)∈E.toSubalgebra :=a.property
   rw [show E.toSubalgebra=Algebra.adjoin F {s} from
     IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic ha,
     Algebra.adjoin_singleton_eq_range_aeval] at hmem
   obtain ⟨g,hg⟩:=hmem
   exact ⟨g,i.injective ((hcomp g).trans hg)⟩
 have hd (g:F[X]) (hg:e g=0) :e (derivative' g)=0:= by
   obtain ⟨a,rfl⟩:f∣g:=hm.symm ▸ minpoly.dvd F z hg
   change e ((f*a).derivative)=0
   have hf' : f.derivative=0:= by
     simp [f,derivative_X_pow]
   simp [derivative_mul,hf',hz]
 exact ⟨Derivation.liftOfSurjective he hd,by
   simpa [e] using Derivation.liftOfSurjective_apply he hd (z7y:F[X])⟩
theorem root_integral {M Γ:Type} [Field M] [LinearOrderedCommGroupWithZero Γ]
    (v :Valuation M Γ) (ι:SeedSeries[X] →+* M)
    (hc : ∀ a :SeedSeries,a≠0→v (ι (C a))=1) (hx :v (ι z7y)<1)
    (G:SeedSeries[X][X]) (r :M) (hlead:G.leadingCoeff.coeff 0≠0)
    (hr :G.eval₂ ι r=0) :v r≤1 := by
  have hpol (g:SeedSeries[X]) :v (ι g)≤1 := by
    induction g using Polynomial.induction_on' with
    | add a b ha hb =>
      rw [map_add]
      exact v.map_add_le ha hb
    | monomial n a =>
      have hca :v (ι (C a))≤1 := by
        by_cases h:a=0
        · simp [h]
        · exact (hc a h).le
      rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow,map_mul,map_pow]
      exact (mul_le_mul' hca (pow_le_one₀ zero_le hx.le)).trans_eq (mul_one 1)
  have hl:v (ι G.leadingCoeff)=1 := by
    have he :ι G.leadingCoeff=ι z7y*ι G.leadingCoeff.divX +
        ι (C (G.leadingCoeff.coeff 0)) := by
      rw [← map_mul,← map_add,X_mul_divX_add]
    have ht:v (ι z7y*ι G.leadingCoeff.divX)<1 := by
      rw [map_mul,mul_comm]
      exact mul_lt_of_le_one_of_lt (hpol _) hx
    rw [he,v.map_add_eq_of_lt_right (ht.trans_eq (hc _ hlead).symm),hc _ hlead]
  classical
  by_contra! hh
  rw [eval₂_eq_sum_range,Finset.sum_range_succ,← leadingCoeff,
      add_eq_zero_iff_eq_neg] at hr
  have hv :=congrArg v hr
  rw [v.map_neg,map_mul,hl,one_mul,map_pow] at hv
  refine (ne_of_lt (v.map_sum_lt (pow_ne_zero _ (zero_lt_one.trans hh).ne') ?_)) hv
  intro i hi
  rw [map_mul,map_pow]
  exact mul_lt_of_le_one_of_lt (hpol _) (pow_lt_pow_right₀ hh (Finset.mem_range.mp hi))
theorem coeff_by {A B:Type} [Semiring A] [Semiring B] (d:A → B) (h0:d 0=0)
   (q:A[X]) (i:ℕ) :
   (q.sum fun j a=>monomial j (d a)).coeff i=d (q.coeff i) := by
 classical
 rw [Polynomial.sum_def,finsetSum_coeff,Finset.sum_eq_single i]
 · exact coeff_monomial_same _ _
 · exact fun j _ h=>coeff_monomial_of_ne _ h.symm
 · intro h
   rw [notMem_support_iff.mp h,h0,monomial_zero_right,coeff_zero]
theorem aNu {A E R:Type} [za6 A] [Field E] [za6 R] [Algebra R E]
   (D:Derivation R E E) (f :A →+* E) (a :E) (P Q:A[X])
   (hc : ∀ i,D (f (P.coeff i))=f (Q.coeff i)) :
   D (P.eval₂ f a)= Q.eval₂ f a+P.derivative.eval₂ f a*D a := by
 let n:=max P.natDegree Q.natDegree+1
 have hP:P.natDegree<n:=zB1 (le_max_left _ _)
 have hQ:Q.natDegree<n:=zB1 (le_max_right _ _)
 have hd:P.derivative.eval₂ f a =
     ∑ i∈z4x n,f (P.coeff i)*(i:E)*a^(i-1) := by
   simp_rw [derivative_apply,eval₂_sum,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X,map_mul,map_natCast]
   exact P.sum_over_range' (fun i=> by simp) n hP
 rw [eval₂_eq_sum_range' f hP,eval₂_eq_sum_range' f hQ,hd,map_sum,
   Finset.sum_mul,← Finset.sum_add_distrib]
 apply Finset.sum_congr rfl
 intro i _
 rw [D.leibniz,D.leibniz_pow,hc]
 simp only [smul_eq_mul,nsmul_eq_mul]
 ring
end
end qnyP9Da
end
section
set_option backward.isDefEq.respectTransparency false
namespace qU1uHGd
noncomputable section
open Polynomial
open cu (L FX)
open P5_7_7 (phys)
open qziIa4d (atZeroRegular)
open q1kuFjb (reduced_pair)
open private common_resultant eval_at_zero from ProximityPrize.SubmissionLower.ZATKiYa
theorem mapped {R S:Type*} [za6 R] [za6 S] (c:R →+* S)
  (F H :R[X]) (d:ℕ) :
  (qW F H d).map c=qW (F.map c) (H.map c) d:= by
 let e :=mapRingHom c
 have he :e.comp C=C.comp c:=RingHom.ext fun a=>map_C c (a :=a)
 have hm (Q:R[X]) : (Q.map C).map e=(Q.map c).map C:= by
  rw [zoi,zoi,he]
 change e (qW F H d)= _
 unfold qW
 rw [← resultant_map_map (F.map C) (an1 F H) d d e,hm]
 congr 1
 simp only [an1,zS4,zNl,map_C,hm,derivative_map,
  e,coe_mapRingHom,map_X]
theorem constant_pencil {R:Type*} [za6 R] (F H :R[X]) (d:ℕ)
   (hd:0<d) (hF:F.natDegree=d) :
   (qW F H d).coeff 0=F.leadingCoeff*F.resultant F.derivative d (d-1) := by
 let e :R[X] →+* R:=constantCoeff
 have he :e.comp C=RingHom.id R:=RingHom.ext fun a=> by simp [e]
 have hm (Q:R[X]) : (Q.map C).map e= Q:= by
   rw [zoi,he,Polynomial.map_id]
 have hc: (an1 F H).map e=F.derivative := by
   simp only [an1,zS4,zNl,hm,map_C,
     show e (z7y:R[X])=0 from coeff_X_zero,C_0,zero_mul,add_zero]
 change e (qW F H d)= _
 unfold qW
 rw [← resultant_map_map (F.map C) (an1 F H) d d e,hm,hc]
 have h:=resultant_add_right_deg F F.derivative d (d-1) 1 (hF ▸ natDegree_derivative_le F)
 rw [show d-1+1=d by omega,pow_one,show F.coeff d=F.leadingCoeff by rw [← hF,leadingCoeff]] at h
 exact h
theorem root_pencil {R S:Type*} [za6 R] [za6 S] (c:R →+* S)
    (F H :R[X]) {d:ℕ} (hd:d≠0) (hf :F.natDegree≤d) (hh:H.natDegree≤d)
    (w u:S) (hr :F.eval₂ c w=0) (hu:F.derivative.eval₂ c w+u*H.eval₂ c w=0) :
    (qW F H d).eval₂ c u=0:= by
  let e :=eval₂RingHom c u
  have he :e.comp C=c:=eval₂RingHom_comp_C c u
  have hm (Q:R[X]) : (Q.map C).eval₂ e w= Q.eval₂ c w:= by rw [eval₂_map,he]
  have hc: (an1 F H).natDegree≤d :=
    (natDegree_add_le _ _).trans (max_le
      ((natDegree_map_le).trans ((natDegree_derivative_le F).trans
        ((Nat.sub_le _ _).trans hf)))
      ((natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hh)))
  change e ((F.map C).resultant (an1 F H) d d)=0
  apply common_resultant _ _ (natDegree_map_le.trans hf) hc hd e w ((hm _).trans hr)
  simpa only [an1,eval₂_add,eval₂_mul,eval₂_C,hm,
    show e (z7y:R[X])=u from eval₂_X c u] using hu
theorem regular {F H T:L[X][X]} {d n:ℕ} (hd:d≠0)
   (hf :F.natDegree≤d) (hh:H.natDegree≤d)
   (hT:qW F H d=C ((z7y:L[X])^n)*T)
   (ht: (T.coeff 0).coeff 0≠0) {w:FX}
   (hr :F.eval₂ phys w=0) (hs :F.derivative.eval₂ phys w≠0) (Q:L[X]) :
   atZeroRegular (-(H.eval₂ phys w/F.derivative.eval₂ phys w)*phys Q^2) := by
 let b := -(H.eval₂ phys w/F.derivative.eval₂ phys w)
 obtain ⟨A,B,hB,hab,hb⟩:=reduced_pair b
 have hB0:B.coeff 0≠0:= by
   intro hz
   have hA0:A.coeff 0≠0:= by
     intro ha
     obtain ⟨U,V,h⟩:=hab
     have he :=congrArg (fun g:L[X]=>g.coeff 0) h
     simp [mul_coeff_zero,ha,hz,coeff_one] at he
   have hA:phys A≠0:=(map_ne_zero_iff phys (zxb L[X] FX)).mpr
     (fun he=>hA0 (by simp [he]))
   have hb0:b≠0:=hb ▸ div_ne_zero hA
     ((map_ne_zero_iff phys (zxb L[X] FX)).mpr hB)
   have hm:b*F.derivative.eval₂ phys w = -H.eval₂ phys w:= by
     simp only [b,neg_mul,div_mul_cancel₀ _ hs]
   have hu:F.derivative.eval₂ phys w+b⁻¹*H.eval₂ phys w=0:= by
     have he :=congrArg (fun t:FX=>b⁻¹*t) hm
     simp only [← mul_assoc,inv_mul_cancel₀ hb0,one_mul,mul_neg] at he
     rw [he,neg_add_cancel]
   have h:=root_pencil phys F H hd hf hh w b⁻¹ hr hu
   rw [hT,eval₂_mul,eval₂_C] at h
   have hn:phys ((z7y:L[X])^n)≠0 :=
     (map_ne_zero_iff phys (zxb L[X] FX)).mpr (pow_ne_zero _ X_ne_zero)
   have hroot :=(mul_eq_zero.mp h).resolve_left hn
   rw [← hb,inv_div] at hroot
   have he :=eval_at_zero T 0 B A (by rwa [← coeff_zero_eq_eval_zero])
     (by rwa [← coeff_zero_eq_eval_zero]) hroot
   exact ht ((coeff_zero_eq_eval_zero _).trans he)
 refine ⟨A*Q^2,B,hB0,?_⟩
 change b*phys Q^2= _
 rw [← hb,map_mul,map_pow,div_mul_eq_mul_div]
end
end qU1uHGd
end
