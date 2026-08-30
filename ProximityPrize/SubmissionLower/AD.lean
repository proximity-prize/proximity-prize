import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.EL
namespace ProximityPrize.SubmissionLower.RCN267
open RCN136 RCN313 RCN138
open RCN132 RCN137
noncomputable section
section PartialDerivatives
variable {σ K:Type*} [Field K]
theorem pderiv_zero_of_degree_zero (i:σ) (F:MvPolynomial σ K)
   (hdegree:F.degreeOf i=0):MvPolynomial.pderiv i F=0:=by
 apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
 intro hmem
 exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hmem) hdegree
theorem pderiv_zero_iff_degree_zero_below_char
   (i:σ) (F:MvPolynomial σ K) (p:ℕ) [CharP K p]
   (hdegree:F.degreeOf i < p):
   MvPolynomial.pderiv i F=0 ↔ F.degreeOf i=0:=by
 classical
 constructor
 · intro hzero
   apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   by_contra hn
   have hpos:0 < d i:=by omega
   have hsmall:d i < p:=(MvPolynomial.monomial_le_degreeOf i hd).trans_lt hdegree
   let e:σ →₀ ℕ:=d-Finsupp.single i 1
   have he:e+Finsupp.single i 1=d:=
     Finsupp.sub_add_single_one_cancel (by omega:d i≠0)
   have hnat:e i+1=d i:=by
     have hh:=congrArg (fun f:σ →₀ ℕ => f i) he
     simpa only [Finsupp.add_apply,Finsupp.single_eq_same] using hh
   have hcast:(d i:K)≠0:=
     (CharP.cast_eq_zero_iff K p (d i)).not.mpr (Nat.not_dvd_of_pos_of_lt hpos hsmall)
   have hcoef:(e i:K)+1≠0:=by
     simpa only [←hnat,Nat.cast_add,Nat.cast_one] using hcast
   have hz:MvPolynomial.coeff e (MvPolynomial.pderiv i F)=0:=by
     rw [hzero,MvPolynomial.coeff_zero]
   rw [MvPolynomial.coeff_pderiv,he] at hz
   exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hd) hcoef hz
 · exact pderiv_zero_of_degree_zero i F
end PartialDerivatives
section SurfaceCommutation
variable {K L:Type*} [Field K] [Field L]
theorem surfaceMap_pderiv_X (φ:Polynomial K →+*L) (i:Fin 4) (j:Fin 3):
   MvPolynomial.pderiv j (surfaceMap φ (MvPolynomial.X i))=
     surfaceMap φ (MvPolynomial.pderiv j.succ (MvPolynomial.X i)):=by
 classical
 refine Fin.cases ?_ (fun k => ?_) i
 · simp [MvPolynomial.pderiv_X,Pi.single_apply,Fin.succ_ne_zero]
 · by_cases h:k=j
   · subst k
     simp
   · simp [MvPolynomial.pderiv_X,Pi.single_apply,h,Fin.succ_inj,apply_ite]
theorem surfaceMap_pderiv (φ:Polynomial K →+*L)
   (F:MvPolynomial (Fin 4) K) (j:Fin 3):
   MvPolynomial.pderiv j (surfaceMap φ F)=
     surfaceMap φ (MvPolynomial.pderiv j.succ F):=by
 classical
 induction F using MvPolynomial.induction_on with
 | C a => simp [MvPolynomial.pderiv_C]
 | add P Q hP hQ => simp only [map_add,hP,hQ]
 | mul_X P i hP =>
     simp only [map_mul,map_add,MvPolynomial.pderiv_mul,hP,surfaceMap_pderiv_X]
theorem surfaceMap_pderiv_R (φ:Polynomial K →+*L) (F:MvPolynomial (Fin 4) K):
   MvPolynomial.pderiv (1:Fin 3) (surfaceMap φ F)=
     surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F):=
 surfaceMap_pderiv φ F 1
end SurfaceCommutation
section BaseRegularity
variable {K:Type*} [Field K]
theorem R_derivative_nonzero (F:MvPolynomial (Fin 4) K) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p):
   MvPolynomial.pderiv (2:Fin 4) F≠0:=by
 intro hzero
 have hd:=(pderiv_zero_iff_degree_zero_below_char (2:Fin 4) F p hsmall).mp hzero
 omega
theorem R_derivative_degree_lt (F:MvPolynomial (Fin 4) K) (hpos:0 < F.degreeOf 2):
   (MvPolynomial.pderiv (2:Fin 4) F).degreeOf 2 < F.degreeOf 2:=by
 have hb:=pderiv_same_degree_bound (2:Fin 4) F (F.degreeOf 2) le_rfl
 omega
theorem equation_not_dvd_R_derivative
   (F:MvPolynomial (Fin 4) K) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p):
   ¬ F∣MvPolynomial.pderiv (2:Fin 4) F:=by
 intro hdiv
 have hle:=RCN081.degreeOf_le_of_dvd (2:Fin 4) F _ hdiv
   (R_derivative_nonzero F p hpos hsmall)
 have hlt:=R_derivative_degree_lt F hpos
 omega
end BaseRegularity
section GeometricRegularity
variable (K L:Type*) [Field K] [Field L] [Algebra (RationalCoefficients K) L]
theorem geometricSurfaceMap_pderiv_R (F:MvPolynomial (Fin 4) K):
   MvPolynomial.pderiv (1:Fin 3) (geometricSurfaceMap K L F)=
     geometricSurfaceMap K L (MvPolynomial.pderiv (2:Fin 4) F):=by
 rw [geometricSurfaceMap_eq_surfaceMap]
 exact surfaceMap_pderiv_R _ F
theorem H_proper_on_every_geometric_factor
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F):
   ¬ g∣geometricSurfaceMap K L (MvPolynomial.pderiv (2:Fin 4) F):=by
 intro hdivH
 apply equation_not_dvd_R_derivative F p hpos hsmall
 exact (geometric_factor_dvd_iff K L F (MvPolynomial.pderiv (2:Fin 4) F)
   hF (by omega) g hg hdivF).mp hdivH
theorem geometric_factor_R_derivative_nonzero
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F):
   MvPolynomial.pderiv (1:Fin 3) g≠0:=by
 intro hgzero
 have hdivH:g∣MvPolynomial.pderiv (1:Fin 3) (geometricSurfaceMap K L F):=by
   obtain ⟨G,hG⟩:=hdivF
   refine ⟨MvPolynomial.pderiv (1:Fin 3) G,?_⟩
   rw [hG,MvPolynomial.pderiv_mul,hgzero,zero_mul,zero_add]
 rw [geometricSurfaceMap_pderiv_R] at hdivH
 exact H_proper_on_every_geometric_factor K L F hF p hpos hsmall g hg hdivF hdivH
theorem geometric_factor_R_degree_positive
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F):
   0 < g.degreeOf (1:Fin 3):=by
 apply Nat.pos_of_ne_zero
 intro hzero
 exact geometric_factor_R_derivative_nonzero K L F hF p hpos hsmall g hg hdivF
   (pderiv_zero_of_degree_zero (1:Fin 3) g hzero)
theorem geometric_factor_R_degree_le
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   (g:MvPolynomial (Fin 3) L) (hdivF:g∣geometricSurfaceMap K L F):
   g.degreeOf (1:Fin 3) ≤ F.degreeOf (2:Fin 4):=by
 have hφ:Function.Injective (geometricPolynomialEmbedding K L):=
   (algebraMap (RationalCoefficients K) L).injective.comp
     (IsFractionRing.injective (Polynomial K) (RationalCoefficients K))
 have hne:geometricSurfaceMap K L F≠0:=by
   rw [geometricSurfaceMap_eq_surfaceMap]
   exact surfaceMap_ne_zero _ hφ F hF
 have hc:(geometricSurfaceMap K L F).degreeOf (1:Fin 3) ≤ F.degreeOf (2:Fin 4):=by
   rw [geometricSurfaceMap_eq_surfaceMap]
   exact surfaceMap_degreeOf_le _ F 1
 exact (coordinate_degree_le_of_dvd (1:Fin 3) g _ hdivF hne).trans hc
theorem geometric_factor_regular_gate
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F):
   0 < g.degreeOf (1:Fin 3)∧g.degreeOf (1:Fin 3) ≤ F.degreeOf (2:Fin 4)∧
     g.degreeOf (1:Fin 3) < p∧MvPolynomial.pderiv (1:Fin 3) g≠0∧
     ¬ g∣geometricSurfaceMap K L (MvPolynomial.pderiv (2:Fin 4) F):=by
 have hle:=geometric_factor_R_degree_le K L F hF.ne_zero g hdivF
 exact ⟨geometric_factor_R_degree_positive K L F hF p hpos hsmall g hg hdivF,
   hle,hle.trans_lt hsmall,
   geometric_factor_R_derivative_nonzero K L F hF p hpos hsmall g hg hdivF,
   H_proper_on_every_geometric_factor K L F hF p hpos hsmall g hg hdivF⟩
end GeometricRegularity
end
end ProximityPrize.SubmissionLower.RCN267
