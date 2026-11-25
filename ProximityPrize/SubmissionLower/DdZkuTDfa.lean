import ProximityPrize.SubmissionLower.DdZqZuDUb
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming DFunLike.congr_fun → zmU, Fin.last → zym, Fin.sum_univ_three → zCj, Fin.val → zf5, Finsupp.degree_eq_sum → zFi, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_surjective → zld, Ideal.span → zye, Module.finrank → zsE, MvPolynomial → z3y, MvPolynomial.X → z9v, MvPolynomial.algHom_ext → zpH
section
namespace P5_8_5
noncomputable section
open i4 P5_8 MvPolynomial
open scoped BigOperators
theorem linear_eval {σ:Type*} [Finite σ] (I:Ideal (z3y σ nU))
  (hI: (affineHilbertPolynomial I).natDegree=1) (x :ℚ) :
  (affineHilbertPolynomial I).eval x =
    affineDegree I*x+(affineHilbertPolynomial I).coeff 0:= by
 have h:=Polynomial.eq_X_add_C_of_natDegree_le_one hI.le
 have hd:affineDegree I=(affineHilbertPolynomial I).coeff 1 := by
  simp [affineDegree,Polynomial.leadingCoeff,hI]
 nth_rw 1 [h]
 simp [hd]
theorem linear_degree_integral {σ:Type*} [Finite σ] (I:Ideal (z3y σ nU))
  (hI: (affineHilbertPolynomial I).natDegree=1) :
  ∃ z :ℤ,affineDegree I=(z :ℚ) := by
 obtain ⟨m,hm⟩:=exists_eval_affineHilbertPolynomial I
 have h₀:=hm m le_rfl
 have h₁:=hm (m+1) (Nat.le_succ m)
 rw [linear_eval I hI] at h₀ h₁
 refine ⟨(affineHilbertFunction I (m+1) :ℤ)-affineHilbertFunction I m,?_⟩
 push_cast at h₁ ⊢
 linarith
private theorem ab6 (L R:BL 2) :
  ke L R=zye {L} ⊔ zye {R} := by
 simp only [ke,← Ideal.span_union,Set.singleton_union]
private theorem cancel_cut {L R x :BL 2} (h:IsRelPrime L R)
  (hx :R*x∈zye {L}) :x∈zye {L} :=
 Ideal.mem_span_singleton.mpr (h.dvd_of_dvd_mul_left (Ideal.mem_span_singleton.mp hx))
theorem dOy {L R:BL 2} (hL:L≠0)
   (hrel :IsRelPrime L R) {P:Ideal (BL 2)}
   (hP:P∈(ke L R).minimalPrimes) :
   (affineHilbertPolynomial P).natDegree=1 := by
 rw [ab6] at hP
 let:P.IsPrime :=hP.isPrime
 obtain ⟨J,hJ,hJP⟩:=Ideal.exists_minimalPrimes_le (le_sup_left.trans hP.le)
 have hnot:R∉J:= by
   intro hr
   obtain ⟨y,hy,hRy⟩:=Ideal.exists_mul_mem_of_mem_minimalPrimes hJ hr
   exact hy (cancel_cut hrel hRy)
 have hcut:P∈(J ⊔ zye {R}).minimalPrimes :=
   ⟨⟨hP.isPrime,sup_le hJP (le_sup_right.trans hP.le)⟩,
     fun Q hQ hQP=>hP.2 ⟨hQ.1,(sup_le_sup_right hJ.le _).trans hQ.2⟩ hQP⟩
 let:J.IsPrime :=hJ.isPrime
 have htop:=natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hL hJ
 rw [Nat.card_fin] at htop
 have hlow:=principalCut_natDegree_affineHilbertPolynomial_add_one hnot hcut
 omega
private theorem bDL {L R:BL 2} (hrel :IsRelPrime L R) :
  IsLeftRegular (zVv (zye {L}) R) := by
 intro x y h
 obtain ⟨x,rfl⟩:=zld x
 obtain ⟨y,rfl⟩:=zld y
 change zVv (zye {L}) R* zVv _ x =
  zVv (zye {L}) R* zVv _ y at h
 rw [← map_mul,← map_mul,Ideal.Quotient.eq,← mul_sub] at h
 exact Ideal.Quotient.eq.mpr (cancel_cut hrel h)
theorem component_count {L R:BL 2} (hL:L≠0)
    (hrel :IsRelPrime L R) (F:ProperCharts L R) :
    F.count≤L.totalDegree*R.totalDegree := by
  classical
  by_cases he :F.count=0
  · simp [he]
  let I:Ideal (BL 2) :=zye {L}
  have hI:I ≠ ⊤ := by
    have hF:=F.minimal ⟨0,Nat.pos_of_ne_zero he⟩
    rw [ab6] at hF
    intro ht
    exact hF.isPrime.ne_top (top_le_iff.mp (ht ▸ le_sup_left.trans hF.le))
  have hd:=natDegree_affineHilbertPolynomial_span_singleton_add_one hL hI
  rw [Nat.card_fin] at hd
  change (affineHilbertPolynomial I).natDegree+1=3 at hd
  have hdI: (affineHilbertPolynomial I).natDegree=2 := by omega
  have hpure (P:Ideal (BL 2)) (hP:P∈(ke L R).minimalPrimesFinset) :
      (affineHilbertPolynomial P).natDegree=1 :=
    dOy hL hrel (Ideal.mem_minimalPrimesFinset.mp hP)
  have hsum:=principalCut_sum_factorial_mul_leadingCoeff_minimalPrimes_le (bDL hrel)
    (le_rfl :R.totalDegree≤R.totalDegree) (fun P hP=> by
      change _=(affineHilbertPolynomial I).natDegree - 1
      rw [hpure P (by rwa [ab6]),hdI])
  rw [← ab6,mul_assoc] at hsum
  change _≤(R.totalDegree :ℚ)*affineDegree I at hsum
  rw [affineDegree_span_singleton hL,mul_comm] at hsum
  have hs : (∑ P∈(ke L R).minimalPrimesFinset,affineDegree P) ≤
      (L.totalDegree :ℚ)*R.totalDegree := by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun P hP => ?_) hsum
    rw [affineDegree,hpure P hP,hdI]
  have hunit (i:Fin F.count) : (1 :ℚ)≤affineDegree (F.component i) := by
    obtain ⟨z,hz⟩:=linear_degree_integral _ (dOy hL hrel (F.minimal i))
    have hpos :=affineDegree_pos (F.minimal i).isPrime.ne_top
    rw [hz] at hpos ⊢
    exact_mod_cast (Int.add_one_le_of_lt (show 0<z by exact_mod_cast hpos))
  have hb: (F.count:ℚ)≤(L.totalDegree :ℚ)*R.totalDegree := by
    calc
      _ = ∑ _:Fin F.count,(1 :ℚ) := by simp
      _ ≤ ∑ i,affineDegree (F.component i) :=Finset.sum_le_sum fun i _=>hunit i
      _ = ∑ P∈Finset.univ.image F.component,affineDegree P :=
        (Finset.sum_image F.distinct.injOn).symm
      _ ≤ ∑ P∈(ke L R).minimalPrimesFinset,affineDegree P :=
        Finset.sum_le_sum_of_subset_of_nonneg (by
          intro P hP
          obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hP
          exact Ideal.mem_minimalPrimesFinset.mpr (F.minimal i)) (fun P _ _=>affineDegree_nonneg P)
      _≤_:=hs
  exact_mod_cast hb
end
end P5_8_5
end
section
namespace P5_8_5
noncomputable section
open i4 P5_8 MvPolynomial
section
variable (P:Ideal (BL 2)) (T:Chart 2)
abbrev VF :=
 Localization.Away (zVv P T.denominator)
def localize :BL 2 →ₐ[nU] VF P T :=
  (IsScalarTower.toAlgHom nU (BL 2 ⧸ P) (VF P T)).comp
    (Ideal.Quotient.mkₐ nU P)
def aOc:VF P T :=
 IsLocalization.Away.invSelf (zVv P T.denominator)
theorem cKm :
  localize P T T.denominator*aOc P T=1 :=
 IsLocalization.Away.mul_invSelf (zVv P T.denominator)
def qR:jo →ₐ[nU] VF P T :=
 aeval fun i=>localize P T (T.numerator i)*aOc P T
variable {P T}
private def Bt {y :Fin 3→nU} (hy :y∈chartOpen P T) :
  (BL 2 ⧸ P) →ₐ[nU] nU :=
 Ideal.Quotient.liftₐ P (aeval y) fun q hq=>hy.1 q hq
private def amk {y :Fin 3→nU} (hy :y∈chartOpen P T) :
  VF P T →ₐ[nU] nU :=
 IsLocalization.Away.liftAlgHom (f :=Bt hy)
  (zVv P T.denominator) (isUnit_iff_ne_zero.mpr hy.2)
private theorem aII {y :Fin 3→nU} (hy :y∈chartOpen P T)
  (q:BL 2) :amk hy (localize P T q)=eval y q :=
 IsLocalization.Away.lift_eq (g:=(Bt hy).toRingHom)
  (zVv P T.denominator) (isUnit_iff_ne_zero.mpr hy.2)
  (zVv P q)
private theorem bfV {y :Fin 3→nU} (hy :y∈chartOpen P T)
  (q:jo) :amk hy (qR P T q)=eval (T.output y) q:= by
 have hu:=congrArg (amk hy) (cKm P T)
 rw [map_mul,aII,map_one] at hu
 have hi:amk hy (aOc P T)=(eval y T.denominator)⁻¹:= by
  rw [← one_div]
  exact (eq_div_iff hy.2).mpr ((mul_comm _ _).trans hu)
 have h: (amk hy).comp (qR P T)=aeval (T.output y) := by
  apply zpH
  intro i
  change amk hy (qR P T (z9v i))=aeval (T.output y) (z9v i)
  rw [qR,aeval_X,map_mul,aII,hi,aeval_X,Chart.output,div_eq_mul_inv]
 exact zmU h q
private theorem cMz [P.IsPrime]
    (hD:T.denominator∉P) {z :VF P T}
    (hz : ∀ y (hy :y∈chartOpen P T),amk hy z=0) :z=0:= by
  obtain ⟨m,a,ha⟩:=IsLocalization.Away.surj
    (zVv P T.denominator) z
  obtain ⟨q,rfl⟩:=zld a
  change z*localize P T T.denominator^m=localize P T q at ha
  have hq:q∈P:= by
    have hmul :T.denominator*q∈P:= by
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K:=nU) P]
      intro y hy
      change eval y (T.denominator*q)=0
      by_cases hyD:eval y T.denominator=0
      · rw [map_mul,hyD,zero_mul]
      · have hy' : y∈chartOpen P T:=⟨hy,hyD⟩
        have he :=congrArg (amk hy') ha
        rw [map_mul,map_pow,aII,aII,hz y hy',zero_mul] at he
        rw [map_mul,← he,mul_zero]
    exact (‹P.IsPrime›.mem_or_mem hmul).resolve_left hD
  have hq0:localize P T q=0:= by
    change algebraMap (BL 2 ⧸ P) (VF P T)
      (zVv P q)=0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq,map_zero]
  rw [hq0] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (S:=VF P T)
    (zVv P T.denominator)).pow m).mul_right_cancel
      (ha.trans (zero_mul _).symm)
theorem bHO [P.IsPrime]
   (hD:T.denominator∉P) :vanishingIdeal nU (T.output '' chartOpen P T)=RingHom.ker (qR P T).toRingHom:= by
 ext q
 change q∈vanishingIdeal nU (T.output '' chartOpen P T)↔qR P T q=0
 constructor
 · intro hq
   apply cMz hD
   intro y hy
   rw [bfV hy]
   exact hq _ ⟨y,hy,rfl⟩
 · intro hq
   rintro _ ⟨y,hy,rfl⟩
   change eval (T.output y) q=0
   rw [← bfV hy,hq,map_zero]
private def KT (j:ℕ) :jo :=
 ∑ i:Fin k,C ((i.val.choose j:nU)*center^(i.val-j))*z9v i
private theorem d2w (y :Fin k→nU) (j:ℕ) :
  eval y (KT j)=awb y j:= by
 simp [KT,awb]
private theorem dH7
  (hT : ∀ y∈chartOpen P T,∀ j:Fin 3,awb (T.output y) j.val=y j) [P.IsPrime]
  (hD:T.denominator∉P) :
  (qR P T).comp (aeval fun j:Fin 3=>KT j.val)=localize P T:= by
 apply zpH
 intro j
 change qR P T (aeval (fun j:Fin 3=>KT j.val) (z9v j)) =
  localize P T (z9v j)
 rw [aeval_X,← sub_eq_zero]
 apply cMz hD
 intro y hy
 rw [map_sub,bfV,aII,d2w,eval_X,hT y hy j,sub_self]
theorem enK {L R:BL 2} (F:ProperCharts L R) (i:Fin F.count) :
    (F.ideal i).IsPrime ∧
      (affineHilbertPolynomial (F.ideal i)).natDegree =
        (affineHilbertPolynomial (F.component i)).natDegree := by
  let P:=F.component i
  let T:=F.bY i
  let:P.IsPrime :=(F.minimal i).isPrime
  have hD:T.denominator∉P:=F.den_reg i
  have hne :zVv P T.denominator≠0 :=
    mt Ideal.Quotient.eq_zero_iff_mem.mp hD
  let:IsDomain (VF P T) :=Localization.Away.isDomain hne
  have hreg:=(IsRegular.of_ne_zero hne).1
  change (vanishingIdeal nU (T.output '' chartOpen P T)).IsPrime ∧
    (affineHilbertPolynomial (vanishingIdeal nU (T.output '' chartOpen P T))).natDegree =
      (affineHilbertPolynomial P).natDegree
  rw [bHO hD]
  refine ⟨RingHom.ker_isPrime _,le_antisymm ?_ ?_⟩
  · let E :=awayPresentationEquiv P T.denominator
    exact (natDegree_affineHilbertPolynomial_le_of_injective
      (E.symm.toAlgHom.comp (Ideal.kerLiftAlg (qR P T)))
      (E.symm.injective.comp (Ideal.kerLiftAlg_injective (qR P T)))).trans
      (natDegree_affineHilbertPolynomial_awayPresentationIdeal_le P T.denominator)
  · exact natDegree_affineHilbertPolynomial_le_of_away_range P T.denominator hreg
      (qR P T)
      (fun q=>⟨_,zmU (dH7 (F.recover i) hD) q⟩) le_rfl
end
end
end P5_8_5
end
section
namespace P5_8_5
noncomputable section
open i4 aFz P5_8 MvPolynomial
private def Admissible (a :Jn) :Prop :=
 a.C≤a.B∧2*a.C≤a.J∧a.J≤a.B+a.C
def within (a b:Jn) :Prop :=a.B≤b.B∧a.J≤b.J∧a.C≤b.C
theorem A9 :
  0<chartCaps.C∧2*chartCaps.C<chartCaps.J∧chartCaps.J<chartCaps.B:= by
 have hB:small.B=83:=rfl
 have hJ:small.J=25:=rfl
 have hC:small.C=11 :=rfl
 simp only [chartCaps,a₀,D,e,hB,hJ,hC]
 decide
theorem bct :Admissible chartCaps := by
 obtain ⟨_,hCJ,hJB⟩:=A9
 refine ⟨?_,hCJ.le,?_⟩ <;> omega
theorem repair_ok (a :Jn) :Admissible a.repair := by
 rcases a with ⟨B,J,C⟩
 simp only [Admissible,Jn.repair]
 omega
theorem jetCaps_ok (p:BL 2) :Admissible (jetCaps p) := by
 have hindex (v :Fin 3 →₀ ℕ) :v.weight zf5=v 1+2*v 2 := by
   simp [Finsupp.weight_eq_sum,zCj,Nat.mul_comm]
 refine ⟨degreeOf_le_totalDegree _ _,?_,?_⟩
 · change 2*p.degreeOf (zym 2)≤p.weightedTotalDegree zf5
   have hd:p.degreeOf (zym 2)≤p.weightedTotalDegree zf5/2 := by
    apply degreeOf_le_iff.mpr
    intro v hv
    have hw:=le_weightedTotalDegree zf5 hv
    rw [hindex] at hw
    change v 2≤p.weightedTotalDegree zf5/2
    omega
   omega
 · change p.weightedTotalDegree zf5≤p.totalDegree+p.degreeOf (zym 2)
   rw [weightedTotalDegree,Finset.sup_le_iff]
   intro v hv
   have ht:=le_totalDegree hv
   have hc:=(degreeOf_le_iff.mp (le_rfl :p.degreeOf (zym 2)≤_)) v hv
   change v.degree≤p.totalDegree at ht
   rw [zFi,zCj] at ht
   rw [hindex]
   change v 2≤p.degreeOf (zym 2) at hc
   omega
def mix (a b u:Jn) :ℚ :=
  a.B*(b.C*((u.J:ℚ) - 2*u.C)+u.C*b.J) +
  a.J*(b.C*((u.B:ℚ) - u.J)+u.C*((b.B:ℚ)+b.C - b.J)) +
  a.C*(((b.B:ℚ) - b.C)*((u.J:ℚ) - 2*u.C) +
    ((b.J:ℚ) - 2*b.C)*((u.B:ℚ) - u.J+u.C))
theorem boxDifference_linear (u a b:Jn) (m:ℚ) :
  boxDifference u a b m=mix a b u*m+boxDifference u a b 0:= by
 unfold boxDifference anJ mix
 ring
theorem mix_symm (a b u:Jn) :mix a b u=mix b a u:= by
 unfold mix
 ring
theorem mix_mono {a a' b u:Jn} (h:within a a') (hb:Admissible b)
  (hu:2*u.C≤u.J) (hu' : u.J≤u.B) :mix a b u≤ mix a' b u:= by
 obtain ⟨hB,hJ,hC⟩:=h
 obtain ⟨hbB,hbJ,hbBJ⟩:=hb
 have p:0≤(u.J:ℚ) - 2*u.C:=sub_nonneg.mpr (by exact_mod_cast hu)
 have q:0≤(u.B:ℚ) - u.J:=sub_nonneg.mpr (by exact_mod_cast hu')
 have r :0≤(b.B:ℚ)+b.C - b.J:=sub_nonneg.mpr (by exact_mod_cast hbBJ)
 have s :0≤(b.B:ℚ) - b.C:=sub_nonneg.mpr (by exact_mod_cast hbB)
 have t:0≤(b.J:ℚ) - 2*b.C:=sub_nonneg.mpr (by exact_mod_cast hbJ)
 unfold mix
 gcongr
private theorem cast_mixedTerm {x y z :Jn} (hy :Admissible y) (hz :Admissible z) :
  (mixedTerm x y z :ℚ)=x.C*((y.J:ℚ) - y.C)*(2*(z.B:ℚ) - z.J) := by
 have hc:y.C≤y.J:= by have :=hy.2.1; omega
 have hj:z.J≤2*z.B:= by obtain ⟨h₁,_,h₂⟩:=hz; omega
 simp [mixedTerm,Nat.cast_sub hc,Nat.cast_sub hj]
theorem floor_mix (a b u:Jn)
  (ha :Admissible a) (hb:Admissible b) (hu:Admissible u) :
  ⌊mix a b u⌋ = (tW a b u:ℤ) := by
 unfold tW
 rw [← Int.ofNat_ediv_ofNat,← Rat.floor_natCast_div_natCast]
 congr 1
 simp only [Nat.cast_add,cast_mixedTerm ha hu,cast_mixedTerm ha hb,
  cast_mixedTerm hb hu,cast_mixedTerm hb ha,cast_mixedTerm hu ha,cast_mixedTerm hu hb]
 norm_num
 unfold mix
 ring
end
end P5_8_5
end
section
set_option autoImplicit true
namespace P5_8_3
noncomputable section
open i4 P5_8 PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
def lastCut:ℕ:=bo8.m*A - 1
def step:ℕ:=gap A+2
def topWeight:JetVariable 2→ℕ:=Pi.single (some (zym 2)) 1
def nativeBand (s :Jn) :Submodule K Equation :=
 restrictWeightedDegree jetDegreeWeight s.B ⊓
 (restrictWeightedDegree indexWeight s.J ⊓ restrictWeightedDegree topWeight s.C)
def rows (w:Node→K) (T:ℕ) :Submodule K Equation :=
  (nativeBand donorCaps ⊓ restrictWeightedDegree (differentialWeight N) T) ⊓
    ⨅ i:Node,(localConstraintAt (d:=2) bo8.m (node i) (w i)).ker
def symbolBand (s :Jn) :Submodule K (z3y (Fin 3) K) :=
  restrictSupport K
    {u:Fin 3 →₀ ℕ | u.degree≤ s.B∧u.weight zf5≤ s.J∧u (zym 2)≤ s.C}
def powerCaps (a :Jn) (l:ℕ) :Jn:=⟨l*a.B,l*a.J,l*a.C⟩
def dM (a s :Jn) :Prop :=a.B≤ s.B∧a.J≤ s.J∧a.C≤ s.C
instance (a s :Jn) :Decidable (dM a s) := by
 unfold dM
 infer_instance
def layerBound (a :Jn) (l:ℕ) :ℕ :=
  if dM (powerCaps a l) donorCaps then
    zsE K (symbolBand (donorCaps.wD (powerCaps a l)))
  else 0
structure CommonData (Q P:Equation) where
 common :Equation
 divisor :Equation
 left:Equation
 right:Equation
 common_dvd:common∣divisor
 azo:Q=divisor*left
 az7:P=divisor*right
 coprime :IsRelPrime left right
 support : ∃ l:ℕ,apQ.initial divisor∣apQ.initial common^l
 combine : ∀ (R:Equation) (l:ℕ),
   (∀ F:Equation,Irreducible F→F∣Q→F∣P →
     0<jetTotalDegree F→F^l∣R)→ common^l∣R
end
end P5_8_3
end
section
set_option autoImplicit true
namespace P5_8_3
noncomputable section
open i4 P5_8 PolynomialDifferential MvPolynomial Finset
open scoped BigOperators
set_option maxHeartbeats 400000
abbrev jetCaps (P:BL 2) :Jn :=
 ⟨P.totalDegree,P.weightedTotalDegree zf5,P.degreeOf (zym 2)⟩
private theorem total_weight :
  (fun j:Option (Fin 3)=>j.elim 0 (1 :Fin 3→ℕ))=jetDegreeWeight:= by
 funext j
 cases j <;> rfl
private theorem top_weight :
  (fun j:Option (Fin 3)=>j.elim 0 (Pi.single (zym 2) (1 :ℕ)))=topWeight:= by
 funext j
 cases j <;> simp [topWeight,Pi.single_apply]
theorem initial_caps (Q:Equation) :jetCaps (apQ.initial Q)=caps Q:= by
 unfold jetCaps caps
 congr 1
 · rw [← weightedTotalDegree_one,apQ.b6k,total_weight]
   rfl
 · exact apQ.b6k zf5 Q
 · rw [← weightedTotalDegree_piSingle,apQ.b6k,top_weight,topWeight,
    weightedTotalDegree_piSingle]
   rfl
private theorem exponent_weights (u:Fin 3 →₀ ℕ) :
   u.degree=u 0+(u 1+u (zym 2)) ∧
    u.weight zf5=u 1+2*u (zym 2) := by
 constructor
 · rw [zFi,Fin.sum_univ_succ,Fin.sum_univ_two]
   rfl
 · rw [Finsupp.weight_apply,Finsupp.sum_fintype _ _ (by simp),Fin.sum_univ_succ,Fin.sum_univ_two]
   simp only [Fin.val_zero,Fin.val_succ,Fin.val_one,smul_eq_mul,mul_zero,mul_one,zero_add]
   change u 1+u (Fin.last 2)*2= _
   rw [Nat.mul_comm _ 2]
theorem actual_caps (P:BL 2) :
   (jetCaps P).C≤(jetCaps P).B∧2*(jetCaps P).C≤(jetCaps P).J ∧
     (jetCaps P).J≤(jetCaps P).B+(jetCaps P).C:= by
 classical
 change P.degreeOf (zym 2)≤P.totalDegree ∧
   2*P.degreeOf (zym 2)≤P.weightedTotalDegree zf5 ∧
   P.weightedTotalDegree zf5≤P.totalDegree+P.degreeOf (zym 2)
 refine ⟨degreeOf_le_totalDegree _ _,?_,?_⟩
 · have h:P.degreeOf (zym 2)≤P.weightedTotalDegree zf5/2 := by
     apply degreeOf_le_iff.mpr
     intro u hu
     have hw:=le_weightedTotalDegree zf5 hu
     rw [(exponent_weights u).2] at hw
     omega
   omega
 · apply Finset.sup_le
   intro u hu
   have hb:=le_totalDegree hu
   have hc:=monomial_le_degreeOf (zym 2) hu
   obtain ⟨h1,h2⟩:=exponent_weights u
   change u.degree≤P.totalDegree at hb
   rw [h1] at hb
   rw [h2]
   omega
theorem repair_band {s :Jn} {P:BL 2} (h:dM (jetCaps P) s) :
  P∈aFz.GS s.repair.B s.repair.J s.repair.C:= by
 obtain ⟨hB,hJ,hC⟩:=h
 obtain ⟨hcB,hcJ,hJC⟩:=actual_caps P
 have hc: (jetCaps P).C≤ min s.C (min s.B (s.J/2)) := by
  exact le_min hC (le_min (hcB.trans hB) (by omega))
 exact aFz.aIz.mpr ⟨hB,le_min hJ (hJC.trans (Nat.add_le_add hB hc)),hc⟩
theorem mem_nativeBand {s :Jn} {Q:Equation} : Q∈nativeBand s↔dM (caps Q) s := by
 simp only [nativeBand,Submodule.mem_inf,mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
  topWeight,weightedTotalDegree_piSingle]
 rfl
theorem caps_dvd {G H :Equation} (h:G∣H) (hH :H≠0) :dM (caps G) (caps H) := by
 refine ⟨weightedTotalDegree_le_of_dvd jetDegreeWeight h hH,
  weightedTotalDegree_le_of_dvd indexWeight h hH,?_⟩
 change G.degreeOf (some (zym 2))≤H.degreeOf (some (zym 2))
 simpa only [topWeight,weightedTotalDegree_piSingle] using weightedTotalDegree_le_of_dvd topWeight h hH
theorem c54 {s :Jn} {G H L Q:Equation} (hQ:Q≠0) (hG:G∣H)
   (he :Q=H*L) (h:dM (caps Q) s) :dM (caps L) (s.wD (caps G)) := by
 have hn:H*L≠0:=he ▸ hQ
 have hH :=left_ne_zero_of_mul hn
 have hL:=right_ne_zero_of_mul hn
 have ⟨hGB,hGJ,hGC⟩:=caps_dvd hG hH
 obtain ⟨hB,hJ,hC⟩:=h
 rw [he] at hB hJ hC
 change (H*L).weightedTotalDegree jetDegreeWeight≤ s.B at hB
 change (H*L).weightedTotalDegree indexWeight≤ s.J at hJ
 change (H*L).degreeOf (some (zym 2))≤ s.C at hC
 rw [weightedTotalDegree_mul _ _ _ hH hL] at hB hJ
 rw [degreeOf_mul_eq hH hL] at hC
 refine ⟨?_,?_,?_⟩
 · change H.weightedTotalDegree jetDegreeWeight≥G.weightedTotalDegree jetDegreeWeight at hGB
   change L.weightedTotalDegree jetDegreeWeight≤ s.B-G.weightedTotalDegree jetDegreeWeight
   omega
 · change H.weightedTotalDegree indexWeight≥G.weightedTotalDegree indexWeight at hGJ
   change L.weightedTotalDegree indexWeight≤ s.J-G.weightedTotalDegree indexWeight
   omega
 · change H.degreeOf (some (zym 2))≥G.degreeOf (some (zym 2)) at hGC
   change L.degreeOf (some (zym 2))≤ s.C-G.degreeOf (some (zym 2))
   omega
def layerCost (a :Jn) (l:ℕ) :ℕ :=
 if dM (powerCaps a l) donorCaps then aMt (donorCaps.wD (powerCaps a l)) else 0
private theorem division_fiber (W e i:ℕ) (he :0<e) :
   ((range (W+1)).filter (fun T=>(W - T)/e=i)).card≤e := by
 classical
 suffices hcard: ((range (W+1)).filter (fun T=>(W - T)/e=i)).card≤(range e).card by
   simpa only [card_range] using hcard
 apply card_le_card_of_injOn (fun T=>(W - T) % e)
 · intro T _
   exact mem_range.mpr (Nat.mod_lt _ he)
 · intro T hT U hU h
   obtain ⟨ht,ht'⟩:=mem_filter.mp hT
   obtain ⟨hu,hu'⟩:=mem_filter.mp hU
   have ht0:=mem_range.mp ht
   have hu0:=mem_range.mp hu
   have htd:=Nat.mod_add_div (W - T) e
   have hud:=Nat.mod_add_div (W-U) e
   rw [ht'] at htd
   rw [hu'] at hud
   dsimp only at h
   omega
theorem cofactor_eq (a :Jn) (ha :0<a.B) :
  Gq a = ∑ i∈range (donorCaps.B/a.B),layerCost a (i+1) := by
 unfold Gq
 apply sum_congr rfl
 intro i hi
 have hb:=(Nat.le_div_iff_mul_le ha).mp (Nat.succ_le_of_lt (mem_range.mp hi))
 simp only [layerCost,dM,powerCaps,hb,true_and]
theorem group_cutoffs (W e M:ℕ) (he :0<e) (cost:ℕ→ℕ)
    (hzero : ∀ j,M≤j→ cost j=0) :
    (∑ T∈range (W+1),cost ((W - T)/e))≤e * ∑ i∈range M,cost i:= by
  classical
  have hs (T:ℕ) :cost ((W - T)/e) =
      ∑ i∈range M,if (W - T)/e=i then cost i else 0:= by
    let j:=(W - T)/e
    change cost j = ∑ i∈range M,if j=i then cost i else 0
    by_cases hj:j<M
    · rw [sum_eq_single j]
      · simp
      · intro i _ hi
        exact ite_eq_right (Ne.symm hi)
      · intro hn
        exact (hn (mem_range.mpr hj)).elim
    · rw [hzero j (Nat.le_of_not_gt hj)]
      symm
      apply sum_eq_zero
      intro i hi
      exact ite_eq_right (show ¬ j=i from fun h=>hj (h.symm ▸ mem_range.mp hi))
  calc
    _ = ∑ T∈range (W+1),∑ i∈range M,
        if (W - T)/e=i then cost i else 0:=sum_congr rfl fun T _=>hs T
    _ = ∑ i∈range M,∑ T∈range (W+1),
        if (W - T)/e=i then cost i else 0:=sum_comm
    _ ≤ ∑ i∈range M,e*cost i:= by
      apply sum_le_sum
      intro i _
      rw [← sum_filter,sum_const,nsmul_eq_mul]
      exact Nat.mul_le_mul_right _ (division_fiber W e i he)
    _ = _:=(mul_sum ..).symm
end
end P5_8_3
end
section
namespace P5_8_5
noncomputable section
open i4 P5_8 MvPolynomial Filter
open scoped BigOperators
def c1 :Prop :=
  ∀ {L R:BL 2} (F:ProperCharts L R),∃ shift:ℕ,∀ m:ℕ,
    (∑ i,affineHilbertFunction (F.ideal i) m) ≤
      zsE nU (aEl (ke L R) chartCaps (m+shift))
def c2 :Prop :=
  ∀ (L R:BL 2),L≠0→R≠0→ IsRelPrime L R →
    ∀ (u:Jn),0< u.C→2*u.C< u.J→u.J< u.B →
    ∀ᶠ m:ℕ in atTop,
      (zsE nU (aEl (ke L R) u m) :ℚ) ≤
        boxDifference u (jetCaps L) (jetCaps R) m
theorem cp0 {a b c d:ℚ}
   (h : ∀ᶠ m:ℕ in atTop,a*(m:ℚ)+b≤ c*(m:ℚ)+d) :a≤ c:= by
 let line (s t:ℚ) :Polynomial ℚ:=Polynomial.C s*Polynomial.X+Polynomial.C t
 have hd (s t:ℚ) : (line s t).natDegree≤1 :=
   Polynomial.natDegree_add_le_of_degree_le
     ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le) (by simp)
 have h' : ∀ᶠ m:ℕ in atTop,(line a b).eval (m:ℚ)≤(line c d).eval (m:ℚ) :=
   h.mono fun _ hm=> by simpa [line] using hm
 simpa [line] using Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
   (hd a b) (hd c d) h'
end
end P5_8_5
end
