import ProximityPrize.SubmissionLower.ZQtCuFa
import ProximityPrize.SubmissionLower.ZkuTDfa
set_option Elab.async false
open _root_ renaming Finsupp.add_apply→mD,Finsupp.single_apply→ oD,Function.Injective→ oK,Ideal.Quotient.mk→lJ,LinearMap.finrank_le_finrank_of_injective→ ov,LinearMap.mulLeft→ oj,Module.finrank→nI,Nat.le_mul_of_pos_right→ oZ,Nat.one_mul→lV,Nat.sub_add_cancel→ oY,Nat.succ_mul→ oq,P5_8.chartCaps→nq,P5_8_1.factorForm→cy,P5_8_1.factorOrders→n5,P5_8_1.flagSpace→aU,P5_8_1.sourceOrders→c9,P5_8_1.targetOrders→lI,P5_8_5.localize→lz,Submodule.finrank_map_le→ oz,Subtype.ext→ ox,Subtype.val→ oy,congrArg→nX
section
set_option autoImplicit true
namespace q2aXx2a
open P5_8_1 MvPolynomial
open scoped Pointwise
local instance :Fact (Nat.Prime i4.p) :=⟨KoalaBear.is_prime⟩
private abbrev Exponent:=Fin 3 →₀ ℕ
private abbrev OnSupport (p:lK) (P:Exponent→Prop) := ∀ e∈p.support,P e
private theorem on_add {p q:lK} {P:Exponent→Prop}
  (hp:OnSupport p P) (hq:OnSupport q P) :OnSupport (p+q) P:= by
 intro e he
 exact (Finset.mem_union.mp (support_add he)).elim (hp e) (hq e)
private theorem on_sub {p q:lK} {P:Exponent→Prop}
  (hp:OnSupport p P) (hq:OnSupport q P) :OnSupport (p - q) P:= by
 intro e he
 exact (Finset.mem_union.mp (support_sub (Fin 3) p q he)).elim (hp e) (hq e)
private theorem on_mul {p q:lK} {P Q R:Exponent→Prop}
  (hp:OnSupport p P) (hq:OnSupport q Q)
  (h : ∀ a b,P a→Q b→R (a+b)) :OnSupport (p*q) R:= by
 classical
 intro e he
 obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp (support_mul p q he)
 exact h a b (hp a ha) (hq b hb)
local notation "Xₚ" => (MvPolynomial.X:Fin 3→lK)
local notation "sₑ" => (fun i:Fin 3=>Finsupp.single i (1 :ℕ))
private theorem on_X {i:Fin 3} {P:Exponent→Prop} (h:P (sₑ i)) :
  OnSupport (Xₚ i) P:= by
 intro e he
 rw [support_X,Finset.mem_singleton] at he
 rwa [he]
private theorem on_XX {i j:Fin 3} {P:Exponent→Prop} (h:P (sₑ i+sₑ j)) :
  OnSupport (Xₚ i*Xₚ j) P:= by
 intro e he
 simp only [MvPolynomial.X,monomial_mul_monomial] at he
 have he' := Finset.mem_singleton.mp (support_monomial_subset he)
 rwa [he']
private theorem mem_space {p:lK} {d:ℕ} {f :Flags} :
 p∈aU d f↔(OnSupport p (fun e=>e.degree=d∧c9 f e)) ∧
   OnSupport (contactChange p) (lI f) :=Iff.rfl
private noncomputable def contactFactor (i:Fin 6) :lK :=
 ![Xₚ 2,Xₚ 1,Xₚ 0 - Xₚ 2,Xₚ 0+Xₚ 1 - Xₚ 2,Xₚ 0,
   Xₚ 0*Xₚ 1+Xₚ 0*Xₚ 2 - Xₚ 2*Xₚ 2] i
private theorem contact_factor (i:Fin 6) :contactChange (cy i)=contactFactor i:= by
 fin_cases i <;> simp [cy ,contactFactor,contactChange] <;> ring
private theorem factor_mem (i:Fin 6) :
    cy i∈aU (yE i) (n5 i) := by
  rw [mem_space]
  constructor
  · fin_cases i <;> simp only [cy ,sub_mul]
    case' «0» => apply on_X
    case' «1» => apply on_X
    case' «2» => refine on_sub (on_X ?_) (on_X ?_)
    case' «3» => apply on_X
    case' «4» => refine on_add (on_sub (on_X ?_) (on_X ?_)) (on_X ?_)
    case' «5» => refine on_add (on_sub (on_XX ?_) (on_XX ?_)) (on_XX ?_)
    all_goals
      simp only [yE,n5 ,c9,map_add,Finsupp.degree_single,
        mD,oD]
      decide
  · rw [contact_factor]
    fin_cases i <;> simp only [contactFactor,Matrix.cons_val_zero',Matrix.cons_val_succ']
    case' «0» => apply on_X
    case' «1» => apply on_X
    case' «2» => refine on_sub (on_X ?_) (on_X ?_)
    case' «3» => refine on_sub (on_add (on_X ?_) (on_X ?_)) (on_X ?_)
    case' «4» => apply on_X
    case' «5» => refine on_sub (on_add (on_XX ?_) (on_XX ?_)) (on_XX ?_)
    all_goals
      simp only [lI,n5 ,mD,oD]
      decide
private theorem b2K (i:Fin 6) :cy i≠0:= by
 let point :Fin 6→Fin 3→F :=
  ![![0,0,1],![0,1,0],![1,0,0],![1,0,0],![1,0,0],![1,0,1]]
 intro h
 have he :=nX (fun p:lK=>eval (point i) p) h
 fin_cases i <;> simp [point,cy] at he
private def scale (k :ℕ) (f :Flags) :Flags :=
 ((k*f.1.1,k*f.1.2),(k*f.2.1.1,k*f.2.1.2),(k*f.2.2.1,k*f.2.2.2))
private theorem mul_mem {p q:lK} {d e :ℕ} {f g h:Flags}
   (hp:p∈aU d f) (hq:q∈aU e g)
   (hs : ∀ a b,c9 f a→c9 g b→c9 h (a+b))
   (ht : ∀ a b,lI f a→lI g b→lI h (a+b)) :
   p*q∈aU (d+e) h:= by
 obtain ⟨hps,hpt⟩:=mem_space.mp hp
 obtain ⟨hqs,hqt⟩:=mem_space.mp hq
 refine mem_space.mpr ⟨on_mul hps hqs ?_,?_⟩
 · rintro a b ⟨ha,hfa⟩ ⟨hb,hgb⟩
   exact ⟨by rw [map_add,ha,hb],hs a b hfa hgb⟩
 · rw [map_mul]
   exact on_mul hpt hqt ht
private theorem factor_pow_mem (i:Fin 6) (k :ℕ) :
   cy i^k∈aU (k*yE i) (scale k (n5 i)) := by
 induction k with
 | zero =>
   rw [pow_zero,mem_space,map_one]
   exact ⟨by simp [OnSupport,c9,scale],by simp [OnSupport,lI,scale]⟩
 | succ k ih =>
   rw [pow_succ,oq]
   refine mul_mem ih (factor_mem i) ?_ ?_
   · intro a b ha hb
     simp only [c9,scale,mD,oq] at *
     omega
   · intro a b ha hb
     simp only [lI,scale,mD,oq] at *
     omega
private theorem restore_mem {p:lK} {d:ℕ} {f :Flags} {i:Fin 6} {k :ℕ}
   (hk :k*yE i≤d)
   (hp:p∈aU (d - k*yE i) (remove f i k)) :
   cy i^k*p∈aU d f := by
 have h:=mul_mem (factor_pow_mem i k) hp (h:=f)
   (by
     intro a b ha hb
     simp only [c9,scale,remove,mD] at *
     omega)
   (by
     intro a b ha hb
     simp only [lI,scale,remove,mD] at *
     omega)
 rwa [Nat.add_sub_of_le hk] at h
private theorem space_finite (d:ℕ) (f :Flags) :Module.Finite F (aU d f) := by
 let S:Set Exponent := {e | e.degree=d∧c9 f e}
 have hS:S.Finite :=
  (Finsupp.finite_of_degree_eq d).subset (fun _ he=>he.1)
 have :Finite S:=hS.to_subtype
 have :Module.Finite F (restrictSupport F S) :=Module.Finite.of_basis (basisRestrictSupport F S)
 have hle :aU d f≤ restrictSupport F S:=inf_le_left
 exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
theorem proof :P5_8_1.c3:= by
 intro d f i k hk
 have :=space_finite d f
 let L:aU (d - k*yE i) (remove f i k) →ₗ[F] aU d f :=
  (oj F (cy i^k)).restrict (fun _ hp=>restore_mem hk hp)
 apply ov (f :=L)
 intro x y hxy
 apply ox
 exact mul_left_cancel₀ (pow_ne_zero _ (b2K i)) (nX oy hxy)
end q2aXx2a
end
section
namespace qIWmIFe
noncomputable section
open i4 P5_8 P5_8_5 MvPolynomial
open aFz (GS aIz bJy)
open scoped BigOperators
private abbrev kA (m:ℕ) :=
 GS (m*chartCaps.B) (m*chartCaps.J) (m*chartCaps.C)
private theorem band_mul {m n:ℕ} {p q:BL 2}
  (hp:p∈kA m) (hq:q∈kA n) :p*q∈kA (m+n) := by
 simpa only [kA,Nat.add_mul] using bJy hp hq
private theorem one_band_zero : (1 :BL 2)∈kA 0:= by
 have hw:weightedTotalDegree Fin.val (1 :BL 2)=0:= by
  rw [← C_1,weightedTotalDegree_C]
 exact aIz.mpr ⟨totalDegree_one.le,hw.le,(degreeOf_one _).le⟩
private theorem chart_rank {L R:BL 2} (F:ProperCharts L R)
   (i:Fin F.count) (m:ℕ) :
   affineHilbertFunction (F.ideal i) m ≤
     nI nU (aEl (F.component i) nq m) := by
 let P:=F.component i
 let T:=F.bY i
 let:P.IsPrime :=(F.minimal i).isPrime
 change affineHilbertFunction (vanishingIdeal nU (T.output '' chartOpen P T)) m≤_
 rw [bHO (F.den_reg i)]
 let j:=IsScalarTower.toAlgHom nU (BL 2 ⧸ P) (VF P T)
 let δ:=lz P T T.denominator
 have hδ:IsUnit δ :=
   IsLocalization.Away.algebraMap_isUnit (S:=VF P T)
     (lJ P T.denominator)
 let y (a :Fin k) :=lz P T (T.numerator a)*aOc P T
 have hy (a :Fin k) :δ*y a=lz P T (T.numerator a) := by
   change lz P T T.denominator*(lz P T (T.numerator a)*aOc P T)= _
   rw [mul_left_comm _ (lz P T (T.numerator a)),cKm,mul_one]
 let V (n:ℕ) :=(aEl P nq n).map j.toLinearMap
 let W (n:ℕ) :=(V n).comap (oj nU (δ^n))
 have hW (n:ℕ) (z :VF P T) :
     z∈W n ↔ ∃ p∈kA n,lz P T p=δ^n*z := by
   change δ^n*z∈V n↔_
   simp only [V,aEl,← Submodule.map_comp,← AlgHom.comp_toLinearMap,
     Submodule.mem_map,AlgHom.toLinearMap_apply,lz ,j]
 have hD:T.denominator∈kA 1 := by
   rw [kA,lV,lV,lV]
   exact aIz.mpr (F.bands i).1
 have hN (a :Fin k) :T.numerator a∈kA 1 := by
   rw [kA,lV,lV,lV]
   exact aIz.mpr ((F.bands i).2 a)
 have hpow (n:ℕ) :T.denominator^n∈kA n:= by
   induction n with
   | zero=>simpa only [pow_zero] using one_band_zero
   | succ n ih=>rw [pow_succ]; exact band_mul ih hD
 have hmono:Monotone W:= by
   intro n l hnl z hz
   obtain ⟨p,hp,he⟩:=(hW _ _).mp hz
   refine (hW _ _).mpr ⟨T.denominator^(l - n)*p,?_,?_⟩
   · simpa only [oY hnl] using band_mul (hpow (l - n)) hp
   · rw [map_mul,map_pow,he,← mul_assoc,← pow_add,oY hnl]
 have hmul (a :Fin k) (n:ℕ) (z :VF P T) (hz :z∈W n) :
     y a*z∈W (n+1) := by
   obtain ⟨p,hp,he⟩:=(hW _ _).mp hz
   refine (hW _ _).mpr ⟨p*T.numerator a,band_mul hp (hN a),?_⟩
   rw [map_mul,he,← hy a,pow_succ]
   ac_rfl
 have h0: (1 :VF P T)∈W 0 :=
   (hW _ _).mpr ⟨1,one_band_zero,by simp⟩
 let Q:=RingHom.ker (qR P T).toRingHom
 let ι: (jo ⧸ Q) →ₐ[nU] VF P T:=Ideal.kerLiftAlg (qR P T)
 have hmem (x :quotientDegreeLE Q m) :δ^m*ι x.val∈V m:= by
   obtain ⟨p,hp,he⟩:=mem_quotientDegreeLE.mp x.property
   change ι x.val∈W m
   rw [← he]
   change aeval y p∈W m
   simpa only [lV] using aeval_mem_of_forall_mul_mem y hmono h0 hmul hp
 let f :quotientDegreeLE Q m →ₗ[nU] V m :=
   (((oj nU (δ^m)).comp ι.toLinearMap).domRestrict
     (quotientDegreeLE Q m)).codRestrict (V m) hmem
 have hf :oK f := by
   intro x z hxz
   have h:δ^m*ι x.val=δ^m*ι z.val :=nX oy hxz
   exact ox (Ideal.kerLiftAlg_injective (qR P T) ((hδ.pow m).mul_left_cancel h))
 exact (ov hf).trans (oz _ _)
private theorem component_ranks {L R:BL 2} (F:ProperCharts L R) :
    ∃ shift:ℕ,∀ m:ℕ,
      (∑ i,nI nU (aEl (F.component i) nq m)) ≤
        nI nU (aEl (ke L R) nq (m+shift)) := by
  classical
  obtain ⟨s,hs⟩:=Ideal.exists_separators_of_pairwise_not_le
    (fun i=>(F.minimal i).isPrime) (fun i j hij =>
      Ideal.not_le_of_mem_minimalPrimes (F.minimal i) (F.minimal j) (fun h=>hij (F.distinct h)))
  let cost (i:Fin F.count) :=
    (s i).totalDegree+(s i).weightedTotalDegree Fin.val+(s i).degreeOf (Fin.last 2)
  let shift := ∑ i,cost i
  obtain ⟨hc,hj,hb⟩:=A9
  have hJ:0<chartCaps.J:= by omega
  have hB:0<chartCaps.B:= by omega
  have hsBand (i:Fin F.count) :s i∈kA shift:= by
    have hcost:cost i≤ shift :=
      Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    change (s i).totalDegree+(s i).weightedTotalDegree Fin.val +
      (s i).degreeOf (Fin.last 2)≤ shift at hcost
    exact aIz.mpr
      ⟨(show (s i).totalDegree≤ shift by omega).trans (Nat.le_mul_of_pos_right _ hB),
       (show (s i).weightedTotalDegree Fin.val≤ shift by omega).trans (oZ  _ hJ),
       (show (s i).degreeOf (Fin.last 2)≤ shift by omega).trans (oZ  _ hc)⟩
  refine ⟨shift,fun m => ?_⟩
  let U (i:Fin F.count) :=aEl (F.component i) nq m
  let V:=aEl (ke L R) nq (m+shift)
  let q:=LinearMap.pi fun i=>(Ideal.Quotient.factorₐ nU (F.minimal i).le).toLinearMap
  let f : ((i:Fin F.count)→U i) →ₗ[nU] ((i:Fin F.count)→BL 2 ⧸ F.component i) :=
    LinearMap.pi fun i =>
      (oj nU (lJ (F.component i) (s i))).comp
        ((U i).subtype.comp (LinearMap.proj i))
  have hf :oK f := by
    intro x y he
    funext i
    let: (F.component i).IsPrime :=(F.minimal i).isPrime
    have hne :lJ (F.component i) (s i)≠0 :=
      mt Ideal.Quotient.eq_zero_iff_mem.mp (fun h=>(hs i i).mp h rfl)
    exact ox (mul_left_cancel₀ hne (congrFun he i))
  have hmem (x : (i:Fin F.count)→U i) :f x∈V.map q:= by
    have hr (i:Fin F.count) :
        ∃ p∈kA m,lJ (F.component i) p=(x i).val :=
      Submodule.mem_map.mp (x i).property
    choose p hp he using hr
    refine Submodule.mem_map.mpr
      ⟨lJ (ke L R) (∑ j,p j*s j),
       Submodule.mem_map.mpr ⟨_,Submodule.sum_mem _ fun j _=>band_mul (hp j) (hsBand j),rfl⟩,?_⟩
    funext i
    change lJ (F.component i) (∑ j,p j*s j) =
      lJ (F.component i) (s i)*(x i).val
    rw [map_sum,Finset.sum_eq_single i]
    · rw [map_mul,he,mul_comm]
    · intro j _ hji
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((F.component i).mul_mem_left _ ((hs j i).mpr hji))
    · simp
  have (i:Fin F.count) :Module.Free nU (U i) :=Module.Free.of_divisionRing nU _
  change (∑ i,nI nU (U i))≤nI nU V
  rw [← Module.finrank_pi_fintype]
  exact (ov (f :=f.codRestrict _ hmem)
    (fun _ _ he=>hf (nX oy he))).trans (oz q V)
theorem proof :P5_8_5.c1 := by
 intro L R F
 obtain ⟨shift,hs⟩:=component_ranks F
 exact ⟨shift,fun m=>(Finset.sum_le_sum fun i _=>chart_rank F i m).trans (hs m)⟩
end
end qIWmIFe
end
