import ProximityPrize.SubmissionLower.ZZNStjd
import ProximityPrize.SubmissionLower.ZgAwAwd
set_option Elab.async false
open _root_ renaming IsFractionRing.injective → zxb, IsLocalization → zNo, Nat.sub_add_cancel → zxt, Nat.sub_le → z7J, Polynomial.C → z1z, Polynomial.algebra → z86, Polynomial.isLocalization → zyz, Polynomial.map_C → zrL, Polynomial.map_X → zSo, Polynomial.map_injective → zTo, Polynomial.map_map → zoi, Polynomial.ringHom_ext' → z3l, PowerSeries → zpm, PowerSeries.C → zMG, PowerSeries.X → zWv, PowerSeries.constantCoeff → zbO, RingHom.comp_apply → zQb
set_option maxHeartbeats 600000
section
namespace q9sUlTb
noncomputable section
open q8Z6NHc (rawDegree)
open qFwMjQd (LineData Chart aax simple)
open MvPolynomial
def c1 :Prop :=
  ∀ {E :Type} [Field E] [IsAlgClosed E] (d s a :ℕ),2≤d→d*s≤a →
    ∃ (f :LineData E d s a) (g:LineData E d s (a+s+1))
      (h:LineData E (d-1) s (a-s)) (C:Finset (aax E)),
      (C.card:ℤ)≤ rawDegree d a s ∧
      (∀ q∈C,simple (fullChart false false false f) (fullChart false false false g)
        (fullChart false false false h) q) ∧
      ∀ {F:Type} [Field F] (k :E →+* F),
        noBoundary (push k f) (push k g) (push k h) ∧
        ∀ (q:aax F),zeroAt (fullChart false false false (push k f))
          (fullChart false false false (push k g)) (fullChart false false false (push k h)) q →
          ∃ u∈C,q=k ∘ u
def c2 :Prop :=
  ∀ {E :Type} [Field E] (f g h:Chart (zpm E)) (q:aax E),
    simple (map zbO f) (map zbO g)
      (map zbO h) q →
    ∃ u:aax (zpm E),zbO ∘ u=q∧zeroAt f g h u
def c3:Prop :=
  ∀ {K:Type} [Field K] (V:ValuationSubring K) (d s a :ℕ),2≤d→d*s≤a →
    ∀ (f :LineData V d s a) (g:LineData V d s (a+s+1)) (h:LineData V (d-1) s (a-s)),
    noBoundary (push (IsLocalRing.residue V) f) (push (IsLocalRing.residue V) g)
      (push (IsLocalRing.residue V) h) →
    ∀ (rev :Bool) (q:aax K),
      zeroAt (fullChart false rev false (push V.subtype f))
        (fullChart false rev false (push V.subtype g)) (fullChart false rev false (push V.subtype h)) q →
      ∃ v :aax V,zeroAt (fullChart false false false f) (fullChart false false false g)
        (fullChart false false false h) v∧samePoint rev q (V.subtype ∘ v)
private theorem samePoint_injective {K:Type} [Field K] {r :Bool} {p q v :aax K}
   (hp:samePoint r p v) (hq:samePoint r q v) :p=q:= by
 obtain ⟨hp0,hp2,hp1⟩:=hp
 obtain ⟨hq0,hq2,hq1⟩:=hq
 funext j
 fin_cases j
 · exact hp0.trans hq0.symm
 · cases r
   · exact hp1.trans hq1.symm
   · have hn:v 1≠0:= fun hz=> by simp [hz] at hp1
     exact mul_right_cancel₀ hn (hp1.trans hq1.symm)
 · exact hp2.trans hq2.symm
theorem of_children (model :c1) (lift:c2) (normalize :c3) :
    qFwMjQd.c1 := by
  classical
  intro E _ _ d s a hd ha f g h A B hA hB
  obtain ⟨f₁,g₁,h₁,C,hcard,hC,hcover⟩:=model (E :=E) d s a hd ha
  obtain ⟨V,k,t,hk,ht,ht'⟩:=valuation_one E
  let ι:=algebraMap (zpm E) (SeriesFrac E)
  let ρ:=IsLocalRing.residue V
  let fP:=mix zMG zWv f f₁
  let gP:=mix zMG zWv g g₁
  let hP:=mix zMG zWv h h₁
  let fV:=mix k t f f₁
  let gV:=mix k t g g₁
  let hV:=mix k t h h₁
  have afe {n b:ℕ} (l l' : LineData E n s b) (r :Bool) :
      map zbO (fullChart false r false (mix zMG zWv l l')) =
        fullChart false r false l:= by
    rw [b8A,push_mix,PowerSeries.constantCoeff_X,PowerSeries.constantCoeff_comp_C,mix_zero,push_id]
  have atOne {n b:ℕ} (l l' : LineData E n s b) :
      push ρ (mix k t l l')=push (ρ.comp k) l' := by
    rw [push_mix,ht',mix_one]
  have inFrac {n b:ℕ} (l l' : LineData E n s b) :
      push ι (mix zMG zWv l l')=push V.subtype (mix k t l l') := by
    rw [push_mix,push_mix,hk,ht]
  have hf1 :push ρ fV=push (ρ.comp k) f₁:=atOne f f₁
  have hg1 :push ρ gV=push (ρ.comp k) g₁ :=atOne g g₁
  have hh1 :push ρ hV=push (ρ.comp k) h₁:=atOne h h₁
  have hfK:push ι fP=push V.subtype fV:=inFrac f f₁
  have hgK:push ι gP=push V.subtype gV:=inFrac g g₁
  have hhK:push ι hP=push V.subtype hV:=inFrac h h₁
  let I:=(↥A) ⊕ (↥B)
  let tag :I→Bool:=Sum.elim (fun _=>false) (fun _=>true)
  let pt:I→aax E :=Sum.elim Subtype.val Subtype.val
  have hpt (i:I) :simple (fullChart false (tag i) false f) (fullChart false (tag i) false g)
      (fullChart false (tag i) false h) (pt i) := by
    rcases i with i | i
    · exact hA _ i.property
    · exact (hB _ i.property).2
  have hboundary (i:I) (hi:tag i=true) :pt i 1=0:= by
    rcases i with i | i
    · cases hi
    · exact (hB _ i.property).1
  have hex (i:I) :=lift (fullChart false (tag i) false fP) (fullChart false (tag i) false gP)
    (fullChart false (tag i) false hP) (pt i)
    (by simpa only [fP,gP,hP,afe] using hpt i)
  choose u hres hu using hex
  obtain ⟨hnob,hcov⟩:=hcover (ρ.comp k)
  have hnob' : noBoundary (push ρ fV) (push ρ gV) (push ρ hV) := by
    rw [hf1,hg1,hh1]
    exact hnob
  have hnormalize (i:I) :=normalize V d s a hd ha fV gV hV hnob' (tag i) (ι ∘ u i)
    (by simpa only [b8A,hfK,hgK,hhK] using zeroAt_map ι (hu i))
  choose v hv he using hnormalize
  have hspecial (i:I) :=hcov (ρ ∘ v i)
    (by simpa only [b8A,hf1,hg1,hh1] using zeroAt_map ρ (hv i))
  choose w hw hw' using hspecial
  have fiber (i j:I) (e :w i=w j) :v i=v j:= by
    refine unique_zero ρ _ _ _ _ _ (hv i) (hv j) ?_ ?_
    · rw [hw' i,hw' j,e]
    · rw [hw' j]
      simpa only [b8A,hf1,hg1,hh1] using simple_map (ρ.comp k) (hC _ (hw j))
  have Za (i j:I) (e :v i=v j) (hr :tag i=tag j) :pt i=pt j:= by
    have hj:=he j
    rw [← hr,← e] at hj
    have hq:=samePoint_injective (he i) hj
    have eu:u i=u j:=funext fun l=>zxb _ _ (congrFun hq l)
    exact (hres i).symm.trans ((congrArg (fun q=>zbO ∘ q) eu).trans (hres j))
  have afu (i j:I) (e :v i=v j) (hi:tag i=false) (hj:tag j=true) :False := by
    have hpi:=he i
    have hpj:=he j
    rw [hi,e] at hpi
    rw [hj] at hpj
    have hm:ι (u j 1*u i 1)=ι 1 := by
      rw [map_mul,map_one]
      change (ι ∘ u j) 1*(ι ∘ u i) 1=1
      rw [show (ι ∘ u i) 1=(V.subtype ∘ v j) 1 from hpi.2.2]
      exact hpj.2.2
    have hm' := congrArg zbO (zxb _ _ hm)
    rw [map_mul,map_one,show zbO (u j 1)=pt j 1 from congrFun (hres j) 1,
      hboundary j hj,zero_mul] at hm'
    exact zero_ne_one hm'
  let emb:I → ↥C:= fun i=>⟨w i,hw i⟩
  have inj:Function.Injective emb:= by
    intro i j e
    have heq :=fiber i j (congrArg Subtype.val e)
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (Subtype.ext (Za _ _ heq rfl))
    · exact (afu _ _ heq rfl rfl).elim
    · exact (afu _ _ heq.symm rfl rfl).elim
    · exact congrArg Sum.inr (Subtype.ext (Za _ _ heq rfl))
  have hN :A.card+B.card≤C.card:= by
    simpa only [I,Fintype.card_sum,Fintype.card_coe] using Fintype.card_le_of_injective emb inj
  exact (by exact_mod_cast hN : (A.card:ℤ)+B.card≤C.card).trans hcard
end
end q9sUlTb
end
section
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
namespace qWz9F7b
noncomputable section
open Polynomial qrKC9pb qj0Yp9c qO4AyGb
open cu (L)
open P5_7_7 (Dg)
open private vForm_coeff fits_by_coeff from ProximityPrize.SubmissionLower.ZtdrOue
open private DU from ProximityPrize.SubmissionLower.ZqYLuMe
open private fits_sub_scaled from ProximityPrize.SubmissionLower.ZgAwAwd
private abbrev dM (J:Input) :Dg→Prop :=
 fits (M:=L) J.s J.l (J.b+J.s) J.h
private theorem ecA {s a b c a' b' : ℕ} {G:Dg}
   (hG:fits s a b c G) (ha :a≤a') (hb:b≤b') :fits s a' b' c G :=
 ⟨hG.1.trans ha,hG.2.1,fun k j h=>(hG.2.2 k j h).trans
   (Nat.add_le_add hb (Nat.mul_le_mul_right s ha))⟩
private theorem fits_X {s a b c:ℕ} {G:Dg} (hG:fits s a b c G) :
   fits s (a+1) b c (G*Polynomial.X) := by
 refine ⟨natDegree_mul_le_of_le hG.1 natDegree_X.le,?_,?_⟩
 · intro k
   cases k with
   | zero=>simp only [coeff_mul_X_zero,natDegree_zero,Nat.zero_le]
   | succ k=>rw [coeff_mul_X]; exact hG.2.1 k
 · intro k j h
   cases k with
   | zero=>simp only [coeff_mul_X_zero,coeff_zero,ne_self_iff_false] at h
   | succ k =>
     rw [coeff_mul_X] at h ⊢
     simpa only [Nat.succ_mul,Nat.add_assoc] using Nat.add_le_add_right (hG.2.2 k j h) s
private theorem fits_polar (J:Input) :dM J J.F.derivative := by
 have hN :J.l-1+1=J.l:=zxt (by have :=J.Ca.two_le; omega)
 have hNw:=congrArg (fun n=>n*J.s) hN
 rw [Nat.add_mul,Nat.one_mul] at hNw
 have hp:fits J.s (J.l-1) J.b J.h J.F.derivative :=
   fits_by_coeff (n:=1) (by simpa [J.Ca.jU] using natDegree_derivative_le J.F)
     (fun k=>⟨((k+1 :ℕ) :L),by rw [coeff_derivative]; simp⟩)
     (by simp only [Nat.one_mul]; omega)
 exact ecA hp (z7J _ _) (Nat.le_add_right _ _)
private theorem fits_vForm (J:Input) :fits J.s (J.l-1) (J.b+J.s) J.h (vForm J) := by
 have hN :J.l-1+1=J.l:=zxt (by have :=J.Ca.two_le; omega)
 have hNw:=congrArg (fun n=>n*J.s) hN
 rw [Nat.add_mul,Nat.one_mul] at hNw
 refine fits_by_coeff (n:=0) ?_ (fun k=>⟨(k :L)-(J.l:L),by
   simpa only [Nat.add_zero] using vForm_coeff J k⟩) ?_
 · apply natDegree_le_iff_coeff_eq_zero.mpr
   intro k hk
   rw [vForm_coeff]
   rcases eq_or_lt_of_le (show J.l≤k by omega) with h | h
   · simp [← h]
   · rw [coeff_eq_zero_of_natDegree_lt (J.Ca.jU ▸ h),zero_mul]
 · simp only [Nat.zero_mul,Nat.add_zero]
   omega
private theorem physical_coeff (F:Dg) (k j:ℕ) :
   ((physicalDerivative F).coeff k).coeff j=((F.coeff k).coeff j).derivative := by
 classical
 rw [physicalDerivative_coeff,DU,coeff_sum,sum_def]
 simp only [coeff_monomial,Finset.sum_ite_eq']
 split_ifs with h
 · rfl
 · rw [notMem_support_iff.mp h,derivative_zero]
private theorem fits_physical (J:Input) :dM J (physicalDerivative J.F) := by
 refine ⟨natDegree_le_iff_coeff_eq_zero.mpr ?_,fun k =>
   natDegree_le_iff_coeff_eq_zero.mpr ?_,?_⟩
 · intro k hk
   have hz :J.F.coeff k=0:=coeff_eq_zero_of_natDegree_lt (J.Ca.jU ▸ hk)
   apply Polynomial.ext
   intro j
   rw [physical_coeff,hz]
   simp
 · intro j hj
   rw [physical_coeff,coeff_eq_zero_of_natDegree_lt ((J.Ca.height k).trans_lt hj),
    derivative_zero]
 · intro k j h
   rw [physical_coeff] at h ⊢
   have hw:=J.weight k j (fun hz=>h (by rw [hz,derivative_zero]))
   have hd:=(natDegree_derivative_le ((J.F.coeff k).coeff j)).trans (z7J _ _)
   omega
private abbrev scalar (t:L) :Dg:=z1z (z1z (z1z t))
private theorem eval_vForm (J:Input) :
  a7W J (vForm J)=a7W J J.F.derivative*jU J false := by
 have hz :=(rootMap_eq_zero_iff J J.F).mpr dvd_rfl
 unfold vForm
 rw [map_sub (a7W J),map_mul (a7W J),map_mul (a7W J),hz,mul_zero,sub_zero]
 rfl
private theorem clear {R:Type*} [Field R] (t b y p d:R)
  (hg:1+t*y≠0) (hp:p≠0) :
  let q:=p*y-(-t)*(p*y*y)
  let h:=p-(-t)*(p*y)-(-t)*q
  h≠0∧0-1*d-(-b)*q=(b*(y/(1+t*y))+(-d/p)/(1+t*y)^2)*h:= by
 dsimp only
 simp only [one_mul,zero_sub,neg_mul,sub_neg_eq_add]
 set g:=1+t*y
 have h:p+t*(p*y)+t*(p*y+t*(p*y*y))=g^2*p:= by dsimp only [g]; ring
 rw [h]
 refine ⟨mul_ne_zero (pow_ne_zero _ hg) hp,?_⟩
 have h1 :b*(y/g)*(g^2*p)=b*y*g*p:= calc
  _=(y/g*g)*(b*g*p) := by ring
  _ = _:= by rw [div_mul_cancel₀ _ hg]; ring
 have h2 : ((-d/p)/g^2)*(g^2*p) = -d:= by
  rw [← mul_assoc,div_mul_cancel₀ _ (pow_ne_zero _ hg),div_mul_cancel₀ _ hp]
 rw [add_mul,h1,h2]
 dsimp only [g]
 ring
theorem proof :qO4AyGb.c1 := by
 intro J τ b hg
 let U:=J.F.derivative
 let V:=vForm J
 let W:Dg:=V*Polynomial.X
 let Q:=V - scalar (-τ)*W
 have hv :=fits_vForm J
 have hV:dM J V:=ecA hv (z7J _ _) le_rfl
 have hW:dM J W:= by
   have hN :J.l-1+1=J.l:=zxt (by have :=J.Ca.two_le; omega)
   simpa only [hN] using fits_X hv
 have hQ:dM J Q:=fits_sub_scaled hV hW (-τ)
 have h0:dM J 0:= by simp [dM,fits]
 have eU:a7W J U=polar J false := by rw [polar,chartEval_false]; rfl
 have eV:a7W J V=polar J false*jU J false :=(eval_vForm J).trans
   (congrArg (fun p=>p*jU J false) eU)
 have eW:a7W J W=polar J false*jU J false*jU J false := by
   dsimp only [W]
   rw [map_mul,eV]
   rfl
 have es (a :L) :a7W J (scalar a)=constant J a :=rfl
 have en (a :L) :constant J (-a) = -constant J a :=map_neg (constMap J) a
 have e1 :constant J 1=1 :=map_one (constMap J)
 have he :=clear (constant J τ) (constant J b) (jU J false) (polar J false)
   (a7W J (physicalDerivative J.F)) hg (polar_false_ne_zero J)
 refine ⟨0 - scalar 1*physicalDerivative J.F - scalar (-b)*Q,
   U - scalar (-τ)*V - scalar (-τ)*Q,
   fits_sub_scaled (fits_sub_scaled h0 (fits_physical J) 1) hQ (-b),
   fits_sub_scaled (fits_sub_scaled (fits_polar J) hV (-τ)) hQ (-τ),?_,?_⟩
 · simpa only [Q,map_sub (a7W J),map_mul (a7W J),es,en,eU,eV,eW] using he.1
 · simp only [Q,map_sub (a7W J),map_mul (a7W J),map_zero (a7W J),
     es,en,e1,eU,eV,eW,qW,jet,chartEval_false]
   exact he.2
end
end qWz9F7b
end
section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
namespace qW0d9ye
noncomputable section
open Polynomial qrKC9pb qO4AyGb
open cu (L)
open P5_7_7 (Dg)
open scoped nonZeroDivisors
private abbrev LiftedRing:=(RatFunc L)[X][X][X]
private def mapThree {A B:Type} [CommRing A] [CommRing B] (e :A →+* B) :
  A[X][X][X] →+* B[X][X][X] :=
 mapRingHom (mapRingHom (mapRingHom e))
section PrimeExtension
variable {K:Type} [Field K]
local notation "P₃" => K[X][X][X]
local notation "P₄" => K[X][X][X][X]
local notation "Q₃" => (RatFunc K)[X][X][X]
private def moveParameter :P₄ ≃+* P₄ :=
 ((Bivariate.swap (R:=K[X][X])).toRingEquiv.trans
   (mapEquiv (Bivariate.swap (R:=K[X])).toRingEquiv)).trans
   (mapEquiv (mapEquiv (Bivariate.swap (R:=K)).toRingEquiv))
private theorem swap_mapped_C {R:Type} [CommRing R] (F:R[X][X]) :
   (F.map C).map (Bivariate.swap (R:=R)).toRingHom =
     F.map (mapRingHom (C:R →+* R[X])) := by
 rw [zoi]
 congr 1
 exact RingHom.ext Bivariate.swap_C
private theorem moveParameter_C (F:P₃) :
  moveParameter (C F)=mapThree (C:K →+* K[X]) F:= by
 change ((Bivariate.swap (R:=K[X][X]) (C F)).map
  (Bivariate.swap (R:=K[X])).toRingHom).map
  (mapRingHom (Bivariate.swap (R:=K)).toRingHom)= _
 rw [Bivariate.swap_C,swap_mapped_C,zoi]
 congr 1
 exact RingHom.ext swap_mapped_C
private abbrev D₁:=(K[X])⁰.map (C:K[X] →+* K[X][X])
private abbrev D₂:=(D₁ (K:=K)).map (C:K[X][X] →+* P₃)
private abbrev D₃:=(D₂ (K:=K)).map (C:P₃ →+* P₄)
local instance :CommSemiring P₄ := @Polynomial.commSemiring P₃ inferInstance
local instance :Algebra K[X][X] (RatFunc K)[X] :=z86 K[X] (RatFunc K)
local instance :Algebra P₃ (RatFunc K)[X][X] :=
 z86 K[X][X] (RatFunc K)[X]
local instance :Algebra P₄ Q₃:=z86 P₃ (RatFunc K)[X][X]
local instance :zNo (R:=K[X][X]) (D₁ (K:=K)) (RatFunc K)[X] :=
 zyz (K[X])⁰ (RatFunc K)
local instance :zNo (R:=P₃) (D₂ (K:=K)) (RatFunc K)[X][X] :=
 zyz (R:=K[X][X]) (D₁ (K:=K)) (RatFunc K)[X]
local instance :zNo (R:=P₄) (D₃ (K:=K)) Q₃ :=
 zyz (R:=P₃) (D₂ (K:=K)) (RatFunc K)[X][X]
private theorem localize_moved (F:P₃) :
  algebraMap P₄ Q₃ (moveParameter (C F))=mapThree RatFunc.C F:= by
 rw [moveParameter_C]
 change (mapThree (C:K →+* K[X]) F).map
  (mapRingHom (mapRingHom (algebraMap K[X] (RatFunc K))))= _
 ext i j k :3
 simp only [mapThree,coe_mapRingHom,coeff_map,RatFunc.algebraMap_C]
private theorem parameter_prime (F:P₃) (hp:Prime F) (hdeg:0<F.natDegree) :
    Prime (mapThree RatFunc.C F) := by
  have hc:Prime (C F:P₄) :=(prime_C_iff (R:=P₃) (r :=F)).mpr hp
  have hs :Prime (moveParameter (C F)) :=
    (MulEquiv.prime_iff (M:=P₄) (N :=P₄) (p:=C F) moveParameter.toMulEquiv).mpr hc
  have hpos :0<(mapThree RatFunc.C F).natDegree := by
    rwa [show (mapThree RatFunc.C F).natDegree=F.natDegree from
      natDegree_map_eq_of_injective
        (zTo _ (zTo _ RatFunc.C_injective)) F]
  have hn:mapThree RatFunc.C F≠0:= fun h=>hpos.ne' (by rw [h,natDegree_zero])
  have hu : ¬ IsUnit (mapThree RatFunc.C F) := fun h=>hpos.ne' (natDegree_eq_zero_of_isUnit h)
  let f :=IsLocalization.toLocalizationMap (R:=P₄) (D₃ (K:=K)) Q₃
  have he :f (moveParameter (C F))=mapThree RatFunc.C F:=localize_moved F
  rw [← he] at hn hu ⊢
  exact @Submonoid.LocalizationMap.map_prime P₄ Q₃ _ _ (D₃ (K:=K)) f
    (moveParameter (C F)) hs hn hu
end PrimeExtension
private def coeffPoly (J:Input) :L[X] →+* RatFunc (EC J) :=
 (algebraMap (EC J)[X] (RatFunc (EC J))).comp (mapRingHom (constMap J))
private def paramMap (J:Input) :RatFunc L →+* RatFunc (EC J) :=
 RatFunc.liftRingHom (coeffPoly J) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
  ((RatFunc.algebraMap_injective _).comp (zTo _ (constMap J).injective)))
private theorem paramMap_poly (J:Input) (p:L[X]) :
  paramMap J (algebraMap L[X] (RatFunc L) p)=coeffPoly J p :=
 RatFunc.liftRingHom_algebraMap _ _ _
private theorem paramMap_C (J:Input) (a :L) :
  paramMap J (RatFunc.C a)=RatFunc.C (constMap J a) := by
 rw [← RatFunc.algebraMap_C,paramMap_poly]
 simp only [coeffPoly,zQb,coe_mapRingHom,zrL,RatFunc.algebraMap_C]
private def rootRat (J:Input) :LiftedRing →+* RatFunc (EC J) :=
 eval₂RingHom (eval₂RingHom (eval₂RingHom (paramMap J) (RatFunc.C (amm J)))
  (RatFunc.C (seed J))) (RatFunc.C (jU J false))
private theorem rootRat_extend (J:Input) (F:Dg) :
    rootRat J (extend RatFunc.C F)=RatFunc.C (a7W J F) := by
  suffices h: (rootRat J).comp (extend RatFunc.C)=RatFunc.C.comp (a7W J) from
    RingHom.congr_fun h F
  apply z3l
  · apply z3l
    · apply z3l
      · ext a :1
        simpa only [rootRat,extend,zQb,coe_mapRingHom,zrL,
          coe_eval₂RingHom,eval₂_C,constMap] using paramMap_C J a
      · simp only [rootRat,extend,zQb,coe_mapRingHom,zrL,
          zSo,coe_eval₂RingHom,eval₂_C,eval₂_X]
        rfl
    · simp only [rootRat,extend,zQb,coe_mapRingHom,zrL,
        zSo,coe_eval₂RingHom,eval₂_C,eval₂_X]
      rfl
  · simp only [rootRat,extend,zQb,coe_mapRingHom,zSo,
      coe_eval₂RingHom,eval₂_X]
    rfl
private theorem rootRat_parameter (J:Input) :
  rootRat J independentParameter=RatFunc.X:= by
 simp only [rootRat,independentParameter,coe_eval₂RingHom,eval₂_C,
  ← RatFunc.algebraMap_X,paramMap_poly,coeffPoly,zQb,coe_mapRingHom,
  zSo]
private theorem lifted_proper (J:Input) (G H :Dg) (hH :a7W J H≠0) :
   ¬ liftedEquation J∣liftedCutter G H := by
 have hF:rootRat J (liftedEquation J)=0:= by
   rw [liftedEquation,rootRat_extend,(rootMap_eq_zero_iff J J.F).mpr (dvd_refl _),map_zero]
 intro hd
 obtain ⟨Q,hQ⟩:=hd
 have hz :rootRat J (liftedCutter G H)=0:= by rw [hQ,map_mul,hF,zero_mul]
 let P: (EC J)[X] :=C (a7W J G)-Polynomial.X*C (a7W J H)
 have hP:rootRat J (liftedCutter G H) =
     algebraMap (EC J)[X] (RatFunc (EC J)) P:= by
   rw [liftedCutter,_root_.map_sub (rootRat J),_root_.map_mul (rootRat J),
     rootRat_extend,rootRat_extend,rootRat_parameter]
   simp only [P,_root_.map_sub,_root_.map_mul,
     RatFunc.algebraMap_C,RatFunc.algebraMap_X]
 rw [hP] at hz
 have hp:=(map_eq_zero_iff _ (RatFunc.algebraMap_injective (EC J))).mp hz
 exact hH (by
   have h:=congrArg (fun p: (EC J)[X]=>p.coeff 1) hp
   simpa [P,coeff_sub,coeff_X_mul] using h)
theorem proof :qO4AyGb.c2 := by
 intro J
 have hp:Prime J.F:=J.Ca.irreducible.prime
 have hd:0<J.F.natDegree := by
  rw [J.Ca.jU]
  exact Nat.zero_lt_of_lt J.Ca.two_le
 exact ⟨parameter_prime J.F hp hd,lifted_proper J⟩
end
end qW0d9ye
end
