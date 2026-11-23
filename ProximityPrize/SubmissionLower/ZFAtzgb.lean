import ProximityPrize.SubmissionLower.ZkOFpKb
import ProximityPrize.SubmissionLower.ZfWgThc
import ProximityPrize.SubmissionLower.ZULJdud
import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.CI
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.ZRfXqSb
set_option Elab.async false
open _root_ renaming Algebra → zZE, DFunLike.congr_fun → zmU, Function.Injective → zq4, IsFractionRing.injective → zxb, IsScalarTower → zsf, IsScalarTower.algebraMap_eq → zYY, Module.IsTorsionFree → zYo, MvPolynomial.C → znf, MvPolynomial.C_injective → zbo, MvPolynomial.X → z9v, MvPolynomial.eval₂Hom → zOD, MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.ringHom_ext → zXT, Nat.cast_nonneg → zqJ, Polynomial.mapEquiv → zNc, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs
section
section
set_option autoImplicit true
namespace qr4gGVa

open P5_7_2 (fO Ls movingOrder)
open q7F2qKe
open qB9xHGe (ng upperGlobal)
open q5oHm3d
open qoK3iCb (uq rateAt graphRate scalarSlope BandWitness)
open TD (GM bCb)
open cu (Shape)
open private global_le from ProximityPrize.SubmissionLower.ZAOw7gb
open private project_mono adM from ProximityPrize.SubmissionLower.ZnAYdcb
abbrev b12 :fO:=⟨12,by decide⟩
abbrev b13:fO:=⟨13,by decide⟩
def boundClip (b:fO) (o j:ℕ) :GM :=
 bCb (upperGlobal b j) (freeCap b o j)
private theorem clip_le (b:fO) (o j:ℕ) (k :Fin 4) :
 clip b o j k≤boundClip b o j k :=min_le_min (global_le b j k) le_rfl
theorem projection_box {b:fO} {o j:ℕ} {dm:ℚ}
  (h:project (aHp b j) (boundClip b o j)≤dm) :
  ProjectionCheck b o j dm :=
 Or.inl ((project_mono _ (clip_le b o j)).trans h)
def tC (s :Ls) :GM:=graph (min s.free.B s.moving.B) (min s.free.U s.moving.U)
private theorem cell_le_graph (s :Ls) (d:Shape) (c:GM) (n e v :ℕ) :
  PN s d c n e v≤project d (bCb c (graph e v)) := by
 have h0:min (c 0) (ordinateCap s n e)≤bCb c (graph e v) 0 :=
  min_le_min le_rfl (min_le_left _ _)
 have rise1 :1*(v :ℚ)=graph e v 1 :=one_mul _
 have rise2 :2*(e :ℚ)*v=graph e v 2 := by
  change _=((2*e*v :ℕ) :ℚ)
  simp only [Nat.cast_mul,Nat.cast_ofNat]
 have tent_le (a r f l:ℚ) :tent a r f l v≤ min a (r*v) :=
  min_le_min le_rfl (min_le_left _ _)
 unfold PN project
 exact add_le_add (add_le_add
  (mul_le_mul_of_nonneg_left h0 (zqJ _))
  (mul_le_mul_of_nonneg_left ((tent_le _ 1 _ _).trans_eq
    (congrArg (min (c 1)) rise1)) (zqJ _)))
  (mul_le_mul_of_nonneg_left ((tent_le _ (2*(e :ℚ)) _ _).trans_eq
    (congrArg (min (c 2)) rise2)) (zqJ _))
private theorem graph_le_box {s :Ls} {n e v :ℕ}
  (he :e≤jU s n) (hv :v≤ seed s n) (k :Fin 4) :
  graph e v k≤tC s k :=
 adM (he.trans (Nat.div_le_self _ _)) (hv.trans (Nat.div_le_self _ _)) k
theorem projection_stage {b:fO} {o j i:ℕ} {dm:ℚ}
   (hi:i∈(movingOrder b).take (j-afterFree b))
   (h0:project (aHp b j) (bCb (boundClip b o j)
     (proper (nV b i).free (nV b i).moving ((nV b i).dI+1)))≤dm)
   (hg:project (aHp b j) (bCb (boundClip b o j) (tC (nV b i)))≤dm) :
   ProjectionCheck b o j dm:= by
 refine Or.inr ⟨i,hi,?_⟩
 refine ⟨(project_mono _ (fun k=>min_le_min (clip_le b o j k) le_rfl)).trans h0,?_,?_⟩
 · exact (project_mono _ (fun k=>min_le_min (clip_le b o j k)
     (graph_le_box le_rfl le_rfl k))).trans hg
 · intro n _ _ e _ he _
   apply peak_of_bound
   intro v hv
   exact (cell_le_graph _ _ _ _ _ _).trans ((project_mono _ (fun k =>
     min_le_min (clip_le b o j k) (graph_le_box he hv k))).trans hg)
def quote (b:fO) (d:ℚ) (g:ℕ) :ℚ :=
 uq b g*(graphRate g-d)/(graphRate g-scalarSlope d g)
def bgt (b:fO) (d h:ℚ) :Bool :=
 (List.range 54).all fun g=>rateAt b d d h (uq b (g+1)) (g+1)
private theorem rate_of_checks {b:fO} {d h:ℚ} (hw:BandWitness b)
   (hd:graphRate 55≤d) (hh:0≤h) (hc:bgt b d h=true) :
   aSz b d d h:= by
 refine ⟨(show 0≤graphRate 55 by unfold graphRate; positivity).trans hd,le_rfl,hd,hh,?_⟩
 intro g hg hg54 hd
 obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hg)
 have hi:i∈List.range 54 :=List.mem_range.mpr (by omega)
 have he :=List.all_eq_true.mp hc i hi
 simp only [rateAt,Bool.or_eq_true,decide_eq_true_eq] at he
 rcases he with ((h | h) | h)
 · exact (not_le_of_gt hd h).elim
 · exact Or.inl h
 by_cases h1 :i+1=1
 · rw [ite_eq_left h1,decide_eq_true_eq] at h
   exact Or.inr (Or.inl ⟨h1,h⟩)
 by_cases h2 :i+1=2
 · rw [ite_eq_right h1,ite_eq_left h2,decide_eq_true_eq] at h
   exact Or.inr (Or.inr (Or.inl ⟨h2,h⟩))
 rw [ite_eq_right h1,ite_eq_right h2,decide_eq_true_eq] at h
 have hg3:3≤ i+1 := by omega
 exact Or.inr (Or.inr (Or.inr ⟨hg3,false,uq b (i+1),
   by simpa [scalarSlope] using h.1,hw _ hg3 hg54,by simpa [scalarSlope,graphRate] using h.2⟩))
private def field (x o shift bits :ℕ) :ℕ :=
 (x >>> (74*o+shift)) &&& (2^bits-1)
private def degree (x o:ℕ) :ℚ:=(field x o 0 48:ℚ)/field x o 48 21
private def height (b:fO) (x o:ℕ) :ℚ:=quote b (degree x o) (field x o 69 5)
theorem row_of_checks {b:fO} {o j:ℕ} (x :ℕ)
   (hw:BandWitness b) (hp:ProjectionCheck b o j (degree x o))
   (hd:graphRate 55≤degree x o) (hh:0≤height b x o)
   (hr :bgt b (degree x o) (height b x o)=true)
   (ha : ∀ k,degree x o*SS b j 0 k+height b x o*SS b j 1 k≤ng b o j k) :
   dqs b o j :=
 ⟨_,_,_,hp,rate_of_checks hw hd hh hr,ha⟩
end qr4gGVa
end
end
section
section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace qBaLURa
noncomputable section
open Polynomial
open cu (L)
open qFwMjQd (LineRing Ez lineVar onLine)
open q33Mraa (Frame)
private abbrev A (σ:Type) :=MvPolynomial σ L
private abbrev B (σ:Type) :=MvPolynomial σ (A σ)
private abbrev E (σ:Type) :=Ez σ
variable {σ:Type}
private def aJs (forward:Bool) : (LineRing σ)[X] →+* (LineRing σ)[X] :=
 eval₂RingHom (zOD (C.comp znf) fun
  | some (false,i) =>
    let u:=C (z9v (some (false,i)))
    let w:=C (z9v (some (true,i)))*Polynomial.X
    if forward then u+w else u - w
  | i=>C (MvPolynomial.X i)) Polynomial.X
private theorem shear_left (b:Bool) :
   (aJs (σ:=σ) (!b)).comp (aJs b)=RingHom.id _:= by
 apply Polynomial.ringHom_ext'
 · apply zXT
   · intro c
     simp [aJs]
   · rintro (_ | ⟨_ | _,i⟩) <;> cases b <;> simp [aJs]
 · simp [aJs]
private def J6: (LineRing σ)[X] ≃+* (LineRing σ)[X] :=
 RingEquiv.ofRingHom (aJs true) (aJs false) (shear_left false) (shear_left true)
private def addTarget : (B σ)[X] ≃+* LineRing σ :=
  (zNc
    ((MvPolynomial.sumAlgEquiv L σ σ).symm.trans
      (MvPolynomial.renameEquiv L ((Equiv.sumComm σ σ).trans
        (Equiv.boolProdEquivSum σ).symm))).toRingEquiv).trans
    (MvPolynomial.optionEquivLeft L (Bool×σ)).symm.toRingEquiv
private def aD: (B σ)[X][X] ≃+* (LineRing σ)[X] :=
 (Bivariate.swap.toRingEquiv.trans (zNc addTarget)).trans J6
private def specialize (z :E σ) : (LineRing σ)[X] →+* E σ :=
 eval₂RingHom (algebraMap (LineRing σ) (E σ)) z
private def ic (z :E σ) :A σ →ₐ[L] E σ :=
 MvPolynomial.aeval fun i=>lineVar (some (false,i))+lineVar (some (true,i))*z
private def zu (z :E σ) :B σ →+* E σ :=
 zOD (ic z).toRingHom (fun i=>lineVar (some (true,i)))
private theorem joint_coordinates (z :E σ) :
    ((specialize z).comp aD.toRingHom).comp (C.comp C)=zu z := by
  apply MvPolynomial.ringHom_ext'
  · apply zXT
    · intro c
      simp [specialize,aD,addTarget,J6,aJs,zu,ic,
        Bivariate.swap_C_C,MvPolynomial.algebraMap_eq]
      exact (IsScalarTower.algebraMap_apply L (LineRing σ) (E σ) c).symm
    · intro i
      simp [specialize,aD,addTarget,J6,aJs,zu,ic,
        Bivariate.swap_C_C,lineVar]
  · intro i
    simp [specialize,aD,addTarget,J6,aJs,zu,
      Bivariate.swap_C_C,lineVar]
private def liftR (R: (A σ)[X]) : (B σ)[X][X] :=
 R.map (C.comp znf)
private theorem specialize_line (z :E σ) (R: (A σ)[X]) :
    specialize z (aD (liftR R)) =
      (onLine (algebraMap L (E σ)) (fun i=>lineVar (some (false,i)))
        (fun i=>lineVar (some (true,i))) (lineVar (σ:=σ) none) R).eval z := by
  change (((specialize z).comp aD.toRingHom).comp
    (mapRingHom (C.comp znf))) R=((evalRingHom z).comp _) R
  apply zmU
  apply Polynomial.ringHom_ext
  · intro q
    have h:=zLs (joint_coordinates z) (znf q)
    change specialize z (aD (C (C (znf q))))= _ at h
    simp only [zQb,coe_mapRingHom,map_C,onLine,coe_eval₂RingHom,eval₂_C]
    change specialize z (aD (C (C (znf q))))= _
    rw [h,zu,zTv]
    apply zmU (f :=(ic z).toRingHom)
      (g:=(evalRingHom z).comp (zOD (C.comp (algebraMap L (E σ)))
        (fun i=>C (lineVar (some (false,i)))+C (lineVar (some (true,i)))*Polynomial.X))) ?_ q
    apply zXT <;> intro c <;> simp [ic]
  · simp [onLine,specialize,aD,addTarget,J6,aJs,Bivariate.swap_Y,lineVar]
private theorem ccE {R: (A σ)[X]} (hR:R.IsPrimitive) : (liftR R).IsPrimitive := by
 intro j hj
 have hn:R.coeff R.natDegree≠0:=leadingCoeff_ne_zero.mpr hR.ne_zero
 have h (i:ℕ) :j∣C (znf (R.coeff i)) := by
   simpa only [liftR,coeff_map,zQb] using
     (C_dvd_iff_dvd_coeff _ _).mp hj i
 have hn' : znf (σ:=σ) (R.coeff R.natDegree)≠0 :=
   (map_ne_zero_iff _ (zbo σ (A σ))).2 hn
 have hC:j=C (j.coeff 0) :=eq_C_of_natDegree_le_zero <|
   (natDegree_le_of_dvd (h _) (C_ne_zero.mpr hn')).trans_eq (natDegree_C _)
 have hb (i:ℕ) :j.coeff 0∣znf (R.coeff i) := by
   simpa only [constantCoeff_apply,coeff_C_zero] using
     map_dvd (constantCoeff : (B σ)[X] →+* B σ) (h i)
 obtain ⟨a,_,ha⟩:=(MvPolynomial.dvd_C_iff_exists hn).mp (hb _)
 have haR:C a∣R:=(C_dvd_iff_dvd_coeff _ _).mpr fun i=> by
   simpa only [ha,MvPolynomial.constantCoeff_C] using
     map_dvd (MvPolynomial.constantCoeff :B σ →+* A σ) (hb i)
 rw [hC,ha]
 exact ((hR a haR).map znf).map Polynomial.C
private theorem common_factor {D K S:Type} [CommRing D] [IsDomain D]
    [UniqueFactorizationMonoid D] [Field K] [Field S] [zZE D K] [IsFractionRing D K]
    [zZE D S] [zZE K S] [zsf D K S]
    (z :S) (hI:IsIntegral K z) (f g:D[X]) (hg:g≠0)
    (hfz :aeval z f=0) (hgz :aeval z g=0) :
    ∃ j,¬IsUnit j∧j∣f∧j∣g:= by
  have factor : ∀ g' : D[X],g' ≠ 0→aeval z g' = 0 →
      ∃ j,Irreducible j∧aeval z j=0∧j∣g' := by
    intro g'
    induction g' using WfDvdMonoid.induction_on_irreducible with
    | zero=>simp
    | unit u hu=>exact fun _ h=>((hu.map (aeval z)).ne_zero h).elim
    | mul a j ha hj ih =>
      intro _ hz
      rw [map_mul,mul_eq_zero] at hz
      rcases hz with hz | hz
      · exact ⟨j,hj,hz,dvd_mul_right _ _⟩
      · obtain ⟨q,hq,hqz,hqa⟩:=ih ha hz
        exact ⟨q,hq,hqz,hqa.trans (dvd_mul_left _ _)⟩
  obtain ⟨j,hj,hjz,hjg⟩:=factor g hg hgz
  let k :=algebraMap D K
  have ev (p:D[X]) :aeval z (p.map k)=aeval z p:= by
    rw [aeval_def,eval₂_map,aeval_def,← zYY]
  have hdeg:j.natDegree≠0:= by
    intro h
    have he :=eq_C_of_natDegree_eq_zero h
    rw [he,aeval_C] at hjz
    have hki:zq4 (algebraMap D S) := by
      rw [zYY D K S]
      exact (algebraMap K S).injective.comp (zxb D K)
    have hc:j.coeff 0=0:=(injective_iff_map_eq_zero _).mp hki _ hjz
    exact hj.ne_zero (by rw [he,hc,C_0])
  have hprim:=hj.isPrimitive hdeg
  have hi:=hprim.irreducible_iff_irreducible_map_fraction_map (K:=K) |>.mp hj
  have hm:=minpoly.irreducible hI
  have hmin:minpoly K z∣j.map k :=minpoly.dvd K z ((ev j).trans hjz)
  exact ⟨j,hj.not_isUnit,hprim.dvd_of_fraction_map_dvd_fraction_map
    ((hm.dvd_symm hi hmin).trans (minpoly.dvd K z ((ev f).trans hfz))),hjg⟩
private theorem joint_injective (z :E σ) {R: (A σ)[X]} (hR:R.IsPrimitive)
  (hz :specialize z (aD (liftR R))=0) :zq4 (zu z) := by
 apply (injective_iff_map_eq_zero _).mpr
 intro q hq
 by_contra hne
 have hq' : specialize z (aD (C (C q)))=0 :=
  (zLs (joint_coordinates z) q).trans hq
 let K:=FractionRing (LineRing σ)
 have hI:IsIntegral K z :=Algebra.IsIntegral.isIntegral z
 obtain ⟨j,hju,hjR,hjq⟩:=common_factor z hI _ _
  ((map_ne_zero_iff _ aD.injective).2 (C_ne_zero.mpr (C_ne_zero.mpr hne))) hz hq'
 have hjQ:aD.symm j∣C (C q) := by
  simpa only [RingEquiv.symm_apply_apply] using map_dvd aD.symm hjq
 have hjP:aD.symm j∣liftR R:= by
  simpa only [RingEquiv.symm_apply_apply] using map_dvd aD.symm hjR
 have he :=eq_C_of_natDegree_le_zero <|
  (natDegree_le_of_dvd hjQ (C_ne_zero.mpr (C_ne_zero.mpr hne))).trans_eq (natDegree_C _)
 rw [he] at hjP
 have hu:=(ccE hR _ hjP).map Polynomial.C
 rw [← he] at hu
 exact hju (by simpa only [RingEquiv.apply_symm_apply] using hu.map aD)
private theorem extend_joint {k D S:Type} [Field k] [CommRing D] [IsDomain D]
   [zZE k D] [Field S] [zZE k S] [IsAlgClosed S] (f :D →ₐ[k] S) (w:σ→S)
   (hw:zq4 (zOD f.toRingHom w)) :
   ∃ e :AlgebraicClosure (FractionRing D) →ₐ[k] S,
     (∀ x :D,e (algebraMap D (AlgebraicClosure (FractionRing D)) x)=f x) ∧
     zq4 (zOD e.toRingHom w) := by
 let F:=FractionRing D
 let G:=AlgebraicClosure F
 have hf :zq4 f.toRingHom:= by
   intro x y h
   apply zbo σ D
   exact hw (by simpa only [zTv] using h)
 let _:zZE D S:=f.toRingHom.toAlgebra
 let _:zsf k D S := .of_algebraMap_eq fun x=>(f.commutes x).symm
 let _:zYo D S:=Module.isTorsionFree_iff_algebraMap_injective.mpr hf
 let _:zYo D G:=Module.isTorsionFree_iff_algebraMap_injective.mpr (by
   rw [zYY D F G]
   exact (algebraMap F G).injective.comp (zxb D F))
 let _:Algebra.IsAlgebraic D G :=
   (IsFractionRing.comap_isAlgebraic_iff (A:=D) (K:=F)).mpr inferInstance
 let e :G →ₐ[D] S:=IsAlgClosed.lift
 have he (x :D) :e (algebraMap D G x)=f x :=e.commutes x
 let _:zZE G S:=e.toRingHom.toAlgebra
 let _:zsf D G S := .of_algebraMap_eq fun x=>(he x).symm
 have hind:AlgebraicIndependent D w:=hw
 exact ⟨e.restrictScalars k,he,hind.extendScalars G⟩
private theorem closure_frame {d s a :ℕ} (z :qFwMjQd.Eline d s a)
  (hj:zq4 (zu z)) :Nonempty (Frame d s a z) := by
 obtain ⟨e,he,hw⟩:=extend_joint (ic z) (fun i=>lineVar (some (true,i))) hj
 refine ⟨⟨e,fun i=>(he (z9v i)).trans ?_,hw⟩⟩
 rw [ic,MvPolynomial.aeval_X]
 rfl
theorem proof :q33Mraa.c1 := by
 intro d s a R hR z hz
 apply closure_frame z (joint_injective z hR ?_)
 rw [specialize_line]
 exact isRoot_of_mem_roots hz
end
end qBaLURa
end
end
