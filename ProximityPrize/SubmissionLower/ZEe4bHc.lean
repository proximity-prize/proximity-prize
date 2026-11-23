import ProximityPrize.SubmissionLower.ZSyXMse
import ProximityPrize.SubmissionLower.ZBkbQJc
import ProximityPrize.SubmissionLower.ZyCQ7Ke
import ProximityPrize.SubmissionLower.ZG9rwXd
import ProximityPrize.SubmissionLower.ZjSNLAa
import ProximityPrize.SubmissionLower.ZsE91Ed
import ProximityPrize.SubmissionLower.ZkOFpKb
import ProximityPrize.SubmissionLower.Z9Rfpte
import ProximityPrize.SubmissionLower.ZVdaXZa
import ProximityPrize.SubmissionLower.ZT8CHOb
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import ProximityPrize.SubmissionLower.DT
import ProximityPrize.SubmissionLower.Z3BnLje
import ProximityPrize.SubmissionLower.ZCvigsb
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.IsSeparable → zw7, Algebra.algebraMap_self → zCp, Field → zrb, Function.Surjective → zpX, IsFractionRing → z0o, Module.Finite → zAa, Polynomial.X → z7y, Polynomial.coeff_map → z0b
section
section
set_option autoImplicit true
theorem qY7pQzb.proof :qmb8rCe.c1 := fun q d h _ hd _ =>
 qOPkAYa.rank_le_cap _ q d h hd
end
section
set_option autoImplicit true
theorem qoRVxvd.proof :qmb8rCe.c2 := fun q d h _ _ hd _ =>
 qOPkAYa.rank_le_cap _ q d h hd
end
section
namespace q1kuFjb
noncomputable section
open Polynomial Finset qQ9yWTb qb0hmCe
open P5 (p)

open P5_7_7 (phys)
open cu (L)
open E7 (Gb)
open scoped Classical WithZero
def c1 :Prop :=
  ∀ q:Curve,Irreducible q →
    ∃ Cq:CurveModel q,Gb L Cq.E Cq.seed≤q.totalDegree
def c2 :Prop :=
  ∀ {q:Curve},Irreducible q → ∀ (Cq:CurveModel q) (s :Fin 2→L),
    Usable q s→Nonempty (AtSite Cq s)
def c4 :Prop :=
  ∀ {q:Curve} (Cq:CurveModel q) {ι:Type} (I:Finset ι)
    (s :ι→Fin 2→L) (A : ∀ i,AtSite Cq (s i)),
    Set.InjOn (fun i=>(A i).place) (I:Set ι) →
    ∀ f :Cq.E[X][X],Irreducible f→0<f.natDegree→f.natDegree<p →
      headScalar f=1 →
      (I.filter fun i => ¬ (coeffIntegral (A i).place.value f ∧
        ((cLN (A i).map 0 f).map phys).Separable)).card≤2*f.natDegree*coeffHeight f
end
end q1kuFjb
end
section
namespace qbnx7gb
noncomputable section
open Polynomial qQ9yWTb qb0hmCe
open P5 (K)
open P5_7_1 (Input)
open cu (L)
variable {x :Input} {U:Finset K} {J:WordChart x U} {q:Curve} {C₀:CurveModel q}
def targetA (C₀:CurveModel q) (R:SiteTarget) :C₀.E :=
 algebraMap L C₀.E R.a+algebraMap L C₀.E R.b*C₀.seed R.coord
def targetB (C₀:CurveModel q) (R:SiteTarget) :C₀.E :=
 algebraMap L C₀.E R.c+algebraMap L C₀.E R.d*C₀.seed R.coord
end
end qbnx7gb
end
section
namespace qWIOgVd
noncomputable section
open Polynomial
open cu (L)
open P5_7_7 (phys)
theorem rev_bound (a :L) {q:L[X]} {n:ℕ} (hq:q.natDegree≤n) :
  (rev a n q).natDegree≤n:= by
 exact (natDegree_reflect_le.trans (max_le le_rfl (by rwa [natDegree_taylor])))
theorem rev_ne (a :L) (n:ℕ) {q:L[X]} (hq:q≠0) :rev a n q≠0:= by
 simpa only [rev,ne_eq,reflect_eq_zero_iff,taylor_eq_zero] using hq
private theorem rev_top (a :L) (n:ℕ) (q:L[X]) :
  (rev a n q).coeff n=q.eval a := by
 rw [rev,coeff_reflect,revAt_le le_rfl,Nat.sub_self,taylor_coeff_zero]
theorem rev_degree {a :L} {n:ℕ} {q:L[X]} (hq:q.natDegree≤n)
  (ha :q.eval a≠0) : (rev a n q).natDegree=n :=
 le_antisymm (rev_bound a hq) (le_natDegree_of_ne_zero ((rev_top a n q).symm ▸ ha))
private theorem rev_at_zero {a :L} {n:ℕ} {q:L[X]} (h:q.natDegree=n) :
  (rev a n q).eval 0=q.leadingCoeff := by
 rw [← coeff_zero_eq_eval_zero,rev,coeff_reflect,revAt_zero,← h,
  ← natDegree_taylor q a]
 exact leadingCoeff_taylor a q
private theorem rev_eval_ne {a y :L} (hy :y≠0) {q:L[X]} {n:ℕ}
  (hq:q.natDegree≤n) (h:q.eval (y⁻¹+a)≠0) : (rev a n q).eval y≠0:= by
 let:Invertible y⁻¹:=invertibleOfNonzero (inv_ne_zero hy)
 have hval :=eval₂_reflect_mul_pow (RingHom.id L) y⁻¹ n (q.taylor a)
  ((natDegree_taylor q a).trans_le hq)
 rw [invOf_eq_inv,inv_inv,eval₂_id,eval₂_id,taylor_eval] at hval
 intro hz
 apply h
 rw [← hval]
 change (rev a n q).eval y*(y⁻¹)^n=0
 rw [hz,zero_mul]
theorem rev_coprime (a :L) (s :ℕ) {P Q:L[X]} (hQ:Q≠0)
    (hc:IsCoprime P Q) :
    IsCoprime (rev a (width s P Q+s) P) (rev a (width s P Q) Q) := by
  let j:=width s P Q
  obtain ⟨hp,hq⟩:=width_bound s P Q
  apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed L L _ _).mpr
  intro y
  simp only [aeval_def,zCp,eval₂_id]
  by_cases hy :y=0
  · subst y
    by_cases hj:Q.natDegree=j
    · exact Or.inr ((rev_at_zero hj).symm ▸ leadingCoeff_ne_zero.mpr hQ)
    · have hlt:Q.natDegree<j:=lt_of_le_of_ne hq hj
      have hm:P.natDegree-s=j:= by
        have he :j=max Q.natDegree (P.natDegree-s) :=rfl
        omega
      have hP:P≠0:= by
        intro hz
        rw [hz,natDegree_zero] at hm
        omega
      have he :P.natDegree=j+s := by omega
      exact Or.inl ((rev_at_zero he).symm ▸ leadingCoeff_ne_zero.mpr hP)
  · have he :=(isCoprime_iff_aeval_ne_zero_of_isAlgClosed L L P Q).mp hc (y⁻¹+a)
    simp only [aeval_def,zCp,eval₂_id] at he
    exact he.imp (rev_eval_ne hy hp) (rev_eval_ne hy hq)
theorem rev_ratio {a :L} (D:Chart a) (s :ℕ) {P Q:L[X]} :
   phys (rev a (width s P Q+s) P)/phys (rev a (width s P Q) Q) =
     x^s*D.changeX (phys P/phys Q) := by
 let j:=width s P Q
 obtain ⟨hp,hq⟩:=width_bound s P Q
 rw [D.CJ P _ hp,D.CJ Q _ hq,map_div₀,pow_add]
 change x^j*x^s*D.changeX (phys P)/(x^j*D.changeX (phys Q))= _
 rw [mul_assoc,mul_div_mul_left _ _ (pow_ne_zero _ x_ne),mul_div_assoc]
end
end qWIOgVd
end
section
set_option autoImplicit true
namespace qVu1nGe
open P5_7_2 (fO)
open q7F2qKe
open qB9xHGe (ng upperGlobal)
open q5oHm3d
open qoK3iCb (BandWitness graphRate rateAt scalarSlope uq)
open TD (bCb)
open private global_le from ProximityPrize.SubmissionLower.ZAOw7gb
open private project_mono from ProximityPrize.SubmissionLower.ZnAYdcb
private def degree (b:fO) (o j:ℕ) :ℚ :=
 project (aHp b j) (bCb (upperGlobal b j) (freeCap b o j))
private def seedRate (b:fO) (o j:ℕ) :ℚ:=max (degree b o j) (graphRate 55)
private def b5T (b:fO) (o j:ℕ) :ℚ :=
 let w:=SS b j 0
 min ((ng b o j 1 - seedRate b o j*w 1)/w 0) (ng b o j 3/w 2)
def paidCheck (b:fO) (o j:ℕ) :Bool :=
  decide (0≤degree b o j∧0≤b5T b o j ∧
    0<SS b j 0 0∧0<SS b j 0 2 ∧
    seedRate b o j*SS b j 0 0≤ng b o j 0 ∧
    seedRate b o j*SS b j 0 2≤ng b o j 2)
def ratesCheck (b:fO) (o j:ℕ) :Bool :=
 let dm:=degree b o j
 let a :=seedRate b o j
 let h:=b5T b o j
 (List.range 54).all fun g=>rateAt b dm a h (uq b (g+1)) (g+1)
private theorem gH {b:fO} {o j:ℕ} (h:paidCheck b o j=true) (k :Fin 4) :
    seedRate b o j*SS b j 0 k+b5T b o j*SS b j 1 k≤ng b o j k := by
  obtain ⟨_,_,hs,hz,h0,h2⟩:=of_decide_eq_true h
  fin_cases k
  · change seedRate b o j*SS b j 0 0+b5T b o j*0≤ng b o j 0
    simpa only [mul_zero,add_zero] using h0
  · change seedRate b o j*SS b j 0 1+b5T b o j*SS b j 0 0≤ng b o j 1
    have h1 :=(le_div_iff₀ hs).mp (min_le_left _ _ :
      b5T b o j≤(ng b o j 1 - seedRate b o j*SS b j 0 1) /
        SS b j 0 0)
    change b5T b o j*SS b j 0 0≤_ at h1
    linarith only [h1]
  · change seedRate b o j*SS b j 0 2+b5T b o j*0≤ng b o j 2
    simpa only [mul_zero,add_zero] using h2
  · change seedRate b o j*0+b5T b o j*SS b j 0 2≤ng b o j 3
    rw [mul_zero,zero_add]
    exact (le_div_iff₀ hz).mp (min_le_right _ _)
private theorem bgt {b:fO} {o j:ℕ} (hw:BandWitness b)
   (hp:paidCheck b o j=true) (hc:ratesCheck b o j=true) :
   aSz b (degree b o j) (seedRate b o j) (b5T b o j) := by
 have h:=of_decide_eq_true hp
 refine ⟨h.1,le_max_left _ _,le_max_right _ _,h.2.1,?_⟩
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
 refine Or.inr (Or.inr (Or.inr ⟨hg3,false,uq b (i+1),?_,hw _ hg3 hg54,?_⟩))
 · simpa [scalarSlope] using h.1
 · simpa [scalarSlope,graphRate] using h.2
theorem row_of_checks {b:fO} {o j:ℕ} (hw:BandWitness b)
  (hp:paidCheck b o j=true) (hr :ratesCheck b o j=true) :dqs b o j:= by
 refine ⟨_,_,_,Or.inl ?_,bgt hw hp hr,gH hp⟩
 exact project_mono _ (fun k=>min_le_min (global_le b j k) le_rfl)
def BandRows (b:fO) :Prop :=
  ∀ (o:Fin (originCount b)) (i:Fin (stopCount b-afterFree b - 1)),
    dqs b o (afterFree b+1+i)
theorem band_of_checks {b:fO} {n:ℕ} (hw:BandWitness b)
  (hn:originCount b=n) (h4 :stopCount b-afterFree b - 1=4)
  (h : ∀ (o:Fin n) (i:Fin 4),
    paidCheck b o (afterFree b+1+i)=true∧ratesCheck b o (afterFree b+1+i)=true) :
  BandRows b:= by
 subst n
 intro o i
 have hi:=h o (Fin.cast h4 i)
 exact row_of_checks hw hi.1 hi.2
set_option quotPrecheck false in
scoped notation "az" => And.intro (by with_unfolding_all rfl) (by with_unfolding_all rfl)
end qVu1nGe
end
end
section
section
set_option autoImplicit true
set_option maxRecDepth 8192
theorem qYzmxYc.proof :qzLARrc.c4 := by
 refine qmb8rCe.gen ⟨164,50,19⟩ 3037 0x13094c39 0xa3f520 (by decide) (by decide)
  (fun q d h _ hd _=>qOPkAYa.rank_le_cap _ q d h hd) qG2jkNc.proof ?_
 refine (qOPkAYa.b6N (⟨⟨120,164,50,3037⟩,19,0,0⟩:P5_7_2.TopRow)).symm.trans ?_
 simp only [q7IA62d.ama,Finset.sum_const,Finset.card_range,smul_eq_mul]
 decide
end
section
set_option autoImplicit true
namespace qZyoMPc
open P5_7 (Bank FarBand Ls jJ terminal cV)

open private bank_ok from ProximityPrize.SubmissionLower.Z9Rfpte
private def check (B J U v :ℕ) :Bool :=
 decide (aP4 B J U≤2880*(v :ℤ))
private def BankCheck (t:Bank) :Prop :=
 check t.shape.B t.shape.J t.shape.U t.arY=true
private theorem stage_cons {s :Ls} {ss :List Ls} (hf :BankCheck s.free)
  (hm:BankCheck s.moving) (ht : ∀ x∈ss,BankCheck x.free∧BankCheck x.moving) :
  ∀ x∈s :: ss,BankCheck x.free∧BankCheck x.moving :=
 List.forall_mem_cons.mpr ⟨⟨hf,hm⟩,ht⟩
private theorem grade_cons {B J:ℕ} {g:jJ} {gs :List jJ}
  (h:check B J g.slots g.arY=true)
  (ht : ∀ x∈gs,check B J x.slots x.arY=true) :
  ∀ x∈g :: gs,check B J x.slots x.arY=true :=
 List.forall_mem_cons.mpr ⟨h,ht⟩
private theorem terminal_checks (b:FarBand) :BankCheck (terminal b) := by
 cases b <;> rfl
set_option maxHeartbeats 5000000 in
private theorem bOp (b:FarBand) :
  ∀ s∈b.row.stages,BankCheck s.free∧BankCheck s.moving:= by
 cases b <;> simp only [FarBand.row]
 all_goals repeat' first
  | exact (fun _ h=>(List.not_mem_nil h).elim)
  | refine stage_cons (by rfl) (by rfl) ?_
set_option maxHeartbeats 5000000 in
private theorem grade_checks (b:FarBand) :
  ∀ g∈b.row.gw,check (terminal b).shape.B (terminal b).shape.J g.slots g.arY=true := by
 cases b <;> dsimp only [terminal,FarBand.row]
 all_goals repeat' first
  | exact (fun _ h=>(List.not_mem_nil h).elim)
  | refine grade_cons rfl ?_
theorem proof :P5_7_4.c2 := by
 intro b t ht
 obtain ⟨hj,hu,_,_⟩:=bank_ok b t ht
 have h:BankCheck t:= by
  rcases ht with rfl | ⟨s,hs,rfl | rfl⟩ | ⟨i,rfl⟩
  · exact terminal_checks b
  · exact (bOp b s hs).1
  · exact (bOp b s hs).2
  · exact grade_checks b (cV b i) (List.get_mem _ _)
 exact bound t.shape t.arY hj hu (of_decide_eq_true h)
end qZyoMPc
end
section
namespace qv2t4Be
noncomputable section
open Polynomial Finset
open scoped WithZero
open P5_7_1_7_4_3_4 (adG bix)
open E7 (KB)
def c1 :Prop :=
  ∀ {K F:Type} [zrb K] [zrb F] [zZE K F] [zAa K F]
    [zw7 K F] (u:Valuation K ℤᵐ⁰),zpX u →
    ∃ (_:IsGalois K (CommonField K F)) (U:Valuation (CommonField K F) ℤᵐ⁰) (e :ℕ),
      0<e∧zpX U ∧ ∀ x :K,U (algebraMap K (CommonField K F) x)=u x^e
def c2 :Prop :=
  ∀ {K F Ω:Type} [zrb K] [zrb F] [zrb Ω] [zZE K F] [zZE K Ω]
    [zZE F Ω] [IsScalarTower K F Ω] [zAa K Ω] [IsGalois K Ω]
    (u:Valuation K ℤᵐ⁰) (v :Valuation F ℤᵐ⁰) (U:Valuation Ω ℤᵐ⁰),
    zpX u→zpX v→zpX U →
    ∀ e n:ℕ,0<e→0<n →
    (∀ x :K,U (algebraMap K Ω x)=u x^e) →
    (∀ x :K,v (algebraMap K F x)=u x^n) →
    ∃ r :ℕ,0< r∧n*r=e ∧
      ∃ j:Fin n ↪ (F →ₐ[K] Ω),∀ b x,U (j b x)=v x^r
theorem of_children (h1 :c1) (h2 :c2) :P5_7_1_7_4_3_4.c3:= by
  classical
  intro E F _ _ _ w m q hf hs hq P hp hcoeff hdvd ι S v hinj hsur hgauss
  let _:zZE (RatFunc E) F:=m.toAlgebra
  have :zAa (RatFunc E) F:=hf
  have :zw7 (RatFunc E) F:=hs
  let K:=RatFunc E
  let Ω:=CommonField K F
  let u:=gaussExtension w.value
  have hu:zpX u:=gauss_surjective _ w.normalized
  have :Infinite ℤᵐ⁰:=Infinite.of_injective (WithZero.exp:ℤ→ℤᵐ⁰) WithZero.exp_injective
  have :Infinite K:=Infinite.of_surjective u hu
  have :zAa K Ω :=
    normalClosure.is_finiteDimensional K F (AlgebraicClosure F)
  obtain ⟨hG,U,e,he,hU,hbase⟩:=h1 (F:=F) u hu
  have :IsGalois K Ω:=hG
  have hlocal (i : ↥S) : ∃ n:ℕ,0<n ∧ ∀ x :K,
      v i (algebraMap K F x)=u x^n:= by
    obtain ⟨n,hn,hv⟩:=hgauss i i.2
    exact ⟨n,hn,scaled_restriction w.value (v i) m n hv⟩
  choose n hn hv using hlocal
  have hfamily (i : ↥S) :=h2 u (v i) U hu (hsur i i.2) hU e (n i) he (hn i) hbase (hv i)
  choose r hr hre j hj using hfamily
  let J:=Σ i : ↥S,Fin (n i)
  let f :J ↪ (F →ₐ[K] Ω) :=⟨fun a=>j a.1 a.2,by
    intro a b hab
    have hvab:v a.1=v b.1 :=eq_of_scaled (hsur _ a.1.2) (hsur _ b.1.2) (hr _) (hr _)
      fun x=>(hj _ _ x).symm.trans ((congrArg (fun σ:F →ₐ[K] Ω=>U (σ x)) hab).trans (hj _ _ x))
    have hab₁:a.1=b.1 :=Subtype.ext (hinj a.1.2 b.1.2 hvab)
    rcases a with ⟨i,a⟩
    rcases b with ⟨k,b⟩
    change i=k at hab₁
    subst k
    exact congrArg (Sigma.mk i) ((j i).injective hab)⟩
  let g:=(algebraMap K Ω).comp (algebraMap E[X] K)
  let R:=P.map g
  let D := ∏ b:J,(z7y-Polynomial.C (f b q))
  have hD:D ∣R:= by
    have hsplit :D ∣(Algebra.lmul K F q).charpoly.map (algebraMap K Ω) := by
      rw [charpoly_split]
      change (∏ b:J,(fun σ:F →ₐ[K] Ω=>z7y-Polynomial.C (σ q)) (f b))∣ _
      rw [← Finset.prod_map (univ :Finset J) f
        (fun σ:F →ₐ[K] Ω=>z7y-Polynomial.C (σ q))]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
    exact hsplit.trans (by simpa only [R,g,Polynomial.map_map,bix] using
      (Polynomial.map_dvd (algebraMap K Ω) hdvd))
  have q0 (k :ℕ) :U (R.coeff k)=adG w.value (P.coeff k)^e := by
    change U ((P.map g).coeff k)= _
    rw [z0b]
    change U (algebraMap K Ω (algebraMap E[X] K _))= _
    rw [hbase,gauss_polynomial]
  have hR (k :ℕ) :U (R.coeff k)≤1 := by
    rw [q0]
    apply pow_le_one₀ zero_le
    exact Finset.sup_le (fun l _=> by simpa using hcoeff k l)
  have hR₀:R.coeff 0≠0:= by
    change (P.map g).coeff 0≠0
    rw [z0b]
    have hg:Function.Injective g :=
      (algebraMap K Ω).injective.comp (IsFractionRing.injective E[X] K)
    exact fun h=>hp (hg (h.trans g.map_zero.symm))
  have q1 :=charge_dvd_le U hR₀ hD hR
  have hsum:charge U D =(e :ℤ)*(∑ i∈S,KB (v i) q:ℕ) := by
    have hne (b:J) :f b q≠0:= by
      change (f b).toRingHom q≠0
      simpa only [map_zero] using (f b).toRingHom.injective.ne hq
    rw [charge_product U univ (fun b:J=>f b q) hne]
    rw [Fintype.sum_sigma,Nat.cast_sum,mul_sum,← Finset.sum_attach S,Finset.attach_eq_univ]
    apply Finset.sum_congr rfl
    intro i _
    have hscl (b:Fin (n i)) : (KB U (f ⟨i,b⟩ q) :ℤ) =
        (r i:ℤ)*(KB (v i) q:ℤ) :=
      zero_scale (hj i b q)
    simp only [hscl,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [← mul_assoc,← Nat.cast_mul,hre i]
  have hoff :order U (R.coeff 0) =
      (e :ℤ)*(-WithZero.log (adG w.value (P.coeff 0))) := by
    simp [order,q0,WithZero.log_pow,← mul_neg]
  rw [hsum,hoff] at q1
  have he' : (0:ℤ)<e := by exact_mod_cast he
  simpa only [Int.toNat_natCast] using
    Int.toNat_le_toNat (le_of_mul_le_mul_left q1 he')
end
end qv2t4Be
end
section
set_option linter.style.haveILetI false
namespace q9r9FBa
noncomputable section
open IsDedekindDomain WithZero
open scoped WithZero
open private eFr from ProximityPrize.SubmissionLower.Y
theorem valuationDVR {K:Type} [zrb K] (u:Valuation K ℤᵐ⁰)
  (hu:zpX u) :IsDiscreteValuationRing u.valuationSubring := by
 let G:=MonoidWithZeroHom.valueGroup (.ofClass u)
 obtain ⟨x,hx⟩:=hu (exp (-1 :ℤ))
 let y : (ℤᵐ⁰)ˣ:=Units.mk0 (u x) (hx ▸ exp_ne_zero)
 have hy :y∈G:=MonoidWithZeroHom.mem_valueGroup _ ⟨x,by simp [y,hx]⟩
 have :Nontrivial G:=⟨⟨⟨y,hy⟩,1,fun h=> by
  have h' := congrArg (fun a :G=>((a.val : (ℤᵐ⁰)ˣ) :ℤᵐ⁰)) h
  simp [y,hx] at h'⟩⟩
 exact Valuation.valuationSubring_isDiscreteValuationRing u
def primeAbove {A B:Type} [CommRing A] [CommRing B] [IsDedekindDomain A]
    [IsDedekindDomain B] [zZE A B] [FaithfulSMul A B]
    (p:HeightOneSpectrum A) (Q:Ideal B) [Q.IsPrime] [Q.LiesOver p.asIdeal] :
    HeightOneSpectrum B :=
  ⟨Q,inferInstance,Ideal.ne_bot_of_mem_primesOver p.ne_bot ⟨inferInstance,inferInstance⟩⟩
theorem adicBase {K:Type} [zrb K] (u:Valuation K ℤᵐ⁰)
   (hu:zpX u) [IsDiscreteValuationRing u.valuationSubring] :
   (IsDiscreteValuationRing.maximalIdeal u.valuationSubring).valuation K=u:= by
 let p:=IsDiscreteValuationRing.maximalIdeal u.valuationSubring
 apply eFr (p.valuation_surjective K) hu
 apply Valuation.isEquiv_of_val_le_one
 intro x
 constructor
 · intro hx
   obtain ⟨a,rfl⟩:=IsDiscreteValuationRing.exists_lift_of_le_one hx
   exact a.property
 · intro hx
   exact p.valuation_le_one (⟨x,hx⟩:u.valuationSubring)
theorem extendPlace {K F:Type} [zrb K] [zrb F] [zZE K F]
   [zAa K F] [zw7 K F]
   (u:Valuation K ℤᵐ⁰) (hu:zpX u) :
   ∃ (v :Valuation F ℤᵐ⁰) (e :ℕ),0<e∧zpX v ∧
     ∀ x :K,v (algebraMap K F x)=u x^e := by
 let A:=u.valuationSubring
 let B:=integralClosure A F
 letI:IsDiscreteValuationRing A:=valuationDVR u hu
 letI:IsDedekindDomain B:=integralClosure.isDedekindDomain A K F
 letI:z0o B F:=IsIntegralClosure.isFractionRing_of_finite_extension A K F B
 letI:FaithfulSMul A B:=(faithfulSMul_iff_algebraMap_injective A B).mpr
   (ValuationSubring.integralClosure_algebraMap_injective u F)
 letI:Module.IsTorsionFree A B:=IsIntegralClosure.isTorsionFree A F
 let p:=IsDiscreteValuationRing.maximalIdeal A
 obtain ⟨Q,hQ,hQP⟩:=Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S:=B)
   (IsLocalRing.maximalIdeal A)
 letI:Q.IsPrime :=hQ.isPrime
 letI:Q.LiesOver p.asIdeal:=hQP
 let P:=primeAbove p Q
 letI:P.asIdeal.LiesOver p.asIdeal:=hQP
 let e :=p.asIdeal.ramificationIdx' P.asIdeal
 have he :0<e :=Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P.asIdeal p.ne_bot)
 refine ⟨P.valuation F,e,he,P.valuation_surjective F,fun x => ?_⟩
 rw [← p.valuation_liesOver F P x,adicBase u hu]
theorem normalExtension :qv2t4Be.c1 := by
 intro K F _ _ _ _ _ u hu
 let Ω:=qv2t4Be.CommonField K F
 have hsep:zw7 K Ω:= by
  apply (le_separableClosure_iff K (AlgebraicClosure F) Ω).mp
  apply normalClosure_le_iff.mpr
  rintro f _ ⟨x,rfl⟩
  exact mem_separableClosure_iff.mpr ((Algebra.IsSeparable.isSeparable K x).map f f.injective)
 letI:IsGalois K Ω:=⟨⟩
 letI:zAa K Ω:=normalClosure.is_finiteDimensional K F _
 obtain ⟨V,e,he,hV,hv⟩:=extendPlace (F:=Ω) u hu
 exact ⟨inferInstance,V,e,he,hV,hv⟩
theorem eqAdicOfCenter {B F:Type} [CommRing B] [IsDedekindDomain B] [zrb F]
   [zZE B F] [z0o B F] (P:HeightOneSpectrum B) (v :Valuation F ℤᵐ⁰)
   (hv :zpX v) (hB : ∀ b:B,v (algebraMap B F b)≤1)
   (hP : ∀ b:B,b∈P.asIdeal↔v (algebraMap B F b)<1) :
   P.valuation F=v := by
 have hle :P.valuationSubringAtPrime F≤v.valuationSubring := by
   rintro z ⟨a,b,hb,rfl⟩
   change v (algebraMap B F a*(algebraMap B F b)⁻¹)≤1
   have hval :v (algebraMap B F b)=1 :=
     le_antisymm (hB b) (not_lt.mp fun h=>hb ((hP b).mpr h))
   rw [map_mul,map_inv₀,hval,inv_one,mul_one]
   exact hB a
 have hproper :v.valuationSubring ≠ ⊤ := by
   intro ht
   obtain ⟨a,ha⟩:=hv (exp 1)
   have hm:a∈v.valuationSubring := by rw [ht]; trivial
   exact (not_le_of_gt (show 1<v a by simp [ha])) hm
 have h:=ValuationSubring.eq_of_le_of_ne_top _ hle hproper
 rw [P.valuationSubringAtPrime_eq_valuationSubring] at h
 exact eFr (P.valuation_surjective F) hv ((Valuation.isEquiv_iff_valuationSubring _ _).mpr h)
theorem centerPlace {K F:Type} [zrb K] [zrb F] [zZE K F]
    (u:Valuation K ℤᵐ⁰) (v :Valuation F ℤᵐ⁰)
    (hv :zpX v) {n:ℕ} (hn:0<n)
    (h : ∀ x :K,v (algebraMap K F x)=u x^n)
    [IsDiscreteValuationRing u.valuationSubring]
    [IsDedekindDomain (integralClosure u.valuationSubring F)]
    [z0o (integralClosure u.valuationSubring F) F] :
    ∃ P:HeightOneSpectrum (integralClosure u.valuationSubring F),
      P.asIdeal.LiesOver (IsDiscreteValuationRing.maximalIdeal u.valuationSubring).asIdeal ∧
        P.valuation F=v := by
  let A:=u.valuationSubring
  let B:=integralClosure A F
  let p:=IsDiscreteValuationRing.maximalIdeal A
  have hA (a :A) :v (algebraMap A F a)≤1 := by
    change v (algebraMap K F (a :K))≤1
    rw [h]
    exact pow_le_one₀ zero_le a.property
  let f :A →+* v.valuationSubring :=
    (algebraMap A F).codRestrict v.valuationSubring.toSubring hA
  letI:zZE A v.valuationSubring :=f.toAlgebra
  letI:IsScalarTower A v.valuationSubring F:=IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  have hB (b:B) :v (algebraMap B F b)≤1 :=
    (Valuation.integer.integers v).isIntegral_iff_v_le_one.mp (IsIntegral.tower_top b.property)
  let g:B →+* v.valuationSubring :=
    (algebraMap B F).codRestrict v.valuationSubring.toSubring hB
  let Q:=(IsLocalRing.maximalIdeal v.valuationSubring).comap g
  letI:Q.IsPrime :=Ideal.IsPrime.comap _
  have hQ (b:B) :b∈Q↔v (algebraMap B F b)<1 :=
    v.mem_maximalIdeal_iff (a :=g b)
  have hQP:Q.LiesOver p.asIdeal:= by
    apply (Ideal.liesOver_iff _ _).mpr
    ext a
    change a∈IsLocalRing.maximalIdeal A↔algebraMap A B a∈Q
    rw [u.mem_maximalIdeal_iff,hQ,← IsScalarTower.algebraMap_apply A B F]
    change u (a :K)<1↔v (algebraMap K F (a :K))<1
    rw [h,← one_pow n,pow_lt_pow_iff_left₀ zero_le zero_le hn.ne',one_pow]
  letI:Q.LiesOver p.asIdeal:=hQP
  letI:FaithfulSMul A B:=(faithfulSMul_iff_algebraMap_injective A B).mpr
    (ValuationSubring.integralClosure_algebraMap_injective u F)
  exact ⟨primeAbove p Q,hQP,eqAdicOfCenter (primeAbove p Q) v hv hB hQ⟩
theorem exponent_eq {K:Type} [zrb K] (u:Valuation K ℤᵐ⁰) (hu:zpX u)
  {m n:ℕ} (h : ∀ x,u x^m=u x^n) :m=n:= by
 obtain ⟨x,hx⟩:=hu (exp 1)
 have h' := congrArg log (h x)
 simpa [hx,log_pow,nsmul_eq_mul] using h'
end
end q9r9FBa
end
end
