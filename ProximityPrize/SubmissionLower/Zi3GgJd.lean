import ProximityPrize.SubmissionLower.ZeoK8Ne
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace qfJaLMa
noncomputable section
open Polynomial
open qWIOgVd (scaleY scaleY_coeff)
variable {R:Type*} [CommRing R]
def pad (a :R) (n:ℕ) (g:R[X]) :R[X] :=(g.taylor a).reflect n
@[simp] theorem pad_zero (a :R) (n:ℕ) :pad a n 0=0:= by simp [pad,reflect_zero]
theorem pad_ne (a :R) (n:ℕ) {g:R[X]} (hg:g≠0) :pad a n g≠0:= by
 simpa only [pad,ne_eq,reflect_eq_zero_iff,taylor_eq_zero] using hg
theorem pad_bound (a :R) {n:ℕ} {g:R[X]} (hg:g.natDegree≤n) :
  (pad a n g).natDegree≤n :=
 natDegree_reflect_le.trans (max_le le_rfl (by rwa [natDegree_taylor]))
def cap (s b d i:ℕ) :ℕ:=b+(d-i)*s
def move (a :R) (s b d:ℕ) (f :R[X][X]) :R[X][X] :=
 f.sum fun i g=>monomial i (pad a (cap s b d i) g)
theorem move_coeff (a :R) (s b d:ℕ) (f :R[X][X]) (i:ℕ) :
   (move a s b d f).coeff i=pad a (cap s b d i) (f.coeff i) := by
 rw [move,Polynomial.sum_def,finsetSum_coeff,Finset.sum_eq_single i]
 · exact coeff_monomial_same _ _
 · exact fun k _ hk=>coeff_monomial_of_ne _ hk.symm
 · simp +contextual
theorem move_degree (a :R) (s b d:ℕ) {f :R[X][X]} (hf :f≠0) :
   (move a s b d f).natDegree=f.natDegree := by
 apply natDegree_eq_of_le_of_coeff_ne_zero
 · exact natDegree_le_iff_coeff_eq_zero.mpr fun i hi=> by
     rw [move_coeff,coeff_eq_zero_of_natDegree_lt hi,pad_zero]
 · rw [move_coeff]
   exact pad_ne _ _ (leadingCoeff_ne_zero.mpr hf)
theorem choose_cap {f :R[X][X]} (hf :f≠0) (s b:ℕ)
   (h : ∀ i,(f.coeff i).natDegree+i*s≤b+f.natDegree*s∨f.coeff i=0) :
   ∃ k≤b,(∀ i,(f.coeff i).natDegree≤ cap s k f.natDegree i) ∧
     ∃ i,f.coeff i≠0∧(f.coeff i).natDegree=cap s k f.natDegree i:= by
 classical
 let P (k :ℕ) := ∀ i,(f.coeff i).natDegree≤ cap s k f.natDegree i
 have hp:P b:= by
   intro i
   by_cases hz :f.coeff i=0
   · simp [hz]
   have hi:=le_natDegree_of_ne_zero hz
   have he : (f.natDegree-i)*s+i*s=f.natDegree*s := by
     rw [← add_mul,Nat.sub_add_cancel hi]
   unfold cap
   have hh:=(h i).resolve_right hz
   omega
 let hP : ∃ k,P k :=⟨b,hp⟩
 let k :=Nat.find hP
 refine ⟨k,Nat.find_min' hP hp,Nat.find_spec hP,?_⟩
 by_contra! hn
 have hk :0<k := by
   have hh:=Nat.find_spec hP f.natDegree
   have he :=hn f.natDegree (leadingCoeff_ne_zero.mpr hf)
   simp only [cap,Nat.sub_self,zero_mul,add_zero] at hh he
   omega
 have hsmall:P (k-1) := by
   intro i
   by_cases hz :f.coeff i=0
   · simp [hz]
   have hle :=Nat.find_spec hP i
   have hne :=hn i hz
   unfold cap at *
   omega
 have :=Nat.find_min' hP hsmall
 omega
variable {F:Type*} [Field F]
abbrev kB (F:Type*) [Field F] :=FractionRing F[X]
abbrev inc:F[X] →+* kB F:=algebraMap _ _
abbrev Xf :kB F:=inc (Polynomial.X:F[X])
private theorem inc_inj:Function.Injective (inc (F:=F)) :=IsFractionRing.injective _ _
theorem Xf_ne : (Xf :kB F)≠0:=(map_ne_zero_iff _ inc_inj).mpr X_ne_zero
private def invEval :F[X] →+* kB F:=eval₂RingHom (inc.comp C) Xf⁻¹
private theorem reflect_inc (g:F[X]) (n:ℕ) (hg:g.natDegree≤n) :
   inc (g.reflect n)=Xf^n*invEval g:= by
 let:Invertible (Xf :kB F)⁻¹:=invertibleOfNonzero (inv_ne_zero Xf_ne)
 have h:=eval₂_reflect_mul_pow (inc.comp C) (Xf :kB F)⁻¹ n g hg
 rw [invOf_eq_inv,inv_inv,← hom_eval₂,eval₂_C_X] at h
 calc
   _=Xf^n*(inc (g.reflect n)*(Xf⁻¹)^n) := by
     rw [mul_left_comm,← mul_pow,mul_inv_cancel₀ Xf_ne,one_pow,mul_one]
   _ = _:=congrArg (Xf^n * ·) h
private theorem invEval_inj:Function.Injective (invEval (F:=F)) :=
 (injective_iff_map_eq_zero _).mpr fun g h=> by
   simpa [h,map_eq_zero_iff _ inc_inj,reflect_eq_zero_iff] using
    reflect_inc g g.natDegree le_rfl
private def invHom:kB F →+* kB F:=IsFractionRing.lift invEval_inj
private theorem invHom_inc (g:F[X]) :invHom (inc g)=invEval g :=
 IsFractionRing.lift_algebraMap invEval_inj g
private theorem invHom_invol:Function.Involutive (invHom (F:=F)) := by
  have hc (a :F) :invHom (inc (C a))=inc (C a) := by rw [invHom_inc]; simp [invEval]
  have hx :invHom (Xf :kB F)=Xf⁻¹:= by
    change invHom (inc Polynomial.X)=Xf⁻¹
    rw [invHom_inc]
    simp [invEval]
  have he :invHom.comp invHom=RingHom.id (kB F) := by
    apply IsFractionRing.ringHom_ext (A:=F[X])
    change ∀ g,((invHom.comp invHom).comp inc) g=((RingHom.id (kB F)).comp inc) g
    apply RingHom.congr_fun
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply,RingHom.id_apply,hc]
    · simp only [RingHom.comp_apply,RingHom.id_apply,show inc Polynomial.X=Xf from rfl,
        hx,map_inv₀,inv_inv]
  exact RingHom.congr_fun he
private def changeX (a :F) :kB F ≃+* kB F :=
 (IsFractionRing.ringEquivOfRingEquiv (K:=kB F) (L:=kB F)
   (taylorEquiv a).toRingEquiv).trans (RingEquiv.ofBijective invHom invHom_invol.bijective)
private theorem change_pad (a :F) (g:F[X]) (n:ℕ) (hg:g.natDegree≤n) :
  inc (pad a n g)=Xf^n*changeX a (inc g) := by
 change inc (pad a n g)=Xf^n*invHom
  (IsFractionRing.ringEquivOfRingEquiv (taylorEquiv a).toRingEquiv (algebraMap F[X] (kB F) g))
 rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap,invHom_inc]
 exact reflect_inc _ _ ((natDegree_taylor g a).trans_le hg)
def changeY {B:Type*} [Field B] (D:B ≃+* B) (v :B) (hv :v≠0) :B[X] ≃+* B[X] :=
 (mapEquiv D).trans (scaleY v⁻¹ v (inv_mul_cancel₀ hv))
theorem move_repr (a :F) (D:kB F ≃+* kB F)
    (hD : ∀ (g:F[X]) n,g.natDegree≤n→inc (pad a n g)=Xf^n*D (inc g))
    (s b d:ℕ) (f :F[X][X]) (hf :f.natDegree≤d)
    (hb : ∀ i,(f.coeff i).natDegree≤ cap s b d i) :
    (move a s b d f).map inc =
      C (Xf^(b+d*s))*changeY D (Xf^s) (pow_ne_zero _ Xf_ne) (f.map inc) := by
  ext i
  simp only [coeff_map,move_coeff,coeff_C_mul,changeY,RingEquiv.trans_apply,
    scaleY_coeff,mapEquiv_apply]
  by_cases hi:i≤d
  · rw [hD _ _ (hb i)]
    have he :b+d*s=cap s b d i+s*i:= by
      unfold cap
      rw [Nat.mul_comm s i,Nat.add_assoc,← add_mul,Nat.sub_add_cancel hi]
    have hpow: (Xf :kB F)^(b+d*s)*((Xf^s)⁻¹)^i=Xf^(cap s b d i) := by
      rw [he,pow_add,pow_mul,inv_pow,mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero i (pow_ne_zero s Xf_ne)),mul_one]
    change Xf^cap s b d i*D (inc (f.coeff i)) =
      Xf^(b+d*s)*(D (inc (f.coeff i))*((Xf^s)⁻¹)^i)
    rw [mul_comm (D (inc (f.coeff i))),← mul_assoc,hpow]
  · rw [coeff_eq_zero_of_natDegree_lt (hf.trans_lt (Nat.lt_of_not_ge hi))]
    rw [pad_zero,map_zero,map_zero,zero_mul,mul_zero]
private theorem move_primitive {a :F} {f :F[X][X]} (hf :f.IsPrimitive) {s b:ℕ}
   (hb : ∀ i,(f.coeff i).natDegree≤ cap s b f.natDegree i)
   (hit : ∃ i,f.coeff i≠0∧(f.coeff i).natDegree=cap s b f.natDegree i) :
   (move a s b f.natDegree f).IsPrimitive := by
 rintro c ⟨g,hg⟩
 have he (i:ℕ) :=congrArg (fun h:F[X][X]=>h.coeff i) hg
 simp only [move_coeff,coeff_C_mul] at he
 have hc:c.coeff 0≠0:= by
   obtain ⟨i,hi,hn⟩:=hit
   have hh:=congrArg (fun h:F[X]=>h.coeff 0) (he i)
   rw [pad,coeff_reflect,revAt_zero,← hn,coeff_taylor_natDegree,mul_coeff_zero] at hh
   intro h
   rw [h,zero_mul] at hh
   exact leadingCoeff_ne_zero.mpr hi hh
 have hdvd:C (c.reverse.taylor (-a))∣f := by
   apply (C_dvd_iff_dvd_coeff _ _).2
   intro i
   by_cases hz :f.coeff i=0
   · rw [hz]; exact dvd_zero _
   let n:=cap s b f.natDegree i
   have hne :g.coeff i≠0:= fun h=>pad_ne a n hz (by rw [he,h,mul_zero])
   have hs :c.natDegree+(g.coeff i).natDegree≤n:= by
     rw [← natDegree_mul (fun h=>hc (by simp [h])) hne,← he]
     exact pad_bound a (hb i)
   have q0:=reflect_mul c (g.coeff i) (F:=c.natDegree) (G:=n-c.natDegree)
     le_rfl (show (g.coeff i).natDegree≤n-c.natDegree by omega)
   rw [Nat.add_sub_of_le (show c.natDegree≤n by omega),← he,pad,reflect_reflect] at q0
   refine ⟨((g.coeff i).reflect (n-c.natDegree)).taylor (-a),?_⟩
   have :=congrArg (fun q:F[X]=>q.taylor (-a)) q0
   simpa only [taylor_taylor,neg_add_cancel,taylor_zero,taylor_mul,reverse] using this
 have hu:=hf _ hdvd
 have hd:=natDegree_eq_zero_of_isUnit hu
 rw [natDegree_taylor,reverse_natDegree,natTrailingDegree_eq_zero.mpr (Or.inr hc),Nat.sub_zero] at hd
 exact isUnit_iff_degree_eq_zero.mpr
   (by rw [degree_eq_natDegree (fun h:c=0=>hc (by rw [h,coeff_zero])),hd]; rfl)
theorem move_irred {a :F} {f :F[X][X]} (hf :Irreducible f) (hd:0<f.natDegree)
  {s b:ℕ} (hb : ∀ i,(f.coeff i).natDegree≤ cap s b f.natDegree i)
  (hit : ∃ i,f.coeff i≠0∧(f.coeff i).natDegree=cap s b f.natDegree i) :
  Irreducible (move a s b f.natDegree f) := by
 have hp:=hf.isPrimitive (Nat.ne_of_gt hd)
 apply (move_primitive hp hb hit).irreducible_of_irreducible_map_of_injective inc_inj
 rw [move_repr a (changeX a) (change_pad a) s b f.natDegree f le_rfl hb]
 exact (irreducible_isUnit_mul ((pow_ne_zero _ Xf_ne).isUnit.map C)).mpr
  (((hp.irreducible_iff_irreducible_map_fraction_map (K:=kB F)).mp hf).map _)
end
end qfJaLMa
end
section
open Polynomial renaming coeff_eq_zero_of_natDegree_lt→qz0
set_option backward.isDefEq.respectTransparency false
namespace qfJaLMa
noncomputable section
open Polynomial Finset
open cu (L)
open E7 (CurveField CurvePlace poleOrder Tq)
open qb0hmCe (cLN coeffHeight)
open q1kuFjb (expansion_coeff)
open scoped WithZero
variable {E :Type} [Field E] [Algebra L E]
private theorem pad_coeff_sum (a :L) (n j:ℕ) (f :E[X]) {N :ℕ} (hN :f.natDegree<N) :
   (pad (algebraMap L E a) n f).coeff j =
     ∑ k∈range N,algebraMap L E ((pad a n ((Polynomial.X:L[X])^k)).coeff j)*f.coeff k := by
 conv_lhs=>rw [f.as_sum_range_C_mul_X_pow' hN]
 simp only [pad,coeff_reflect,map_sum,finsetSum_coeff,taylor_mul,taylor_C,coeff_C_mul]
 apply sum_congr rfl
 intro k _
 rw [mul_comm]
 congr 1
 have h:=congrArg (fun p:E[X]=>p.coeff (revAt n j))
   (map_taylor ((Polynomial.X:L[X])^k) a (algebraMap L E))
 simpa only [coeff_map,Polynomial.map_pow,map_X] using h.symm
private abbrev size (f :E[X][X]) :=(f.support.sup fun i=>(f.coeff i).natDegree)+1
omit [Algebra L E] in
private theorem lt_size (f :E[X][X]) (i:ℕ) : (f.coeff i).natDegree<size f := by
 classical
 by_cases hi:i∈f.support
 · exact Nat.lt_succ_of_le (le_sup (f := fun j=>(f.coeff j).natDegree) hi)
 · rw [notMem_support_iff.mp hi,natDegree_zero]
   exact Nat.zero_lt_succ _
theorem exp_phys_degree (e :E →ₐ[L] LaurentSeries L) (k :ℤ) (f :E[X][X]) (i:ℕ) :
  ((cLN e k f).coeff i).natDegree≤(f.coeff i).natDegree := by
 apply natDegree_le_iff_coeff_eq_zero.mpr
 intro j hj
 rw [expansion_coeff,qz0 hj,map_zero,HahnSeries.coeff_zero]
theorem exp_ord_degree (e :E →ₐ[L] LaurentSeries L) (k :ℤ) (f :E[X][X]) :
  (cLN e k f).natDegree≤f.natDegree := by
 apply natDegree_le_iff_coeff_eq_zero.mpr
 intro i hi
 ext j
 rw [expansion_coeff,qz0 hi,coeff_zero,map_zero,HahnSeries.coeff_zero,
  coeff_zero]
theorem exp_move (e :E →ₐ[L] LaurentSeries L) (k :ℤ) (a :L) (s b d:ℕ) (f :E[X][X]) :
  cLN e k (move (algebraMap L E a) s b d f)=move a s b d (cLN e k f) := by
 apply Polynomial.ext
 intro i
 apply Polynomial.ext
 intro j
 rw [expansion_coeff,move_coeff,move_coeff]
 let m:E →+ L:=(HahnSeries.coeff.addMonoidHom k).comp e.toRingHom.toAddMonoidHom
 let n:=cap s b d i
 change m ((pad (algebraMap L E a) n (f.coeff i)).coeff j)= _
 rw [pad_coeff_sum a n j _ (lt_size f i),map_sum]
 have hc:=pad_coeff_sum a n j ((cLN e k f).coeff i)
  ((exp_phys_degree e k f i).trans_lt (lt_size f i))
 rw [show (algebraMap L L a)=a from rfl] at hc
 rw [hc]
 apply sum_congr rfl
 intro t _
 rw [expansion_coeff]
 change (e (_ *_)).coeff k= _
 rw [map_mul,e.commutes,LaurentSeries.algebraMap_apply,HahnSeries.C_apply,
  HahnSeries.coeff_single_zero_mul]
 rfl
theorem move_val_le (w:CurvePlace L E) (a :L) (s b d:ℕ) (f :E[X][X])
   {M:ℤᵐ⁰} (h : ∀ i j,w.value ((f.coeff i).coeff j)≤M) (i j:ℕ) :
   w.value (((move (algebraMap L E a) s b d f).coeff i).coeff j)≤M:= by
 rw [move_coeff,pad_coeff_sum a _ j _ (lt_size f i)]
 apply w.value.map_sum_le
 intro t _
 rw [map_mul]
 by_cases hz : ((pad a (cap s b d i) ((Polynomial.X:L[X])^t)).coeff j)=0
 · rw [hz,map_zero,map_zero,zero_mul]
   exact zero_le
 · rw [w.on_constants _ hz,one_mul]
   exact h i t
private theorem pole_mono (w:CurvePlace L E) {x y :E} (h:w.value x≤w.value y) :
   poleOrder w.value x≤poleOrder w.value y := by
 unfold poleOrder
 by_cases hx :w.value x=0
 · rw [hx,WithZero.log_zero,Int.toNat_zero]
   exact Nat.zero_le _
 exact Int.toNat_le_toNat ((WithZero.log_le_log hx
   (ne_of_gt ((zero_lt_iff.mpr hx).trans_le h))).mpr h)
private abbrev Coeffs (f :E[X][X]) :=Fin (f.natDegree+1)×Fin (size f)
private def entries (f :E[X][X]) (i:Coeffs f) :E :=(f.coeff i.1).coeff i.2
theorem move_height (h:CurveField L E) (a :L) (s b d:ℕ) (f :E[X][X]) :
    coeffHeight (move (algebraMap L E a) s b d f)≤ coeffHeight f := by
  classical
  let g:=move (algebraMap L E a) s b d f
  have hp:=aFU.of_children
    bRt.proof bRu.proof L E h
  change (∑ᶠ w:CurvePlace L E,Tq w.value (entries g)) ≤
    ∑ᶠ w:CurvePlace L E,Tq w.value (entries f)
  refine finsum_le_finsum (agN.b27 hp _)
    (agN.b27 hp _) fun w => ?_
  obtain ⟨i,_,hi⟩:=Finset.exists_mem_eq_sup (univ :Finset (Coeffs f)) univ_nonempty
    (fun ij=>w.value (entries f ij))
  have hmax (j k :ℕ) :w.value ((f.coeff j).coeff k)≤w.value (entries f i) := by
    by_cases hj:j<f.natDegree+1
    · by_cases hk :k<size f
      · exact le_trans (le_sup (f := fun ij=>w.value (entries f ij))
          (mem_univ (⟨j,hj⟩,⟨k,hk⟩))) hi.le
      · rw [qz0 ((lt_size f j).trans_le (Nat.le_of_not_gt hk)),map_zero]
        exact zero_le
    · rw [qz0 (by omega :f.natDegree<j),coeff_zero,map_zero]
      exact zero_le
  exact Finset.sup_le fun (j:Coeffs g) _=>(pole_mono w (move_val_le w a s b d f hmax j.1 j.2)).trans
    (le_sup (f := fun ij=>poleOrder w.value (entries f ij)) (mem_univ i))
theorem aJj (w:CurvePlace L E) (a :E →ₐ[L] LaurentSeries L) {c:E}
   (hv :w.value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a c))
   (h:w.value c≤1) (hn: (a c).coeff 0≠0) :w.value c=1 := by
 apply le_antisymm h
 by_contra! hl
 rw [hv] at hl
 have hl' : (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a c)≤WithZero.exp (-1) := by
   by_cases hz : (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a c)=0
   · rw [hz]
     exact zero_le
   apply (WithZero.log_le_iff_le_exp hz).mp
   have hh:=(WithZero.log_lt_iff_lt_exp (a :=0) hz).mpr (by rwa [WithZero.exp_zero])
   omega
 exact hn (LaurentSeries.coeff_zero_of_lt_valuation L (D:=1) hl' (by decide))
end
end qfJaLMa
end
