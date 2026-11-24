import ProximityPrize.SubmissionLower.ZqZuDUb
set_option Elab.async false
open _root_ renaming AddMonoidAlgebra.supported→p7,AlgHom.comp_apply→qJ,Fin.sum_univ_three→pG,FiniteDimensional→qx,Finset.range→aU,Finset.sum_add_distrib→pQ,Finset.sum_congr→lJ,Finset.sum_filter→ ov,Finset.sum_range_succ→qU,Finsupp.add_apply→n5,Finsupp.degree_eq_sum→qm,Finsupp.single→nI,Finsupp.single_apply→ oj,Function.Injective→ oz,Function.LeftInverse→p9,Int.natCast_nonneg→qz,KoalaBear.is_prime→p6,LinearMap.finrank_le_finrank_of_injective→qG,LinearMap.ker→ oZ,LinearMap.mulLeft→sS,Module.Finite.of_fg→sH,Module.finrank→mD,MvPolynomial.algHom_ext→pU,MvPolynomial.homogeneousSubmodule→ ox,MvPolynomial.support_mul→pL,Nat.add_sub_cancel→ oK,Nat.cast_add→ oY,Nat.le_add_left→qM,Nat.lt_succ_of_le→pC,P5_8.bo8→nX,P5_8_2.Multiplicities→ oq,P5_8_2.Orders→c9,P5_8_2.factorFlags→lz,P5_8_2.initialFlags→lV,P5_8_2.offset→lI,P5_8_2.planeSpace→cy,Submodule.inclusion→sI,Submodule.inclusion_injective→qy,Submodule.mem_iInf→ oD,Subtype.ext→ oy,congrArg→nq,le_max_left→pz,mul_left_cancel₀→p5
section
set_option autoImplicit true
namespace P5_8_2
open i4 Finset
set_option maxHeartbeats 10000
set_option maxRecDepth 100
private theorem sum_poly_value (f :ℤ→ℤ) (a b c d value :ℤ) (n:ℕ)
  (h : ∀ x,f x=poly a b c d x) (hn:sumFormula a b c d n = 12*value) :
  (∑ i∈aU n,f i)=value := by
 simp_rw [h]
 have he :=(gvl a b c d n).trans hn
 omega
private theorem count_offsets (m J q v :ℕ) (hv :v≤J) :
  (∑ u∈aU (m+J-q),if J≤u+v then 1 else 0)=m+v-q:= by
 rw [← ov,← card_eq_sum_ones]
 have hf : ((aU (m+J-q)).filter fun u=>J≤u+v)=Ico (J-v) (m+J-q) := by
  ext u
  simp only [mem_filter,mem_range,mem_Ico]
  omega
 rw [hf,Nat.card_Ico]
 omega
private theorem column_grade (s :Source) (hv : ∀ j∈s.E,j.v≤ s.J) (q:ℕ) :
   (∑ u∈aU (s.m+s.J-q),(aTf s q ((u:ℤ) - s.J)).card) =
     ∑ j∈s.E,if j.q=q then s.m+j.v-q else 0:= by
 simp only [aTf,card_eq_sum_ones,ov]
 rw [sum_comm]
 refine lJ rfl fun j hj => ?_
 by_cases hq:j.q=q
 · simp only [hq,true_and,ite_true]
   rw [← count_offsets s.m s.J q j.v (hv j hj)]
   exact lJ rfl fun u _=> by
     have he : (0:ℤ)≤u-(s.J:ℤ)+j.v↔s.J≤u+j.v := by omega
     simp only [he]
 · simp only [hq,false_and,ite_false,sum_const_zero]
private theorem columns_of_shape (s :Source) (h:Rz s) :
  (∑ q∈aU (s.B+1),∑ u∈aU (s.m+s.J-q),(aTf s q ((u:ℤ) - s.J)).card) =
    ∑ j∈s.E,(s.m+j.v-j.q) := by
 calc
  _ = ∑ q∈aU (s.B+1),∑ j∈s.E,if j.q=q then s.m+j.v-q else 0 :=
    lJ rfl fun q _=>column_grade s (fun j hj=>(h.support j hj).2.1) q
  _ = _:= by
    rw [sum_comm]
    refine lJ rfl fun j hj => ?_
    have hq:=mem_range.mpr (pC (h.support j hj).1)
    rw [sum_eq_single_of_mem j.q hq (fun q _ hne=>ite_eq_right (Ne.symm hne)),ite_eq_left rfl]
private theorem tri_eq_sum (n:ℕ) :tri n = ∑ i∈aU (n+1),i:= by
 rw [sum_range_id,tri,oK,mul_comm]
private theorem tri_twice (n:ℕ) :tri n*2=n*(n+1) := by
 rw [tri_eq_sum,sum_range_id_mul_two,oK,mul_comm]
private theorem tri_succ (n:ℕ) :tri (n+1)=tri n+n+1 := by
 rw [tri_eq_sum,qU,← tri_eq_sum,add_assoc]
private theorem partial_triangle (n l:ℕ) :
   (∑ a∈aU l,(n-a))+tri (n-l)=tri n:= by
 induction l with
 | zero=>simp
 | succ l ih =>
   rw [qU]
   by_cases hl:l<n
   · have he :n-l=(n-(l+1))+1 := by omega
     rw [he,tri_succ] at ih
     omega
   · have he :n-(l+1)=n-l:= by omega
     simp only [he]
     omega
private theorem jets_plus_tail (m B J C delta :ℕ)
    (hBJ:J≤B) (hJC:2*C≤J) (hm:m+delta=B+1) :
    (∑ j∈aH1 B J C,(m+j.v-j.q)) +
      (∑ c∈aU (C+1),∑ b∈aU (J-2*c+1),tri (b+2*c-delta)) =
        ∑ c∈aU (C+1),∑ _b∈aU (J-2*c+1),tri (m+c) := by
  simp only [aH1,sum_sigma,Jet.q,Jet.v,Jet.a,Jet.b,Jet.c]
  rw [← pQ]
  refine lJ rfl fun c hc => ?_
  rw [← pQ]
  refine lJ rfl fun b hb => ?_
  have ha (a :ℕ) :m+(b+2*c)-(a+b+c)=m+c-a := by omega
  have ht:b+2*c-delta=m+c-(B-(b+c)+1) := by
    have :=mem_range.mp hb
    have :=mem_range.mp hc
    omega
  simp only [ha,ht]
  exact partial_triangle (m+c) (B-(b+c)+1)
private theorem columns_plus_tail_of_shape (s :Source) (hs :Rz s)
    (delta cut cap height mult:ℕ) (balance :ℕ→ℤ) (fiber :ℕ→Finset ℕ)
    (hE :s.E=aH1 s.B s.J s.C) (hm:s.m+delta=s.B+1)
    (hcut:cut=s.B+1) (hcap:cap=s.m+s.J) (hheight:height=s.C+1)
    (hmult:mult=s.m) (hb:balance=fun (u:ℕ)=>(u:ℤ)-s.J)
    (hf :fiber=fun c=>aU (s.J-2*c+1)) :
    (∑ q∈aU cut,∑ u∈aU (cap-q),(aTf s q (balance u)).card) +
      (∑ c∈aU height,∑ b∈fiber c,tri (b+2*c-delta)) =
        ∑ c∈aU height,∑ _b∈fiber c,tri (mult+c) := by
  rw [hcut,hcap,hheight,hmult,hb,hf,columns_of_shape s hs,hE]
  exact jets_plus_tail s.m s.B s.J s.C delta hs.aQV hs.index_top hm
private theorem columns_plus_tail :
    (∑ q∈aU 6252,∑ u∈aU (6559-q),(aTf nX q (lI u)).card) +
      (∑ c∈aU 980,∑ b∈bbW c,tri (b+2*c-1652)) =
        ∑ c∈aU 980,∑ _b∈bbW c,tri (4600+c) :=
  columns_plus_tail_of_shape nX P5_8.donor_shape 1652 6252 6559 980 4600 lI bbW
    rfl rfl rfl rfl rfl rfl rfl rfl
private theorem tail_reindex (f :ℕ→ℕ) :
    (∑ c∈aU 980,∑ b∈bbW c,f (b+2*c)) =
      ∑ v∈aU 1960,((v/2+1)*f v) := by
  calc
    _ = ∑ c∈aU 980,∑ v∈Ico (2*c) 1960,f v := by
      refine lJ rfl fun c hc => ?_
      rw [sum_Ico_eq_sum_range]
      have he :1960 - 2*c=1959 - 2*c+1 := by
        have :=mem_range.mp hc
        omega
      rw [bbW,he]
      exact lJ rfl fun b _=> by rw [add_comm]
    _ = ∑ c∈aU 980,∑ v∈aU 1960,if 2*c≤v then f v else 0:= by
      refine lJ rfl fun c _ => ?_
      have hf :Ico (2*c) 1960=(aU 1960).filter (fun v=>2*c≤v) := by
        ext v
        simp only [mem_Ico,mem_filter,mem_range,and_comm]
      rw [hf,ov]
    _ = _:= by
      rw [sum_comm]
      refine lJ rfl fun v hv => ?_
      have hf : ((aU 980).filter fun c=>2*c≤v)=aU (v/2+1) := by
        ext c
        simp only [mem_filter,mem_range]
        have :=mem_range.mp hv
        omega
      rw [← ov,hf,sum_const,card_range,smul_eq_mul]
private theorem sum_pairs (f :ℕ→ℕ) (n:ℕ) :
   (∑ i∈aU (2*n),f i) = ∑ i∈aU n,(f (2*i)+f (2*i+1)) := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [show 2*(n+1)=(2*n+1)+1 by omega,sum_range_succ,sum_range_succ,ih,
     qU ,add_assoc]
private theorem tail_value :
   (∑ c∈aU 980,∑ b∈bbW c,tri (b+2*c-1652))=0x1116af433:= by
 rw [tail_reindex (fun v=>tri (v-1652))]
 let f := fun v :ℕ=>(v/2+1)*tri (v-1652)
 change (∑ v∈aU (1652+308),f v)= _
 rw [sum_range_add f 1652 308]
 have hzero : (∑ v∈aU 1652,f v)=0:= by
   apply sum_eq_zero
   intro v hv
   have h:v-1652=0:= by have :=mem_range.mp hv; omega
   simp [f,h,tri]
 rw [hzero,zero_add]
 change (∑ w∈aU (2*154),f (1652+w))= _
 rw [sum_pairs (fun w=>f (1652+w)) 154]
 have hpair (i:ℕ) :f (1652+2*i)+f (1652+(2*i+1))=(827+i)*(2*i+1)^2 := by
   have h0:=tri_twice (2*i)
   have h1 :=tri_twice (2*i+1)
   have ht:tri (2*i)+tri (2*i+1)=(2*i+1)^2 := by
     have he : (2*i)*(2*i+1)+(2*i+1)*(2*i+1+1)=(2*i+1)^2*2 := by ring
     omega
   simp only [f,show (1652+2*i)/2+1=827+i by omega,
     show (1652+(2*i+1))/2+1=827+i by omega,Nat.add_sub_cancel_left,
     ← mul_add,ht]
 simp_rw [hpair]
 have hv :=sum_poly_value (fun x=>(827+x)*(2*x+1)^2) 827 3309 3312 4
   0x1116af433 154 (by intro; unfold poly; ring) (by decide)
 exact_mod_cast hv
private theorem main_value :
    (∑ c∈aU 980,∑ _b∈bbW c,tri (4600+c))=0xaa2ac507fd6:= by
  have hm :
      2*(↑(∑ c∈aU 980,∑ _b∈bbW c,tri (4600+c)) :ℤ) =
        ∑ c∈aU 980,((1960-(2:ℤ)*c)*(4600+c)*(4601+c)) := by
    simp only [bbW,sum_const,card_range,smul_eq_mul,Nat.cast_sum,mul_sum]
    refine lJ rfl fun c hc => ?_
    have hn: (↑(1959-2*c+1) :ℤ)=1960-2*c:= by have :=mem_range.mp hc; omega
    have ht:=nq (fun n:ℕ=>(n:ℤ)) (tri_twice (4600+c))
    push_cast at ht
    rw [Nat.cast_mul,hn,show (4601 :ℤ)+c=4600+c+1 by ring]
    linear_combination (1960-2*(c:ℤ))*ht
  rw [sum_poly_value (fun x=>(1960-2*x)*(4600+x)*(4601+x))
    0x9a88e7cc0 (-24295240) (-16442) (-2) 0x154558a0ffac 980
    (by intro; unfold poly; ring) (by decide)] at hm
  have ht: (2:ℤ)*0xaa2ac507fd6=0x154558a0ffac:= by decide
  exact Int.ofNat_inj.mp (p5 (by decide : (2:ℤ)≠0) (hm.trans ht.symm))
theorem column_count :
   (∑ q∈aU 6252,∑ u∈aU (6559-q),(aTf nX q (lI u)).card) =
     0xaa19ae58ba3:= by
 have h:=columns_plus_tail
 rw [tail_value,main_value] at h
 exact Nat.add_right_cancel (h.trans (by decide :0xaa2ac507fd6=0xaa19ae58ba3+0x1116af433))
end P5_8_2
end
section
set_option autoImplicit true
namespace P5_8_2
open i4 Finset
def c1 :Prop :=
  ∀ q<6252,∀ u<6559 - q,
    (GU nX q (lI u)).rank +
      mD F (cy (deg q) (lV q u)) ≤
      (aTf nX q (lI u)).card
def c2 :Prop :=
 ∀ d a,expected d a≤ mD F (cy d a)
def c3:Prop :=
  ∀ d a m,cost m≤d →
    mD F (cy (d - cost m) (wD a m)) ≤
      mD F (cy d a)
def c4 :Prop :=
  ∃ pick :ℕ→ℕ→ oq,
    0x47a97605ca1 ≤ ∑ q∈aU 6252,∑ u∈aU (6559 - q),m5 q u (pick q u)
private theorem cY5 (h2 :c2) (h3:c3) (q u:ℕ) (m:oq) :
   m5 q u m≤ mD F (cy (deg q) (lV q u)) := by
 unfold m5
 split
 · rename_i h
   exact (h2 _ _).trans (h3 _ _ _ h)
 · exact Nat.zero_le _
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :P5_8.c2 := by
 refine ⟨?_,bsK⟩
 obtain ⟨pick,hp⟩:=h4
 have hb (q:ℕ) (hq:q∈aU 6252) (u:ℕ) (hu:u∈aU (6559-q)) :
    (GU nX q (lI u)).rank+m5 q u (pick q u) ≤
    (aTf nX q (lI u)).card :=
  (Nat.add_le_add_left (cY5 h2 h3 q u (pick q u)) _).trans
    (h1 q (mem_range.mp hq) u (mem_range.mp hu))
 have hs :=(sum_le_sum fun q hq=>sum_le_sum (hb q hq)).trans column_count.le
 simp only [pQ] at hs
 change aWw nX 6252 +
  (∑ q∈aU 6252,∑ u∈aU (6559-q),m5 q u (pick q u))≤0xaa19ae58ba3 at hs
 omega
end P5_8_2
end
section
set_option autoImplicit true
namespace qHvCGFa
open i4 P5_8_2 Finset MvPolynomial
open scoped Pointwise
noncomputable section
local notation "V" => (MvPolynomial.X (R:=F) :Fin 3→lK)
abbrev Exp:=Fin 3 →₀ ℕ
def ex (a b c:ℕ) :Exp:=Finsupp.equivFunOnFinite.symm ![a,b,c]
@[simp] theorem ex_zero (a b c:ℕ) :ex a b c 0=a :=rfl
@[simp] theorem ex_one (a b c:ℕ) :ex a b c 1=b:=rfl
@[simp] theorem ex_two (a b c:ℕ) :ex a b c 2=c:=rfl
theorem ex_eta (e :Exp) :ex (e 0) (e 1) (e 2)=e := by
 ext i
 fin_cases i <;> rfl
def Ac (j:Jet) :Exp:=ex j.a j.b j.c
def rowExp (j:Jet) :Exp:=ex j.b j.c j.a
def bYa (e :Exp) :Jet:=⟨e 2,e 1,e 0⟩
theorem colExp_injective :oz Ac:= by
 intro i j h
 have hl:p9 bYa Ac:= by rintro ⟨c,b,a⟩; rfl
 exact hl.injective h
def target :lK →ₐ[F] lK:=aeval ![V 2+V 0-V 1,V 0,V 1]
def source (q:ℕ) :lK →ₗ[F] lK :=
 (sS F (V 0^(q - deg q))).comp (bqh 0).toLinearMap
private def b6v :lK →ₐ[F] lK:=aeval ![V 0+V 1,V 1,V 2]
private theorem inverseP_comp:b6v.comp (bqh 0)=AlgHom.id F lK:= by
 apply pU
 intro i
 fin_cases i <;> simp [b6v,bqh]
theorem source_injective (q:ℕ) :oz (source q) := by
 have hP:oz (bqh 0) :=
  (show p9 b6v (bqh 0) from
    fun f=>AlgHom.congr_fun inverseP_comp f).injective
 intro f g h
 apply hP
 exact p5 (pow_ne_zero _ (X_ne_zero (R:=F) (0:Fin 3))) h
private def swapEnds :Equiv.Perm (Fin 3) :=Equiv.swap 0 2
private theorem flagQ: (rename (R:=F) swapEnds).comp (bqh 0)=bqh 1 := by
 have h0:swapEnds 0=2 := by decide
 have h1 :swapEnds 1=1 := by decide
 have h2 :swapEnds 2=0:= by decide
 apply pU
 intro i
 fin_cases i <;> simp [bqh,h0,h1,h2]
private theorem flagO:target.comp (bqh 0)=bqh 2 := by
 apply pU
 intro i
 fin_cases i <;> simp [target,bqh]
 ring
private theorem flag_test {q u:ℕ} (f :cy (deg q) (lV q u))
  (i:Fin 3) {e :Exp} (he :e∈(bqh i f.val).support) :
  ((lV q u i).1≤(e 1 :ℤ)+e 2) ∧
    ((lV q u i).2≤(e 1 :ℤ)+2*e 2) := by
 have hh:f.val∈flagSpace i (lV q u i) :=
  ((oD _).mp f.property.2) i
 exact (AddMonoidAlgebra.mem_supported.mp hh) he
private theorem P_support {q u:ℕ} (f :cy (deg q) (lV q u))
   {e :Exp} (he :e∈(bqh 0 f.val).support) :
   e 0+e 1+e 2=deg q∧e 2≤979∧e 1+2*e 2≤1959 ∧
     0≤lI u+(e 1 :ℤ)+2*e 2 := by
 have hf :f.val.IsHomogeneous (deg q) :=f.property.1
 have hX (i:Fin 3) :=isHomogeneous_X F i
 have hP: (bqh 0 f.val).IsHomogeneous (deg q) := by
   have h:=hf.aeval (![V 0-V 1,V 1,V 2] :Fin 3→lK)
     (fun i=> by fin_cases i <;> first | exact (hX 0).sub (hX 1) | exact hX _)
   simpa [bqh] using h
 have hd:=hP (MvPolynomial.mem_support_iff.mp he)
 change e.weight (fun _:Fin 3=>1)=deg q at hd
 rw [← Finsupp.degree_eq_weight_one,qm,pG] at hd
 have hp:=(flag_test f 0 he).2
 change -offset u≤(e 1 :ℤ)+2*e 2 at hp
 have hswap:e.mapDomain swapEnds=ex (e 2) (e 1) (e 0) := by
   have hw (i:Fin 3) :=Finsupp.mapDomain_apply_of_injective swapEnds.injective e i
   have h0:swapEnds 0=2 := by decide
   have h1 :swapEnds 1=1 := by decide
   have h2 :swapEnds 2=0:= by decide
   ext i
   fin_cases i
   · change (e.mapDomain swapEnds) 0=e 2
     simpa only [h2] using hw 2
   · change (e.mapDomain swapEnds) 1=e 1
     simpa only [h1] using hw 1
   · change (e.mapDomain swapEnds) 2=e 0
     simpa only [h0] using hw 0
 have heQ:e.mapDomain swapEnds∈(bqh 1 f.val).support := by
   rw [MvPolynomial.mem_support_iff,← flagQ,qJ,coeff_rename_mapDomain _ swapEnds.injective]
   exact MvPolynomial.mem_support_iff.mp he
 have hq:=flag_test f 1 heQ
 rw [hswap] at hq
 change (deg q:ℤ)-979≤(e 1 :ℤ)+e 0 ∧
   2*(deg q:ℤ) - 1959≤(e 1 :ℤ)+2*e 0 at hq
 exact ⟨hd,by omega,by omega,by omega⟩
private theorem source_indices {q u:ℕ}
   (f :cy (deg q) (lV q u)) {e :Exp}
   (he :e∈(source q f.val).support) :
   (bYa e).q=q∧(bYa e).c≤979∧(bYa e).v≤1959 ∧
     0≤lI u+((bYa e).v :ℤ) := by
 classical
 change e∈(V 0^(q - deg q)*bqh 0 f.val).support at he
 let a0:=nI (0:Fin 3) (q - deg q)
 have hn:=MvPolynomial.mem_support_iff.mp he
 rw [MvPolynomial.X_pow_eq_monomial,coeff_monomial_mul',one_mul] at hn
 change (if a0≤e then (bqh 0 f.val).coeff (e-a0) else 0)≠0 at hn
 have ha :a0≤e := by
   by_contra hnle
   exact hn (ite_eq_right hnle)
 have hb:e-a0∈(bqh 0 f.val).support :=
   MvPolynomial.mem_support_iff.mpr (by simpa only [ite_eq_left ha] using hn)
 obtain ⟨hd,ht,hi,hl⟩:=P_support f hb
 have hdeg:deg q≤q:=min_le_left _ _
 have heq :a0+(e-a0)=e :=add_tsub_cancel_of_le ha
 rw [← heq]
 have h0:a0 0=q - deg q:= by simp [a0]
 have h1 :a0 1=0:= by simp [a0]
 have h2 :a0 2=0:= by simp [a0]
 simp only [Jet.q,Jet.v,Jet.a,Jet.b,Jet.c,bYa,n5 ,
   h0,h1,h2,zero_add,oY ,Nat.cast_mul,Nat.cast_ofNat]
 exact ⟨by omega,ht,hi,by omega⟩
theorem apx (s :Source) {B J C q u:ℕ} (hE :s.E=aH1 B J C)
  (hB:J≤B) (hJC:2*C≤J) (hJ:1959≤J) (hC:979≤C) (hq:q≤B)
  (f :cy (deg q) (lV q u)) {e :Exp}
  (he :e∈(source q f.val).support) :
  bYa e∈aTf s q (lI u) := by
 have hs :=source_indices f he
 refine mem_filter.mpr ⟨?_,hs.1,hs.2.2.2⟩
 rw [hE]
 exact (b8U hB hJC _).mpr ⟨hs.1.trans_le hq,hs.2.2.1.trans hJ,hs.2.1.trans hC⟩
theorem target_order {q u:ℕ} (f :cy (deg q) (lV q u))
  {e :Exp} (he :e∈(target (source q f.val)).support) :
  4600-(q:ℤ) - lI u≤(e 1 :ℤ)+2*e 2 := by
 classical
 change e∈(target (V 0^(q - deg q)*bqh 0 f.val)).support at he
 rw [map_mul,← qJ,flagO] at he
 have hs :=pL (target (V 0^(q - deg q))) (bqh 2 f.val) he
 obtain ⟨a,_,b,hb,rfl⟩:=Finset.mem_add.mp hs
 have h:=(flag_test f 2 hb).2
 change 4600-(q:ℤ) - lI u≤(b 1 :ℤ)+2*b 2 at h
 simp only [n5 ,oY]
 omega
end
end qHvCGFa
end
section
namespace qNtJgmd
open P5_8_2 MvPolynomial
noncomputable section
local instance :Fact (Nat.Prime i4.p) :=⟨p6⟩
private abbrev Exponent:=Fin 3 →₀ ℕ
private abbrev Forms (d:ℕ) :=ox (Fin 3) F d
private abbrev Triangle (n:ℕ) :=Σ k :Fin n,Fin (k.val+1)
private theorem cuc (n:ℕ) :Nat.card (Triangle n)=tri n:= by
 rw [Nat.card_sigma]
 simp only [Nat.card_fin]
 rw [Fin.sum_univ_eq_sum_range (fun k=>k+1),← show
   (∑ k∈aU (n+1),k) = ∑ k∈aU n,(k+1) by
     rw [Finset.sum_range_succ',add_zero],Finset.sum_range_id,tri,oK,
   Nat.mul_comm]
private theorem degree_eq (e :Exponent) :e.degree=e 0+e 1+e 2 := by
 rw [qm,pG,add_assoc]
private def exponent (d k c:ℕ) :Exponent :=
 Finsupp.equivFunOnFinite.symm ![d - k,k - c,c]
private theorem bdB (d k c:ℕ) (hk :k≤d) (hc:c≤k) :
  (exponent d k c).degree=d:= by
 rw [degree_eq]
 change d - k+(k - c)+c=d
 omega
private theorem exponent_recover (d:ℕ) (e :Exponent) (he :e.degree=d) :
   exponent d (e 1+e 2) (e 2)=e := by
 rw [degree_eq] at he
 ext i
 fin_cases i
 · change d-(e 1+e 2)=e 0
   omega
 · change e 1+e 2 - e 2=e 1
   omega
 · rfl
private def cJL (d:ℕ) : {e :Exponent // e.degree=d} ≃ Triangle (d+1) where
  toFun e :=⟨⟨e.1 1+e.1 2,by
    have he :=e.property
    rw [degree_eq] at he
    omega⟩,⟨e.1 2,pC (qM _ _)⟩⟩
  invFun p:=⟨exponent d p.1 p.2,bdB d p.1 p.2
    (Nat.lt_succ_iff.mp p.1.isLt) (Nat.lt_succ_iff.mp p.2.isLt)⟩
  left_inv e :=oy (exponent_recover d e.1 e.2)
  right_inv p:= by
    have h:=p.2.isLt
    apply Sigma.ext
    · apply Fin.ext
      change p.1.val - p.2.val+p.2.val=p.1.val
      omega
    · apply (Fin.heq_ext_iff (by
        change p.1.val - p.2.val+p.2.val+1=p.1.val+1
        omega)).2
      rfl
private theorem forms_finrank (d:ℕ) :mD F (Forms d)=tri (d+1) := by
 change mD F (ox (Fin 3) F d)= _
 rw [homogeneousSubmodule_eq_finsupp_supported]
 change mD F (restrictSupport F _)= _
 rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport F _)]
 exact (Nat.card_congr (cJL d)).trans (cuc _)
private abbrev iy (a :c9) :=(normalize a).1.toNat
private abbrev extra (a :c9) :=((normalize a).2 - (normalize a).1).toNat
private abbrev FlagRows (a :c9) :=Triangle (iy a) ⊕ Triangle (extra a)
private theorem c9a (a :c9) :Nat.card (FlagRows a)=yC a := by
 rw [Nat.card_sum,cuc,cuc]
 rfl
private def rowExponent (d:ℕ) (a :c9) :FlagRows a→Exponent
 | .inl p=>exponent d p.1 p.2
 | .inr p=>exponent d (p.1.val+iy a - p.2.val) p.2
private theorem extra_lt (a :c9) (b c:ℕ) (h:iy a≤b+c)
  (hbad : ¬ (a.1≤(b:ℤ)+c∧a.2≤(b:ℤ)+2*c)) :
  b+c - iy a+c<extra a := by
 let u:ℤ:=(normalize a).1
 have h₀:0≤u:=pz _ _
 have h₁:a.1≤u:=(pz _ _).trans (le_max_right _ _)
 have h₂:a.2≤ max u a.2 :=le_max_right _ _
 have hw:0≤ max u a.2 - u:=sub_nonneg.mpr (pz _ _)
 change u.toNat≤b+c at h
 change b+c - u.toNat+c<(max u a.2 - u).toNat
 omega
private theorem has_row (d:ℕ) (a :c9) (e :Exponent) (he :e.degree=d)
   (hbad : ¬ (a.1≤(e 1 :ℤ)+e 2∧a.2≤(e 1 :ℤ)+2*e 2)) :
   ∃ r,rowExponent d a r=e := by
 by_cases h:e 1+e 2< iy a
 · exact ⟨.inl ⟨⟨e 1+e 2,h⟩,⟨e 2,pC (qM _ _)⟩⟩,
     exponent_recover d e he⟩
 · have hr :=extra_lt a (e 1) (e 2) (by omega) hbad
   refine ⟨.inr ⟨⟨e 1+e 2 - iy a+e 2,hr⟩,
     ⟨e 2,pC  (qM  _ _)⟩⟩,?_⟩
   change exponent d (e 1+e 2 - iy a+e 2+iy a-e 2) (e 2)=e
   rw [show e 1+e 2 - iy a+e 2+iy a-e 2=e 1+e 2 by omega]
   exact exponent_recover d e he
private theorem flag_homogeneous (i:Fin 3) (d:ℕ) (p:Forms d) :
  (bqh i p.val).IsHomogeneous d:= by
 have hx (j:Fin 3) : (MvPolynomial.X j:lK).IsHomogeneous 1 :=isHomogeneous_X F j
 have hp:p.val.IsHomogeneous d:=p.property
 have hy (y :Fin 3→lK) (h : ∀ j,(y j).IsHomogeneous 1) :
    (MvPolynomial.aeval y p.val).IsHomogeneous d:= by
  simpa only [one_mul] using hp.aeval y h
 unfold bqh
 split_ifs <;> apply hy <;> intro j <;> fin_cases j <;>
  first | exact (hx _).sub (hx _) | exact hx _
private def Bu (d:ℕ) (a :Flags) :Forms d →ₗ[F] ((Σ i:Fin 3,FlagRows (a i))→F) :=
 LinearMap.pi fun r =>
  ((lcoeff F (rowExponent d (a r.1) r.2)).comp (bqh r.1).toLinearMap).domRestrict (Forms d)
private theorem ker_mem (d:ℕ) (a :Flags) (f :oZ (Bu d a)) :
   f.val.val∈cy d a := by
 refine ⟨f.val.property,(oD _).mpr fun i => ?_⟩
 change bqh i f.val.val∈p7 F F _
 rw [AddMonoidAlgebra.mem_supported']
 intro e hbad
 by_cases he :e.degree=d
 · obtain ⟨r,hr⟩:=has_row d (a i) e he hbad
   have hz :=congrFun (LinearMap.mem_ker.mp f.property) ⟨i,r⟩
   change (bqh i f.val.val).coeff (rowExponent d (a i) r)=0 at hz
   rwa [hr] at hz
 · exact (flag_homogeneous i d f.val).coeff_eq_zero he
theorem proof :P5_8_2.c2 := by
 intro d a
 let:qx F (Forms d) :=
   sH (homogeneousSubmodule_fg (Fin 3) F d)
 have hs :cy d a≤Forms d:=inf_le_left
 let:qx F (cy d a) :=
   FiniteDimensional.of_injective (sI hs) (qy hs)
 let L:=Bu d a
 let g:oZ L →ₗ[F] cy d a :=
   ((Forms d).subtype.domRestrict (oZ L)).codRestrict _ (ker_mem d a)
 have hg:oz g:= by
   intro x y h
   have h' := nq (fun z :cy d a=>(z :lK)) h
   exact oy (oy (show x.val.val=y.val.val from h'))
 have hk :=qG hg
 have hd:=L.finrank_range_add_finrank_ker
 rw [forms_finrank] at hd
 have hr :mD F (LinearMap.range L) ≤
     mD F ((Σ i:Fin 3,FlagRows (a i))→F) :=(LinearMap.range L).finrank_le
 rw [Module.finrank_pi,← Nat.card_eq_fintype_card,Nat.card_sigma,pG] at hr
 simp only [c9a] at hr
 unfold expected
 omega
end
end qNtJgmd
end
section
set_option autoImplicit true
namespace qZtSHva
open P5_8_2 MvPolynomial Finset
open scoped BigOperators
noncomputable section
local instance :Fact (Nat.Prime i4.p) :=⟨p6⟩
local notation "Xₚ" => MvPolynomial.X (R:=F) (σ:=Fin 3)
local notation "h" => Xₚ 0
local notation "u" => Xₚ 1
local notation "v" => Xₚ 2
private def factor (j:Fin 6) :lK :=
 ![v,u,h,h+u,h+v,h*u+h*v+u*v] j
private def orderSpace (a :c9) :Submodule F lK :=
 p7 F F {e :Fin 3 →₀ ℕ |
  a.1≤(e 1 :ℤ)+e 2∧a.2≤(e 1 :ℤ)+2*e 2}
private theorem mem_orderSpace {a :c9} {P:lK} :
  P∈orderSpace a ↔ ∀ e∈P.support,
    a.1≤(e 1 :ℤ)+e 2∧a.2≤(e 1 :ℤ)+2*e 2 :=
 Iff.rfl
private theorem mem_mul {a b:c9} {P Q:lK}
  (hP:P∈orderSpace a) (hQ:Q∈orderSpace b) :
  P*Q∈orderSpace (a.1+b.1,a.2+b.2) := by
 apply mem_orderSpace.mpr
 intro e he
 obtain ⟨s,hs,t,ht,rfl⟩:=Finset.mem_add.mp (pL P Q he)
 obtain ⟨hs₁,hs₂⟩:=mem_orderSpace.mp hP s hs
 obtain ⟨ht₁,ht₂⟩:=mem_orderSpace.mp hQ t ht
 simp only [n5 ,oY]
 omega
private theorem mem_zero_orders (P:lK) :P∈orderSpace (0,0) := by
 apply mem_orderSpace.mpr
 intro e _
 have h₁:0≤(e 1 :ℤ) :=qz _
 have h₂:0≤(e 2 :ℤ) :=qz _
 constructor <;> omega
private theorem mem_pow {a :c9} {P:lK} (hP:P∈orderSpace a) (k :ℕ) :
   P^k∈orderSpace ((k :ℤ)*a.1,(k :ℤ)*a.2) := by
 induction k with
 | zero=>simpa using mem_zero_orders 1
 | succ k ih =>
   simpa only [pow_succ,Nat.cast_succ,add_mul,one_mul] using mem_mul ih hP
private theorem mem_prod {ι:Type} (s :Finset ι) (P:ι→lK) (a :ι→c9)
   (ha : ∀ j∈s,P j∈orderSpace (a j)) :
   (∏ j∈s,P j)∈orderSpace (∑ j∈s,(a j).1,∑ j∈s,(a j).2) := by
 classical
 induction s using Finset.induction_on with
 | empty=>simpa using mem_zero_orders 1
 | insert j s hj ih =>
   rw [prod_insert hj,sum_insert hj,sum_insert hj]
   have hj' : P j∈orderSpace (a j) :=ha j (mem_insert_self _ _)
   have hs : (∏ k∈s,P k)∈orderSpace (∑ k∈s,(a k).1,∑ k∈s,(a k).2) :=
     ih fun k hk=>ha k (mem_insert_of_mem hk)
   exact mem_mul (a :=a j) (b:=(∑ k∈s,(a k).1,∑ k∈s,(a k).2)) hj' hs
private theorem mem_X {a :c9} (i:Fin 3)
  (ha :a.1≤((nI i (1 :ℕ)) 1 :ℤ)+(nI i (1 :ℕ)) 2)
  (hb:a.2≤((nI i (1 :ℕ)) 1 :ℤ)+2*(nI i (1 :ℕ)) 2) :
  Xₚ i∈orderSpace a := by
 apply mem_orderSpace.mpr
 intro e he
 rw [support_X,mem_singleton] at he
 subst e
 exact ⟨ha,hb⟩
private theorem mem_XX {a :c9} (i j:Fin 3)
   (ha :a.1≤((nI i 1+Finsupp.single j 1 :Fin 3 →₀ ℕ) 1 :ℤ) +
     (nI i 1+Finsupp.single j 1 :Fin 3 →₀ ℕ) 2)
   (hb:a.2≤((nI i 1+Finsupp.single j 1 :Fin 3 →₀ ℕ) 1 :ℤ) +
     2*(nI i 1+Finsupp.single j 1 :Fin 3 →₀ ℕ) 2) :
   Xₚ i*Xₚ j∈orderSpace a := by
 apply mem_orderSpace.mpr
 intro e he
 obtain ⟨s,hs,t,ht,rfl⟩:=Finset.mem_add.mp (pL _ _ he)
 rw [support_X,mem_singleton] at hs ht
 subst s t
 exact ⟨ha,hb⟩
private theorem conic_P:bqh 0 (factor 5)=h*u+h*v - u*u:= by
 simp [bqh,factor]
 ring
private theorem conic_Q:bqh 1 (factor 5)=v*u+v*h - u*u:= by
 simp [bqh,factor]
 ring
private theorem conic_O:bqh 2 (factor 5)=v*u+v*h - u*u:= by
 simp [bqh,factor]
 ring
private theorem mem_u:u∈orderSpace (1,1) := by
 apply mem_X
 all_goals norm_num [oj]
private theorem mem_v :v∈orderSpace (1, 2) := by
 apply mem_X
 all_goals norm_num [oj]
private theorem mem_v_sub_u:v - u∈orderSpace (1,1) := by
 refine (orderSpace (1,1)).sub_mem ?_ mem_u
 apply mem_X
 all_goals norm_num [oj]
private theorem mem_conic_P:h*u+h*v - u*u∈orderSpace (1,1) := by
 refine (orderSpace (1,1)).sub_mem ((orderSpace (1,1)).add_mem ?_ ?_) ?_
 all_goals apply mem_XX
 all_goals norm_num [n5 ,oj]
private theorem mem_conic_QO:v*u+v*h - u*u∈orderSpace (1, 2) := by
 refine (orderSpace (1, 2)).sub_mem ((orderSpace (1, 2)).add_mem ?_ ?_) ?_
 all_goals apply mem_XX
 all_goals norm_num [n5 ,oj]
private theorem cN8 (j:Fin 6) (i:Fin 3) :
   bqh i (factor j)∈orderSpace (lz j i) := by
 fin_cases i
 · fin_cases j
   · simpa [bqh,factor,lz] using mem_v
   · simpa [bqh,factor,lz] using mem_u
   · exact mem_zero_orders _
   · exact mem_zero_orders _
   · exact mem_zero_orders _
   · change bqh 0 (factor 5)∈orderSpace (1,1)
     rw [conic_P]
     exact mem_conic_P
 · fin_cases j
   · exact mem_zero_orders _
   · simpa [bqh,factor,lz] using mem_u
   · simpa [bqh,factor,lz] using mem_v_sub_u
   · simpa [bqh,factor,lz] using mem_v
   · exact mem_zero_orders _
   · change bqh 1 (factor 5)∈orderSpace (1, 2)
     rw [conic_Q]
     exact mem_conic_QO
 · fin_cases j
   · simpa [bqh,factor,lz] using mem_u
   · exact mem_zero_orders _
   · simpa [bqh,factor,lz] using mem_v_sub_u
   · exact mem_zero_orders _
   · simpa [bqh,factor,lz] using mem_v
   · change bqh 2 (factor 5)∈orderSpace (1, 2)
     rw [conic_O]
     exact mem_conic_QO
private theorem d5V (j:Fin 6) : (factor j).IsHomogeneous (yE j) := by
 have hx (i:Fin 3) :=isHomogeneous_X F i
 fin_cases j <;> simp [factor,yE]
 · exact hx _
 · exact hx _
 · exact hx _
 · exact (hx _).add (hx _)
 · exact (hx _).add (hx _)
 · exact (((hx _).mul (hx _)).add ((hx _).mul (hx _))).add ((hx _).mul (hx _))
private theorem b2K (j:Fin 6) :factor j≠0:= by
 intro hz
 fin_cases j
 · simpa [factor] using nq (eval (![0,0,1] :Fin 3→F)) hz
 · simpa [factor] using nq (eval (![0,1,0] :Fin 3→F)) hz
 · simpa [factor] using nq (eval (![1,0,0] :Fin 3→F)) hz
 · simpa [factor] using nq (eval (![1,0,0] :Fin 3→F)) hz
 · simpa [factor] using nq (eval (![1,0,0] :Fin 3→F)) hz
 · simpa [factor] using nq (eval (![1,1,0] :Fin 3→F)) hz
private def product (m:oq) :lK := ∏ j,factor j^m j
private theorem product_mem {d:ℕ} {a :Flags} {m:oq}
    (hd:cost m≤d) {P:lK} (hP:P∈cy (d - cost m) (wD a m)) :
    product m*P∈cy d a := by
  obtain ⟨hdeg,hflag⟩:=Submodule.mem_inf.mp hP
  refine Submodule.mem_inf.mpr ⟨?_,(oD _).mpr fun i => ?_⟩
  · have hp: (product m).IsHomogeneous (cost m) := by
      unfold product cost
      apply IsHomogeneous.prod
      intro j _
      simpa only [Nat.mul_comm] using (d5V j).pow (m j)
    have hdegree :=hdeg
    rw [mem_homogeneousSubmodule] at hdegree ⊢
    simpa only [Nat.add_sub_of_le hd] using hp.mul hdegree
  · have hi:bqh i P∈orderSpace (wD a m i) :=(oD _).mp hflag i
    let spent:Orders :=
      (∑ j,(m j:ℤ)*(lz j i).1,∑ j,(m j:ℤ)*(lz j i).2)
    have hp:bqh i (product m)∈orderSpace spent:= by
      rw [product,map_prod]
      simp only [map_pow]
      exact mem_prod univ _ (fun j=>((m j:ℤ)*(lz j i).1,
        (m j:ℤ)*(lz j i).2)) fun j _=>mem_pow (cN8 j i) (m j)
    have he : (spent.1+(wD a m i).1,spent.2+(wD a m i).2)=a i:= by
      apply Prod.ext <;> dsimp [spent,wD] <;> omega
    change bqh i (product m*P)∈orderSpace (a i)
    rw [map_mul,← he]
    exact mem_mul hp hi
theorem proof :P5_8_2.c3:= by
 intro d a m hd
 have :Module.Finite F (ox (Fin 3) F d) :=
  sH (homogeneousSubmodule_fg (Fin 3) F d)
 have hle :cy d a≤ox (Fin 3) F d:=inf_le_left
 have :Module.Finite F (cy d a) :=
  Module.Finite.of_injective (sI hle) (qy hle)
 let f :=(sS F (product m)).domRestrict (cy (d-cost m) (wD a m))
 let g:=f.codRestrict (cy d a) (fun P=>product_mem hd P.property)
 have hn:product m≠0 :=
  Finset.prod_ne_zero_iff.mpr fun j _=>pow_ne_zero _ (b2K j)
 apply qG (f :=g)
 intro P Q hpq
 exact oy (p5 hn (nq Subtype.val hpq))
end
end qZtSHva
end
