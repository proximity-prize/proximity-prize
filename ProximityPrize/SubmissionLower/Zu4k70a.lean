import ProximityPrize.SubmissionLower.Zx0Npsd
set_option Elab.async false
open _root_ renaming Finset → zJe, Finset.card_image_of_injective → ze7, Finset.sum_le_sum → zQk, Function.Injective → zq4, IsFractionRing.injective → zxb, LinearMap.range → zWl, Module.finrank → zsE, MvPolynomial.eval → zY9, Nat.add_le_add_left → z3b, Nat.add_le_add_right → zlr, Nat.mul_le_mul_right → ztf, Nat.sub_le_sub_left → zTu, Polynomial.C_injective → zmy, Polynomial.eval_C → zFf, Polynomial.eval_add → zvF, Polynomial.eval_mul → zbr, Polynomial.map_mul → zNl, Polynomial.map_ne_zero_iff → zeI, Set.ncard_coe_finset → zik
section
set_option autoImplicit true
namespace P6_3
noncomputable section
open P6 Polynomial ProximityPrize.Benchmark gR
open Rv (Adjugate lK)
open private aSU ccE bYK from ProximityPrize.SubmissionLower.B3
theorem dsk {u:e9} {T:qo u} {R:Relation T} {D:Reduction u T R}
    (B:KJ u T R D) (hnp:baQ B)
    (W:lK u (pJ R) D.height (afT B) (aeb B))
    (hroom:k+3*D.height+(pJ R).card≤blockLength) :
    Nonempty (Adjugate u (pJ R) D.height) := by
  change 131072 + 3*D.height+(pJ R).card≤262144 at hroom
  let A:=B.α
  let V:= fun j=>(B.β j).map twist
  let s :=uO (A 0) (A 1)
  let t:=uO (V 0) (V 1)
  have htw (P:K[X]) : (P.map twist).natDegree=P.natDegree :=
    natDegree_map_eq_of_injective twist.injective _
  have ht:t=uO (B.β 0) (B.β 1) := by simp only [t,V,uO,htw]
  have ha :B.a.natDegree+t≤D.height:=ht ▸ B.first_degree
  have hb:B.b.natDegree+s≤D.height:=B.second_degree
  have hv :IsCoprime (V 0) (V 1) :=B.β_primitive.map (mapRingHom twist)
  have hout (j l:Fin 2) : (W.output j l).natDegree<131072+D.height:= by
    by_cases hz :W.output j l=0
    · simp [hz]
    · exact (natDegree_lt_iff_degree_lt hz).mpr (W.output_degree j l)
  let L:= fun l=>A 0*W.output 1 l - A 1*W.output 0 l
  let N := fun j=>V 1*W.output j 0-V 0*W.output j 1
  let w:= fun i=>B.a.eval (node i)*((A 0).eval (node i)*u 1 i-(A 1).eval (node i)*u 0 i)
  let z := fun i=>B.b.eval (node i)*((V 0).eval (node i)*(u 1 i)^p-(V 1).eval (node i)*(u 0 i)^p)
  have hn (i:I) (hi:i∉pJ R) (j l:Fin 2) :
      (W.output j l).eval (node i) =
        B.a.eval (node i)*(V l).eval (node i)*u j i -
        B.b.eval (node i)*(A j).eval (node i)*(u l i)^p:= by
    rw [← W.nodes i hi]
    simp only [afT,aeb,eval_mul,eval_neg,A,V]
    ring
  obtain ⟨P,hP,heP⟩:=ccE (pJ R) V L w (131072+D.height+s) hv
    (fun l=>bYK (aSU A 0) (aSU A 1) (hout 1 l) (hout 0 l))
    (by intro i hi j; simp only [L,w,eval_sub,eval_mul,hn i hi]; ring)
    (by change t<_; omega) (by change _+t+_≤_; omega)
  obtain ⟨Q,hQ,heQ⟩:=ccE (pJ R) A N z (131072+D.height+t) B.α_primitive
    (fun j=>bYK (aSU V 1) (aSU V 0) (hout j 0) (hout j 1))
    (by intro i hi j; simp only [N,z,eval_sub,eval_mul,hn i hi]; ring)
    (by change s<_; omega) (by change _+s+_≤_; omega)
  change P.natDegree+t<131072+D.height+s at hP
  change Q.natDegree+s<131072+D.height+t at hQ
  let σ:=RingEquiv.ofBijective twist ⟨twist.injective,Finite.surjective_of_injective twist.injective⟩
  let τ:=σ.symm.toRingHom
  have hundo (x :K) :τ (twist x)=x :=σ.symm_apply_apply x
  have hfixed (i:I) :τ (node i)=node i:= by
    have hh:twist (node i)=node i:=Native.ahU i
    simpa only [hh] using hundo (node i)
  have hmap (F:K[X]) (i:I) : (F.map τ).eval (node i)=τ (F.eval (node i)) :=
    kL.aC4 τ _ _ (hfixed i)
  have hβ (l:Fin 2) (i:I) : (V l).eval (node i)=twist ((B.β l).eval (node i)) :=
    kL.aC4 twist _ _ (Native.ahU i)
  let b:=B.b.map τ
  let Q' := Q.map τ
  have heQ' (i:I) (hi:i∉pJ R) :Q'.eval (node i)=b.eval (node i) *
      ((B.β 0).eval (node i)*u 1 i-(B.β 1).eval (node i)*u 0 i) := by
    rw [show Q'.eval (node i)=τ (Q.eval (node i)) from hmap Q i,heQ i hi]
    change τ (B.b.eval (node i)*((V 0).eval (node i)*twist (u 1 i) -
      (V 1).eval (node i)*twist (u 0 i)))= _
    simp only [b,hmap,hβ,map_mul,map_sub,hundo]
  let det:=A 0*B.β 1 - A 1*B.β 0
  let denom:=B.a*b*det
  let num := fun j=>b*B.β j*P - B.a*A j*Q'
  have hb' : b.natDegree=B.b.natDegree :=natDegree_map_eq_of_injective τ.injective _
  have hQ' : Q'.natDegree= Q.natDegree :=natDegree_map_eq_of_injective τ.injective _
  have hvdeg (j:Fin 2) : (B.β j).natDegree≤t:=ht ▸ aSU B.β j
  have hadeg (j:Fin 2) : (A j).natDegree≤ s :=aSU A j
  have ddet:det.natDegree≤ s+t:=(natDegree_sub_le _ _).trans (max_le
    (natDegree_mul_le.trans (Nat.add_le_add (hadeg 0) (hvdeg 1)))
    (natDegree_mul_le.trans (Nat.add_le_add (hadeg 1) (hvdeg 0))))
  refine ⟨⟨denom,mul_ne_zero (mul_ne_zero B.a_ne ((zeI τ.injective).mpr B.b_ne)) hnp,
    ?_,num,?_,?_⟩⟩
  · calc
      denom.natDegree≤B.a.natDegree+b.natDegree+det.natDegree :=
        natDegree_mul_le.trans (zlr natDegree_mul_le _)
      _≤2*D.height:= by omega
  · intro j
    apply degree_le_natDegree.trans_lt
    exact_mod_cast (show (num j).natDegree<131072+2*D.height from by
      apply (natDegree_sub_le _ _).trans_lt
      apply max_lt
      · have :=hvdeg j
        exact (natDegree_mul_le.trans (zlr natDegree_mul_le _)).trans_lt (by omega)
      · have :=hadeg j
        exact (natDegree_mul_le.trans (zlr natDegree_mul_le _)).trans_lt (by omega))
  · intro i hi j
    fin_cases j
    · change denom.eval (node i)*u 0 i=(num 0).eval (node i)
      simp only [denom,num,det,eval_mul,eval_sub,heP i hi,heQ' i hi,w]
      ring
    · change denom.eval (node i)*u 1 i=(num 1).eval (node i)
      simp only [denom,num,det,eval_mul,eval_sub,heP i hi,heQ' i hi,w]
      ring
end
end P6_3
end
section
set_option autoImplicit true
namespace P6_3
open P6
open Rv (Bank)
open scoped BigOperators
open private cV3 from ProximityPrize.SubmissionLower.AY
open private aJH cEs from ProximityPrize.SubmissionLower.B3
private theorem dim_rows (d b s t:ℕ) (rows :Fin (b+1)→ℕ)
    (hr : ∀ i:Fin (b+1),(∑ j∈Finset.range (b+1 - i.val),
      (d+1 - 131071*(i.val+j))*(s+1 - i.val)*(t+1 - j))=rows i) :
    BN.acN d b s t = ∑ i,rows i :=
  aJH _ rows hr
private theorem gtd (aV:Bank) :
    BN.acN EJ 5 aV.first aV.second=0x760c3462 := by
  cases aV
  · refine (dim_rows _ _ _ _
      ![0x3075beef,0x20a94cf8,0x1437ae0e,0xaf3cfbc,78159761,18418464] ?_).trans ?_
    · intro i; fin_cases i <;> decide
    · decide
  · refine (dim_rows _ _ _ _
      ![0x3119a870,0x20b7f037,0x1401d340,0xab23f22,75243896,17459169] ?_).trans ?_
    · intro i; fin_cases i <;> decide
    · decide
private theorem eEg (aV:Bank) :
    BN.acN 563858 4 (aV.first - 1) (aV.second - 1)=0x3b27d226:= by
  cases aV
  · refine (dim_rows _ _ _ _
      ![0x1c89c044,0x11535390,0x911ba1c,60081094,10764400] ?_).trans ?_
    · intro i; fin_cases i <;> decide
    · decide
  · refine (dim_rows _ _ _ _
      ![0x1cd7ddd8,0x114af320,0x8ee4adc,58307830,10289500] ?_).trans ?_
    · intro i; fin_cases i <;> decide
    · decide
private theorem corner_surplus (aV:Bank) :
    BN.acN EJ 5 aV.first aV.second -
        BN.acN 563858 4 (aV.first - 1) (aV.second - 1) =
      blockLength*3765+1073724 := by
  rw [gtd,eEg]
  decide
theorem bVn (aV:Bank) (n h:ℕ) (hn:n≤blockLength) (hh:24378≤h) :
    aPB aV n h:= by
  let s :=aV.first - 1
  let t:=aV.second - 1
  have hm:BN.acN (EJ-(k - 1) - h) 4 s t ≤
      BN.acN 563858 4 s t:= by
    have hcut:EJ-(k - 1) - 24378=563858:= by decide
    rw [← hcut]
    unfold BN.acN
    apply zQk
    intro i _
    apply zQk
    intro j _
    exact ztf _ (ztf _
      (Nat.sub_le_sub_right (zlr (zTu hh _) _) _))
  unfold aPB
  rw [cV3]
  calc
    n*3765≤blockLength*3765:=ztf _ hn
    _<BN.acN EJ 5 aV.first aV.second - BN.acN 563858 4 s t:= by
      change _<BN.acN EJ 5 aV.first aV.second -
        BN.acN 563858 4 (aV.first - 1) (aV.second - 1)
      rw [corner_surplus]
      exact Nat.lt_add_of_pos_right (by decide)
    _≤_:=zTu hm _
theorem fVw:aPP=0x26edb1891b20706:= by
  unfold aPP arz
  exact cEs 0x147ffafff86 48756 210 0x26edb1891b20706
    (by decide) (by decide) (by decide) (by decide)
theorem bank_price_exact (aV:Bank) :
    aPP+aV.b5A=match aV with
      | .st=>0x26edb2100b20730
      | .ts=>0x26edb227db20730:= by
  rw [fVw]
  cases aV <;> decide
theorem dyt (aV:Bank) :aPP+aV.b5A≤0x26edb227db20730:= by
  rw [bank_price_exact]
  cases aV <;> decide
end P6_3
end
section
set_option autoImplicit true
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P6_3
noncomputable section
open P6 Polynomial gR
open Rv (lK)
open private column bC7 bcH bcI bGK bOU bOV outputs bN1 bJJ bLh from ProximityPrize.SubmissionLower.B3
private theorem azo {u T R D} (B:KJ u T R D) :
    JO B.a B.β=column p (afT B) := by
  rw [bOU]
  exact (bGK p B.a B.β).trans (congrArg (column p)
    (show (fun j=>B.a*(B.β j).map twist)=afT B by rfl))
private theorem az7 {u T R D} (B:KJ u T R D) :
    J9 B.b B.α=column 1 (aeb B) := by
  simp only [J9,aeb,column,jH,seed,zNl,Polynomial.map_neg,pow_one]
  ring
theorem cbU {u:e9} {T:qo u} {R:Relation T}
    {D:Reduction u T R} (B:KJ u T R D) :
    Nonempty (lK u (pJ R) D.height (afT B) (aeb B)) := by
  let U:=afT B
  let V:=aeb B
  have amp_ne (v :Fin 2→K[X]) (hv :IsCoprime (v 0) (v 1)) : ∃ j,v j≠0:= by
    by_contra! hz
    obtain ⟨a,b,hab⟩:=hv
    simp [hz] at hab
  obtain ⟨l,hl⟩:=amp_ne B.β B.β_primitive
  obtain ⟨j,hj⟩:=amp_ne B.α B.α_primitive
  have hU : ∃ l,U l≠0 :=
    ⟨l,mul_ne_zero B.a_ne ((zeI twist.injective).mpr hl)⟩
  have hV : ∃ j,V j≠0:=⟨j,neg_ne_zero.mpr (mul_ne_zero B.b_ne hj)⟩
  have hu:uO (U 0) (U 1)≤D.height:= by
    unfold uO
    apply max_le
    all_goals
      apply natDegree_mul_le.trans
      apply le_trans _ B.first_degree
      apply z3b
      rw [natDegree_map_eq_of_injective twist.injective]
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hv :uO (V 0) (V 1)≤D.height:= by
    unfold uO
    apply max_le
    all_goals
      simp only [V,aeb,natDegree_neg]
      apply natDegree_mul_le.trans
      apply le_trans _ B.second_degree
      apply z3b
    · exact le_max_left _ _
    · exact le_max_right _ _
  let φ:=algebraMap K[X] kB
  have hinj:zq4 φ:=zxb K[X] kB
  have hd (P:nC) : (sZ P).natDegree=P.natDegree :=natDegree_map_eq_of_injective hinj _
  have hn {P:nC} (hp:P≠0) :sZ P≠0:=(zeI hinj).mpr hp
  have hdir :=B.same_direction
  rw [Z4,azo,az7] at hdir
  have he :=congrArg (Polynomial.map φ) hdir
  simp only [zNl] at he
  have hdom:=max_le_max (bcH p U) (bcH 1 V)
  obtain ⟨htight,hcp⟩:=bOV (sZ D.U) (sZ D.V)
    (sZ (column p U)) (sZ (column 1 V))
    (hn D.U_ne) (hn D.V_ne) (hn (bC7 (by decide :p≠0) hU)) D.coprime he
    (by simp only [hd,D.max_degree]; exact hdom.trans (max_le hu hv))
  simp only [hd,D.max_degree] at htight
  refine ⟨⟨outputs p B.output,hU,hV,?_,?_,?_,?_⟩⟩
  · exact le_antisymm (max_le hu hv) (htight ▸ hdom)
  · intro f hfU hfV
    have hunit :=hcp.isUnit_of_dvd'
      ((mapRingHom φ).map_dvd (bcI p U f hfU))
      ((mapRingHom φ).map_dvd (bcI 1 V f hfV))
    apply isUnit_iff_degree_eq_zero.mpr
    change IsUnit ((f.map Polynomial.C).map φ) at hunit
    simpa only [degree_map_eq_of_injective hinj,
      degree_map_eq_of_injective zmy] using isUnit_iff_degree_eq_zero.mp hunit
  · intro j l
    apply degree_le_natDegree.trans_lt
    have ht:B.output.natDegree<P0.k+D.height:= by
      by_cases hz :B.output=0
      · simp [hz]
      · exact (natDegree_lt_iff_degree_lt hz).mpr B.output_degree
    exact_mod_cast (bN1 B.output _).trans_lt ht
  · apply bJJ p (by decide) u (pJ R) U V B.output
    have h:=B.nodes
    rwa [bLh,azo,az7] at h
end
end P6_3
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace P6_3_1
noncomputable section
open MvPolynomial wT
open aez (awZ GA)
open Rv (Bank)
open P6_3 (EJ)
open bjY (akW)
open private aaZ IY aIw from ProximityPrize.SubmissionLower.AY
open private aHJ from ProximityPrize.SubmissionLower.B3
abbrev Source (F:Type*) [Field F] (aV:Rv.Bank) :=
  filtered (F:=F) (vO 131071) (A6 EJ 5 aV.first aV.second)
variable {F:Type*} [Field F] {N :ℕ} {L:MvPolynomial (Fin 5) F}
variable (aV:Rv.Bank) (C:awZ N L) {h:ℕ}
    (hdeg : ∀ j,L.weightedTotalDegree (vO 131071 j)=GA h j)
private def nodeMap (i:Fin N) :Source F aV →ₗ[F] IY aV C hdeg i :=
  (zWl (aaZ aV C hdeg i)).mkQ.comp
    (a8H EJ 131071 5 aV.first aV.second 3 (C.x i) (C.first i) (C.firstSlope i)
      (C.second i) (C.secondSlope i))
include hdeg in
theorem bKY (hL:L≠0) (hcapacity :131071+h≤EJ)
    (hs :P6_3.aPB aV N h) :
    ∃ G:Source F aV,¬ L∣G.val ∧ ∀ i,∃ R:akW F aV,
      C.ic i G.val - C.ic i L*R.val∈restrictWeightedOrder oH 4 := by
  have hfit : ∀ j,GA h j≤A6 EJ 5 aV.first aV.second j:= by
    intro j
    cases aV <;> fin_cases j <;> simp [GA,A6,Rv.Bank.first,Rv.Bank.second] <;> omega
  have hshift: (fun j=>A6 EJ 5 aV.first aV.second j-GA h j) =
      A6 (EJ - 131071 - h) 4 (aV.first - 1) (aV.second - 1) := by
    funext j
    fin_cases j <;> simp [A6,GA,Nat.sub_sub]
    omega
  let mult:=aNQ (vO 131071) (A6 EJ 5 aV.first aV.second)
    (GA h) L hL hdeg hfit
  have hmult:zsE F (zWl mult) =
      V (EJ - 131071 - h) 131071 4 (aV.first - 1) (aV.second - 1) := by
    rw [LinearMap.finrank_range_of_inj (a3Z _ _ _ L hL hdeg hfit),
      hshift,awB]
  let (i:Fin N) :Module.Free F (IY aV C hdeg i) :=Module.Free.of_divisionRing F _
  let:Module F (∀ i:Fin N,IY aV C hdeg i) :=Pi.module _ _ _
  have hlocal:zsE F (∀ i:Fin N,IY aV C hdeg i) =
      N*(J 4 aV.first aV.second-J 3 (aV.first - 1) (aV.second - 1)) := by
    rw [Module.finrank_pi_fintype]
    simp only [aIw aV C hdeg,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have hdim:zsE F (∀ i:Fin N,IY aV C hdeg i) +
      zsE F (zWl mult)<zsE F (Source F aV) := by
    rw [hlocal,hmult,awB]
    change N*(J 4 aV.first aV.second-J 3 (aV.first - 1) (aV.second - 1)) <
      V EJ 131071 5 aV.first aV.second -
        V (EJ - 131071 - h) 131071 4 (aV.first - 1) (aV.second - 1) at hs
    omega
  obtain ⟨G,hG,hnot⟩:=aHJ (G := ∀ i:Fin N,IY aV C hdeg i)
    (LinearMap.pi (nodeMap aV C hdeg)) (zWl mult) hdim
  refine ⟨G,(a5K _ _ _ L hL hdeg hfit G).not.mp hnot,?_⟩
  intro i
  have hi:nodeMap aV C hdeg i G=0:=congrFun hG i
  obtain ⟨R,hR⟩:=(Submodule.Quotient.mk_eq_zero _).mp hi
  refine ⟨R,(weightedTruncation_eq_zero_iff _ _ _).mp ?_⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hR).symm
end
end P6_3_1
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace P6_3_2
noncomputable section
open P6 Polynomial MvPolynomial ProximityPrize.Benchmark
open Rv (an0)
open P6_3 (arz)
open agK (ko point bxi)
abbrev UJ (u:e9) (Γ:zJe K) := ∀ γ∈Γ,B5 u γ
structure blb {u:e9} {Γ:zJe K} (F:UJ u Γ) where
  equation :I→ko
  degree : ∀ i,(equation i).totalDegree≤an0
  agrees : ∀ γ (hγ:γ∈Γ) i,
    zY9 (point γ (F γ hγ).decoder) (equation i)=0 ↔
      (F γ hγ).decoder.eval (node i)=u 0 i+γ*u 1 i
private theorem cby {u:e9} (Γ:zJe K) (F:UJ u Γ)
    (P Q:K[X]) (hP:P.degree<131072) (hQ:Q.degree<131072)
    (hpencil : ∀ γ (hγ:γ∈Γ),(F γ hγ).decoder=P+Polynomial.C γ*Q) :
    Γ.card≤t+1 := by
  classical
  rcases Γ.eq_empty_or_nonempty with rfl | ⟨r,hr⟩
  · simp
  let S:=(F r hr).support
  let mismatch (i:I) :=P.eval (node i)≠u 0 i∨Q.eval (node i)≠u 1 i
  have lg {γ:K} (hγ:γ∈Γ) {i:I} (hi:i∈(F γ hγ).support) :
      P.eval (node i)+γ*Q.eval (node i)=u 0 i+γ*u 1 i:= by
    simpa only [hpencil γ hγ,zvF,zbr,zFf]
      using (F γ hγ).lg i hi
  have unique {γ δ:K} (hγ:γ∈Γ) (hδ:δ∈Γ) {i:I}
      (hi:i∈(F γ hγ).support) (hj:i∈(F δ hδ).support) (hm:mismatch i) :
      γ=δ:= by
    by_contra hne
    have hγi:=lg hγ hi
    have hδi:=lg hδ hj
    have h:=show (γ-δ)*(Q.eval (node i) - u 1 i)=0 by
      linear_combination hγi - hδi
    have he :=sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne))
    rw [he,add_right_cancel_iff] at hγi
    exact hm.elim (fun hbad=>hbad hγi) (fun hbad=>hbad he)
  have witness (γ : ↥(Γ.erase r)) :
      ∃ i∈(F γ.val (Finset.mem_erase.mp γ.property).2).support,mismatch i:= by
    let M:=F γ.val (Finset.mem_erase.mp γ.property).2
    by_contra hw
    apply M.nonjoint
    refine ⟨⟨P,hP,?_⟩,⟨Q,hQ,?_⟩⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i,hi,Or.inl hn⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i,hi,Or.inr hn⟩
  choose index hindex hmismatch using witness
  let f : ↥(Γ.erase r) → ↥((Finset.univ :zJe I) \ S) := fun γ =>
    ⟨index γ,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hi =>
      (Finset.mem_erase.mp γ.property).1
        (unique (Finset.mem_erase.mp γ.property).2 hr (hindex γ) hi (hmismatch γ))⟩⟩
  have hf :zq4 f := by
    intro γ δ h
    have he :index γ=index δ:=congrArg Subtype.val h
    have hδ:=hindex δ
    rw [← he] at hδ
    exact Subtype.ext (unique (Finset.mem_erase.mp γ.property).2
      (Finset.mem_erase.mp δ.property).2 (hindex γ) hδ (hmismatch γ))
  have hcard:=Finset.card_le_card_of_injective hf
  have he :=Finset.card_erase_add_one hr
  have hS:179827≤S.card:=(F r hr).dw
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
    IRSProfile.card_index] at hcard
  change Γ.card≤82318
  omega
private theorem cbA {u:e9} {Γ:zJe K} {F:UJ u Γ}
    (C:blb F) (J:Ideal ko) (W:zJe K) (hW:W⊆Γ)
    (hzero : ∀ γ (hγ:γ∈W),point γ (F γ (hW hγ)).decoder∈zeroLocus kB J)
    (hpersistent:131072 ≤ {i | C.equation i∈J}.ncard) :
    W.card≤t+1 := by
  classical
  let keep:=Finset.univ.filter fun i=>C.equation i∈J
  have hk :131072≤keep.card:= by
    rw [← zik]
    exact hpersistent.trans_eq (congrArg Set.ncard (by ext i; simp [keep]))
  obtain ⟨S,hS,hcard⟩:=Finset.exists_subset_card_eq hk
  let P:=Lagrange.interpolate S node (u 0)
  let Q:=Lagrange.interpolate S node (u 1)
  have hinj:Set.InjOn node (S:Set I) :=node.injective.injOn
  have hP:P.degree<(131072 :ℕ) := by
    simpa only [P,hcard] using Lagrange.degree_interpolate_lt (u 0) hinj
  have hQ:Q.degree<(131072 :ℕ) := by
    simpa only [Q,hcard] using Lagrange.degree_interpolate_lt (u 1) hinj
  apply cby W (fun γ hγ=>F γ (hW hγ)) P Q hP hQ
  intro γ hγ
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hinj
  · rw [hcard]
    exact (F γ (hW hγ)).degree
  · rw [hcard]
    have hm: (Polynomial.C γ*Q).degree≤Q.degree := by
      refine (Polynomial.degree_mul_le _ _).trans ?_
      simpa only [zero_add] using add_le_add_left (Polynomial.degree_C_le (a :=γ)) Q.degree
    exact (Polynomial.degree_add_le _ _).trans_lt (max_lt hP (hm.trans_lt hQ))
  · intro i hi
    have hcut:=(Finset.mem_filter.mp (hS hi)).2
    have hz :=hzero γ hγ _ hcut
    rw [zvF,zbr,zFf]
    exact (C.agrees γ (hW hγ) i).mp hz |>.trans (by
      rw [Lagrange.eval_interpolate_at_node _ hinj hi,Lagrange.eval_interpolate_at_node _ hinj hi])
private theorem dg7: ((t+1 :ℕ) :ℚ)≤arz := by
  change ((82318:ℕ) :ℚ)≤((0x147ffafff86:ℕ) :ℚ)/((48756:ℕ) :ℚ)
  apply (le_div_iff₀ (by positivity)).mpr
  exact_mod_cast (show (82318:ℕ)*48756≤0x147ffafff86 by decide)
private theorem eE2 (m:ℕ) (hm:m<131072) :
    (((Fintype.card I - m)*an0:ℕ) :ℚ) ≤
      arz*((dw - m:ℕ) :ℚ) := by
  rw [IRSProfile.card_index]
  change (((262144 - m)*10747782 :ℕ) :ℚ) ≤
    ((0x147ffafff86:ℕ) :ℚ)/48756*((179827 - m:ℕ) :ℚ)
  rw [div_mul_eq_mul_div,le_div_iff₀ (by positivity)]
  exact_mod_cast (show (262144 - m)*10747782*48756 ≤
    0x147ffafff86*(179827 - m) by omega)
theorem cIr {u:e9} {Γ:zJe K} (F:UJ u Γ) (C:blb F)
    (g s :ko) (hg:g≠0) (hdeg:g.totalDegree≤42)
    (hroot : ∀ γ (hγ:γ∈Γ),zY9 (point γ (F γ hγ).decoder) g=0 ∧
      zY9 (point γ (F γ hγ).decoder) s≠0) :
    (Γ.card:ℚ)≤42*arz^2 := by
  classical
  let x :Γ→(Fin 3→kB) := fun γ=>point γ (F γ γ.property).decoder
  have hinj:zq4 x := by
    intro γ δ h
    apply Subtype.ext
    apply zmy
    apply zxb K[X] kB
    exact congrFun h 1
  let S:=Γ.attach.image x
  have hcard:S.card=Γ.card:= by
    simp only [S,ze7 _ hinj,Finset.card_attach]
  rw [← hcard]
  refine bxi g s hg C.equation (L:=131072) (A:=dw)
    (by decide) hdeg C.degree ((by norm_num : (1 :ℚ)≤((t+1 :ℕ) :ℚ)).trans dg7)
    eE2 S
    (fun y hy => ?_) (fun y hy => ?_) (fun J hJ => ?_)
  · obtain ⟨γ,-,rfl⟩:=Finset.mem_image.mp hy
    exact hroot γ γ.property
  · obtain ⟨γ,-,rfl⟩:=Finset.mem_image.mp hy
    let M:=F γ γ.property
    have hsub: (M.support :Set I) ⊆ {i | aeval (x γ) (C.equation i)=0} :=
      fun i hi=>(C.agrees γ γ.property i).mpr (M.lg i hi)
    exact M.dw.trans (by simpa only [zik] using Set.ncard_le_ncard hsub)
  · let W:=Γ.attach.filter fun γ=>x γ∈zeroLocus kB J
    let V:=W.image (fun γ:Γ=>(γ:K))
    have hV:V⊆Γ:= fun γ hγ=> by
      obtain ⟨δ,-,rfl⟩:=Finset.mem_image.mp hγ
      exact δ.property
    have hV0 : ∀ γ (hγ:γ∈V),point γ (F γ (hV hγ)).decoder∈zeroLocus kB J:= by
      intro γ hγ
      obtain ⟨δ,hδ,rfl⟩:=Finset.mem_image.mp hγ
      exact (Finset.mem_filter.mp hδ).2
    have hcount:=cbA C J V hV hV0 hJ
    have hW:W.card=V.card:=(ze7 W Subtype.val_injective).symm
    have he : (S:Set (Fin 3→kB))∩zeroLocus kB J=(W.image x :zJe _) := by
      ext y
      simp only [S,W,Set.mem_inter_iff,Finset.mem_coe,Finset.mem_filter,Finset.mem_image]
      constructor
      · rintro ⟨⟨γ,hγ,rfl⟩,h⟩
        exact ⟨γ,⟨hγ,h⟩,rfl⟩
      · rintro ⟨γ,⟨hγ,h⟩,rfl⟩
        exact ⟨⟨γ,hγ,rfl⟩,h⟩
    rw [he,zik,ze7 _ hinj,hW]
    exact (by exact_mod_cast hcount: (V.card:ℚ)≤((t+1 :ℕ) :ℚ)).trans dg7
end
end P6_3_2
end
