import ProximityPrize.SubmissionLower.ZFZJbJc
import ProximityPrize.SubmissionLower.Z9wruub
import ProximityPrize.SubmissionLower.P6Split
set_option Elab.async false
open _root_ renaming Finset → zJe, Finset.card_image_of_injOn → zaG, Fintype.card_fin → zgY, Function.Injective → zq4, IsFractionRing.injective → zxb, LinearMap.range → zWl, Module.finrank → zsE, MvPolynomial → z3y, MvPolynomial.X → z9v, MvPolynomial.eval → zY9, Nat.add_le_add_left → z3b, Nat.mul_le_mul_left → zBI, Polynomial → zM1, Polynomial.C → z1z, Polynomial.eval_C → zFf, Polynomial.eval_add → zvF, Polynomial.eval_map_apply → zdm, Polynomial.eval_mul → zbr, Set.ncard_coe_finset → zik
section
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxHeartbeats 900000
namespace P6_4
open P6 Finset
open wT (V J)
open private count cV bTL c6V from ProximityPrize.SubmissionLower.CQ
open private b0X b0K cWi cV5 b0Z b0Q cWk cWb b0V b0R cWg cWc b0W b0T cWh cWe bo6 b0P b6U cWa b0Y b0N cWj cV8 bo5 b0M b6T cV7 b0L cV6 from ProximityPrize.SubmissionLower.A
open private b0U cWf b0S cWd b0O cV9 from ProximityPrize.SubmissionLower.B7
private theorem aJK (h H e N lo s t ds dt c g c' g' j:ℕ)
    (hlo:lo≤h) (hmax :h≤33561) (hH :H+e=h) (hN :N+e=262144)
    (hc:count 5 s t=c) (hg:cV 5 s t=g)
    (hc' : count 4 (s-ds) (t-dt)=c') (hg' : cV 4 (s-ds) (t-dt)=g')
    (hj:J 4 s t - J 3 (s-ds) (t-dt)=j) (hgain:c' ≤ j)
    (hmargin:262144*j+(588237-lo)*c' + 131071*g <
      719308*c+131071*g') :
    N*(J 4 s t - J 3 (s-ds) (t-dt))+V (719307 - 131071 - H) 131071 4 (s-ds) (t-dt)
      < V 719307 131071 5 s t:= by
  have hv :=bTL 719307 131071 5 s t (by decide)
  have hv' := bTL (719307 - 131071 - H) 131071 4 (s-ds) (t-dt) (by omega)
  rw [hc,hg] at hv
  rw [hc',hg'] at hv'
  have hw:719307 - 131071 - H+1≤(588237-lo)+e := by omega
  have hm:N*j+(719307 - 131071 - H+1)*c' ≤
      262144*j+(588237-lo)*c' := by
    calc
      _≤N*j+((588237-lo)+e)*c' :=
        z3b (Nat.mul_le_mul_right _ hw) _
      _=N*j+e*c' + (588237-lo)*c' := by ring
      _≤N*j+e*j+(588237-lo)*c' :=
        Nat.add_le_add_right (z3b (zBI _ hgain) _) _
      _ = _:= by rw [← Nat.add_mul,hN]
  rw [hj]
  omega
theorem bVn (b:Bank) (h H e N :ℕ) (hlo:bes b≤h)
    (hmax :h≤DY) (hH :H+e=h) (hN :N+e=blockLength) :
    N*(J 4 b.s b.t - J 3 (b.s - b.dS) (b.t - b.dT)) +
      V (apL - 131071 - H) 131071 4 (b.s - b.dS) (b.t - b.dT) <
      V apL 131071 5 b.s b.t:= by
  cases b with
  | NK =>
    exact aJK h H e N 24378 16 10 1 2 2982 9324 1675 4189 2010
      hlo hmax hH hN b0X.1 b0X.2 b0K.1 b0K.2
      (by rw [cWi,cV5]) (by decide) (by decide)
  | Jj =>
    exact aJK h H e N 32504 8 7 1 3 952 2814 355 809 855
      hlo hmax hH hN b0Z.1 b0Z.2 b0Q.1 b0Q.2
      (by rw [cWk,cWb]) (by decide) (by decide)
  | Mh =>
    exact aJK h H e N 24378 10 16 2 1 2982 9324 1675 4189 2010
      hlo hmax hH hN b0V.1 b0V.2 b0R.1 b0R.2
      (by rw [cWg,cWc]) (by decide) (by decide)
  | Mi =>
    exact aJK h H e N 24378 11 10 2 2 2002 6174 985 2419 1495
      hlo hmax hH hN b0W.1 b0W.2 b0T.1 b0T.2
      (by rw [cWh,cWe]) (by decide) (by decide)
  | w22Swapped =>
    exact aJK h H e N 24378 10 11 2 2 2002 6174 985 2419 1495
      hlo hmax hH hN b0U.1 b0U.2 b0S.1 b0S.2
      (by rw [cWf,cWd]) (by decide) (by decide)
  | Sb =>
    exact aJK h H e N 32504 8 6 2 3 798 2324 215 459 800
      hlo hmax hH hN bo6.1 bo6.2 b0P.1 b0P.2
      (by rw [b6U,cWa]) (by decide) (by decide)
  | YD =>
    exact aJK h H e N 32504 7 8 3 1 952 2814 355 809 855
      hlo hmax hH hN b0Y.1 b0Y.2 b0N.1 b0N.2
      (by rw [cWj,cV8]) (by decide) (by decide)
  | YJ =>
    exact aJK h H e N 32504 6 8 3 2 798 2324 215 459 800
      hlo hmax hH hN bo5.1 bo5.2 b0M.1 b0M.2
      (by rw [b6T,cV7]) (by decide) (by decide)
  | Y1 =>
    exact aJK h H e N 32504 6 8 3 3 798 2324 175 364 835
      hlo hmax hH hN bo5.1 bo5.2 b0L.1 b0L.2
      (by rw [b6T,cV6]) (by decide) (by decide)
  | w33Swapped =>
    exact aJK h H e N 32504 8 6 3 3 798 2324 175 364 835
      hlo hmax hH hN bo6.1 bo6.2 b0O.1 b0O.2
      (by rw [b6U,cV9]) (by decide) (by decide)
local notation "oP" e "," m "," z=>c6V e m z normalCap 131073 48756 (by decide) (by decide)
theorem dyr (b:Bank) : (b.biR:ℚ)+5*bcp b≤normalCap:= by
  cases b with
  | NK=>exact oP 36,9174936,0x771000024
  | Jj=>exact oP 30,7602090,0x86f00001e
  | Mh=>exact oP 36,9174936,0x7f0000024
  | Mi=>exact oP 36,9174936,0x771000024
  | w22Swapped=>exact oP 36,9174936,0x7f0000024
  | Sb=>exact oP 34,8650654,0x7f0000022
  | YD =>exact oP 30,7602090,0x3f800001e
  | YJ=>exact oP 34,8650654,0x673000022
  | Y1=>exact oP 39,9961359,0x8ee000027
  | w33Swapped=>exact oP 39,9961359,0x7f0000027
theorem bank_rate_ge (b:Bank) : (262144 :ℚ)≤ chartRate b:= by
  have hm: (262144 :ℕ)≤b.M:= by cases b <;> decide
  have hr : (1 :ℚ)≤131073/48756:= by
    apply (le_div_iff₀ (by positivity : (0:ℚ)<48756)).mpr
    rw [one_mul]
    exact_mod_cast (show (48756:ℕ)≤131073 by decide)
  exact (by exact_mod_cast hm: (262144 :ℚ)≤b.M).trans
    (by simpa only [one_mul,chartRate] using
      mul_le_mul_of_nonneg_right hr (by positivity : (0:ℚ)≤b.M))
end P6_4
end
section
set_option autoImplicit true
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace P6_4
noncomputable section
open P6 MvPolynomial
open aiH (bk6 aNg cNI)
open private exceptions aE5 dmm bOd cql cqk from ProximityPrize.SubmissionLower.L
open private aMJ aaD bbL numerator af0 denominator aUo c3O c1S bc6 Uj b9E cKu from ProximityPrize.SubmissionLower.A1
theorem assign {u:e9} {deleted:zJe I} {Γ:zJe K}
    {F:UJ u deleted Γ} {b:Bank} (A:biX F b) :
    ∃ (exceptional:zJe K) (charts :Fin 5→zJe K),
      exceptional.card≤b.biR ∧
      (∀ γ∈Γ,γ∈exceptional ∨ ∃ j,γ∈charts j) ∧
      ∀ j,∃ hsub:charts j⊆Γ,∀ γ (hγ:γ∈charts j),
        bk6 (aNg A.Q j) (F.mark γ (hsub hγ)).decoder γ (γ^p) := by
  classical
  obtain ⟨exceptional,hfee,hex⟩:=exceptions A.Q A.nonzero p b.a b.b (by decide)
    (by cases b <;> decide) A.degreeS A.degreeT Γ
  have hassign (γ:K) (hγ:γ∈Γ) (hn:γ∉exceptional) :
      ∃ j:Fin 5,bk6 (aNg A.Q j) (F.mark γ hγ).decoder γ (γ^p) := by
    let f :=aE5 A.Q γ (γ^p)
    have hdeg:f.natDegree≤5 :=
      (Polynomial.natDegree_map_le).trans ((dmm A.Q).le.trans A.degreeY)
    have hroot :f.IsRoot (F.mark γ hγ).decoder :=
      (bOd A.Q _ γ (γ^p)).trans (A.aiq γ hγ)
    obtain ⟨j,hj,hz,hnz⟩:=cNI p 5 f
      (hex γ hγ hn) hdeg (by decide) _ hroot
    refine ⟨⟨j,hj⟩,?_,?_⟩
    · rw [← bOd,cql]
      exact hz
    · rw [← bOd,cqk,cql]
      exact hnz
  let charts (j:Fin 5) :=Γ.filter fun γ =>
    ∃ hγ:γ∈Γ,bk6 (aNg A.Q j) (F.mark γ hγ).decoder γ (γ^p)
  refine ⟨exceptional,charts,hfee,?_,?_⟩
  · intro γ hγ
    by_cases he :γ∈exceptional
    · exact Or.inl he
    · obtain ⟨j,hj⟩:=hassign γ hγ he
      exact Or.inr ⟨j,Finset.mem_filter.mpr ⟨hγ,hγ,hj⟩⟩
  · intro j
    refine ⟨fun _ hγ=>(Finset.mem_filter.mp hγ).1,?_⟩
    intro γ hγ
    obtain ⟨_,h⟩:=(Finset.mem_filter.mp hγ).2
    exact h
private theorem dDK
    {u:e9} {deleted:zJe I} (P:N7 deleted)
    {Γ:zJe K} (F:UJ u deleted Γ) (b:Bank)
    (Λ:zJe K) (hsub:Λ⊆Γ) (hne :Λ.Nonempty)
    (G:z3y (Fin 4) K) (hG:G.weightedTotalDegree LV≤b.E)
    (hroot : ∀ γ (hγ:γ∈Λ),
      bk6 G (F.mark γ (hsub hγ)).decoder γ (γ^p)) :
    Nonempty (TaylorChart u P F b Λ) := by
  classical
  let point (γ:K) :Fin 3→kB:=if h:γ∈Λ then
    aMJ (F.mark γ (hsub h)).decoder γ (γ^p) else fun _=>0
  have hpnt (γ:K) (hγ:γ∈Λ) :
      point γ=aMJ (F.mark γ (hsub hγ)).decoder γ (γ^p) := by
    simp [point,hγ]
  refine ⟨{
    subset :=hsub
    equation :=aaD G
    equation_ne := ?_
    equation_degree :=(bbL G).trans hG
    numerator :=numerator G 131071
    af0:=af0 _ _
    denominator :=denominator G 131071
    cut_degree := ?_
    point :=point
    slope := fun γ hγ=> by rw [hpnt γ hγ]; rfl
    on_equation := fun γ hγ=> by rw [hpnt γ hγ,aUo,(hroot γ hγ).1,map_zero]
    regular := ?_
    reconstruction := ?_ }⟩
  · obtain ⟨γ,hγ⟩:=hne
    have hn:=(hroot γ hγ).2
    intro hz
    apply hn
    apply (zxb (zM1 K) kB)
    rw [map_zero,← aUo,← c3O,hz,map_zero,map_zero]
  · intro i
    unfold D4
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact c1S cxL.proof G 131071 b.E (by cases b <;> decide) hG _
    · apply (totalDegree_mul _ _).trans
      have ha : (C (σ:=Fin 3) (algebraMap K kB (u 0 (P.index i))) +
          z9v 1*C (algebraMap K kB (u 1 (P.index i)))).totalDegree≤1 := by
        exact (totalDegree_add _ _).trans (max_le (by simp)
          ((totalDegree_mul _ _).trans (by simp)))
      exact Nat.add_le_add (bc6 G 131071 b.E hG) ha
  · intro γ hγ
    rw [hpnt γ hγ,denominator,map_pow,aUo]
    exact pow_ne_zero _ (fun h=>(hroot γ hγ).2
      ((zxb (zM1 K) kB) (h.trans (map_zero _).symm)))
  · intro γ hγ
    rw [hpnt γ hγ]
    apply Uj cxM.proof
    · exact b9E (F.mark γ (hsub hγ)).degree
    · exact (hroot γ hγ).1
    · intro n hn
      have pp:=CharP.char_is_prime_of_two_le K p (by decide)
      intro hz
      have hn' := pp.dvd_factorial.mp ((CharP.cast_eq_zero_iff K p _).mp hz)
      exact (not_lt_of_ge (hn'.trans hn)) (by decide)
theorem dIs {u:e9} {deleted:zJe I} (P:N7 deleted)
    {Γ:zJe K} {F:UJ u deleted Γ} {b:Bank} (A:biX F b) :
    ∃ (exceptional:zJe K) (charts :Fin 5→zJe K),
      exceptional.card≤b.biR ∧
      (∀ γ∈Γ,γ∈exceptional ∨ ∃ j,γ∈charts j) ∧
      ∀ j,charts j = ∅ ∨ Nonempty (TaylorChart u P F b (charts j)) := by
  obtain ⟨exceptional,charts,hfee,hcover,hcharts⟩:=assign A
  refine ⟨exceptional,charts,hfee,hcover,fun j => ?_⟩
  rcases (charts j).eq_empty_or_nonempty with he | hn
  · exact Or.inl he
  · obtain ⟨hsub,hroot⟩:=hcharts j
    exact Or.inr (dDK P F b (charts j) hsub hn (aNg A.Q j)
      ((cKu A.Q j).trans A.degreeTotal) hroot)
end
end P6_4
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
namespace P6_4
noncomputable section
open P6 MvPolynomial
open wT (vO A6 filtered Wb)
open Qo (yV YF aab graph bTn equation b1J
  aa2 bZY ayz auL bDV bpu
  bpv b7W)
open bju (interpolant Wj afY cbi cbj bZ2 bZ6 bFp b9R bs0)
open private aCW from ProximityPrize.SubmissionLower.A1
open private c1v c1l from ProximityPrize.SubmissionLower.L
open private bPb from ProximityPrize.SubmissionLower.B
open private an2 c1z from ProximityPrize.SubmissionLower.B7
private theorem c7G {u:e9} {T:qo u} {R:Relation T}
    {D:Reduction u T R} {A:ap3 R} (B:aLU D A) :
    bTM T.height B.U B.V:= by
  have loc_ne :jH (gR.mL node (pJ R))≠0 :=
    fun hz=>(gR.S8 node (pJ R)).ne_zero
      ((Polynomial.map_injective _ Polynomial.C_injective) (hz.trans (Polynomial.map_zero _).symm))
  have hU:A.U≠0:= by
    intro h
    have hg:=A.graphU
    rw [h,map_zero,D.U_factor] at hg
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr A.content_ne) (mul_ne_zero loc_ne D.U_ne) hg.symm
  have hV:A.V≠0:= by
    intro h
    have hg:=A.graphV
    rw [h,map_zero,D.V_factor] at hg
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr A.content_ne) (mul_ne_zero loc_ne D.V_ne) hg.symm
  exact ⟨(zBI _ (aCW hU B.U_dvd 3)).trans A.Ca.1,
    (zBI _ (aCW hU B.U_dvd 4)).trans A.Ca.2.1,
    (zBI _ (aCW hV B.V_dvd 3)).trans A.Ca.2.2.1,
    (zBI _ (aCW hV B.V_dvd 4)).trans A.Ca.2.2.2⟩
private theorem c7H {u:e9} {T:qo u} {R:Relation T}
    {D:Reduction u T R} {A:ap3 R} (B:aLU D A)
    (hH :T.height≤DY) :
    B.U.degreeOf 3≤2∧B.U.degreeOf 4≤3 ∧
      B.V.degreeOf 3≤3∧B.V.degreeOf 4≤2 := by
  obtain ⟨hUS,hUT,hVS,hVT⟩:=c7G B
  have hh:T.height≤33561 :=hH
  exact ⟨Nat.le_of_lt_succ (an2 _ _ 3 _ hUS (by change _<(48755-_)*3; omega)),
    Nat.le_of_lt_succ (an2 _ _ 4 _ hUT (by change 48755<(48755-_)*4; omega)),
    Nat.le_of_lt_succ (an2 _ _ 4 _ hVS (by change 48755<(48755-_)*4; omega)),
    Nat.le_of_lt_succ (an2 _ _ 3 _ hVT (by change _<(48755-_)*3; omega))⟩
private theorem c1u {u:e9} {T:qo u} {R:Relation T}
    {D:Reduction u T R} {A:ap3 R} (B:aLU D A)
    (hr :Xb D.U D.V=4) (hs :YF B.U B.V=1) (ht:aab B.U B.V=1) :
    False := by
  let f :zM1 K →ₐ[K] kB:=IsScalarTower.toAlgHom K (zM1 K) kB
  have hf :zq4 f :=zxb (zM1 K) kB
  have hold:K1.Xb D.U D.V=4 :=(aSg.bC4 D.U D.V).symm.trans hr
  have hr' : Aj.ajp K1.p D.U D.V=4 :=hold
  rw [c1l] at hr'
  exact c1v p f hf A.content B.U B.V D.U D.V A.content_ne D.U_ne
    B.U_omits B.V_omits B.graphU B.graphV hr' hs ht
private theorem drW {u:e9} {T:qo u} {R:Relation T}
    {D:Reduction u T R} {A:ap3 R} (B:aLU D A)
    (hr :Xb D.U D.V=4) (hH :T.height≤DY) :
    ∃ aV:Bank,YF B.U B.V=aV.dS∧aab B.U B.V=aV.dT ∧
      bes aV≤T.height:= by
  obtain ⟨pUS,pUT,pVS,pVT⟩:=c7G B
  obtain ⟨bUS,bUT,bVS,bVT⟩:=c7H B hH
  have hlo:24378≤T.height:= by
    by_contra! h
    have hs₁:B.U.degreeOf 3<1 :=
      an2 _ _ 1 _ pUS (by change _<(48755-_)*1; omega)
    have hs₂:B.V.degreeOf 3<2 :=
      an2 _ _ 2 _ pVS (by change 48755<(48755-_)*2; omega)
    have ht₁:B.U.degreeOf 4<2 :=
      an2 _ _ 2 _ pUT (by change 48755<(48755-_)*2; omega)
    have ht₂:B.V.degreeOf 4<1 :=
      an2 _ _ 1 _ pVT (by change _<(48755-_)*1; omega)
    exact c1u B hr (by unfold YF; omega) (by unfold aab; omega)
  have hhi (hw:YF B.U B.V=3∨aab B.U B.V=3) :32504≤T.height:= by
    by_contra! h
    have hs₁:B.U.degreeOf 3<2 :=
      an2 _ _ 2 _ pUS (by change _<(48755-_)*2; omega)
    have hs₂:B.V.degreeOf 3<3 :=
      an2 _ _ 3 _ pVS (by change 48755<(48755-_)*3; omega)
    have ht₁:B.U.degreeOf 4<3 :=
      an2 _ _ 3 _ pUT (by change 48755<(48755-_)*3; omega)
    have ht₂:B.V.degreeOf 4<2 :=
      an2 _ _ 2 _ pVT (by change _<(48755-_)*2; omega)
    unfold YF aab at hw
    omega
  have hs :YF B.U B.V=1∨YF B.U B.V=2∨YF B.U B.V=3:= by
    unfold YF
    omega
  have ht:aab B.U B.V=1∨aab B.U B.V=2∨aab B.U B.V=3:= by
    unfold aab
    omega
  rcases hs with hs | hs | hs <;> rcases ht with ht | ht | ht
  · exact (c1u B hr hs ht).elim
  · exact ⟨.NK,hs,ht,hlo⟩
  · exact ⟨.Jj,hs,ht,hhi (Or.inr ht)⟩
  · exact ⟨.Mh,hs,ht,hlo⟩
  · exact ⟨.Mi,hs,ht,hlo⟩
  · exact ⟨.Sb,hs,ht,hhi (Or.inr ht)⟩
  · exact ⟨.YD,hs,ht,hhi (Or.inl hs)⟩
  · exact ⟨.YJ,hs,ht,hhi (Or.inl hs)⟩
  · exact ⟨.Y1,hs,ht,hhi (Or.inl hs)⟩
private theorem ceU {u:e9} {T:qo u} {R:Relation T}
    (D:Reduction u T R) (e :zM1 K) :
    Aj.ad9 p u (pJ R) (z1z e*D.U)
      (z1z e*D.V) (z1z e*D.output) := by
  let G:=jH (gR.mL node (pJ R))
  have hG : ∀ i∉pJ R,G.eval (z1z (node i))≠0:= by
    intro i hi
    rw [show G=K1.jH _ from rfl,Aj.ari,Polynomial.C_ne_zero]
    exact fun hz=>hi ((gR.Principal.aVH node
      ProximityPrize.Benchmark.IRSProfile.domain.injective _ i).mp hz)
  exact @bPb u p 131072 T.height R (pJ R) G D.U D.V D.output
    hG D.U_factor D.V_factor D.output_factor e
private theorem eLX {u:e9} {T:qo u} {R:Relation T}
    {D:Reduction u T R} {A:ap3 R} (B:aLU D A)
    (hH :T.height≤DY) (P:N7 (pJ R)) :
    Nonempty (bTn u P D.height B.U B.V) := by
  let x :Fin P.N→K:=P.nodes
  let a (i:Fin P.N) :K:=u 0 (P.index i)
  let b (i:Fin P.N) :K:=u 1 (P.index i)
  let v (i:Fin P.N) :=afY (x i) (a i) (b i) (a i^p) (b i^p) B.U B.V
  let W:=interpolant x v
  have hx :zq4 x :=
    ProximityPrize.Benchmark.IRSProfile.domain.injective.comp P.index.injective
  have hnodes (i:Fin P.N) :Wj (x i) W=v i :=
    cbi x hx v (fun _=>cbj ..) i
  have hdeg (j:Fin 5) :W.degreeOf j ≤
      (P.N - 1)*(z9v 0:z3y (Fin 5) K).degreeOf j +
      (if j=3 then YF B.U B.V else if j=4 then aab B.U B.V else 0) :=
    bZ2 x hx v j _ (fun i=>bZ6 j
      (x i) (a i) (b i) (a i^p) (b i^p) B.U B.V)
  have hm:yV W:=⟨Nat.eq_zero_of_le_zero (by simpa [degreeOf_X] using hdeg 1),
    Nat.eq_zero_of_le_zero (by simpa [degreeOf_X] using hdeg 2)⟩
  have hs :W.degreeOf 3≤YF B.U B.V:= by simpa [degreeOf_X] using hdeg 3
  have ht:W.degreeOf 4≤aab B.U B.V:= by simpa [degreeOf_X] using hdeg 4
  have hbound:131072+D.height≤P.N := by
    have hh:T.height≤33561 :=hH
    have hD:=D.height_eq
    have hP:=P.size
    omega
  have hsmall:W.degreeOf 3<p:= by
    obtain ⟨huS,_,hvS,_⟩:=c7H B hH
    unfold YF at hs
    change W.degreeOf 3<2130706433
    omega
  have hdegree :=bRc.bqM p (by decide) W hm hsmall
  have hWdeg: (graph p W).natDegree<P.N := by
    rw [hdegree]
    have hh:W.degreeOf 0≤P.N - 1 := by simpa [degreeOf_X] using hdeg 0
    omega
  let G:=z1z A.content*D.output
  have hDdeg:D.output.natDegree≤131071+D.height:= by
    by_cases hz :D.output=0
    · simp [hz]
    have hd:=(Polynomial.natDegree_lt_iff_degree_lt hz).mpr D.output_degree
    change D.output.natDegree<131072+D.height at hd
    omega
  have hGdeg:G.natDegree≤131071+D.height :=
    (Polynomial.natDegree_C_mul_le A.content D.output).trans hDdeg
  have hrel :Aj.ad9 p u (pJ R) (graph p B.U) (graph p B.V) G:= by
    rw [B.graphU,B.graphV]
    exact ceU D A.content
  have heval (i:Fin P.N) : (graph p W).eval (z1z (x i))=G.eval (z1z (x i)) := by
    rw [bFp,hnodes]
    exact c1z p (P:=P) hrel i
  have hgraph:graph p W=G:= by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (Polynomial.C_injective.comp hx) heval
    rw [zgY]
    exact max_lt hWdeg (by omega)
  have hheight:W.degreeOf 0≤131071+D.height:= by
    rw [← hdegree,hgraph]
    exact hGdeg
  refine ⟨⟨W,hm,hheight,hs,ht,?_⟩⟩
  intro i
  change aa2 (x i) (a i) (b i) (a i^p) (b i^p) (B.U*z9v 1+B.V*z9v 2 - W)=0
  rw [map_sub,b9R _ _ _ _ _ _ _ B.U_omits B.V_omits,
    bs0 _ _ _ _ _ W hm,hnodes]
  exact sub_self _
theorem dPl {u:e9} {T:qo u} {R:Relation T}
    {D:Reduction u T R} {A:ap3 R} (B:aLU D A)
    (hr :Xb D.U D.V=4) (hH :T.height≤DY) (P:N7 (pJ R)) :
    ∃ b:Bank,bes b≤T.height∧Nonempty (asP u P b D.height) := by
  obtain ⟨W⟩:=eLX B hH P
  obtain ⟨aV,hs,ht,hfloor⟩:=drW B hr hH
  let L:=equation B.U B.V W.W
  have hdeg : ∀ j,L.weightedTotalDegree (vO 131071 j) =
      A6 (131071+D.height) 1 aV.dS aV.dT j:= by
    simpa only [L,equation,hs,ht] using b1J 131071 D.height B.U B.V W.W
      B.U_ne B.V_ne B.U_omits B.V_omits W.omits B.height W.height W.degreeS W.degreeT
  have hL:L≠0:= by
    intro hz
    have he :=hdeg 1
    simp [hz,A6,weightedTotalDegree] at he
  have hf :L∈filtered (vO 131071)
      (A6 (131071+D.height) 1 aV.dS aV.dT) :=
    (Wb _ _ _).mpr fun j=>(hdeg j).le
  obtain ⟨hy,hdy,hns,hds,hnt,hdt⟩:=bZY 131071 D.height aV.dS aV.dT
    B.U B.V W.W B.U_omits B.V_omits W.omits B.V_ne hf
  refine ⟨aV,hfloor,⟨{
    L:=L
    L_ne :=hL
    degrees :=hdeg
    order_one := ?_
    numerator :=ayz B.U W.W
    denominator :=auL B.V
    ayD:=bDV B.V B.V_omits B.V_ne
    linear :=bpu B.U B.V W.W B.U_omits B.V_omits W.omits
    primitive :=bpv B.U B.V W.W B.U_omits B.V_omits W.omits B.V_ne B.relPrime
    numerator_Y:=hy
    denominator_Y:=hdy
    numerator_S:=hns
    denominator_S:=hds
    numerator_T:=hnt
    denominator_T:=hdt
  }⟩⟩
  intro i
  exact b7W _ _ _ _ _ B.U B.V W.W B.relPrime
    B.U_omits B.V_omits W.omits (W.node i)
end
end P6_4
end
section
set_option autoImplicit true
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace P6_4
noncomputable section
open MvPolynomial
open P6 (DY)
open wT (V J filtered aNQ a3Z a5K vO A6 awB a8H oH)
open private aHJ from ProximityPrize.SubmissionLower.Z
abbrev Source (F:Type*) [Field F] (b:Bank) :=
  filtered (F:=F) (vO 131071) (A6 apL 5 b.s b.t)
abbrev akW := @WN.akW
variable {F:Type*} [Field F]
variable {N :ℕ} {L:z3y (Fin 5) F} {b:Bank} {H :ℕ}
  (D:WN.a9S N L b)
open private IY aaZ aIw from ProximityPrize.SubmissionLower.B7
private def nodeMap (i:Fin N) :Source F b →ₗ[F] IY D i :=
  (zWl (aaZ D i)).mkQ.comp
    (a8H apL 131071 5 b.s b.t 3 (D.x i) (D.first i) (D.firstSlope i) (D.second i) (D.secondSlope i))
private theorem exu (Q:Source F b) (i:Fin N) (hi:nodeMap D i Q=0) :
    ∃ R:akW F b,D.ic i Q.val - D.ic i L*R.val ∈
      restrictWeightedOrder oH 4 := by
  have hmem:a8H apL 131071 5 b.s b.t 3 (D.x i)
      (D.first i) (D.firstSlope i) (D.second i) (D.secondSlope i) Q ∈
      zWl (aaZ D i) :=
    (Submodule.Quotient.mk_eq_zero _).mp hi
  obtain ⟨R,hR⟩:=hmem
  refine ⟨R,(weightedTruncation_eq_zero_iff _ _ _).mp ?_⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hR).symm
theorem d4H (h e :ℕ) (hmin:bes b≤h) (hmax :h≤DY)
    (hH :H+e=h) (hN :N+e=262144)
    (hdeg : ∀ j,L.weightedTotalDegree (vO 131071 j)=b.GA H j) :
    ∃ Q:Source F b,¬ L∣Q.val ∧ ∀ i,∃ R:akW F b,
      D.ic i Q.val - D.ic i L*R.val∈restrictWeightedOrder oH 4 := by
  have hupper :H≤33561 := by
    have hh:h≤33561 :=hmax
    omega
  have hD:apL=719307:=rfl
  have hfit : ∀ i,b.GA H i≤A6 apL 5 b.s b.t i:= by
    intro i
    cases b <;> fin_cases i <;>
      simp [WN.Bank.GA,WN.Bank.s,WN.Bank.t,WN.Bank.dS,WN.Bank.dT,A6,hD] <;> omega
  have hshift: (fun i=>A6 apL 5 b.s b.t i - b.GA H i) =
      A6 (apL - 131071 - H) 4 (b.s-b.dS) (b.t-b.dT) := by
    funext i
    fin_cases i <;> simp [A6,WN.Bank.GA,hD] <;> omega
  let mult:=aNQ (vO 131071) (A6 apL 5 b.s b.t)
    (b.GA H) L D.nonzero hdeg hfit
  have hdimMult:zsE F (zWl mult) =
      V (apL - 131071 - H) 131071 4 (b.s-b.dS) (b.t-b.dT) := by
    rw [LinearMap.finrank_range_of_inj
      (a3Z _ _ _ L D.nonzero hdeg hfit),hshift,awB]
  have hdimLocal:zsE F (∀ i:Fin N,IY D i) =
      N*(J 4 b.s b.t - J 3 (b.s-b.dS) (b.t-b.dT)) := by
    letI (i:Fin N) :Module.Free F (IY D i) :=Module.Free.of_divisionRing F _
    rw [Module.finrank_pi_fintype]
    simp only [aIw D,Finset.sum_const,Finset.card_univ,zgY,smul_eq_mul]
  have hdim:zsE F (∀ i:Fin N,IY D i) +
      zsE F (zWl mult)<zsE F (Source F b) := by
    rw [hdimLocal,hdimMult,awB]
    exact bVn b h H e N hmin hmax hH hN
  letI:Module F (∀ i:Fin N,IY D i) :=Pi.module _ _ _
  obtain ⟨Q,hQ,hnot⟩:=aHJ (G := ∀ i:Fin N,IY D i)
    (LinearMap.pi (nodeMap D)) (zWl mult) hdim
  exact ⟨Q,(a5K _ _ _ L D.nonzero hdeg hfit Q).not.mp hnot,
    fun i=>exu D Q i (congrFun hQ i)⟩
end
end P6_4
end
section
set_option autoImplicit true
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace P6_4
noncomputable section
open P6 gR MvPolynomial
open wT (oH bDi boM bc5 aHG bDX aju aCK vO Wb a2W aV4 arB beB aVT Qb ME MD aP3 bNc bgg aTD xx bNb)
open private bNf from ProximityPrize.SubmissionLower.AH
variable {u:e9} {deleted:zJe I} {P:N7 deleted} {b:Bank} {H :ℕ}
    (D:asP u P b H)
open private cBm cH3 cCT from ProximityPrize.SubmissionLower.B7
theorem c74 (hH :H≤33561) (Q Q' : zM1 K)
    (hQ:Q.natDegree≤131071) (hQ' : Q'.natDegree≤131071)
    (s t:K) (S:zJe (Fin P.N)) (hS:179827≤S.card) (hc:a2W u P Q Q' s t S) :
    aeval (aju Q Q' s t) D.L=0:= by
  apply aHG S P.nodes aV4 1
  · intro i hi
    have ho:=cH3 oH (D.ic i D.L) (D.order_one i)
    have hd:=pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder z1z ho
      (bDi _ _ _ _ _ s t Q Q' (hc i hi).1 (hc i hi).2)
    change (Polynomial.X-Polynomial.C (P.nodes i))^1 ∣
      aeval (aCK (P.nodes i) (u 0 (P.index i)) (u 1 (P.index i))
        (u 0 (P.index i)^p) (u 1 (P.index i)^p) s t Q Q') (D.ic i D.L) at hd
    rwa [WN.asP.ic,boM] at hd
  · have hdeg:D.L.weightedTotalDegree (vO 131071 0)≤131071+H :=
      le_of_eq (D.degrees 0)
    have hd:=bc5 131071 (131071+H) D.L hdeg Q Q' hQ hQ' s t
    omega
theorem d4X (h:ℕ) (hmin:bes b≤h) (hmax :h≤DY)
    (hH :H+deleted.card=h) :
    ∃ G:Source K b,¬ D.L∣G.val ∧
      ∀ (Q Q' : zM1 K),Q.natDegree≤131071→Q'.natDegree≤131071 →
        ∀ (s t:K) (S:zJe (Fin P.N)),179827≤S.card→a2W u P Q Q' s t S →
          aeval (aju Q Q' s t) G.val=0:= by
  obtain ⟨G,hnot,hnode⟩:=d4H (cBm D) h deleted.card hmin hmax hH P.size D.degrees
  refine ⟨G,hnot,?_⟩
  intro Q Q' hQ hQ' s t S hS hc
  have hmax' : h≤33561 :=hmax
  have hrel :=c74 D (by omega) Q Q' hQ hQ' s t S hS hc
  apply aHG S P.nodes aV4 4
  · intro i hi
    obtain ⟨R,hR⟩:=hnode i
    exact bDX 4 _ _ _ _ _ s t Q Q' G.val D.L R.val
      (hc i hi).1 (hc i hi).2 hrel hR
  · have hd:=bc5 131071 apL G.val
      ((Wb _ _ _).mp G.property 0) Q Q' hQ hQ' s t
    change _≤719307 at hd
    omega
def gpg {u:e9} {T:qo u} {R:Relation T} (D:Reduction u T R)
    {Γ:zJe K} (hΓ:Tt u Γ) (hn : ∀ γ∈Γ,Normal u γ) :
    UJ u (pJ R) Γ where
  mark γ hγ:=Classical.choice (P6.aCl u Γ hΓ γ hγ)
  survives γ hγ i hi hid :=
    (D.deleted_error γ (hn γ hγ) _ i hid)
      ((Classical.choice (P6.aCl u Γ hΓ γ hγ)).lg i hi)
theorem a5H {u:e9} {γ:K} (M:B5 u γ) :
    M.decoder.natDegree≤131071 := by
  apply Polynomial.natDegree_le_of_degree_le
  exact Order.le_of_lt_succ (show M.decoder.degree<(131072 :ℕ) from M.degree)
theorem bYQ {u:e9} {deleted:zJe I} (P:N7 deleted)
    {γ:K} (M:B5 u γ) :
    a2W u P M.decoder (M.decoder.map twist) γ (γ^p) (arB P M.support) := by
  intro i hi
  have h:=M.lg (P.index i) ((aVT P M.support i).mp hi)
  refine ⟨h,?_⟩
  change (M.decoder.map twist).eval (node (P.index i)) =
    u 0 (P.index i)^p+γ^p*u 1 (P.index i)^p
  rw [kL.aC4 twist M.decoder _ (Native.ahU (P.index i)),h]
  simp only [map_add,map_mul,P0.twist,frobenius_def]
theorem d3X {u:e9} {deleted:zJe I} {P:N7 deleted}
    {b:Bank} {H :ℕ} (C:asP u P b H) (h:ℕ)
    (hmin:bes b≤h) (hmax :h≤DY) (hH :H+deleted.card=h)
    {Γ:zJe K} (F:UJ u deleted Γ) :Nonempty (biX F b) := by
  obtain ⟨G,hG,hgAnn⟩:=d4X C h hmin hmax hH
  let Q:=aP3 5 G.val C.numerator C.denominator
  have hne :Q≠0:=bNc apL 131071 5 b.s b.t
    G.val C.L G.property hG C.numerator C.denominator C.ayD C.linear C.primitive
  obtain ⟨hY,hS,hT⟩:=bgg apL 131071 5 b.s b.t G.val G.property
  have hy :Q.weightedTotalDegree Qb≤5:= by
    simpa [Q,aP3] using
      aTD Qb 5 5 1 1 0 (xx G.val)
        C.numerator C.denominator (by simpa using hY) C.numerator_Y C.denominator_Y (by omega)
  have hs :Q.weightedTotalDegree ME≤b.a := by
    simpa [Q,aP3,WN.Bank.a] using
      aTD ME 5 b.s 0 b.dS b.dS (xx G.val)
        C.numerator C.denominator (by simpa using hS) C.numerator_S C.denominator_S (by omega)
  have ht:Q.weightedTotalDegree MD ≤b.b:= by
    simpa [Q,aP3,WN.Bank.b] using
      aTD MD 5 b.t 1 b.dT (b.dT-1) (xx G.val)
        C.numerator C.denominator (by simpa using hT) C.numerator_T C.denominator_T (cCT b).ge
  refine ⟨⟨Q,hne,hy,hs,ht,bNf Q b.a b.b hs ht,?_⟩⟩
  intro γ hγ
  let M:=F.mark γ hγ
  let S:=arB P M.support
  have hS:179827≤S.card:= by
    rw [beB P M.support (F.survives γ hγ)]
    exact M.dw
  have hd:=a5H M
  have hd' : (M.decoder.map twist).natDegree≤131071 :=
    Polynomial.natDegree_map_le.trans hd
  have hcorrect :=bYQ P M
  have hmax' : h≤33561 :=hmax
  have hrel :=c74 C (by omega) _ _ hd hd' γ (γ^p) S hS hcorrect
  exact bNb apL 131071 5 b.s b.t G.val C.L G.property
    C.numerator C.denominator C.linear _ _ γ (γ^p) hrel
    (hgAnn _ _ hd hd' γ (γ^p) S hS hcorrect)
end
end P6_4
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace P6_4
noncomputable section
open P6 MvPolynomial
open scoped BigOperators
open wT (arB aVT beB aV4)
open private a5X bxi from ProximityPrize.SubmissionLower.L
open private ddh from ProximityPrize.SubmissionLower.Z
variable {u:e9} {deleted:zJe I} {P:N7 deleted}
  {Γ Λ:zJe K} {F:UJ u deleted Γ} {b:Bank}
private theorem eKV (hsub:Λ⊆Γ) (P₀ P₁:zM1 K)
    (h₀:P₀.degree<(131072 :ℕ)) (h₁:P₁.degree<(131072 :ℕ))
    (qW : ∀ γ (hγ:γ∈Λ),
      (F.mark γ (hsub hγ)).decoder=P₀+Polynomial.C γ*P₁) :
    Λ.card≤P.N := by
  classical
  have mismatch (γ:Λ) :
      ∃ i:Fin P.N,
        (P₀.eval (P.nodes i)≠u 0 (P.index i)∨P₁.eval (P.nodes i)≠u 1 (P.index i)) ∧
        P₀.eval (P.nodes i)+(γ:K)*P₁.eval (P.nodes i) =
          u 0 (P.index i)+(γ:K)*u 1 (P.index i) := by
    let M:=F.mark γ (hsub γ.property)
    obtain ⟨idx,hi,hm⟩ :
        ∃ idx∈M.support,P₀.eval (node idx)≠u 0 idx∨P₁.eval (node idx)≠u 1 idx := by
      by_contra hn
      push Not at hn
      exact M.nonjoint ⟨⟨P₀,h₀,fun j hj=>(hn j hj).1⟩,⟨P₁,h₁,fun j hj=>(hn j hj).2⟩⟩
    obtain ⟨i,rfl⟩:=(P.Z1 idx).mpr (F.survives γ (hsub γ.property) idx hi)
    refine ⟨i,hm,?_⟩
    have hh:=M.lg (P.index i) hi
    change (F.mark (γ:K) (hsub γ.property)).decoder.eval (P.nodes i)= _ at hh
    simpa only [qW _ γ.property,zvF,zbr,
      zFf] using hh
  let f :Λ→Fin P.N := fun γ=>Classical.choose (mismatch γ)
  have hf :zq4 f := by
    intro γ δ he
    apply Subtype.ext
    obtain ⟨hm,hγ⟩:=Classical.choose_spec (mismatch γ)
    have hδ:=(Classical.choose_spec (mismatch δ)).2
    change f γ=f δ at he
    change
      (P₀.eval (P.nodes (f γ))≠u 0 (P.index (f γ)) ∨
        P₁.eval (P.nodes (f γ))≠u 1 (P.index (f γ))) at hm
    change P₀.eval (P.nodes (f γ))+(γ:K)*P₁.eval (P.nodes (f γ)) =
      u 0 (P.index (f γ))+(γ:K)*u 1 (P.index (f γ)) at hγ
    change P₀.eval (P.nodes (f δ))+(δ:K)*P₁.eval (P.nodes (f δ)) =
      u 0 (P.index (f δ))+(δ:K)*u 1 (P.index (f δ)) at hδ
    rw [← he] at hδ
    exact ddh (F:=K) hγ hδ hm
  simpa only [Fintype.card_coe,zgY] using Fintype.card_le_of_injective f hf
variable (bY:TaylorChart u P F b Λ)
theorem cFf (γ:K) (hγ:γ∈Λ) (i:Fin P.N) :
    zY9 (bY.point γ) (D4 u P bY.numerator bY.denominator i)=0 ↔
      (F.mark γ (bY.subset hγ)).decoder.eval (P.nodes i) =
        u 0 (P.index i)+γ*u 1 (P.index i) := by
  let val :=zY9 (bY.point γ)
  let x :=algebraMap K kB (P.nodes i)
  change val (D4 u P bY.numerator bY.denominator i)=0↔_
  have heval :=zdm val (C x) (p:=bY.numerator)
  unfold D4
  change val (bY.numerator.eval (C x)-_)=0↔_
  rw [map_sub,← heval]
  change (bY.numerator.map val).eval (val (C x))-_=0↔_
  rw [show val (C x)=x by simp [val],show bY.numerator.map val= _ from bY.reconstruction γ hγ]
  rw [zbr,zFf,show x=algebraMap K kB (P.nodes i) from rfl,
    zdm,map_mul,map_add,map_mul]
  simp only [val,eval_C,eval_X,bY.slope γ hγ]
  rw [← map_mul,← map_add,sub_eq_zero]
  constructor
  · intro h
    exact (algebraMap K kB).injective (mul_left_cancel₀ (bY.regular γ hγ) h)
  · intro h
    rw [h]
theorem dIi (γ:K) (hγ:γ∈Λ) :
    179827 ≤ {i | zY9 (bY.point γ) (D4 u P bY.numerator bY.denominator i)=0}.ncard:= by
  let M:=F.mark γ (bY.subset hγ)
  have hsub: (arB P M.support :Set (Fin P.N)) ⊆
      {i | zY9 (bY.point γ) (D4 u P bY.numerator bY.denominator i)=0} := by
    intro i hi
    exact (cFf bY γ hγ i).mpr (M.lg _ ((aVT P M.support i).mp hi))
  have h:=Set.ncard_le_ncard hsub
  rw [zik,beB P M.support (F.survives γ (bY.subset hγ))] at h
  exact M.dw.trans h
theorem dIL (J:Ideal (z3y (Fin 3) kB)) (W:zJe K) (hW:W⊆Λ)
    (hzero : ∀ γ∈W,bY.point γ∈zeroLocus kB J)
    (hpersist:131072 ≤ {i | D4 u P bY.numerator bY.denominator i∈J}.ncard) :
    W.card≤P.N := by
  classical
  let keep:=Finset.univ.filter fun i=>D4 u P bY.numerator bY.denominator i∈J
  have hk :131072≤keep.card:= by
    rw [← zik]
    exact hpersist.trans_eq (congrArg Set.ncard (by ext i; simp [keep]))
  obtain ⟨S,hS,hcard⟩:=Finset.exists_subset_card_eq hk
  let P₀:=Lagrange.interpolate S P.nodes (fun i=>u 0 (P.index i))
  let P₁:=Lagrange.interpolate S P.nodes (fun i=>u 1 (P.index i))
  have hinj:Set.InjOn P.nodes (S:Set (Fin P.N)) :=aV4.injOn
  have hd₀:P₀.degree<(131072 :ℕ) := by
    simpa only [P₀,hcard] using Lagrange.degree_interpolate_lt (fun i=>u 0 (P.index i)) hinj
  have hd₁:P₁.degree<(131072 :ℕ) := by
    simpa only [P₁,hcard] using Lagrange.degree_interpolate_lt (fun i=>u 1 (P.index i)) hinj
  apply eKV (P:=P) (F:=F) (fun _ hg=>bY.subset (hW hg)) P₀ P₁ hd₀ hd₁
  intro γ hγ
  let M:=F.mark γ (bY.subset (hW hγ))
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hinj
  · rw [hcard]
    exact Polynomial.degree_le_natDegree.trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le (a5H M)))
  · rw [hcard]
    have hm: (z1z γ*P₁).degree≤P₁.degree := by
      refine (Polynomial.degree_mul_le _ _).trans ?_
      simpa only [zero_add] using add_le_add_left (Polynomial.degree_C_le (a :=γ)) P₁.degree
    exact (Polynomial.degree_add_le _ _).trans_lt (max_lt hd₀ (hm.trans_lt hd₁))
  · intro i hi
    have hcut:D4 u P bY.numerator bY.denominator i∈J:=(Finset.mem_filter.mp (hS hi)).2
    have hz :zY9 (bY.point γ) (D4 u P bY.numerator bY.denominator i)=0 :=
      hzero γ hγ _ hcut
    rw [zvF,zbr,zFf]
    exact (cFf bY γ (hW hγ) i).mp hz |>.trans (by
      rw [Lagrange.eval_interpolate_at_node _ hinj hi,Lagrange.eval_interpolate_at_node _ hinj hi])
theorem dIr {u:e9} {deleted:zJe I} {P:N7 deleted}
    {Γ Λ:zJe K} {F:UJ u deleted Γ} {b:Bank}
    (bY:TaylorChart u P F b Λ) : (Λ.card:ℚ)≤bcp b:= by
  classical
  let S:=Λ.image bY.point
  let R:ℚ:=chartRate b
  have hRbig: (262144 :ℚ)≤R:=bank_rate_ge b
  have hone : (1 :ℚ)≤262144 := by
    exact_mod_cast (show (1 :ℕ)≤262144 by decide)
  have hR:1≤R:=hone.trans hRbig
  have hN :P.N≤262144 := by have :=P.size; omega
  have hinj:Set.InjOn bY.point (Λ:Set K) := by
    intro γ hγ δ hδ he
    apply (algebraMap K kB).injective
    exact (bY.slope γ hγ).symm.trans ((congrFun he 1).trans (bY.slope δ hδ))
  have hcard:S.card=Λ.card:=zaG hinj
  let cuts :=D4 u P bY.numerator bY.denominator
  have hratio (m:ℕ) (hm:m<131072) :
      (((Fintype.card (Fin P.N) - m)*b.M:ℕ) :ℚ)≤R*((179827 - m:ℕ) :ℚ) := by
    have hnat : (P.N - m)*48756≤131073*(179827 - m) := by omega
    have hrat : ((P.N - m:ℕ) :ℚ)*48756≤131073*((179827 - m:ℕ) :ℚ) := by
      exact_mod_cast hnat
    have hh: ((P.N - m:ℕ) :ℚ)≤(131073/48756:ℚ)*((179827 - m:ℕ) :ℚ) := by
      linarith
    rw [zgY,Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hh (by positivity :0≤(b.M:ℚ))).trans_eq (by dsimp [R,chartRate]; ring)
  rw [← hcard]
  refine bxi bY.equation bY.denominator bY.equation_ne cuts
    (L:=131072) (A:=179827) (by decide) bY.equation_degree bY.cut_degree hR hratio S
    (fun x hx => ?_) (fun x hx => ?_) (fun J hJ => ?_)
  · obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hx
    exact ⟨bY.on_equation γ hγ,bY.regular γ hγ⟩
  · obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hx
    exact dIi bY γ hγ
  · let W:=Λ.filter fun γ=>bY.point γ∈zeroLocus kB J
    have hW:W⊆Λ:=Finset.filter_subset _ _
    have hWimage :W.image bY.point=S.filter (· ∈ zeroLocus kB J) := by
      ext x
      simp only [W,S,Finset.mem_image,Finset.mem_filter]
      constructor
      · rintro ⟨γ,⟨hγ,hJγ⟩,rfl⟩
        exact ⟨⟨γ,hγ,rfl⟩,hJγ⟩
      · rintro ⟨⟨γ,hγ,rfl⟩,hJγ⟩
        exact ⟨γ,⟨hγ,hJγ⟩,rfl⟩
    have hbound:=dIL bY J W hW (fun γ hγ=>(Finset.mem_filter.mp hγ).2) hJ
    rw [a5X,← hWimage,zaG (hinj.mono hW)]
    exact (by exact_mod_cast hbound.trans hN : (W.card:ℚ)≤262144).trans hRbig
end
end P6_4
end
section
set_option autoImplicit true
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace P6_4
open P6
def c1 :Prop :=
  ∀ u,abC u → ∀ (T:qo u) (R:Relation T),
    Nonempty (ap3 R)
def c2 :Prop :=
  ∀ (u:e9) (T:qo u) (R:Relation T) (D:Reduction u T R),
    T.height≤DY → ∀ (A:ap3 R),
      Nonempty (aLU D A)
private theorem dFt (b:Bank) (Γ exceptional:zJe K)
    (charts :Fin 5→zJe K) (hfee :exceptional.card≤b.biR)
    (hcover : ∀ γ∈Γ,γ∈exceptional ∨ ∃ j,γ∈charts j)
    (hcharts : ∀ j,((charts j).card:ℚ)≤bcp b) :
    Γ.card≤normalCap:= by
  classical
  have hsub:Γ⊆exceptional∪Finset.univ.biUnion charts := by
    intro γ hγ
    exact Finset.mem_union.mpr ((hcover γ hγ).imp id (fun ⟨j,hj⟩ =>
      Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,hj⟩))
  have hcount:=(Finset.card_le_card hsub).trans
    (Finset.card_union_le _ _ |>.trans (z3b Finset.card_biUnion_le _))
  have hbound: (Γ.card:ℚ)≤b.biR+5*bcp b:= by
    calc
      (Γ.card:ℚ)≤(exceptional.card:ℚ) + ∑ j:Fin 5,((charts j).card:ℚ) := by
        exact_mod_cast hcount
      _≤(b.biR:ℚ) + ∑ _j:Fin 5,bcp b:= by
        exact add_le_add (by exact_mod_cast hfee) (Finset.sum_le_sum fun j _=>hcharts j)
      _ = _:= by simp
  have hcap:=hbound.trans (dyr b)
  exact_mod_cast hcap
theorem of_children (h1 :c1) (h2 :c2) :P6.c4 := by
  intro u hu T R D _ hr Γ hΓ hn
  classical
  have hmax :=aEz hu T
  obtain ⟨A⟩:=h1 u hu T R
  obtain ⟨B⟩:=h2 u T R D hmax A
  let P:=wT.c1h (pJ R)
  let F:=gpg D hΓ hn
  obtain ⟨b,hfloor,⟨C⟩⟩:=dPl B hr hmax P
  obtain ⟨Q⟩:=d3X C T.height hfloor hmax D.height_eq F
  obtain ⟨exceptional,charts,hfee,hcover,hcharts⟩:=dIs P Q
  refine dFt b Γ exceptional charts hfee hcover fun j => ?_
  rcases hcharts j with he | bY
  · simp only [he,Finset.card_empty,Nat.cast_zero]
    unfold bcp
    positivity
  · exact dIr (Classical.choice bY)
end P6_4
end
