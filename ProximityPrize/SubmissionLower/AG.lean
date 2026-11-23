import ProximityPrize.SubmissionLower.X
import ProximityPrize.SubmissionLower.Y
set_option Elab.async false
open _root_ renaming Algebra→ ov,Algebra.IsIntegral→pC,Algebra.algebraMap→nq,Algebra.trdeg→ oY,AlgebraicIndependent→ oK,CommRing→lV,Fintype.card→cy,Fintype.card_sum→ oz,FractionRing→nI,Ideal→lJ,Ideal.Quotient.commRing→ oy,Ideal.Quotient.mk→ oq,Ideal.Quotient.mkₐ→pQ,Ideal.mem_sup_right→pL,Ideal.span→ oj,Ideal.subset_span→pz,Module.Finite→ ox,Module.finrank→ oZ,MvPolynomial→c9,MvPolynomial.X→lI,MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite→pG,Nat.cast_ofNat→ oD,Sum.inl→nX,Sum.inr→n5,aR.Shape→aU,dN.GeoJets→lz,ringKrullDim→mD
set_option autoImplicit true
section
set_option maxHeartbeats 0
set_option maxRecDepth 50000
namespace acY
open acY.Compact
private def p0:Chunk 3303 4 898043648 :=
 cert _ _ _ 0x9c540a0852509a4e984c964a064894460444924202400016b4b25a0c5c0e1cc4cc68106a121418206e25358ad60c0c4c984414b29976ca5850c9f132a7148c91f3f692cf3939e4ecf4fc27a67e9fa71478e3e0a088c3c8a3a8838368634328430062e2c822a0428268024022200161aae580c5e0e1c1eca66106c1214182022649e415ae981899301ef905d232e92487941f2ceeef82f647d259f330bc9d9e85dc88963a7aa8d39f8f82821f0f1e8e9e0e0d9d8d0c9d0c018b8b1c8a810a099c090088800586ae160317838707b219841b048506369b892c82b5d303132601052cace58190f283e59c654e29192ce92ce8939e4ecf4fc27a67e9ea9b4daa540a085250a84ea64ca44a0648a2460444a0420240009e1ab65a0c5c0ebc1ec668106a121418206e24758ad60c0c4c98441748cba496ca587cb3bbbe0bd91f49679c9cf2767a17722267e9ea6547 (by decide +kernel) (by decide +kernel)
private def p4 :Chunk 3307 4 910732486 :=
 cert _ _ _ 0x2715028214942693a6132592819225118111249080900005ad2c968317038731331a041a848506081b894d62b58303132613df20a594cb90f283e59dddf0464b3a7330a4e514fa7e13d33f5053023471f0504461e451d441c1b431a194218031716411502141340120111000b0d572c062f070e0f65330836090a0c1011324f20ad74c0c4c980f7c8296532ed94a0f96719538a464b3a873ce4e793b3d3f09e99fa82a7935f8f82821f0f1e8e9e0e0d9d8d0c9d0c018b8b1c8a810a099c090088800586ae160317838707b219841b048506369b892c82b5d303132603df20a594cb90f283e59dddf05ec8fa873e661793b3d0bb91133f5054c26d52a0504292854275326522503245123022250210120004f0d5b2d062e075e0f63340835090a0c1037123ac56b0606264c27be454b299749243ca0f967777c1192cea1ce8939e4ecf4fc27a67e9fa7048 (by decide +kernel) (by decide +kernel)
private def p8:Chunk 3311 4 924279515 :=
 cert _ _ _ 0x2715028214942693a6132592819225118111249080900005ad2c968317038731331a041a848506081b894d62b583031326118720ba5a843ca09f132a7148c9674e679c9cf2767a17722267e9ea63468e3e0a088c3c8a3a8838368634328430062e2c822a0428268024022200161aae580c5e0e1c1eca66106c1214182022649e415ae981899300c39052ca65c87941f2ceeef82f647d399f330bc88a4e497722267e9faa14d7e3e0a087c3c7a3a7838367634327430062e2c722a0428267024022200161ab8580c5e0e1c1ec866106c121418da6e24b20ad74c0c4c98061c82e96a10f283e59dddf0464b3a733a24e793b3d3f09e99fa7ea3d36a95028214942a13a993291281922891811128108090002786ad96831703af07b19a041a848506081b891d62b58303132613df20a594cbb652c3e59dddf05ec8f9fb50e79cc2f2767a17722267ea0a7348 (by decide +kernel) (by decide +kernel)
private def zF:Chunk 3315 4 937197969 :=
 cert _ _ _ 0x138a81410a4a1349d30992c940c91288c088924840480002d6964b418b81c398998d020d424283040dc4a6b15ac18189930b9882e919721e507cb3bbbe0bd91f5127449cf2767a7e13d3b72152fa3c71f0504461e451d441c1b431a194218031716411502141340120111000b0d572c062f070e0f65330836090a0c1011324f20ad74c0c4c981cc414b299721e507cb3bbbe08c96759679c9cf2767a7e13d33f2154aa6bf1f05043e1e3d1d3c1c1b3b1a193a18031716391502141338120111000b0d5c2c062f070e0f64330836090a0c6d371259056ba606264c0e620ba5a860ca0f967777c17b23e7ed399f330bc88a4e497722267e9daa04eaa540a085250a84ea64ca44a0648a2460444a0420240009e1ab65a0c5c0ebc1ec668106a121418206e24758ad60c0c4c98461c8296532e43ca0f967777c1192ceb2ce8939e4ecf4fc27a67e9da6547 (by decide +kernel) (by decide +kernel)
private def TF:Chunk 3319 4 950461479 :=
 cert _ _ _ 0x9c540a0852509a4e984c964a064894460444924202400016b4b25a0c5c0e1cc4cc68106a121418206e25358ad60c0c4c9847f7988a96532e43ca09f132a7148c9675127ccc2f2767a17722267e41a71478e3e0a088c3c8a3a8838368634328430062e2c822a0428268024022200161aae580c5e0e1c1eca66106c1214182022649e415ae981899300fef3105d2d4306507cb3bbbe0bd91f3f6a24e8939453e9f8444cfd375409cfc7c1410f878f474f0706cec6864e8600c5c58e45408504ce0480444002c3570b018bc1c383d90cc20d8242831b4dc496415ae981899300fef31152ca65c87941f2ceeef823259d449e7273c9d9e9f84f4edd3953a9d54a81410a4a1509d4c9948940c91448c088940840480013c356cb418b81d783d8cd020d424283040dc48eb15ac18189930b988296532e60ca99f132a7148c9675967ccc2f2767a17722267e9ca6646 (by decide +kernel) (by decide +kernel)
private def WU:Chunk 3323 4 963821922 :=
 cert _ _ _ 0x9c540a0852509a4e984c964a064894460444924202400016b4b25a0c5c0e1cc4cc68106a121418206e25358ad60c0c4c9847f7988296532e60ca0f967777c17b23e7ed459d1273c9d9e9f84f4edd334f0931c7c14111879147510706d0c686508600c5c59045408504d00480444002c355cb018bc1c383d94cc20d82428304044c93c82b5d303132606f73105d2d4306507cb3bbbe08c96751679cc2f2767a7e13d3b74d54ba73f1f05043e1e3d1d3c1c1b3b1a193a18031716391502141338120111000b0d5c2c062f070e0f64330836090a0c6d371259056ba606264c03fbcc414b2997306507cb3bb8e29192cea2cc2f22293925dc8899fa6aa7936a95028214942a13a993291281922891811128108090002786ad96831703af07b19a041a848506081b891d62b58303132611fde620ba5a860ca0f967777c17b23ea2ce8939e4ecf4fc27a76e41a6748 (by decide +kernel) (by decide +kernel)
private def p24 :Chunk 3327 4 977285953 :=
 cert _ _ _ 0x9c540a0852509a4e984c964a064894460444924202400016b4b25a0c5c0e1cc4cc68106a121418206e25358ad60c0c4c985bdcc414b2997306507cb38ca9c523259d669f330bc9d9e85dc889db9029cd2238f8282230f228ea20e0da18d0ca10c018b8b208a810a09a0090088800586ab960317838707b299841b048506080899279056ba606264c0243bdcc4174b5112941f2ceeef82f647cfdacd3a24e793b3d3f08899f902ab541f8f82821f0f1e8e9e0e0d9d8d0c9d0c018b8b1c8a810a099c090088800586ae160317838707b219841b048506369b892c82b5d303132606f731052ca65cc1941f2ceeef82f647d669e7273c9d9e9f84f4edd315349d54a81410a4a1509d4c9948940c91448c088940840480013c356cb418b81d783d8cd020d424283040dc48eb15ac18189930b7b9882e96a2252a67c4ca9c523259d459f330bc88a4e497722267e98a6e47 (by decide +kernel) (by decide +kernel)
private def p28:Chunk 3331 4 989872571 :=
 cert _ _ _ 0x138a81410a4a1349d30992c940c91288c088924840480002d6964b418b81c398998d020d424283040dc4a6b15ac18189930890ef73105d2d444a507cb3bbbe0bd91f3f6b3ce8939e4ecf4fc22276e3ea7a4a8e3e0a088c3c8a3a8838368634328430062e2c822a0428268024022200161aae580c5e0e1c1eca66106c1214182022649e415ae981899300cdef731152ca65cc1941f2ceeef823259d679f330bc9d9e9f84f4edc7d5509efc7c1410f878f474f0706cec6864e8600c5c58e45408504ce0480444002c3570b018bc1c383d90cc20d8242831b4dc496415ae98189930090ef73105d2d444a54f3bb8e29192ceb3cc2939452724bb9113b71fd4da6d52a0504292854275326522503245123022250210120004f0d5b2d062e075e0f63340835090a0c1037123ac56b0606264c2243bdcc454b2997306507cb3bbbe0bd91f3f6b34f3939e4ecf4fc27a76e3fa804a (by decide +kernel) (by decide +kernel)
private def p32 :Chunk 3335 4 1002793001 :=
 cert _ _ _ 0x9c540a0852509a4e984c964a064894460444924202400016b4b25a0c5c0e1cc4cc68106a121418206e25358ad60c0c4c985d04877b9882e96a2552a7e59dddf0464b3ad13e661793b3d3f09e9db8ee9dd2a38f8282230f228ea20e0da18d0ca10c018b8b208a810a09a0090088800586ab960317838707b299841b048506080899279056ba606264c0e8337bc61c8296532e894a9e7777c17b2ceb44e8939e4ecf4fc22276e3caab4f7e3e0a087c3c7a3a7838367634327430062e2c722a0428267024022200161ab8580c5e0e1c1ec866106c121418da6e24b20ad74c0c4c981d04877b9882e96a225283e59dddf05ec8fad13ce4e793b3d3f09e9db8f2a9d42a95028214942a13a993291281922891811128108090002786ad96831703af07b19a041a848506081b891d62b583031326119bdee622a594cba252a67c4ca9c523259d679f330bc88a4e497722276ee2a7f48 (by decide +kernel) (by decide +kernel)
private def p36:Chunk 3339 3 760424226 :=
 cert _ _ _ 0x238f8282230f228ea20e0da18d0ca10c018b8b208a810a09a0090088800586ab960317838707b299841b048506080899279056ba606264c025fd04877b9882e96a225283e59dddf05ec8faa73e661793b3d3f09e9f98e6ad545f8f82821f0f1e8e9e0e0d9d8d0c9d0c018b8b1c8a810a099c090088800586ae160317838707b219841b048506369b892c82b5d303132607419bdee620ba465d12953ceee38a464b3aa73a24e5149c92ee444edc7354c9d54a81410a4a1509d4c9948940c91448c088940840480013c356cb418b81d783d8cd020d424283040dc48eb15ac18189930ba090ef73105d2d444a507cb3bbbe0bd91f3f6b44f3939e4ecf4fc22276e3ba824b (by decide +kernel) (by decide +kernel)
private def c:Chunk 3303 39 9314912770 :=
 add p0 <| add p4 <| add p8 <| add zF <| add TF <| add WU <| add p24 <| add p28 <| add p32 <| p36
end acY
end
section
namespace ap7
open aR dN BO GJ lB YV
open MeasureTheory MvPolynomial
open scoped BigOperators Pointwise
def c1 :Prop :=
  ∀ (J:lJ lz) (a h:aU),vE a→vE h →
    (∀ P,J.IsMinimalPrime P→ mD (lz ⧸ P)≤2) →
    ox (VM a h) (axZ J a h)
def c2 :Prop :=
  ∀ (J:lJ lz) (a h:aU),vE a→vE h →
    ox (VM a h) (axZ J a h) →
    ∀ (uG:Finset (lJ lz)) (v :lJ lz→ℕ),
      (∀ P∈uG,∃ hP:J.IsMinimalPrime P,oA J P hP.isPrime=(v P:ℕ∞)) →
      (∑ P∈uG,v P*Ux P a h) ≤
        oZ (VM a h) (axZ J a h)
def c3:Prop :=
  ∀ (p q a h:aU),bF p→bF q→bF a→bF h →
    ∀ (F G U V:ae9 a h),aJ9 F p→aJ9 G q →
      aJ9 U a→aJ9 V h →
      ox (VM a h) (ae9 a h ⧸ oj {F,G,U,V}) →
      (oZ (VM a h)
        (ae9 a h ⧸ oj {F,G,U,V}) :ℝ) ≤
        avz (cap p) (cap q) (cap a) (cap h)
private theorem cTk {p:aU} (hp:vE p) :
  vE (p.scale 6) := by
 obtain ⟨⟨hb,hj⟩,ht⟩:=hp
 change (6*p.j≤6*p.b∧3*(6*p.t)≤6*p.j)∧0<6*p.t
 omega
private theorem dgo {σ:Type*} (p:aU) (ι:uL p→σ) :
  aJ9 (Uq p ι) p:= by
 classical
 intro e he
 unfold Uq at he
 obtain ⟨m,hm,he⟩:=Finset.mem_biUnion.mp (support_sum he)
 obtain ⟨hb,hj,ht⟩:=(Finset.mem_filter.mp hm).2
 rw [MvPolynomial.prod_X_pow,C_mul_monomial] at he
 have heq :=Finset.mem_singleton.mp (support_monomial_subset he)
 have heval (i:Fin 4) :e i=(m i).val := by
  rw [heq]
  simp [Finsupp.indicator]
 simp only [Fin.sum_univ_four] at hb hj
 have hindex : (m 1).val+2*(m 2).val+3*(m 3).val≤p.j:= by
  change 0*(m 0).val+1*(m 1).val+2*(m 2).val+3*(m 3).val≤p.j at hj
  omega
 change (∀ i,0≤(e i:ℝ))∧(e 0:ℝ)+e 1+e 2+e 3≤p.b ∧
  (e 1 :ℝ)+2*e 2 + 3*e 3≤p.j∧(e 3:ℝ)≤p.t
 simp only [heval]
 exact ⟨fun _=>Nat.cast_nonneg _,by exact_mod_cast hb,
  by exact_mod_cast hindex,by exact_mod_cast ht⟩
private theorem dgn {F:lz} {p:aU} (hF:yy F p)
  (a h:aU) :aJ9 (EG a h F) p :=
 fun e he=>bxf hF e (support_map_subset _ _ he)
private theorem dew (F G:lz) (a h:aU) :
   (Ib F G).map (EG a h) ⊔ oj {a4d a h,a8j a h} =
     oj {EG a h F,EG a h G,a4d a h,a8j a h} := by
 rw [Ib,Ideal.map_span,Set.image_insert_eq,Set.image_singleton,← Ideal.span_union]
 congr 1
 ext x
 simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
 tauto
private theorem ase {F:Set M5→ℝ} {G:aU→ℤ}
  (heq : ∀ x :aU,bF x→32*F (cap x)=(G x :ℝ))
  {a :aU} (ha :bF a) (x :aU) (hx :bF x) :
  32*ahk F (cap a) (cap x)=(gI G a x :ℝ) := by
 rw [ahk,gI,Int.cast_sub,mul_sub,← anN hx ha,
  heq _ (Nc hx ha),heq _ hx]
private def Q9 (p q a h:aU) :ℤ :=
 gI (gI (gI (gI Dn p) q) a) h ⟨0,0,0⟩
private theorem bJi (p q a h:aU)
  (hp:bF p) (hq:bF q) (ha :bF a) (hh:bF h) :
  32*avz (cap p) (cap q) (cap a) (cap h)=(Q9 p q a h:ℝ) := by
 have hv :=ase
  (F:= fun P=>(volume P).toReal) (G:=Dn) bWq hp
 have hm:=ase (ase (ase hv hq) ha) hh
  ⟨0,0,0⟩ (⟨by decide,by decide⟩:bF ⟨0,0,0⟩)
 rw [auw] at hm
 exact hm
private theorem eAY (p q a h:aU) :
  Q9 p q (a.scale 6) (h.scale 6)=36*Q9 p q a h:= by
 simp only [Q9,gI,Dn,Shape.plus,Shape.scale,
  Nat.cast_add,Nat.cast_mul,oD,Nat.cast_zero]
 ring
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :GJ.c3:= by
  intro F G p q a h hF _ hproper hp hq ha hh hFp hGq uG v hsurfaces
  let A:=a.scale 6
  let H :=h.scale 6
  let J:=Ib F G
  let d:=oZ (VM A H) (axZ J A H)
  have hA:vE A:=cTk ha
  have hH :vE H :=cTk hh
  have hfin:=h1 J A H hA hH (fun P hP=>(bf6 hF hproper hP).le)
  have hcycle :=h2 J A H hA hH hfin uG v hsurfaces
  have hfin' : ox (VM A H)
      (ae9 A H ⧸ oj {EG A H F,EG A H G,
        a4d A H,a8j A H}) := by
    rw [← dew]
    exact hfin
  have hsparse :=h3 p q A H hp.1 hq.1 hA.1 hH.1
    (EG A H F) (EG A H G) (a4d A H) (a8j A H)
    (dgn hFp _ _) (dgn hGq _ _)
    (dgo _ _) (dgo _ _) hfin'
  rw [← dew] at hsparse
  change (d:ℝ)≤_ at hsparse
  have hb:=mul_le_mul_of_nonneg_left hsparse (by norm_num : (0:ℝ)≤32)
  rw [bJi p q A H hp.1 hq.1 hA.1 hH.1,eAY,Int.cast_mul] at hb
  have hz : (↑(32*d) :ℤ)≤36*Q9 p q a h:= by exact_mod_cast hb
  have hn:0≤Q9 p q a h:= by
    have hnonneg: (0:ℤ) ≤ ↑(32*d) :=Int.natCast_nonneg _
    omega
  have hd:32*d≤36*iH p q a h:= by
    change 32*d≤36*(Q9 p q a h).toNat
    exact_mod_cast (show (↑(32*d) :ℤ) ≤ ↑(36*(Q9 p q a h).toNat) by
      simpa only [Nat.cast_mul,oD,Int.toNat_of_nonneg hn] using hz)
  exact (Nat.mul_le_mul_left 32 hcycle).trans hd
end ap7
end
section
set_option maxHeartbeats 1000000
namespace cyh
noncomputable section
open aR dN BO GJ ap7
open MvPolynomial
open scoped BigOperators
private theorem gEa (k A:Type) [Field k] [lV A] [IsDomain A]
   [ov k A] [Algebra.FiniteType k A] {n:ℕ} (hd:mD A≤n) :
   oY k A≤n:= by
 obtain ⟨s,g,hg,hint⟩:=exists_integral_inj_algHom_of_fg k A
 let B:=c9 (Fin s) k
 let:ov B A:=g.toRingHom.toAlgebra
 have :IsScalarTower k B A := .of_algebraMap_eq fun c=>(g.commutes c).symm
 have :FaithfulSMul B A:=(faithfulSMul_iff_algebraMap_injective B A).mpr hg
 have :pC B A:=algebraMap_isIntegral_iff.mp hint
 have hdB:mD B=s := by
   simp [B,pG,
     ringKrullDim_eq_zero_of_field]
 obtain ⟨l,hl⟩:=Order.le_krullDim_iff.mp (le_of_eq hdB.symm)
 obtain ⟨Q,-,hQ,he⟩:=Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal
   (⊥ : lJ A) (by simp [← RingHom.ker_eq_comap_bot])
 let:Q.IsPrime :=hQ
 have :Q.LiesOver l.head.asIdeal:=(Ideal.liesOver_iff _ _).mpr he.symm
 obtain ⟨L,hL,-,-⟩:=Ideal.exists_ltSeries_of_hasGoingUp l Q
 have hsA: (s :WithBot ℕ∞)≤ mD A :=
   Order.le_krullDim_iff.mpr ⟨L,hL.trans hl⟩
 have hs :s≤n:= by exact_mod_cast hsA.trans hd
 have hz :oY B A=0 :=
   trdeg_eq_zero_iff.mpr (Algebra.IsIntegral.isAlgebraic (R:=B) (A:=A))
 rw [← trdeg_add_eq k B (A:=A),hz,add_zero]
 simpa [B] using (show (s :Cardinal.{0})≤n by exact_mod_cast hs)
private theorem b58 (k σ A D:Type) [Field k] [Fintype σ]
    [lV A] [ov k A] [lV D]
    [ov k D] [ov (nI (c9 σ k)) D]
    [IsScalarTower k (nI (c9 σ k)) D]
    (f :A →ₐ[k] D) (hd:oY k A≤ cy σ)
    (c:σ→A) (hc : ∀ i,f (c i) =
      nq (nI (c9 σ k)) D
        (nq (c9 σ k) (nI (c9 σ k)) (lI i)))
    (x :A) :IsAlgebraic (nI (c9 σ k)) (f x) := by
  let B:=c9 σ k
  let F:=nI B
  by_contra hx
  have hX:oK k (fun i:σ=>nq B F (lI i)) :=
    (algebraicIndependent_X σ k).map'
      (f :=IsScalarTower.toAlgHom k B F) (IsFractionRing.injective B F)
  have hx' : oK F (fun _:Unit=>f x) := by
    apply algebraicIndependent_unique_type_iff.mpr
    exact (show Transcendental F (f x) from hx)
  have h:=hX.sumElim_comp hx'
  have h' : oK k (f ∘ Sum.elim (fun _:Unit=>x) c) := by
    convert h using 1
    funext i
    cases i with
    | inl _=>rfl
    | inr i=>exact hc i
  have hle :=(AlgebraicIndependent.of_comp f h').cardinalMk_le_trdeg.trans hd
  rw [Cardinal.mk_fintype,oz ,Fintype.card_unit] at hle
  have :1+Fintype.card σ≤ cy σ:= by exact_mod_cast hle
  omega
private theorem cEf (σ:Type) [Fintype σ] [Zero σ]
  [DecidablePred (fun x :σ=>x=0)] [DecidablePred (fun x :σ=>x≠0)] :
  cy {x :σ // x≠0} + 1=cy σ:= by
 rw [Fintype.card_subtype_compl (fun x :σ=>x=0)]
 have h:cy {x :σ // x=0} = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨⟨0,rfl⟩,fun x=>Subtype.ext x.property⟩
 rw [h]
 have :0<cy σ:=Fintype.card_pos_iff.mpr ⟨0⟩
 omega
private theorem cHV {D:Type} [lV D]
  (S:Subring D) (a :aU) (c:uL a→D) (x :Fin 4→D)
  (hc : ∀ m≠0,c m∈S) (hx : ∀ i,x i∈S)
  (hz : ∑ m∈Bz a,c m * ∏ i:Fin 4,x i^(m i).val=0) :
  c 0∈S:= by
 classical
 let t (m:uL a) :=c m * ∏ i:Fin 4,x i^(m i).val
 have ht:t 0=c 0:= by simp [t]
 have hm:0∈Bz a := by simp [Bz]
 have hsum:=Finset.sum_erase_add (Bz a) t hm
 rw [ht,show (∑ m∈Bz a,t m)=0 from hz] at hsum
 have hneg:c 0 = -(∑ m∈(Bz a).erase 0,t m) :=
  eq_neg_of_add_eq_zero_right (by simpa [add_comm] using hsum)
 rw [hneg]
 exact S.neg_mem (S.sum_mem fun m hm=>S.mul_mem
  (hc m (Finset.mem_erase.mp hm).1) (S.prod_mem fun i _=>S.pow_mem (hx i) _))
set_option backward.isDefEq.respectTransparency false in
private theorem eOd (J:lJ lz) (a h:aU)
    (hd : ∀ P,J.IsMinimalPrime P→ mD (lz ⧸ P)≤2)
    (Q:lJ (axZ J a h)) (hQ:Q.IsPrime) :Q.IsMaximal:= by
  classical
  let:Q.IsPrime :=hQ
  let k :=GeoField
  let σ:=aav a h
  let τ := {m:uL a // m≠0} ⊕ {m:uL h // m≠0}
  let B:=c9 σ k
  let F:=VM a h
  let I:lJ (ae9 a h) :=
    J.map (EG a h) ⊔ oj {a4d a h,a8j a h}
  let:lV (axZ J a h) :=oy I
  let D:=axZ J a h ⧸ Q
  let:lV D:=oy Q
  let q:ae9 a h →ₐ[F] D :=
    (pQ F Q).comp (pQ F I)
  let e :lz →ₐ[k] D :=
    (q.restrictScalars k).comp (MvPolynomial.mapAlgHom (Algebra.ofId k F))
  have hJe :J≤RingHom.ker e.toRingHom:= by
    intro z hz
    change q (EG a h z)=0
    have hzI:EG a h z∈I :=
      Ideal.mem_sup_left (Ideal.mem_map_of_mem (EG a h) hz)
    change oq Q (oq I (EG a h z))=0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hzI,map_zero]
  have : (RingHom.ker e.toRingHom).IsPrime :=RingHom.ker_isPrime e.toRingHom
  obtain ⟨P,hP,hPe⟩:=J.exists_minimalPrimes_le hJe
  have :P.IsPrime :=hP.isPrime
  let A:=lz ⧸ P
  let:lV A:=oy P
  let W:=c9 τ A
  let r :A →ₐ[k] D:=Ideal.Quotient.liftₐ P e fun z hz=>hPe hz
  let coeff (i:σ) :D:=nq F D (nq B F (lI i))
  let param:τ→D :=
    (Sum.elim (fun m=>coeff (nX m.val)) (fun m=>coeff (n5 m.val)))
  let f :W →ₐ[k] D:=aevalTower r param
  let coord (i:Fin 4) :D:=q (lI i)
  let S:=f.toRingHom.range
  have hcoord (i:Fin 4) :coord i∈S:= by
    let z :A:=oq P (lI i)
    refine ⟨C z,?_⟩
    change f (C z)=coord i
    calc
      f (C z)=r z :=aevalTower_C r param z
      _=e (lI i) :=rfl
      _=coord i:= by simp [e,coord,MvPolynomial.mapAlgHom_apply]
  have hcoeff₁ (m:uL a) (hm:m≠0) :coeff (nX m)∈S :=
    ⟨lI (nX ⟨m,hm⟩),aevalTower_X r param (nX ⟨m,hm⟩)⟩
  have hcoeff₂ (m:uL h) (hm:m≠0) :coeff (n5 m)∈S :=
    ⟨lI (n5 ⟨m,hm⟩),aevalTower_X r param (n5 ⟨m,hm⟩)⟩
  have hzero (p:ae9 a h) (hp:p∈I) :q p=0:= by
    change oq Q (oq I p)=0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp,map_zero]
  have hcut (b:aU) (ι:uL b→σ) (hb:Uq b ι∈I) :
      ∑ m∈Bz b,coeff (ι m) * ∏ i:Fin 4,coord i^(m i).val=0:= by
    calc
      _=q (Uq b ι) := by
        rw [Uq,map_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_mul,map_prod]
        simp only [map_pow]
        exact congrArg (· * ∏ i:Fin 4,coord i^(m i).val)
          (q.commutes (nq B F (lI (ι m)))).symm
      _=0:=hzero _ hb
  have hcoeff (i:σ) :coeff i∈S:= by
    cases i with
    | inl m =>
      by_cases hm:m=0
      · subst m
        exact cHV S a (fun m=>coeff (nX m)) coord
          hcoeff₁ hcoord (hcut a nX (pL (pz (by simp))))
      · exact hcoeff₁ m hm
    | inr m =>
      by_cases hm:m=0
      · subst m
        exact cHV S h (fun m=>coeff (n5 m)) coord
          hcoeff₂ hcoord (hcut h n5 (pL (pz (by simp))))
      · exact hcoeff₂ m hm
  have hcard:cy τ+2=cy σ:= by
    change cy (_ ⊕ _)+2=cy (_ ⊕ _)
    rw [oz ,oz]
    have ha :=cEf (uL a)
    have hh:=cEf (uL h)
    omega
  have hdW:mD W≤ cy σ:= by
    change mD (c9 τ A)≤_
    rw [pG,Nat.card_eq_fintype_card,
      ← hcard,Nat.cast_add]
    rw [oD,add_comm (cy τ:WithBot ℕ∞) 2]
    exact add_le_add_left (hd P hP) (cy τ:WithBot ℕ∞)
  have hw:=gEa k W hdW
  have hlift (i:σ) : ∃ z :W,f z=coeff i:=hcoeff i
  choose u hu using hlift
  have halg (i:Fin 4) :IsAlgebraic F (coord i) := by
    obtain ⟨z,hz⟩:=hcoord i
    change f z=coord i at hz
    rw [← hz]
    exact b58 k σ W D f hw u hu z
  have hsurj:Function.Surjective q :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hadj:Algebra.adjoin F (Set.range coord) = ⊤ := by
    rw [show coord=q ∘ lI from rfl,Set.range_comp,Algebra.adjoin_image,
      MvPolynomial.adjoin_range_X,Algebra.map_top,(AlgHom.range_eq_top q).mpr hsurj]
  have h:=Algebra.isAlgebraic_adjoin_iff.mpr (Set.forall_mem_range.mpr halg)
  rw [hadj] at h
  have :pC F D :=
    Algebra.isAlgebraic_iff_isIntegral.mp (Algebra.isAlgebraic_iff.mpr h)
  exact Ideal.Quotient.maximal_of_isField Q
    (isField_of_isIntegral_of_isField' (Field.toIsField F))
set_option backward.isDefEq.respectTransparency false in
theorem proof :ap7.c1 := by
 intro J a h _ _ hd
 let F:=VM a h
 let S:=axZ J a h
 let:Field F:=inferInstanceAs (Field (VM a h))
 have :IsArtinianRing F:=DivisionRing.instIsArtinianRing
 have hS:Ring.KrullDimLE 0 S :=
  Ring.krullDimLE_zero_iff.mpr (eOd J a h hd)
 exact (Module.finite_iff_krullDimLE_zero F S).mpr hS
end
end cyh
end
section
namespace bjG
noncomputable section
open K1 cu qQ XY Polynomial
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
def c2 :Prop :=
  ∀ (f :Equation),Irreducible f→0<f.natDegree→f.natDegree<p →
    ∃ (g:aix) (a :L[X]),aw5 f g a ∧
      ag6 (C f) (cT8 g) ∧
      oU (C f) ⟨0,f.natDegree,0,My f⟩ ∧
      oU (cT8 g) ⟨0,f.natDegree,1,My f⟩
end
end bjG
end
section
namespace czG
noncomputable section
open K1 cu qQ XY bjG Polynomial
private theorem c2K (f :Equation) (j:ℕ) :
    oU (C f) ⟨0,f.natDegree,j,My f⟩:= by
  intro v y hv
  cases v with
  | zero =>
    rw [coeff_C_zero] at hv
    change y+0≤f.natDegree∧0≤j ∧
      (((C f :Jet).coeff 0).coeff y).totalDegree≤My f
    rw [coeff_C_zero,Nat.add_zero]
    exact ⟨le_natDegree_of_ne_zero hv,Nat.zero_le j,
      Finset.le_sup (f := fun i=>(f.coeff i).totalDegree)
        (Polynomial.mem_support_iff.mpr hv)⟩
  | succ v =>
    rw [coeff_C_succ,coeff_zero] at hv
    exact (hv rfl).elim
theorem proof :bjG.c2 := by
 intro f hi hd hp
 obtain ⟨g,a,ha,hproper,_⟩:=YZ.c2P f hi hd hp
 refine ⟨g,a,ha,hproper,c2K f 0,?_⟩
 change oU (YZ.alD g) ⟨0,f.natDegree,1,My f⟩
 exact YZ.bWO hproper.left_ne (c2K f 1)
  le_rfl (dvd_refl (C f :Jet)) ha
end
end czG
end
