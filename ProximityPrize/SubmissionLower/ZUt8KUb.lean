import ProximityPrize.SubmissionLower.ZloDYIb
set_option Elab.async false
open _root_ renaming Ideal.mem_span_singleton→ oy,Ideal.span→mD,MvPolynomial.C→c9,MvPolynomial.X→lI,MvPolynomial.aeval→nX,MvPolynomial.lcoeff→ ov,MvPolynomial.le_weightedTotalDegree→nq,MvPolynomial.monomial_le_degreeOf→n5,P5_7_2.TopRow→aU,Polynomial.C→cy,Polynomial.X→lz,Polynomial.hasseDeriv→nI,Submodule→lJ,Submodule.mem_comap→ oq,Submodule.mem_iInf→ ox,Submodule.restrictScalars_mem→ oj,q7F2qKe.weakAgreement→lV
section
set_option autoImplicit true
namespace q7F2qKe
noncomputable section
open Polynomial

open P5_7_2 (ChosenRow anM)

open DP (VY)
theorem chosen_mem {h D Crt word r s} (R : @ChosenRow h D Crt word r s) :
  R.jet∈VY Crt word s (anM h r s) :=
 Submodule.subset_span ⟨R.raw,R.mem,rfl⟩
end
end q7F2qKe
end
section
set_option autoImplicit true
namespace q7IA62d
noncomputable section
open Polynomial Finset
open scoped BigOperators
open P5 (I)
open P5_7_2 (A fO TopRow topDonors row)

open cu (L)
open DP (jF zG ad0)
open jA (jK kS mA vC lP gY ahb aCk aox ahH jH)
def profile (b:fO) (strong:Bool) :TopRow :=
 if strong then (topDonors b).2 else (topDonors b).1
def cutoff (t:aU) :ℕ:=t.shape.m*lV - 1
def clearance (h:ℕ) (t:aU) :ℕ:=(t.shape.B+t.shape.J)*h
def CapsCut (h:ℕ) (t:aU) (W:ℕ) (P:jK) :Prop :=
  vC P≤t.shape.B∧lP P≤t.shape.J∧P.degreeOf (some 2)≤t.YM ∧
    gY P≤t.shape.U∧ahb h (W+clearance h t) P
def capColumns (t:aU) (a :mA →₀ ℕ) :Prop :=
 a.weight (fun i=>i.elim 0 (fun _=>1))≤t.shape.B ∧
 a.weight (fun i=>i.elim 0 Fin.val)≤t.shape.J ∧
 a (some 2)≤t.YM∧a none≤t.shape.U
def kO (h:ℕ) (a :mA →₀ ℕ) :=
 a.sum (fun i e=>i.elim 0 (fun j=>(131071+h - j.val)*e))
def coord (a :mA →₀ ℕ) (n:ℕ) :jK →ₗ[L] L :=
 (Polynomial.lcoeff L n).comp ((ov L[X] a).restrictScalars L)
def Aw (h:ℕ) (t:aU) (W:ℕ) :lJ L jK :=
  ⨅ a,⨅ n,⨅ (_ : ¬ (capColumns t a∧n+kO h a≤W+clearance h t)),
    LinearMap.ker (coord a n)
theorem mem_ambient {h t W P} : P∈Aw h t W↔CapsCut h t W P:= by
  classical
  simp only [Aw,ox ,LinearMap.mem_ker]
  change (∀ a n,¬ (capColumns t a∧n+kO h a≤W+clearance h t) →
    (P.coeff a).coeff n=0)↔_
  constructor
  · intro hp
    have hs (a :mA →₀ ℕ) (ha :a∈P.support) :
        capColumns t a∧(P.coeff a).natDegree+kO h a≤W+clearance h t:= by
      by_contra hn
      exact (leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp ha))
        (by simpa only [coeff_natDegree] using hp a (P.coeff a).natDegree hn)
    exact ⟨Finset.sup_le fun a ha=>(hs a ha).1.1,
      Finset.sup_le fun a ha=>(hs a ha).1.2.1,
      MvPolynomial.degreeOf_le_iff.mpr fun a ha=>(hs a ha).1.2.2.1,
      MvPolynomial.degreeOf_le_iff.mpr fun a ha=>(hs a ha).1.2.2.2,
      fun a ha=>(hs a ha).2⟩
  · rintro ⟨hB,hJ,hC,hU,hW⟩ a n hn
    by_contra hc
    have ha :a∈P.support :=MvPolynomial.mem_support_iff.mpr (fun hz=>hc (by simp [hz]))
    exact hn ⟨⟨(nq _ ha).trans hB,
      (nq _ ha).trans hJ,
      (n5 _ ha).trans hC,
      (n5 _ ha).trans hU⟩,
      (Nat.add_le_add_right (le_natDegree_of_ne_zero hc) _).trans (hW a ha)⟩
def contactLinear (x v :L) :jK →ₗ[L] jK :=
  (nX (R:=L[X]) (fun j:mA =>
    if j=some 0 then
      lI (some 0)+MvPolynomial.C (cy v) -
        c9 (cy x-Polynomial.X)*lI (some 1) -
        c9 ((cy x-Polynomial.X)^2)*lI (some 2)
    else lI j)).toLinearMap.restrictScalars L
def ays (t:aU) (x v :L) :lJ L jK :=
  ⨅ a :mA →₀ ℕ,
    ((mD {((lz-Polynomial.C x)^(t.shape.m-3*a (some 0)) :
      L[X])}).restrictScalars L).comap
      (((ov L[X] a).restrictScalars L).comp (contactLinear x v))
theorem bsz {t x v P} :
    P∈ays t x v ↔ ∀ a :mA →₀ ℕ,
      (lz-Polynomial.C x)^(t.shape.m-3*a (some 0)) ∣
        (aCk x v P).coeff a := by
  simp only [ays,ox ,oq,oj,
    LinearMap.comp_apply,LinearMap.restrictScalars_apply,MvPolynomial.lcoeff_apply,
    oy]
  rfl
def amm (t:aU) (word:I→L) :lJ L jK :=
 ⨅ i,ays t (ad0 i) (word i)
def oneNumerator {h} {D:jF h} (Crt:zG D) :L[X][X] :=
 Crt.numerator 0 %ₘ (D.block 0).map (cy :L →+* L[X])
abbrev oneDenominator {h} {D:jF h} (Crt:zG D) :L[X] :=
 Crt.denominator 0
theorem oneNumerator_small {h} {D:jF h} (Crt:zG D) (hh:0<h) :
  (oneNumerator Crt).natDegree<h:= by
 let H :=(D.block 0).map (cy :L →+* L[X])
 have hd:H.natDegree=h:=(natDegree_map _).trans (D.degree 0)
 have hn:H≠1 := by
  intro he
  rw [he,natDegree_one] at hd
  omega
 change (Crt.numerator 0 %ₘ H).natDegree<h
 exact (natDegree_modByMonic_lt _ ((D.monic 0).map _) hn).trans_eq hd
theorem oneNumerator_congruence {h} {D:jF h} (Crt:zG D) :
   let H :=(D.block 0).map (cy :L →+* L[X])
   let a :=(D.constant 0).map (cy :L →+* L[X]) +
     C (lz (R:=L))*(D.slope 0).map (cy :L →+* L[X])
   H∣a*oneNumerator Crt +
     C (oneDenominator Crt*lz)*(D.offset 0).map (cy :L →+* L[X]) := by
 dsimp only
 let A:=(D.constant 0).map (cy :L →+* L[X]) +
   C (lz (R:=L))*(D.slope 0).map (cy :L →+* L[X])
 have hd:=(dvd_modByMonic_sub (Crt.numerator 0)
   ((D.block 0).map (cy :L →+* L[X]))).mul_left A
 refine (dvd_iff_dvd_of_dvd_sub ?_).2 (Crt.congruence 0)
 simpa only [add_sub_add_right_eq_sub,mul_sub,oneNumerator,oneDenominator,A] using hd
def a6h {h} {D:jF h} (Crt:zG D) :kS[X] :=
 ahH (oneNumerator Crt) (oneDenominator Crt)
abbrev Lq:=MvPolynomial (Fin 3) kS[X]
def forward {h} {D:jF h} (Crt:zG D) :jK →ₐ[L] Lq :=
  MvPolynomial.aevalTower
    (((Algebra.ofId kS[X] Lq).restrictScalars L).comp
      (Polynomial.mapAlgHom (Algebra.ofId L kS)))
    (fun i:mA=>i.elim
      (c9 (cy (algebraMap L[X] kS lz)))
      (fun j=>c9 (nI j.val (a6h Crt)) +
        ∑ k :Fin 3,if k.val≤j.val then
          c9 (nI (j.val - k.val) (jH (D.block 0))) *
            lI k else 0))
def btN {h} {D:jF h} (Crt:zG D) (t:aU) :lJ L jK :=
  ((mD {((c9 (jH (D.block 0)) :Lq) ^
    (t.shape.B+t.shape.J))}).restrictScalars L).comap (forward Crt).toLinearMap
theorem mem_poleSpace {h} {D:jF h} {Crt:zG D} {t P} :
  P∈btN Crt t ↔
    (c9 (jH (D.block 0)))^(t.shape.B+t.shape.J)∣forward Crt P:= by
 simp only [btN,oq,oj,
  oy]
 rfl
def source {h} {D:jF h} (Crt:zG D) (word:I→L)
    (t:aU) (W:ℕ) :lJ L jK :=
  Aw h t W ⊓ (amm t word ⊓ btN Crt t)
def seedDerivative (a :ℕ) (P:jK) :=aox (Finsupp.single none a) P
def Yd {h} (D:jF h) (a :ℕ) (P:jK) :jK :=
 c9 ((D.block 0)^(3*a))*seedDerivative a P
def necessary {h} {D:jF h} (Crt:zG D) (word:I→L) (t:aU) :
    Submodule L jK :=
  Submodule.span L {Q | ∃ W a P,P∈source Crt word t W ∧
    W+(3*h)*a≤ cutoff t∧Q=seedDerivative a P}
def ama (t:aU) (f :ℕ→ℕ→ℕ→ℕ) :ℕ :=
  ∑ q∈range (t.shape.B+1),∑ c∈range (min q (min t.YM (t.shape.J/2))+1),
    ∑ j∈range (min (q-c) (t.shape.J-2*c)+1),f q c j
def width (t:aU) (q c j:ℕ) :ℕ :=
 t.shape.m*lV+j+2*c - 131071*q
def eMG (h:ℕ) (t:aU) :ℕ :=
 h*((t.shape.U+1)*ama t (fun q _ _=>t.shape.B+t.shape.J - q)+t.poleRank)
def contactDebit (t:aU) :ℕ:=262144*((t.shape.U+1)*t.avF)
def layerCeiling (d:ℕ) (t:aU) :ℕ :=
 (t.shape.U+1)*ama t (fun q c j=>min (width t q c j) (3*d*c))
def required (b:fO) (strong:Bool) :ℕ :=
 if strong then layerCeiling (row b).declaredHi (profile b strong)+1 else 1
end
end q7IA62d
end
section
set_option autoImplicit true
namespace qxRSHvb
noncomputable section

open P5_7_2 (fO)
open q7F2qKe (wX)



abbrev gap (b:fO) :ℕ:=lV - wX b
abbrev linearRate (b:fO) :ℚ:=1+3*262144/(gap b:ℚ)
abbrev quadraticRate (b:fO) :ℚ:=13+8*262144/(gap b:ℚ)
abbrev nativeSlope (d:ℚ) (g:ℕ) (dualWord:Bool) :ℚ :=
 d/(3*(g:ℚ))+4*g+8+(if dualWord then 1 else 0)
abbrev persistentRate (b:fO) (g:ℕ) :ℚ :=
 let alpha :ℚ:=1+2*(262144/(lV:ℚ))*wX b
 2*alpha*g+((262144-wX b:ℕ) :ℚ)/gap b-alpha
end
end qxRSHvb
end
section
set_option autoImplicit true
namespace qB9xHGe
open P5_7_2 (fO)
private def multipliers (b:fO) :List Nat := match b.val with
 | 0=>[0x2283944023f69028,0x186f4550e1b6552c,0x17b5ed448891f740,0xd581dd93deedc1,0x262fb354c88cc2]
 | 1=>[0x1b66af511117cc28,0x1ce4ea357d9dff2c,0x17aaf731717fea40,0xd59e486877e041,0x2508bc3a6e24c2]
 | 2=>[0x1a80506d5e14a028,0x1c7c531d2920402c,0x171810db2788e040,0xd33fa38e970841,0x24639ef0a6e7c2]
 | 3=>[0x19b1bf0cf2045828,0x1c085adb03d3d52c,0x168b3a3b7116e340,0xd0f7c0990d3bc1,0x23da2b106bd742]
 | 4=>[0x18c849d9606d9028,0x1ba2c6162ad5df2c,0x160368828b93ce40,0xeb1d46b425d7c1,0x2c4a362124c7c2]
 | 5=>[0x1817ad09c61f9a28,0x1b3eec192798132c,0x15808f4105309040,0xb2e01aead75841,0x332c0a5ac920c2]
 | 6=>[0x1758e686c88bab28,0x1adc95bcd026c42c,0xce496fbfff8b1,0x150236bf0e822540,0xbee6df532c4741,0x39da0f7f8cce42]
 | 7=>[0x121584202e51dc28,0x114bc470e8e3c22c,0xed7d58ae6334fc0,0x84f0750398f2c1,0x25da6acfe5b742,0x142cd42a9cdda044,0xcc8c2a73d4fec5,0x38b494ea4ed246]
 | 8=>[0xf46c16802393aa8,0x20d2d32942e8522c,0x46d375d74a6ead,0x1ede6c31048eb1,0x10ca60f22b02db40,0x32fdedf0d390c1,0x2b1ed8238451c2,0x13efc687e64f4144,0x65117d234fff45,0x384f6e4a8f7446]
 | 9=>[0x1a76947791315528,0x2912451f2779c02c,0x3803cb3747392d,0x129c2dc9b670a630,0x52fa7053960431,0x12aed1e7a4a032,0x2e9b63a9d833b5,0xb0cfb868cbd36,0xde14220bf6920c0,0x1be27efc168bc1,0x1b21855f0a9e42,0x613864bc3,0x1366b60b3b666d44,0x52b6b15c628b45,0x292aa5241c54c6]
 | 10=>[0x13fd75ae6da65f28,0x20f9bae015b4602c,0x323cfbaa2aebad,0xbe9c950135d0f30,0x45f0cc117afdb1,0xf65aea0550ab2,0x224f68a3778635,0x6edb46bac0836,0xa486d0ac02caac0,0x13ad32d91f25c1,0x174180fb284f42,0x8445f50c3,0xe7c87987c633dc4,0x3e9edcbd4cbec5,0x222da948658f46]
 | 11=>[0x129f2a2d16376c28,0x14a02a4cbdab2d2c,0x345e057dd0c92d,0x281640e240748030,0x5c4b6fcd309431,0x18423cdcb9b9b2,0x562c477c0dc35,0x97fb358d53ad4c0,0xb98bac8f3b041,0xece2bb799a942,0x4b78fa243,0xd58c9d6ea26f944,0x2927c0bbb52f45,0x1a0fd991c0c246]
 | 12=>[0x101f1eb9aa9dfc28,0x11b6948f93d7f62c,0x30d6a7f7ba44ad,0x2294c9cfeffba630,0x5602ed6a7844b1,0x169b87541b79b2,0x9be8d9b35696034,0x499f1968a62d35,0x109adfae02beb6,0x85936c5ca8c6f40,0x86f7acb36b2c1,0xd52b8ad80b8c2,0x6224a37c3,0xbbfdcab3dc9e644,0x251d7e79b9e6c5,0x181513da0cdcc6]
 | _=>[0x1c81b48bcc45da4,0xfbce1d9fb7a4128,0x11442b1402e3682c,0x2c54fa9d36342d,0x91ee614d1e22e,0x21bb9d16e7730e30,0x54f708d9623db1,0x14ffec5c2e03b2,0xb37a515aab0d2b4,0x4e7999e7ed3b35,0x1371cd634f8336,0x661057a1d04ae40,0x64c2ade72f3c1,0x3981cc00944c2,0x66ae795c3,0x8c522751f6c6b44,0x19403669e60645,0xc7af5ac6665c6]
private def packed (b:fO) :Nat := match b.val with
 | 0=>0x618510d5877ac8fa6437b854a0cbdece80fdc67754a03c910bdf1161000000061918ba7a024d52fae87d854a0cbe490b43539fa95640e3f21732225872b0216150d43208bc6f4e1830d400000033e1bdb186aa5d9dd5c5c7c3f59a000000079f5e4799c1656e85ad008000000288383faa710ffd06481d13109100000000617e9870a2d4bcd958815854a0cbd915da519a7f84295dd426724965872b021618e12295eeed3970f29e14a635ae3cff4e58fb23e836e06e5fdde4fcf7033361755867febeb7ca2625970cf2b756b2e8730f9738130b355bd9c25e70a3d71617cc1b18e58bd9ab5072c5925f359710fbbcef19d243b005b777956d19a90661757b081324ae40cafe05216d98523352a31094a7032ab952bc18ba333333461719d7812189a90cf826e147ae1c8ea07ce45c48356e82fd5d4dceae147ae2618b36fb73aea5ce0de6330ca6404e373026edea37e538c378ba9524a73570861a17cbafb849740757dcab851ec47466ab1f7ccd14177e702601d8a1eb851f61782a6af80c2e1de7fffe2f07dc034a3fc6886d482860616a2e8d2bd23c79f
 | 1=>0x618176744002c6c535bbd11745d1deb60b18a2234c22fd6e11ba64c158a669b618bf3104432d2dc910d251745d1e478da2431f78bf09f1fa1f6707e58a669b6194146ddad0d84cfdfe691745d1e71048eddf9c9c9bcfe2ab141d17a2d0e576151753767ce6d0d1514f800000033dca0337e77b4e6a5c027d39bf0000000076956e038ba2552640f7b4000000287f2fb63c05e4f6647d7525bf200000000617efaf8377cbd8fa876c11745d1da52c486bf0436378f5fcb11212d22d0e57618e491cf98ad3e2a93d63cf97bd64f5baae61a5a0bfff44580e735d62e3da56175c17e4478b8a02b69b51745d1d7f8c48ac3d30a2e9b72dfb63fc258a669b617d05970ccabca3e351331177ded9e26ed8b68c7f715c02d3488c5eb7ac2716175ee333d5aaf4d0817e65ef3e65387652b7e852483eaada38e5fd5c28f5c361721e14ea769a3b49b4cae147aec97d91ec9179a762582707e1b3266666667618b78cc614ea4f7d03b95ededee4e9b171f073b196118b1ff37c9068cf359d61a0d552367c95abc5af7a8f5c29475150304c18395457de7efe3835c28f5c361789c98f7182df80172086d678d03478b6c20173956f05de353c99fbed61bf
 | 2=>0x61821b5c5808c5117b8d4dd1745ddde66e3aa843b1b25d2797badaefa46a5c5618c4e34b9c6d0d5b804d5d1745de381a2f99abd70274ec7d4626744a46a5c561946e616a8cd646d04ab5d1745de619637b974dd94f9f88548edc70ba5e354615213d6a1b86bb3f8867c0000003352bea95ba6e10fc59becd2b349000000078ee70c5705a54145674300000002811f6030cbf3acf9460ffa9d5da8000000617f8dcd1aa2bbcbe60ac9d1745dd97b840329855c9f2f0690c90520ba5e354618ea746ef38d1d4e19b8719227263fb36020d8fbf74beeb16a78e6bc322ae4617650409e88b6c9fb0188b2bc0bd718bc063baa98497b2e77ccabb3298914b617d66359660bab1e15fb0f0f0f158f5254604da5cf61bb8a2dbde587bd80106176870ab09aad7ac4ad6b9403b9d2a93bb27c5b6e239a693de647e42e147af61729ca36e6e9894746223d70a3dc8b41a590b784b5747f2ff5bc70c47ae148618bb91de1a0a33ff64eebe31649cdc9842c5377280f087b47650fee268cf3661a033ed034493e440da06b851ec467845d2116c45cb67aa346b0ef12e147af61790abede202dd39652a11e4c610344f13958d0bc21905a9d20965f586fb59
 | 3=>0x6182724f141ec30b106bd68ba2e95cef6b3900753c8e8cd6e0491c318699500618c7e4a3162cea35cb2ae8ba2e96275b0da68163f5dee6b97d994cb869950061949cf5ab28d4147cdab68ba2e9650d75340bf2be9adf298a7d02b9cbc6a7f6152a17b8c486a80e2446c00000032c06e150a2eb2f25577d5c53e6f80000007b84da2ee0bc532387cf2c000000279f3e1fcc3fb61db444c4d48b6c8000000618028f57058ba164c57a68ba2e958ab0287295f57abbeada56100ec4bc6a7f618f0d9473e4cfd68ec8a3d350fde3080e92101b90964e957a6c61a115f578f6176e4e69226b500b2dcb995e059d63ed9d9cf993a458aeccc0502849b14314617dcec51b90b8ce839d59818182580ed58cb885ee866b7192c298e8d54732c6176fe0af81cabb8f3e2b56cea9751d2e9a8b4f7e40c5a27c144b5abb33333461731e5dd79c96f74519c570a3d7c7ef3b97c7fcf7cac7c0efe331293333334618bfedc8374a1932e9448b71d844cfd3788b0bbada12846ace2b428a9e8a10619f9ec367589227c09cf9c28f5cc5a47b4a7a8e70f45777f297b6554cccccd6179829b43262dadaf7adbd1e8a383423cd9abb1481030578f80016137cafe4
 | 4=>0x61831ba713bec921bac400236ebadda6d2e74994e03d5c9bef8d43e30666667618cdf970c90d9db64f6e8236ebae57058e39c6d15bcee206ce9032b06666676194fb5981f2e1b96c2f18236ebae91a15187c8bddbaeedbb6e33c8b126e979615342860c26793a04d7000000003873270486c02440d5564c9f690000000007e0b6b70aed85e97cf5a100000002c0d3bf62b71f78f342aa029358000000006180897c97d4bb4143cae4236ebad7c1369a987190b51e5c4b36228c126e979618f448c2e44db53427c35941291e61f59ce1e4c6ec7ce458a41837c251eb8661774e010bceb3e2b164badbc0a6555f7c97d7209a23bab0b5421d6595c28f6617e1768340ec1d9d0f245941291da42ffe6ef696d067b3127efb648251eb8661779b51d5baa9fde32a175c28f650ffcee9de87d52449e8a5299b1c28f5c296173a15b5a2296de07510689d520c72fe3f7ae8f92156790ec374fd9999999a618c468a540eb722f2996356a1edd545f0adf9bd6110981a4b4ed716dd70a3e619f128fe9f2b3aec53c5999999a53aa4610030d20563747b528276666666676179f4cd74d22d87c87dd1c2236b833f887755c29214b054b4ac39304129e42
 | 5=>0x6183c43b4a64c5e163e6eec11b765c2345fd1877ac502c57438e83469f7ceda618d401b12acd62296771ec11b7663b4b3b7f137dd6b3dcbf317999f9f7ceda61955b402f5ade0268762ec11b76675f45bc9960bdf08e84f459f7d81f7ceda6153e4225d7c766ddd8e700000003725b5213799b1e375362273380e0000000808092651d565c66d3af080000002b080c66412d9269341176d9d5c8000000061812271a87eb7ec94c822c11b7656fb54fdb6e9fc181e070b122b9809ba5e4618faad71d08d7966315485ab50fe461d006a212c134fdf0379902b39f7ceda6177e2a43b9ab17b713907d70a3dd4916ca1bcc59bd57a6e475c91c2d2b020d617e7dc426f2be23c31e7cfe8c1a5888a400c3d425046ae92139cb71e946b7661780dc271fea84fb3b1b5eb851f5032d7183290fbf849ac0265a787eb851ec6174233ef13693df99533a8f5c29467606360cf054b90762c97e08eaccccccd618c8a1525c8b36c7bf1b66f2ff1538b6376ac5ccfb157e35ac058fbd2389f1619e8bf1ee44b0032943c1eb851f51f4c66b771c53fb77194aab7155d70a3d8617a6a767f101c4e5072a37887e49030245bad823fc96052092e8ceda9be392
 | 6=>0x6185da423e30d4d626aca51f00e35fcd0b8e4f8c0c755c1acb7536b50d00410618f0ff0d72ae4a1bfe1091f00e36727bf15e62bdc2add8055d9e65f0d004106197289820b0ec807e600d1f00e36ad1cfe44b3479f9be36dcb4f3d9251eb866155f32b391082da3e3c6000000039a18ac620ba97c9d51731e88130800000082e7f11488a4661c68ab800000002c405bc999f7be3313f942d6c66980000006182f1a083ccc6710706851f00e3591949bff74726d64db5da983f6e251eb86619150d92232e5e85e41b7d752cee7bfd1f95287d2284da01a35a95ca699daa6179b83f6440bf161ce310a41f9bd5ac9f2757f9999f1a30ab322ca4a699daa6180330016b6cc8c3ab54c0048915bf1196b37b53860aaa74c88d3727f7912b617a178bc91eb1a3d604c147f6a5cf69ee6b3ce07feef97199b7045d947ae15617610535cd2a24a83abdf0a8601c84487102eeee7f0173636bc80c151eb852618e417cc0aac1f119ea763db9355700f67166c6545637b48c65f2c65285b8f619f7d8b4860bb4eda2d0ae147aed3ea4651e6a1df9246ecb03e8e766147ae2617c4e08208c1c36c8308c62550f1022ae298f6aaaa4904f87412b24b0df6b1
 | 7=>0x7a8ed232bf86e737fa579bf78985eba8f272fbfb66f26c66652aeda74cccccd7a9956b58d32f4b16b7f73f78985f1ef040f7d7509b6dbf8e6c79a474e1db017a789ce33718cde879422ff78985dfe0169f16895b804c0edea3dc784cccccd7aaba4a221ab086517f4d3f78985fb1b5ccbbe0d92b36daa5e2d1b274e1db017a73fcf78606c8a726290e34fa29dd6db6a23e8096752b2bf22409a3cee88227a812ffe2650d4d1e384024713e16317eadee6c8c875993ba6749ab7baa39967a75ddcc8450bf5f5716825defec591b8d1507dc19f2c999a664b0ea80000007a6d42c78352a28e6f2cdfae147b4bb0f2ab6ffcda18a6bdbec989ac66666677a933d34d396bf3178213839d36dd90631a18c1e07a6677acead6f1055d5d5e7a99d26797caa553aae450787878ccfb2771dc669614a655dad99cff06060617a67eac3ed047e9978a1a0ca63fe3af3655bcb244a0ab5424fc999d56c6c6c77a7cb636606c0f4016b428d3c98c88d045bc70080357c0341cc5d24678c59267a5c01e23f161367b0d1d2e44ab18b1b13d4895395d820341cc5d246799f620
 | 8=>0x7a9d60fdd7bcc975174c1f40aa13c64be6e40968c6613c570398a2b386872b17ab8cbb65fe4e6e07b279740aa13d17788cdba6f258b2e30f40e88a80e5e6947a890eb28cd0b0093a65cb40aa13bec80aecda1d6dfadd30e2663eb006872b17aa08ef0c836ce5e350e5740aa13c7cbcdb5c38428256c32149020db0e5e6947a7dcec68c36a9b7be8f0740aa13bce2ab5a775d72a5ca0f4ed6a9e706872b17a88e7ba33f2b9574085f00d76e0bd2a94a27cde30a9894c635dac5b75641c77a7e414ca4ca9c9ac67d723f7898b8898dd96c04bfbcc95e6572f0b0016872c7a7a63f4c95e8c660b1ea45f6265ade40fc155ed3ee9c6ad07acf73dae147af7a9edfb6f1e2b2afee8e3b40aa13b92ae734c1c2c99ac74e1fdef1f68e0eb297ab52daaae62b4e9cf0ad4cccccd3a343c06de4cb6f416a1ac04291b00000007a73bc5009827a9f6dcefc39d36d9f10c74358a4564c64eb443153539c0268d7a84bd584f660fa20d0dedef145e89125fe99da33633903202c12aadb622efc7a6f307bbdf01596632626bc2d020c168066708b8c32e03202c12aadb0df6b1
 | 9=>0x5520128ef27699cef37a7d56041934751c0ec2bf76e829cf3bc2cda60000000552c0bf07e10b1b069fc295604193f93850599e8b82ebb40186851629b962e65518cd336cba80023b1819560419309c74a621d7e500ca7166298a9400000005520ca4c314e9b8ee7b73d5604193545acfab71c3c3379bc8847266b3d70a3e55103b93483c7a7ac9084673692c2b87e9f70793590878a0727cae6947ae1485511969d0c5e84cea09165041893ad961795ede663eb77cf048b1c3b6862fb35510923db75c7800ccd42e9c5eeeaaee81a1fc9730a2588a93ae074d7ae147b550af96f50f0713b9dcccac4d84fa7b376cf167e19ce968135272e235c28f5d5518aa6fe6967bdd5132cf92217e2a4261cd0cb1f124369a6e3c1804a8f5c295512097cd91c7d73b33c20374bc72a53ea83c07b233f7593ac70f1e047ae1485541353cafc861acb9cb7f92217e1d1c62375a08fe5294aa533422fddc28f5d55049d8b212e0f15d43f94142dc788c122e05ba347ea901b65dd17b445d174654f69c0b55cc1385b5b7db5810628b39a634e7372457e01b65dd17b445d1746
 | 10=>0x588afdaf54b48dafb104b1bda3702fb6aeb932d8faedd7c2c89b85e2000000058953900eff09d2e9b5d8e3884b7b6eda4b4343a86b548d446bd1469fa1cac1588259585ee073e4dd9471bda3702b58a3e9d1c94b50982b50d8ecfb00000005889906172108cf2c68a89bda3702f7d3d21b92c82e4b788a684d98a9e1e1e258791dd4fd246d3652e8f9bda37025f45da95ce2d17246a57c7649c88000000587aa5e6f660752cdebd6e8a703ca7077fef477414bdc5f88e7392298091b225879a0028618675c4af4968ab8cda5083ebb987cc8fac67a3e75dfa12e147af58746f0716466170e539d1e6c7e4a189bf9cf860d2d134efe172d86fccccccd5884087298f66bb231fa61e6e1c3a37e3fd26632937ad51175458d7d765cc335885a9fcb62e6c49e1ff1b059a1523c66cbaff3f3d6b444839397d19dc28f5d62b3a5c15f36530b48f9ec4d482997c383c1274c551ff38e85119892c3299005878dfc43a540e96b0fa8a63cf54887769fe2eb0398810277c0ba387ecb3be0586834bbe82012ea66e878a0c49c0ae0592947f4109050277c0ba387e8ba2e9
 | 11=>0x4e5d03ab2670723443ba7350e560a5e5e6c6e658bcb28741c2b2d5e400000004e6401f8aae480eedc217b50e560acc16e9551767119b7bd8728f5d9fb6c6084e58d952bd405dca0171d8c2a506a337fc0e7b6db563d760d4fb218e00000004e5c8017e9306eb1e44b8b50e560a443a2a8b496bffea6b288bdfa29f3b165c4e4fce6fb2725b689a9ba0c2a5069f87b3ac7838804fb5eff02ef96000000004e4ef14b66385ef63c7e7cc2a5069fcdf7ae31ed3de6959759cce5fef3b165c4e519b4fc2345ac65538ea2c0e701f57bcc9c15d07e975e672974dda00000004e42a216baba5508983eb4c2a5069b142b06b8b70f1f7481c755769000000004e4a5365191457f2d7fa1be57f191c775cd7d15309cf54a70c74b6592d2d2d34e4401d31dfa55a63ed752d86ce8189a8c19ec94e8c243ead2c079ff0f0f0f14ec897d653f43e14482f73a4713e913f79c35107c57623413e7017e6d2d2d2e4e39c731d0140e2041b292a611970832c6d5d465f49f501db74ccd44999999a4e2e682aec42125839b4ff0fec670a8c4c399327b0ff801db74ccd449e1c30b
 | 12=>0x4e9e1199b5946fa8226bbd42c3ca2403fb42dacf6c42466e939867ba00000004ea4208ef9167a3626281ef1a9fc28edfed60537d72b16ceba2f6fe20e560424e99f4f9ebbc591e3c25a8d391fc216333b638896099d682cd6f6b81d70a3d84e9d119286e06c1cc6eb725e353fa25d87d38fb5262015ea41cc4baab851eb94e90c42b14d25684152820d391fc1ddc32c1465e227dd53f33ac4f7e66666674e8f7acd0830599bf622b0d391fc1e28e83c79bc5f8b64e1e5dfa980828d3194e92884a75ea55e510c6d41edd479dad312cfe7a945d653690ef99c466666674e837fe9e4c24ffcd039d0d391fc19947ed3c4641fd423faf2af2cd0f5c28f64e8ac005db6652e488471804d19e9af67c9ab5aa2bddd41d0da2e1e4b3804d24e83fc1cd72650d5d57511e8259695d12b49bef3621eb37304581fe78f5c290518ee18853d83a6e9a504d53ba2110567084a5721b5d82e04ca29b72e74db424e7a972a9b400e33073fff3171fe883db58ba2d8da7cd01d1c974646d1745d24e6f4257150e1281c2cf277715ce8aa42e31af2fdb99a01d1c974646d1745d2
 | _=>0x4e9de7a0baea599c51ff808f27bba3cd2eb9611897cad5d8151923c790000004ea3c9097ab0637b50c00f202752a865b5d6c3a691426633aa60269b878d4fe4e99bb10d2be459638e19ed329fea10f83824353e7bc95e9ed8b4a6f10000004e9ccb1a860056a35e71b52e147b2277c4f85c9b35e4b555718e09ac90000004e90907225ee42fa391382d329fe9d912e1748c2c5e734adb891290e90000004e8fcb327bfe424f737f61a5fcd11d5eb389cfbb4137f4a48f70729f90000004e9106c0162e47a1ce0838f28bd89fa5c84b2c7894f5c48dc25a8148a7f5e894e8a7fe4248241b9318288019ae79bb403e9236dca38a391d6887358db4b4b54e849c3700743c6fe6aef000572b9a51a9312b15a85623702590973ecc3c3c44e83b3f31a6a3b23a15e5c9177de969b2342125d65ed72eb065b91f510000004e7a6d89a7ac2ee165ebedb8428012915d538e9331eff2991bb260aeae1e1e252f436f23dca0d90c6cd5a8b62bd09b64b2c4ad556a2701cf67dacac9e4129f4e6f23c8ad6a134109fc406dae510b0f7e76ea6b9da9601cf67dacac9e4129f
def multiplierNum (b:fO) (i:Nat) (k :Fin 4) :Nat :=
 (((multipliers b).find? (fun x=>x &&& 0x7f == 4*i+k.val)).getD 0) >>> 7
def residualNum (b:fO) (o:Nat) (k :Fin 4) :Nat :=
 let off :=(![0,72,139,205] :Fin 4→Nat) k
 let width :=(![72,67,66,47] :Fin 4→Nat) k
 (packed b >>> (252*o+off)) &&& (2^width-1)
end qB9xHGe
end
