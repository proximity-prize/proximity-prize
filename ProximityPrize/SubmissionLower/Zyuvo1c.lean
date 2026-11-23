import ProximityPrize.SubmissionLower.ZEGTqPa
import ProximityPrize.SubmissionLower.Zf6e2ca
import ProximityPrize.SubmissionLower.Z8rcaBc
set_option Elab.async false
open _root_ renaming IsFractionRing.injective → zxb, MvPolynomial.eval → zY9, Nat.cast_nonneg → zqJ, Nat.le_mul_of_pos_left → zCV, RingHom.comp_apply → zQb
set_option maxHeartbeats 1200000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qINqgHe
noncomputable section
open Polynomial
open P6 (K)
open cu (L FX aZ qD)
open DP
open P6_7_1 (seedBox seedSpecialize)
open private cyS.bKs from ProximityPrize.SubmissionLower.Z
open private cSV from ProximityPrize.SubmissionLower.Z
abbrev Sl:qC →+* Source :=C.comp (C.comp C)
abbrev Bg (Q:Source) (j i a :ℕ) :qC:=((Q.coeff j).coeff i).coeff a
theorem seedCoeff_mul (d:qC) (Q:Source) (j i a :ℕ) :
    Bg (Sl d*Q) j i a=d*Bg Q j i a := by
  simp only [Bg,Sl,zQb,coeff_C_mul]
theorem seedC_dvd (d:qC) (Q:Source) :
    Sl d∣Q ↔ ∀ j i a,d∣Bg Q j i a := by
  simp only [Sl,zQb,C_dvd_iff_dvd_coeff,Bg]
theorem ambient_caps {h s W Q} (hQ:Q∈Aw h s W) (j i a :ℕ) :
    (Bg Q j i a).totalDegree≤ s.U:= by
  classical
  rw [MvPolynomial.totalDegree,Finset.sup_le_iff]
  intro e he
  exact (not_not.mp fun hn=>(MvPolynomial.mem_support_iff.mp he)
    (hQ j i a e fun he' => hn he'.2.2.1))
theorem box_caps {z t Q} (hQ:Q∈seedBox z t) (j i a :ℕ) (k :Fin 2) :
    (Bg Q j i a).degreeOf k≤(![z,t] :Fin 2→ℕ) k := by
  classical
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro e he
  have hz : ¬ (z<e 0∨t<e 1) :=
    fun hb=>(MvPolynomial.mem_support_iff.mp he) (hQ j i a e hb)
  fin_cases k
  · exact le_of_not_gt fun h=>hz (Or.inl h)
  · exact le_of_not_gt fun h=>hz (Or.inr h)
private theorem ambient_cancel {h s W d Q} (hd:d≠0)
    (hQ:Sl d*Q∈Aw h s W) :Q∈Aw h s W:= by
  classical
  intro j i a e he
  by_contra hne
  have hb:Bg Q j i a≠0:= fun hz=>hne (by
    change (Bg Q j i a).coeff e=0
    simp [hz])
  have hp:Bg (Sl d*Q) j i a≠0:= by
    rw [seedCoeff_mul]
    exact mul_ne_zero hd hb
  obtain ⟨f,hf⟩:=MvPolynomial.support_nonempty.mpr hp
  have hel:awN h s W j i a f :=
    not_not.mp fun hn=>(MvPolynomial.mem_support_iff.mp hf) (hQ j i a f hn)
  have hw:=MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)
  have hc:=ambient_caps hQ j i a
  rw [seedCoeff_mul,MvPolynomial.totalDegree_mul_of_isDomain hd hb] at hc
  exact he ⟨hel.1,hel.2.1,hw.trans (le_trans (Nat.le_add_left _ _) hc),hel.2.2.2⟩
theorem complete_cancel {h:ℕ} {D:jF h} (crt:zG D)
    (word:P6.I→L) (s :cu.Shape) (W:ℕ) {d:qC} {Q:Source}
    (hd:d≠0) (hQ:Sl d*Q∈complete crt word s W) :
    Q∈complete crt word s W:= by
  rcases SetLike.mem_coe.mp hQ with ⟨⟨ha,hp⟩,hc⟩
  refine ⟨⟨ambient_cancel hd ha,?_⟩,?_⟩
  · intro k a i j e he
    have hz :Bg (Km (ad0 k) (word k) (Sl d*Q)) j i a=0 :=
      MvPolynomial.ext _ _ fun f=> by simpa [Bg,Fg] using hp k a i j f he
    rw [map_mul,cyS.bKs,seedCoeff_mul] at hz
    simpa [Fg] using congrArg (fun T:qC=>T.coeff e)
      ((mul_eq_zero.mp hz).resolve_left hd)
  · change _∣forward crt (Sl d*Q) at hc
    change _∣forward crt Q
    have hf :forward crt (Sl d)=pW (C (algebraMap qC aQ d)) :=
      cSV crt d
    rw [map_mul,hf] at hc
    have hn:algebraMap qC aQ d≠0 :=
      by simpa only [map_zero] using (zxb qC aQ).ne hd
    have hu:IsUnit (pW (C (algebraMap qC aQ d)) :US) :=
      (isUnit_iff_ne_zero.mpr hn).map (pW.comp C)
    exact hu.dvd_mul_left.mp hc
theorem box_cancel {z t d Q} (hd:d≠0)
    (hQ:Sl d*Q∈seedBox z t) :Q∈seedBox z t:= by
  classical
  intro j i a e he
  by_contra hne
  have hm:e∈(Bg Q j i a).support :=MvPolynomial.mem_support_iff.mpr hne
  have hz :=box_caps hQ j i a
  rw [seedCoeff_mul] at hz
  have hcap k :e k≤(![z,t] :Fin 2→ℕ) k := by
    have hk :=hz k
    rw [MvPolynomial.degreeOf_mul_eq (n:=k) hd (MvPolynomial.support_nonempty.mp ⟨e,hm⟩)] at hk
    exact (MvPolynomial.le_degreeOf_of_mem_support k hm).trans ((Nat.le_add_left _ _).trans hk)
  exact he.elim (not_lt_of_ge (hcap 0)) (not_lt_of_ge (hcap 1))
theorem physical_seed_zero {Q:Source} {z :K}
    (hz :seedSpecialize (U4 Q) z=0) (j i a :ℕ) :
    zY9 (Z7 z) (Bg Q j i a)=0:= by
  let f :L[X] →+* FX:=algebraMap L[X] FX
  let ev :qC →+* L:=zY9 (Z7 z)
  let g:qC[X] →+* aZ :=
    Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap L FX)) (MvPolynomial.C (f Polynomial.X))
  have hb: (qD z).comp g=f.comp (Polynomial.mapRingHom ev) := by
    apply Polynomial.ringHom_ext
    · intro b
      have he : (qD z).comp (MvPolynomial.map (algebraMap L FX))=(f.comp C).comp ev := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [qD,zQb,f,ev]
          rfl
        · intro k
          fin_cases k <;> simp [qD,Z7,cu.jz,f,ev]
      simpa [g] using DFunLike.congr_fun he b
    · simp [g,qD]
  have he :=congrArg (fun T:qQ.IW=>(T.coeff j).coeff i) hz
  simp only [seedSpecialize,Polynomial.coe_mapRingHom,Polynomial.coeff_map,U4,
    Polynomial.coeff_mapAlgHom_apply,coeff_zero] at he
  change ((qD z).comp g) ((Q.coeff j).coeff i)=0 at he
  rw [hb] at he
  have h:=(map_eq_zero_iff f (zxb L[X] FX)).mp he
  simpa [ev,Bg] using congrArg (fun T:L[X]=>T.coeff a) h
end
end qINqgHe
end
section
set_option autoImplicit true
namespace qrT6Ada
noncomputable section
open P6_7_1 (Origin introCap lastOrigin lineFee)
open q3rjQGe
open TD (GM FP)
open scoped BigOperators
def a (_:Origin) (_:Free) :ℚ:=38740117
def b (_:Origin) (_:Free) :ℚ:=4640
def digit (w n i:ℕ) :ℕ:=n/2^(w*i) % 2^w
def rectDigits (o:Origin) :ℕ :=
  ([0x68958c2575611382e8,0x85cde3a5f439e80000002,0xaee9ef9e1af7f20000002,
    0x8093dda6f3aeb60000002,0x774dd76a2603100000002,0x7c54b0285b66300000002,
    0x5fb817f28dc6680000002,0x6c4cf82e11e7300000002,0xe0c902dfe280b06cf0,
    0x951145e77c00df5693,0x5a25c1f48a19900000002,0x6961be6f1c33f40000002,
    0x8be68be4ca43b80000002] :List ℕ).get o
def residualDigits (o:Origin) :ℕ :=
  ([0x30b600036b41af4f802d36071aca120d66e0889,0xe67face8082c36f95fc13306af957919db50b393c,0x12d50fd98067b8ea5470113755877d8df9206bb970,
    0xdd7eb898086339003b81370a24f9e5214466ffe38,0xcd8517d009136f6a1cc1475d0afc0d390189aac0c,0xd62de33008b0ae6260c13e22d62cd92bb3c16bc4c,
    0xa4e420f00ae2c75a6fc172a84473d5776d1c37a3c,0xba90973809eb9ae980c15b8fd97be95620b428e4c,0x30b60003c7e245274071544f69ca8263ec1d434,
    0x30b60004c3069275008eb8652392a4392eb3650,0x9b4b0ac80b503cc26cc17ce2876369862c114210c,0xb58960c00a24f2b1354160eb7f48db5dda517df14,
    0xf10026c007ec0dd649c12e5844af3d113692525dc] :List ℕ).get o
def jumpDigits (o:Origin) :ℕ :=
  ([0x2e576c796c4428e645b753852098cbdde11169,0x9e940326cb56b52b5d64d9a464ed13cd1a600b,0x0,
    0x5c61b2ddb78400000000000000000000000000,0x99fc477406a6016b3faa739fae,0xa4edef77f3000000000000000000000000000,
    0x4e77da084ae973b64aa2c772c34218fdfc7a5d,0x399fd157938c00000000000000000000000000,0x0,
    0x0,0x7b216ecb43cdbac3590bac0c1c1249a80758f,0x0,
    0x0] :List ℕ).get o
abbrev dualNum0:ℕ:=0x1631423a5ab371
abbrev dualNum1 :ℕ:=0x7d7425136805
abbrev dualNum2 :ℕ:=0x76cc34fc661
def zN (o:Origin) :ℕ:=digit 29 (rectDigits o) 0
def arN (o:Origin) :ℕ:=digit 29 (rectDigits o) 1
def brN (o:Origin) :ℕ:=digit 29 (rectDigits o) 2
def z (o:Origin) :ℚ:=zN o
def ar (o:Origin) :ℚ:=arN o
def br (o:Origin) :ℚ:=(brN o:ℚ)/32
def residualN (o:Origin) (k :Fin 4) :ℕ:=digit 45 (residualDigits o) k.val
def residual (o:Origin) :GM:= fun k=>residualN o k
def jumpN (o:Origin) (j:Fin 3) :ℕ:=digit 53 (jumpDigits o) j.val
def a4Q (o:Origin) (j:Fin 3) :ℚ:=jumpN o j
def freeDual:GM := ![(dualNum0:ℚ)/500,(dualNum1 :ℚ)/500,(dualNum2 :ℚ)/200,0]
theorem freeDual_nonneg (k :Fin 4) :0≤freeDual k := by
  fin_cases k
  · exact div_nonneg (zqJ dualNum0) (by decide : (0:ℚ)≤500)
  · exact div_nonneg (zqJ dualNum1) (by decide : (0:ℚ)≤500)
  · exact div_nonneg (zqJ dualNum2) (by decide : (0:ℚ)≤200)
  · exact le_rfl
def freePart (o:Origin) (s :bAL) :GM :=
  if o=0∧s=termStop then freeDual else 0
def a3D (o:Origin) (s :bAL) :GM:=residual o+freePart o s
def globalRate (k :Fin 4) :ℚ:=SS 0 termTrial k+SS 2 termTrial k
def corePrice (o:Origin) (s :bAL) :GM :=
  Fin.cases (rankPrice o) (Fin.lastCases
    (fun k=>(z o+ar o+1)*axisWeight k+br o*SS 1 termTrial k)
    (fun i:Free=> fun k=>a o i*SS 0 i.castSucc k+b o i*SS 1 i.castSucc k)) s
def unit (o:Origin) (j:Fin 3) :ℚ :=
  ∑ k :Fin 4,residual o k*(mixedCols (originShape o) k j:ℚ)
def iL (o:Origin) (j:Fin 3) :ℚ :=
  ∑ i:Origin,if i≤o then a4Q i j else 0
def factorBook :ℚ := ∑ i:Origin,∑ j:Fin 3,a4Q i j*(introCap i.val j:ℚ)
def freeBook :ℚ:=FP freeDual (allFreeCap 0)
def globalBook :ℚ:=FP globalRate initialBound
def Absorbs :Prop :=
  ∀ v :Fin 3→ℕ,(∀ j,v j≤ introCap lastOrigin.val j) →
    v 1≤v 0→0<v 1→0<v 2 →
    (lineFee (v 0) (v 1) (v 2) :ℚ)+FP (residual lastOrigin) (kK v (asShape v)) ≤
      ∑ j,unit lastOrigin j*(v j:ℚ)
end
end qrT6Ada
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qHuUuEa
noncomputable section
open P6 (K I p dw blockLength)
open P5_7 (midAgreement farAgreement)
open P6_7_1 (Input degree heights)
open q3rjQGe (persistentRate linearRate gap)
open DQ (Ag)
open axI (c7Q)
open P5_7_7 (UJ hit mem_sites linear_count)
open private OF OF.mk ceY qTOdRca.rho aaM gAN from ProximityPrize.SubmissionLower.Zf6e2ca
open private cK1 cK2 cK3 from ProximityPrize.SubmissionLower.CR
open private hitmiss_pair from ProximityPrize.SubmissionLower.Zz5zkKe
open Finset Polynomial
open scoped Classical
private theorem degree_le (x :Input) {γ:K} (hγ:γ∈x.Γ) :
    (x.F.scalar γ).natDegree≤degree :=
  (P6_7.aic x.F hγ).trans (Nat.add_le_add_left (heights x).2 _)
theorem persistent {x T J Q e H} (he :0<e) (heP:e<p)
    (A:DescendedMarks x T J Q e H) : (T.card:ℚ)≤persistentRate e*H+e := by
  obtain ⟨U,hU,hexc,n,⟨bY⟩⟩:=c7Q T x.M.label x.F.scalar J e H he heP
    A.curve (fun _ _ _ _ h=>sub_left_inj.mp h) A.marks
  have hw:OF x.M.word U x.F.scalar degree := by
    refine OF.mk (x.F.distinct.mono (hU.trans A.subset))
      (fun γ hγ=>degree_le x (A.subset (hU hγ))) ?_
    intro γ hγ
    let m:=x.F.mark γ (A.subset (hU hγ))
    exact ⟨m.bad.support,(by decide :midAgreement≤dw).trans m.bad.dw,
      m.scalar_hits⟩
  have hu:=ceY bY hw he (by decide) (by decide)
  have heQ: (1 :ℚ)≤e := by exact_mod_cast he
  have hx : ((T \ U).card:ℚ)≤(Ag e :ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card:ℚ)=((T \ U).card:ℚ)+(U.card:ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _≤(Ag e :ℚ)*H+((2*aaM*degree*(Ag e :ℚ)+qTOdRca.rho degree)*H+1) :=
      add_le_add hx hu
    _≤(Ag e :ℚ)*H+((2*aaM*degree*(Ag e :ℚ)+qTOdRca.rho degree)*H+e) :=
      add_le_add le_rfl (add_le_add le_rfl heQ)
    _=persistentRate e*H+e := by
      rw [gAN he]
      unfold persistentRate qTOdRca.rho
      ring
private theorem count {w:I→K} {T:Finset K} {z :K→K} {s :K→K[X]} {H :ℕ}
    (M:UJ degree w T z s)
    (hsite : ∀ i,(T.filter fun γ=>hit w s γ i).card≤H ∨
      (T.filter fun γ => ¬ hit w s γ i).card≤H) :
    (T.card:ℚ)≤linearRate*H+1 := by
  by_cases hz :H=0
  · have hone :T.card≤1 := by
      by_contra! h
      obtain ⟨a,ha,b,hb,hab⟩:=one_lt_card.mp h
      have hc:=hitmiss_pair M ha hb hab
      obtain ⟨i,hi⟩:=card_pos.mp ((by decide :0<P5_7.gap degree).trans_le hc)
      obtain ⟨hi₁,hi₂⟩:=mem_sdiff.mp hi
      rcases hsite i with hw | hm
      · rw [hz] at hw
        exact (Nat.not_lt_zero _) ((card_pos.mpr ⟨a,mem_filter.mpr ⟨ha,mem_sites.mp hi₁⟩⟩).trans_le hw)
      · rw [hz] at hm
        exact (Nat.not_lt_zero _) ((card_pos.mpr ⟨b,mem_filter.mpr ⟨hb,
          fun hh=>hi₂ (mem_sites.mpr hh)⟩⟩).trans_le hm)
    simpa only [hz,Nat.cast_zero,mul_zero,zero_add] using (show (T.card:ℚ)≤1 by exact_mod_cast hone)
  have h:=linear_count M (Nat.pos_of_ne_zero hz) (by decide) hsite
  have hmul :T.card*gap≤blockLength*H := by
    rw [Nat.mul_comm T.card]
    exact (Nat.mul_le_mul_right _ (by decide :gap≤P5_7.gap degree)).trans h
  have hgap: (0:ℚ)<gap:=Nat.cast_pos.mpr (by decide)
  have hT: (T.card:ℚ)≤(blockLength:ℚ)/gap*H := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hgap).mpr (by exact_mod_cast hmul)
  refine hT.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
  apply mul_le_mul_of_nonneg_right _ (zqJ H)
  rw [linearRate,mul_div_assoc]
  have hn:0≤(blockLength:ℚ)/gap:=div_nonneg (zqJ _) hgap.le
  linarith only [hn]
theorem linear {x T J Q H} (A:DescendedMarks x T J Q 1 H) :
    (T.card:ℚ)≤linearRate*H+1 := by
  obtain ⟨hJ,C₀,hC₀,hseed,hsf,hs,hyf,hy⟩:=A.curve
  let:Fact (Irreducible C₀) :=⟨hC₀⟩
  obtain ⟨R⟩:=cK1 C₀ J 1 hJ hseed hsf hs Nat.one_pos
  obtain ⟨n,B,t,hbase,_,hroots⟩:=cK2 C₀ J 1 R T x.M.label x.F.scalar A.marks
  have hH :=cK3 C₀ J 1 H n R B Nat.one_pos hyf hy
  have M:UJ degree x.M.word T x.M.label x.F.scalar := by
    refine ⟨fun _ _ _ _ h=>sub_left_inj.mp h,x.F.distinct.mono A.subset,
      fun γ hγ=>degree_le x (A.subset hγ),?_⟩
    intro γ hγ
    let m:=x.F.mark γ (A.subset hγ)
    exact (by decide :farAgreement≤dw).trans
      (m.bad.dw.trans (card_le_card fun i hi=>mem_sites.mpr (m.scalar_hits i hi)))
  exact count M (qo38hre.sections B hH M.Kw hbase hroots x.M.word)
end
end qHuUuEa
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qHuUuEa
noncomputable section
open P6 (K p)
open P6_7_1 (Input Poles)
open q3rjQGe (FreeRateOK NativeOK graphRate nativeRate nativeSlope quadraticRate marks onCurves)
open cu (L qD)
open gT (Ambient kM)
open pI (by6)
open YY (bAG xg Si by9 aef a9E)
open private cag c2p ddj c0U b1I diE from ProximityPrize.SubmissionLower.G
open private mix mix_zero ePj from ProximityPrize.SubmissionLower.ZzWMDba
open Finset
open scoped Classical
def c1 :Prop :=
  ∀ (x :Input) (_P:Poles x) (T:Finset K) (J:Ideal kM)
    (Q:MvPolynomial (Fin 2) L) (H :ℕ),DescendedMarks x T J Q 2 H →
    (T.card:ℚ)≤16*(2*(Q.totalDegree :ℚ))+quadraticRate*H+2
def c2 :Prop :=
  ∀ (x :Input) (_P:Poles x) (T:Finset K) (J:Ideal kM)
    (Q:MvPolynomial (Fin 2) L) (e H g c W M:ℕ),DescendedMarks x T J Q e H →
    3≤e→NativeOK e g c W M →
    (T.card:ℚ)≤nativeSlope Q.totalDegree e*((e :ℚ)*Q.totalDegree) +
      nativeRate e g c W*H+e
private theorem rated_descended (h1 :c1) (h2 :c2)
    {x :Input} (P:Poles x) {T:Finset K} {J Q e H} (A:DescendedMarks x T J Q e H)
    (he :0<e) {d a b:ℚ} (hr :FreeRateOK d a b) (hd: (Q.totalDegree :ℚ)≤d)
    (direct : (T.card:ℚ)≤((p+1 :ℕ) :ℚ)*Q.totalDegree) :
    (T.card:ℚ)≤a*((e :ℚ)*Q.totalDegree)+b*H+e := by
  have ha :0≤a :=hr.1.trans ((le_max_left _ _).trans hr.2.2.1)
  have hH : (0:ℚ)≤H :=zqJ _
  have hE : (0:ℚ)≤e :=zqJ _
  have hmass :0≤(e :ℚ)*Q.totalDegree :=mul_nonneg hE (zqJ _)
  have hdir : (T.card:ℚ)≤graphRate e*((e :ℚ)*Q.totalDegree) := by
    rw [← mul_assoc,graphRate,div_mul_cancel₀ _ (Nat.cast_pos.mpr he : (0:ℚ)<e).ne']
    exact direct
  by_cases h:a<graphRate e
  · rcases hr.2.2.2.2 e he h with hb | hb | hb | hb
    · have heP:e<p:=(zCV e A.plane_pos).trans_lt A.seed_lt
      exact mix_zero ha h hH hE hdir (persistent he heP A) hb
    · obtain ⟨rfl,hb⟩:=hb
      exact mix_zero ha h hH hE hdir (linear A) hb
    · obtain ⟨rfl,ha₀,hb⟩:=hb
      exact mix ha₀ h hH hE hdir (h1 x P T J Q H A) hb
    · obtain ⟨he₃,g,c,W,M,hw,ha₀,hb⟩:=hb
      have hs :nativeSlope Q.totalDegree e≤nativeSlope d e := by
        unfold nativeSlope
        exact add_le_add (add_le_add
          (div_le_div_of_nonneg_right hd (mul_nonneg (by norm_num) hE)) le_rfl) le_rfl
      have hone :=(h2 x P T J Q e H g c W M A he₃ hw).trans
        (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hs hmass) le_rfl) le_rfl)
      exact mix ha₀ h hH hE hdir hone hb
  · exact hdir.trans ((mul_le_mul_of_nonneg_right (le_of_not_gt h) hmass).trans
      ((le_add_of_nonneg_right (mul_nonneg hr.2.2.2.1 hH)).trans (le_add_of_nonneg_right hE)))
private theorem fTy (h1 :c1) (h2 :c2)
    (x :Input) (P:Poles x) {I:Ideal Ambient} (geom:by6 I)
    {d a b:ℚ} (hr :FreeRateOK d a b) (hD: (aef I:ℚ)≤d) :
    ((marks x I).card:ℚ)≤(a+1)*aef I+b*a9E I:= by
  let T:=marks x I
  let D:=aef I
  let H :=a9E I
  have ha :0≤a :=hr.1.trans ((le_max_left _ _).trans hr.2.2.1)
  have hdP:D <p:= by exact_mod_cast hD.trans_lt hr.2.1
  have slice :bAG I:=⟨geom.1,geom.2.1,geom.2.2.1,geom.2.2.2.1⟩
  obtain ⟨f,hf,hI,hpos,hdeg⟩:=GK.proof I slice
  have hdegQ: (f.totalDegree :ℚ)≤D:=Nat.cast_le.mpr hdeg
  have hlabels : ∀ z∈T.image x.M.label,qD z f=0:= by
    intro z hz
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hz
    apply c2p (mem_filter.mp hγ).2
    rw [hI]
    exact Ideal.mem_span_singleton_self f
  have hcard: (T.image x.M.label).card=T.card :=
    card_image_of_injective _ (fun _ _ h=>sub_left_inj.mp h)
  change (T.card:ℚ)≤(a+1)*D+b*H
  suffices h: (T.card:ℚ)≤a*D+b*H+D by
    calc _≤_:=h
         _ = _:= by ring
  by_cases hc:by9 (xg I)
  · obtain ⟨Q,hQ,hIQ⟩:=hc
    have hde :=b1I f hf.ne_zero Q (hI.symm.trans hIQ)
    obtain ⟨e,he,hcurve,hmass⟩:=ePj I Q slice geom.2.2.2.2 hQ hIQ
    have hmarks :DescendedMarks x T (Si I) Q e H :=
      ⟨filter_subset _ _,hcurve,hQ,hIQ,hde ▸ hpos,hmass.trans_lt hdP,
        fun _ hγ=>cag (mem_filter.mp hγ).2⟩
    have hdir :=ddj f hf.ne_zero (hdeg.trans_lt hdP)
      (T.image x.M.label) hlabels
    rw [hcard,hde] at hdir
    have htotal:=rated_descended h1 h2 P hmarks he hr
      ((show (Q.totalDegree :ℚ)≤D from hde ▸ hdegQ).trans hD) (by exact_mod_cast hdir)
    have hmassQ: (e :ℚ)*Q.totalDegree≤D:= by
      rw [mul_comm]
      exact_mod_cast hmass
    have heQ: (e :ℚ)≤D :=
      Nat.cast_le.mpr ((zCV e hmarks.plane_pos).trans hmass)
    exact htotal.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hmassQ ha) le_rfl) heQ)
  · have hm:=c0U p f hf (hI ▸ hc) (T.image x.M.label) hlabels
    rw [hcard] at hm
    have hq: (T.card:ℚ)≤(f.totalDegree :ℚ)^2 := by exact_mod_cast hm
    have hfa : (f.totalDegree :ℚ)≤a :=(hdegQ.trans hD).trans
      ((le_max_left _ _).trans hr.2.2.1)
    calc
      _≤(f.totalDegree :ℚ)^2 :=hq
      _≤a*D:= by rw [pow_two]; exact mul_le_mul hfa hdegQ (zqJ _) ha
      _≤_:=le_add_of_nonneg_right (mul_nonneg hr.2.2.2.1 (zqJ _)) |>.trans
        (le_add_of_nonneg_right (zqJ _))
theorem of_children (h1 :c1) (h2 :c2) :q3rjQGe.c4 := by
  intro x P C d a b hr hC
  have hs :onCurves x C=C.qv.biUnion (marks x) := by
    ext γ
    constructor
    · intro h
      obtain ⟨hγ,I,hI,hm⟩:=mem_filter.mp h
      exact mem_biUnion.mpr ⟨I,hI,mem_filter.mpr ⟨hγ,hm⟩⟩
    · intro h
      obtain ⟨I,hI,hm⟩:=mem_biUnion.mp h
      exact mem_filter.mpr ⟨(mem_filter.mp hm).1,I,hI,(mem_filter.mp hm).2⟩
  have hsum : ∑ I∈C.qv,aef I=C.cost 0:=rfl
  have hsumH : ∑ I∈C.qv,a9E I=C.cost 1 :=rfl
  rw [hs]
  calc
    _ ≤ ∑ I∈C.qv,((marks x I).card:ℚ) :=diE _ _
    _ ≤ ∑ I∈C.qv,((a+1)*aef I+b*a9E I) := by
      apply sum_le_sum
      intro I hI
      have hD:aef I≤C.cost 0 :=
        hsum ▸ single_le_sum (fun _ _=>Nat.zero_le _) hI
      exact fTy h1 h2 x P (C.geometric I hI) hr ((Nat.cast_le.mpr hD).trans hC)
    _ = _:= by simp only [sum_add_distrib,← mul_sum,← Nat.cast_sum,hsum,hsumH]
end
end qHuUuEa
end
