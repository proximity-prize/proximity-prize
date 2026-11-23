import ProximityPrize.SubmissionLower.P6Defs
set_option Elab.async false
open _root_ renaming Finset → zJe, Finset.mem_filter → zO0, Fintype.card → zhP, Nat.mul_le_mul_right → ztf
section
set_option autoImplicit true
namespace P6_5
noncomputable section
open Polynomial P6
structure Direction (cap:ℕ) (u:e9) (deleted:zJe I) where
  den:K[X]
  U:K[X]
  V:K[X]
  A:Fin 2→K[X]
  out:Fin 2→Fin 2→K[X]
  den_nodes : ∀ i,den.eval (node i)≠0
  U_ne :U≠0
  V_ne :V≠0
  U_dvd:U∣den
  coprime :IsCoprime U V
  phase :U*den.map twist=V*den
  degrees_eq :V.natDegree=U.natDegree
  primitive :IsCoprime (A 0) (A 1)
  height:U.natDegree+uO (A 0) (A 1)+deleted.card≤ cap
  out_degree : ∀ i j,(out i j).degree <
    (k+U.natDegree+uO (A 0) (A 1) :ℕ)
  nodes : ∀ x∉deleted,∀ i j,(out i j).eval (node x) =
    U.eval (node x)*((A i).map twist).eval (node x)*u j x -
    V.eval (node x)*(A j).eval (node x)*twist (u i x)
variable {cap A:ℕ} {u:e9} {deleted:zJe I}
def Direction.s (F:Direction cap u deleted) :=uO (F.A 0) (F.A 1)
def Direction.amp (F:Direction cap u deleted) (γ:K) :=F.A 0+C γ*F.A 1
structure Regular (F:Direction cap u deleted) (γ:K) :Prop where
  amp_ne :F.amp γ≠0
  degree_eq : (F.amp γ).natDegree=F.s
  adjacent:IsCoprime (F.amp γ) ((F.amp γ).map twist)
  content_unit :IsCoprime (F.amp γ) F.U
  node_unit : ∀ i∉deleted,(F.amp γ).eval (node i)≠0
def excluded (F:Direction cap u deleted) (Γ:zJe K) :zJe K:= by
  classical exact Γ.filter (fun γ => ¬ Regular F γ)
structure by5 (F:Direction cap u deleted) where
  G:K[X]
  L:K[X]
  monic:G.Monic
  left:G∣F.U
  right:G.map twist∣F.V
  degree_lt:L.degree<(k+F.s+G.natDegree :ℕ)
  nodes : ∀ i∉deleted,L.eval (node i)=G.eval (node i) *
    ((F.A 0).eval (node i)*u 1 i-(F.A 1).eval (node i)*u 0 i)
structure Offset (F:Direction cap u deleted) {η:K} (anchor :a9J A u η) where
  qW:K[X]
  ajX:qW.degree<k
  E :K[X]
  Q:K[X]
  E_monic:E.Monic
  left:E∣F.U
  right:E.map twist∣F.V
  proper :Q.degree<E.degree
  reduced:IsCoprime Q E
  raw:I→K
  raw_fixed : ∀ i∉deleted,twist (raw i)=raw i
  first : ∀ i∉deleted,u 0 i+η*u 1 i-anchor.decoder.eval (node i) =
    (F.amp η).eval (node i)*raw i/F.den.eval (node i)
  second : ∀ i∉deleted,u 1 i - qW.eval (node i) =
    Q.eval (node i)/E.eval (node i)+(F.A 1).eval (node i)*raw i/F.den.eval (node i)
end
end P6_5
end
section
set_option autoImplicit true
set_option maxRecDepth 12000
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
namespace P6
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem
open gR ProximityPrize.Benchmark
open yP.baR yP.a92
open scoped NNReal
theorem crX :
    (zhP I:ℝ)*(1 - radius)=(0x2be72fc0:ℝ)/4096:= by
  rw [IRSProfile.card_index]
  norm_num [radius,Xt,claimedRadius]
theorem blm {s :ℕ}
    (hs : (zhP I:ℝ)*(1 - radius)≤ s) :dw≤ s := by
  rw [crX] at hs
  have hlt: (179826:ℝ)<(0x2be72fc0:ℝ)/4096:= by norm_num
  have hn:179826<s := by exact_mod_cast hlt.trans_le hs
  exact hn
theorem a1v (u:e9) (γ:K)
    (hγ:IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius) :
    Principal.akD node (u 0) (u 1) k dw γ:= by
  let:NeZero k :=⟨by decide⟩
  exact Principal.cVE node u k dw radius
    (fun _ hT=>blm hT) γ hγ
theorem aCl (u:e9) (Γ:zJe K) (hΓ:Tt u Γ) (γ:K) (hγ:γ∈Γ) :
    Nonempty (B5 u γ) := by
  obtain ⟨S,hS,⟨P,hP,he⟩,hn⟩:=a1v u γ (hΓ γ hγ)
  exact ⟨⟨S,P,hS,hP,he,hn⟩⟩
open private ard from ProximityPrize.SubmissionLower.CP
local notation "asr" left "," right "," mant "," shift "," power "," total =>
  ard left right (z :=mant) (w:=shift) (e :=power) (s :=total) (by decide) (by decide) (by decide)
private theorem complement_pow: (0x2be72fc0:ℕ)^12800≤2^377040:= by
  have h1 : (0x2be72fc0:ℕ)^1≤0x2be72fc0*2^0:= by decide
  have h2 :=asr h1,h1,0x7877ad1b5681000,0,2,0
  have h4 :=asr h2,h2,0xe2c1a8f01645471,58,4,58
  have h8:=asr h4,h4,0xc8da80c810cfe46,60,8,176
  have MV:=asr h8,h8,0x9d9623b82fca242,60,16,412
  have h24 :=asr MV,h8,0xf7479a11135ff2c,59,24,647
  have h25:=asr h24,h1,0xa9a15a71fa9922e,30,25,677
  have h50:=asr h25,h25,0xe0ccde3ac05f774,59,50,1413
  have h100:=asr h50,h50,0xc56728d9bf339c0,60,100,2886
  have abH :=asr h100,h100,0x9837ee7106020ea,60,200,5832
  have h400:=asr abH,abH,0xb504eebd1392beb,59,400,11723
  have h800:=asr h400,h400,0xfffff35f6474749,59,800,23505
  have h1600:=asr h800,h800,0xffffe6bec9885c8,60,1600,47070
  have sJ:=asr h1600,h1600,0xffffcd7d958e865,60,3200,94200
  have h6400:=asr sJ,sJ,0xffff9afb351440b,60,6400,188460
  have h12800:=asr h6400,h6400,0xffff35f6920549a,60,12800,376980
  refine h12800.trans ?_
  calc
    0xffff35f6920549a*2^376980≤2^60*2^376980 :=
      ztf _ (by decide)
    _=2^(60+376980) :=(pow_add (2 :ℕ) 60 376980).symm
    _=2^377040:=congrArg (fun e :ℕ=>(2 :ℕ)^e) (by decide)
theorem coO :
    (0x2be72fc0:ℕ)^12800*2^6960≤0x40000000^12800:= by
  calc
    _≤(2 :ℕ)^377040*2^6960:=ztf _ complement_pow
    _=(2^30)^12800:= by simp only [← pow_mul,← pow_add]
    _=0x40000000^12800:=congrArg (fun b:ℕ=>b^12800) (by decide)
theorem cc3: (1 - Xt)^IRSProfile.repetitions≤ claimedError 6960:= by
  have hcomplement: (1 - Xt:ℝ≥0)=0x2be72fc0/0x40000000:= by
    apply NNReal.coe_injective
    have hr :Xt≤1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [ Xt,claimedRadius]
    rw [NNReal.coe_sub hr]
    norm_num [ Xt,claimedRadius]
  change (1 - Xt)^128≤ claimedError 6960
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (100:ℕ)≠0)).mp
  rw [← pow_mul,yP.C42.cFE,hcomplement]
  change ((0x2be72fc0:ℝ≥0)/0x40000000)^12800≤1/(2 :ℝ≥0)^6960
  rw [div_pow,div_le_div_iff₀ (by positivity) (by positivity),one_mul]
  exact_mod_cast coO
theorem cc2 :Xt∈Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [ Xt,claimedRadius,IRSProfile.minRelativeDistance]
theorem glY:NG+1<(0x7f000001 :ℕ)^6:= by decide
theorem b7Y: (LM+1)^2<(0x7f000001 :ℕ)^6:= by decide
theorem bXn (f w:I→YP)
    (hd: (δᵣ(w,f) :ℝ)≤ radius) :dw≤aaC f w:= by
  classical
  have hpos :0<zhP I:= by rw [IRSProfile.card_index]; decide
  have hposR: (0:ℝ)<zhP I:= by exact_mod_cast hpos
  have hradius :radius =
      1-((zhP I:ℝ)*(1 - radius))/zhP I:= by
    rw [mul_comm,mul_div_cancel_right₀ _ hposR.ne']
    ring
  have hagree :=(Code.relHammingDist_le_one_sub_div_iff hpos).mp
    (show (δᵣ(w,f) :ℝ)≤1-((zhP I:ℝ)*(1 - radius))/zhP I by
      rwa [← hradius])
  have hcard:Code.agree f w≤aaC f w:= by
    unfold Code.agree aaC
    apply Finset.card_le_card
    intro i hi
    simp only [zO0,Finset.mem_univ,true_and] at hi ⊢
    exact hi
  exact (blm hagree).trans hcard
theorem bwW (hlist:i4.axW dw LM) :
    Code.Lambda (awE :Set (I→YP)) radius≤(LM:ℕ∞) :=
  i4.bwW hlist (yP.FM.a5W ▸ b7Y.le)
    radius bXn
def a5V (U:yP.FM.bAd) :zJe K:= by
  classical
  exact Finset.univ.filter fun γ=>IsMCA (AffineLineGenerator K) IRSProfile.code γ U radius
theorem b9I
    (hscalar : ∀ u Γ,Tt u Γ→Γ.card≤NG) (U:yP.FM.bAd) :
    (a5V U).card≤NG:= by
  classical
  apply yP.FM.c8F IRSProfile.baseCode
    (⊤ : ModuleCode I K K) radius NG
    (by rw [yP.FM.a5W]; exact glY.le)
    (fun u _ Γ hΓ=>hscalar u Γ hΓ) U (by simp) (a5V U)
  intro γ hγ
  change γ∈Finset.univ.filter (fun z=>IsMCA (AffineLineGenerator K)
    IRSProfile.code z U radius) at hγ
  simp only [zO0,Finset.mem_univ,true_and] at hγ
  rw [yP.FM.c1k] at hγ
  exact hγ
theorem b8S (hscalar : ∀ u Γ,Tt u Γ→Γ.card≤NG) :
    mcaError (AffineLineGenerator K) IRSProfile.code radius ≤
      (NG:ENNReal)/(zhP K:ENNReal) := by
  classical
  refine iSup_le fun U => ?_
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  change ENNReal.ofReal (((a5V U).card:ℝ)/zhP K)≤_
  calc
    _≤ENNReal.ofReal ((NG:ℝ)/zhP K) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right (by exact_mod_cast b9I hscalar U)
        (by positivity)
    _ = _:= by
      rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]
theorem b1L :
    (NG+LM)*2 ^ 128≤(0x7f000001 :ℕ)^6:= by decide
theorem b4q (hlist:i4.axW dw LM)
    (hscalar : ∀ u Γ,Tt u Γ→Γ.card≤NG) :
    ToyProblem.certifiedGammaError IRSProfile.code Xt≤ reductionTarget := by
  have hNat :=ENat.toNat_le_of_le_natCast (bwW hlist)
  have hList :
      ((Code.Lambda (awE :Set (I→YP)) radius).toNat :ENNReal) /
        (zhP K:ENNReal)≤(LM:ENNReal)/zhP K :=
    ENNReal.div_le_div_right (by exact_mod_cast hNat) _
  have hreal: ((NG+LM:ℕ) :ℝ)/zhP K≤(1 :ℝ)/2 ^ 128:= by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    norm_num only [one_mul]
    exact_mod_cast (yP.FM.a5W ▸ b1L :
      (NG+LM)*2 ^ 128≤zhP K)
  have hENN : ((NG+LM:ℕ) :ENNReal)/zhP K ≤
      (1 :ENNReal)/2 ^ 128:= by
    have h:=ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast,ENNReal.ofReal_div_of_pos (by positivity)] at h
    simpa using h
  rw [← ENNReal.coe_le_coe,ToyProblem.coe_certifiedGammaError]
  calc
    _≤(NG:ENNReal)/zhP K+(LM:ENNReal)/zhP K :=
      add_le_add (b8S hscalar) hList
    _=((NG+LM:ℕ) :ENNReal)/zhP K:= by
      rw [← ENNReal.add_div,Nat.cast_add]
    _≤(1 :ENNReal)/2 ^ 128:=hENN
    _=(reductionTarget :ENNReal) := by
      norm_num [reductionTarget,ProximityGap.prizeThreshold]
theorem c5P (hlist:i4.axW dw LM)
    (hscalar : ∀ u Γ,Tt u Γ→Γ.card≤NG) :
    ProtocolClaim 6960 radiusNumerator radiusDenominator where
  admissible :=cc2
  reduction :=b4q hlist hscalar
  score :=cc3
end
end P6
end
