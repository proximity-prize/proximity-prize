import ProximityPrize.SubmissionLower.ZPuXYRc
set_option Elab.async false
open _root_ renaming Int.natCast_nonneg → zbO, IsFractionRing.injective → zxb, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.degreeOf_C → z6c, MvPolynomial.degreeOf_mul_le → zbF, Nat.cast_mul → z2R, Nat.le_div_iff_mul_le → z1g, Nat.mul_le_mul_right → ztf, Polynomial.C → z1z, Polynomial.map_add → zS4, Polynomial.map_mul → zNl, Submodule → zpI, Submodule.mem_bot → zLn, Submodule.span_mono → zgw
section
set_option autoImplicit true
namespace P6_7_1
noncomputable section
open Polynomial
open P6 (K p dw)
open cu (L FX Equation Jet j9 yq jz qD Vg)
open DP (jF ad0 dOu)
open qQ (zI N5 aLQ)
theorem heights (x :Input) :packetLo≤x.h∧x.h≤packetHi:= by
  obtain ⟨ha,hb⟩:=x.kA
  change (packetLo:ℤ)≤x.M.iF at ha
  change x.M.iF≤(packetHi:ℤ) at hb
  change packetLo≤x.M.iF.toNat∧x.M.iF.toNat≤packetHi
  omega
theorem poles (x :Input) :Nonempty (Poles x) := by
  let M:=x.M
  let H :=x.H
  let σ:=frobenius L p
  rcases x.bY with ⟨hm,hd,_,hm',hd',_,hcop,hnode,hdet,hdet',hmarks⟩
  let A:=j9 (M.factor*M.A₀)
  let B:=j9 (M.factor*M.A₁)
  let Q:=j9 M.Q
  have hdet0:IsCoprime (Q*A) H := by
    simpa [Q,A,H,M,j9,mul_assoc] using hdet
  have hdet1 :IsCoprime (Q.map σ*A.map σ) (H.map σ) := by
    simpa [Q,A,H,M,j9,mul_assoc,σ,zNl] using hdet'
  let D:jF x.h :=
    ⟨![H,H.map σ],![Q,Q.map σ],![A,A.map σ],![B,B.map σ],
      fun i=> by fin_cases i <;> first | exact hm | exact hm',
      fun i=> by fin_cases i <;> first | exact hd | exact hd',
      hcop,fun i=> by fin_cases i <;> first | exact hdet0 | exact hdet1⟩
  obtain ⟨crt⟩:=atp.dRH D
  refine ⟨⟨D,crt,rfl,rfl,rfl,rfl,rfl,?_,?_⟩⟩
  · intro i j
    fin_cases i
    · exact (hnode j).1
    · exact (hnode j).2
  · intro γ hγ i
    let z :=algebraMap K L (M.label γ)
    have hz :j9 (M.factor*M.wK γ)=A+(@z1z L _) z*B:= by
      simp [A,B,z,P1.FJ.wK,j9,mul_add,mul_left_comm]
    obtain ⟨h₀,h₁,hr₀,hr₁⟩:=hmarks γ hγ
    fin_cases i
    · change IsCoprime (A+(@z1z L _) z*B) H ∧
        H∣(A+(@z1z L _) z*B)*j9 (x.F.scalar γ)+(@z1z L _) z*Q
      rw [← hz]
      exact ⟨h₀,hr₀⟩
    · have hσ: (j9 (M.factor*M.wK γ)).map σ =
          A.map σ+(@z1z L _) (z^p)*B.map σ:= by
        rw [hz,zS4,zNl,Polynomial.map_C]
        rfl
      change IsCoprime (A.map σ+(@z1z L _) (z^p)*B.map σ) (H.map σ) ∧
        H.map σ∣(A.map σ+(@z1z L _) (z^p)*B.map σ)*j9 (x.F.scalar γ) +
          (@z1z L _) (z^p)*Q.map σ
      rw [← hσ]
      exact ⟨h₁,hr₁⟩
theorem necessary {x :Input} (P:Poles x) {s W} (hW:W<s.m*dw)
    {g:Jet} (hg:g∈P.rows s W) {γ:K} (hγ:γ∈x.Γ) :
    cu.rD g (x.M.label γ) (x.F.scalar γ)=0:= by
  let B:=x.F.mark γ hγ
  have hd: (j9 (x.F.scalar γ)).natDegree≤131071+x.h:= by
    rw [j9,Polynomial.natDegree_map]
    exact P6_7.aic x.F hγ
  refine atp.dPr P.crt x.word P.nodes _ _ (P.marks γ hγ) hd B.bad.support
    B.bad.dw ?_ s W hW g hg
  intro i hit
  rw [j9,ad0,Polynomial.eval_map,Polynomial.eval₂_hom,B.scalar_hits i hit]
theorem rectBank_le {x :Input} (P:Poles x) (s :Rectangle) (W:ℕ) :
    rectBank P s W≤P.rows s.box W :=
  zgw (Set.image_mono inf_le_left)
theorem rectBank_mono {x :Input} (P:Poles x) {s s' : Rectangle}
    (hm:s.m=s'.m) (hB:s.B=s'.B) (hJ:s.J=s'.J)
    (hz :s.z≤ s'.z) (ht:s.t≤ s'.t) {W W' : ℕ} (hW:W≤W') :
    rectBank P s W≤ rectBank P s' W' := by
  apply zgw (Set.image_mono ?_)
  intro g hg
  rcases SetLike.mem_coe.mp hg with ⟨hg₁,hg₂⟩
  refine ⟨dOu P.crt x.word hm hB hJ (Nat.add_le_add hz ht) hW hg₁,?_⟩
  intro j i a e he
  exact hg₂ j i a e (he.imp (lt_of_le_of_lt hz) (lt_of_le_of_lt ht))
theorem ctc (t:Test) :
    (Lc t).m=terminal.m∧(Lc t).B=terminal.B∧(Lc t).J=terminal.J ∧
      (Lc t).z≤terminal.z∧(Lc t).t≤terminal.t:= by
  rcases t with _ | ⟨i,a⟩
  · exact ⟨rfl,rfl,rfl,le_rfl,le_rfl⟩
  · by_cases h:a=0
    · rw [Lc,ite_eq_left h]
      exact ⟨rfl,rfl,rfl,min_le_left _ _,le_rfl⟩
    · rw [Lc,ite_eq_right h]
      exact ⟨rfl,rfl,rfl,le_rfl,min_le_left _ _⟩
theorem gDx {x :Input} {P:Poles x} (R:TerminalSource P) (t:Test)
    {qs :Finset zI} (geom : ∀ q∈qs,N5 q) (pass : ∀ q∈qs,FullPass P q)
    {f :Equation} (hf :aLQ qs f) :Trace P t f := by
  intro W hW g hg hn
  apply hf.divides_leading g _ hn
  intro q hq
  apply baD.proof q g _ (geom q hq)
  · have h:=(Nat.div_le_self (rectCut terminal-W) (2*x.h)).trans (Nat.sub_le (rectCut terminal) W)
    have hp:1+rectCut terminal<p:= by decide
    exact (Nat.add_le_add_left h 1).trans_lt hp
  intro a b hab
  have hpos :0<2*x.h:= by
    have h:=(heights x).1
    change 2350≤x.h at h
    omega
  have hab' : a+b≤(rectCut terminal-W)/(2*x.h) := by
    unfold powerAt at hab
    omega
  have hd:=(z1g hpos).mp hab'
  rw [Nat.mul_comm (a+b),Nat.mul_add] at hd
  have hW' : W≤ rectCut terminal:=Nat.le_sub_one_of_lt hW
  have hle :W+2*x.h*a+2*x.h*b≤ rectCut terminal:= by omega
  obtain ⟨hm,hB,hJ,hz,ht⟩:=ctc t
  exact pass q hq _ (rectBank_mono P hm hB hJ hz ht hle
    (R.shift t _ _ (R.shift t _ _ hg 0 a) 1 b))
theorem axis_degree_le {f :Equation} {a :Fin 2} {u:ℕ} (h:axisDegree f a≤u) (j:ℕ) :
    (f.coeff j).degreeOf a≤u:= by
  by_cases hj:j∈f.support
  · exact (Finset.le_sup (f := fun i=>(f.coeff i).degreeOf a) hj).trans h
  · simp [notMem_support_iff.mp hj]
theorem seedCap_lt (i:jJ) :seedCap i<p :=
  (min_le_left _ _).trans_lt (by decide)
private theorem graph_specialize (z :K) :
    (evalRingHom (jz z)).comp (Vg (F:=FX) p).toRingHom =
      qD z := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [Vg,qD]
  · intro i
    fin_cases i <;> simp [Vg,qD]
theorem native_restriction {f :Equation} (hn:f≠0) {a b:ℕ}
    (ha :a<p) (hz :axisDegree f 0≤a) (ht:axisDegree f 1≤b) :
    ∃ g:P5_7.OneSeedEquation,g≠0∧g.natDegree≤f.natDegree ∧
      P5_7.NativeSeedBound g (a+p*b) ∧ ∀ z S,P5_7.atNative g z S=yq f z S:= by
  let φ:=(Vg (F:=FX) p).toRingHom
  refine ⟨f.map φ,?_,natDegree_map_le,?_,?_⟩
  · have hl:=cu.bG0 p (by decide) (f.coeff f.natDegree)
      (by simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hn)
      ((axis_degree_le hz _).trans_lt ha)
    intro hz'
    apply hl
    have he :=congrArg (fun g:P5_7.OneSeedEquation=>g.coeff f.natDegree) hz'
    rwa [coeff_map,coeff_zero] at he
  · intro j
    rw [coeff_map]
    exact cu.b33 p a b _ (axis_degree_le hz _) (axis_degree_le ht _)
  · intro z S
    rw [P5_7.atNative,eval₂_map,graph_specialize,yq]
end
end P6_7_1
end
section
set_option autoImplicit true
namespace qxWWUna
open P6 (dw)
open P6_7_1 (afa Intro stages introductions)
open cu (Shape ku triangle)
structure Bank where
  shape :Shape
  dI:ℕ
  DG:ℕ
def free (i:afa) :Bank :=
  ⟨(stages.get i).free,(stages.get i).dI,
    (![0x164cb3986,0x21037c14f,0x59ad98b2c,0x68a452f8d,0x2097f5e9ca9] :Fin 5→ℕ) i⟩
def moving (i:afa) :Bank :=
  ⟨(stages.get i).moving,(stages.get i).dI,
    (![0xa7159e621adf0,0xfee8415076d80,0x1a756d94439f69,0x37a05020674ba3,
      0xb0eee3696695fe8] :Fin 5→ℕ) i⟩
def aux (i:Intro) :Bank :=
  ⟨(introductions.get i).2,(introductions.get i).1,
    (![0x91402bcfc,0x2e8e71d0f0,0x18be336321,0x5740c1d8ac,0x58dec5dfcd,0x82cbb8f188,
      0x1290f7f6e00,0x1391019a3e4,0x21037c14f,0x68a452f8d,0x22eac35aa64,
      0x24dcc373cb8] :Fin 12→ℕ) i⟩
def count (h:ℕ) (b:Bank) :ℕ:=b.shape.m*dw - 2*h*b.dI
def O3 (h:ℕ) (b:Bank) (mode :ℕ) :ℕ :=
  triangle b.shape.U*ku b.shape (fun q j =>
    count h b+j-q*(131071-h)-mode*(2*h*j))
def j3 (h:ℕ) (b:Bank) :ℕ:=DP.bga b.shape+2*h*b.DG
structure Tests (h:ℕ) (b:Bank) (mode :ℕ) :Prop where
  jet:b.shape.J≤b.shape.B
  seed :b.shape.B≤b.shape.U
  char :b.shape.B<K1.p
  pole :P5_7_4.poleRank b.shape≤triangle b.shape.U*agU.arY b.shape+b.DG
  width :b.shape.B*(131071-h)<count h b
  strict :j3 h b<O3 h b mode
end qxWWUna
end
section
set_option autoImplicit true
set_option maxSynthPendingDepth 8
namespace qxWWUna
noncomputable section
open P6 (K)
open P6_7_1 (Input BaseAvoid seedSpecialize)
open cu (L FX Jet)
open Polynomial
open private bEl from ProximityPrize.SubmissionLower.Q
private def seedKernel (z :K) :zpI FX Jet where
  carrier := {g | seedSpecialize g z=0}
  zero_mem' := by simp [seedSpecialize]
  add_mem' {g r} hg hr := by
    change seedSpecialize g z=0 at hg
    change seedSpecialize r z=0 at hr
    change seedSpecialize (g+r) z=0
    unfold seedSpecialize at *
    rw [zS4,hg,hr,add_zero]
  smul_mem' c g hg:= by
    change seedSpecialize g z=0 at hg
    change seedSpecialize (c•g) z=0
    unfold seedSpecialize at *
    rw [Algebra.smul_def,zNl,hg,mul_zero]
theorem exists_selected {x :Input} (V:zpI FX Jet) (D:Finset Jet)
    (hn : ∃ g∈V,g≠0) (hp : ∀ f∈D,∃ g∈V,¬ f∣g) :
    ∃ g∈V,g≠0∧BaseAvoid x V g ∧ ∀ f∈D,¬ f∣g:= by
  classical
  let:Infinite FX:=Infinite.of_injective _ (zxb L[X] FX)
  let T := {γ:K // γ∈x.Γ}
  let F := {f :Jet // f∈D}
  let test (γ:T) :=seedKernel (x.M.label γ.val)
  let tests :Option (T ⊕ F)→zpI FX V
    | none => ⊥
    | some (.inl γ)=>if V≤test γ then ⊥ else (test γ).comap V.subtype
    | some (.inr f)=>bEl V f.val
  have top (W:zpI FX V) {g:Jet} (hg:g∈V) (h: (⟨g,hg⟩:V)∉W) :W ≠ ⊤ :=
    fun he=>h (he ▸ Submodule.mem_top)
  have hb: (⊥ : zpI FX V) ≠ ⊤ := by
    obtain ⟨g,hg,hz⟩:=hn
    exact top _ hg (fun hh=>hz (congrArg Subtype.val ((zLn FX).mp hh)))
  have ht : ∀ k,tests k ≠ ⊤ := by
    intro k
    rcases k with _ | γ | f
    · exact hb
    · change (if V≤test γ then ⊥ else (test γ).comap V.subtype) ≠ ⊤
      split_ifs with h
      · exact hb
      · have hw : ∃ g∈V,g∉test γ:= by
          by_contra! hh
          exact h hh
        obtain ⟨g,hg,hh⟩:=hw
        exact top _ hg hh
    · obtain ⟨g,hg,hh⟩:=hp f.val f.property
      exact top _ hg hh
  obtain ⟨g,hg⟩:=Submodule.exists_forall_notMem_of_forall_ne_top (K:=FX) (M:=V) tests ht
  refine ⟨g.val,g.property,fun hz=>hg none ((zLn FX).mpr (Subtype.ext hz)),?_,?_⟩
  · intro γ hγ hz r hr
    let k :T:=⟨γ,hγ⟩
    by_cases h:V≤test k
    · exact h hr
    · exact (hg (some (.inl k)) (by
        change g∈(if V≤test k then ⊥ else (test k).comap V.subtype)
        rw [ite_eq_right h]
        exact hz)).elim
  · exact fun f hf hd=>hg (some (.inr ⟨f,hf⟩)) hd
end
end qxWWUna
end
section
set_option autoImplicit true
namespace qFAh60c
noncomputable section
open Polynomial
open P6 (I node dw)
open P6_7_1 (Input packetLo packetHi)
open aR (ao jF embed)
open jA
open qlc9qed (ays)
abbrev Bank :=qlc9qed.Bank
def width :Bank→ℕ
  | .cheap=>249
  | .strong=>490
def az0:Bank→ℕ
  | .cheap=>0x11df582f2a
  | .strong=>0xc0f07efa48
def rank :Bank→ℕ
  | .cheap=>37748460
  | .strong=>0x21c0b23ac9f
def cut (b:Bank) :ℕ:=b.m*dw - 1
def ambientCount (b:Bank) (h:ℕ) :ℕ :=
  (width b+1)*(az0 b+b.basePole*h)
def eMG (b:Bank) (h:ℕ) :ℕ :=
  h*((width b+1)*b.basePole+b.poleExcess)
structure OnePole (x :Input) where
  data :jF x.Γ x.F.scalar
  bY:kH data
  block :data.H=x.H
  height:data.H.natDegree=x.h
  Kw : ∀ γ,data.z γ=embed (x.M.label γ)
def Aw (b:Bank) (h t:ℕ) :zpI ao jK :=
  qlc9qed.Aw b h t ⊓
    (MvPolynomial.restrictWeightedDegree (R:=ao[X])
      (Pi.single (none :mA) 1) (width b)).restrictScalars ao
def contacts (x :Input) (b:Bank) :zpI ao jK :=
  ⨅ i:I,ays b.m (embed (node i)) (x.word i)
def pole {x :Input} (P:OnePole x) (b:Bank) :zpI ao jK :=
  NR.amn P.data P.bY b.box (jH P.data.H)
def aV {x :Input} (P:OnePole x) (b:Bank) (t:ℕ) :zpI ao jK :=
  Aw b x.h t ⊓ (contacts x b ⊓ pole P b)
def powerAt (h t:ℕ) :ℕ:=1+(cut .strong - t)/(3*h)
abbrev topCeiling:ℕ:=0x21b316316b0
theorem emz (x :Input) :packetLo≤x.h∧x.h≤packetHi:= by
  obtain ⟨hl,hh⟩:=x.kA
  change (2350:ℤ)≤x.M.iF at hl
  change x.M.iF≤(2369:ℤ) at hh
  change 2350≤x.M.iF.toNat∧x.M.iF.toNat≤2369
  omega
theorem mem_ambient {b h t F} : F∈Aw b h t ↔
    Jn b.box F∧gY F≤width b∧ahb h (t+(b.box.b+b.box.j)*h) F:= by
  have hw:width b≤b.U:= by cases b <;> decide
  simp only [Aw,Submodule.mem_inf,Submodule.restrictScalars_mem,
    qlc9qed.mem_ambient,MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
    MvPolynomial.weightedTotalDegree_piSingle,gY]
  exact ⟨fun ⟨⟨hc,_,ht⟩,hs⟩=>⟨hc,hs,ht⟩,
    fun ⟨hc,hs,ht⟩=>⟨⟨hc,hs.trans hw,ht⟩,hs⟩⟩
end
end qFAh60c
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qqW9Gbd
noncomputable section
open Polynomial
open cu (L FX Jet A5)
open DP axj
open P6_7_1 (Input Poles Rectangle seedBox rectComplete rectBank)
open private aUq cNg cEw from ProximityPrize.SubmissionLower.Z
private theorem seedCoeff_axis (i a :Fin 2) (r :ℕ) (P:qC) :
    (Bg i r P).degreeOf a≤P.degreeOf a := by
  classical
  conv_lhs=>rw [P.as_sum,map_sum]
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e he => ?_)
  have hm:MvPolynomial.monomial e (P.coeff e) =
      znf (P.coeff e)*z9v i^(e i) *
        z9v (CI i)^(e (CI i)) := by
    simp only [MvPolynomial.X_pow_eq_monomial,MvPolynomial.C_apply,
      MvPolynomial.monomial_mul_monomial,zero_add,mul_one]
    have he' : Finsupp.single i (e i)+Finsupp.single (CI i) (e (CI i))=e := by
      apply Finsupp.ext
      intro k
      fin_cases k <;> fin_cases i <;> simp [CI]
    rw [he']
  have hin:CI i≠i:= by fin_cases i <;> decide
  have hi:translation i (z9v i:qC) =
      Polynomial.X+C (z9v i) := by simp [translation,add_comm]
  have ho:translation i (z9v (CI i) :qC) =
      C (z9v (CI i)) := by simp [translation,hin]
  have hc:translation i (znf (P.coeff e))=C (znf (P.coeff e)) := by
    simp [translation,← MvPolynomial.algebraMap_eq]
  rw [hm]
  change ((translation i (_ *_ *_)).coeff r).degreeOf a≤_
  rw [map_mul,map_mul,map_pow,map_pow,hi,ho,hc,← C_pow,coeff_mul_C,
    coeff_C_mul,coeff_X_add_C_pow]
  have hcast (n:ℕ) : (n:qC).degreeOf a=0:= by
    rw [← map_natCast (znf:L →+* qC),z6c]
  have hpows (j:Fin 2) (n:ℕ) :
      ((z9v j:qC)^n).degreeOf a≤n*(if a=j then 1 else 0) := by
    simpa only [MvPolynomial.degreeOf_X] using
      MvPolynomial.degreeOf_pow_le a (z9v j:qC) n
  have hmain: (znf (P.coeff e) *
      ((z9v i:qC)^(e i-r)*(↑((e i).choose r) :qC))).degreeOf a ≤
      (e i-r)*(if a=i then 1 else 0) := by
    refine (zbF _ _ _).trans ?_
    rw [z6c,zero_add]
    refine (zbF _ _ _).trans ?_
    rw [hcast,add_zero]
    exact hpows _ _
  refine (zbF _ _ _).trans ((Nat.add_le_add hmain (hpows _ _)).trans ?_)
  refine le_trans ?_ (MvPolynomial.le_degreeOf_of_mem_support a he)
  have ha :a=i∨a=CI i:= by fin_cases a <;> fin_cases i <;> decide
  rcases ha with rfl | rfl
  · simp [Ne.symm hin]
  · simp [hin]
private theorem cleared_seedBox {h:ℕ} (D:jF h) {z t:ℕ} {Q:Source}
    (hQ:Q∈seedBox z t) (i:Fin 2) (r :ℕ) :BA D i r Q∈seedBox z t:= by
  intro j k a e he
  simp only [BA,Fg,pW,RingHom.comp_apply]
  rw [coeff_C_mul,coeff_C_mul,coeff_mul,MvPolynomial.coeff_sum]
  simp only [aXQ,coeff_map,MvPolynomial.coeff_C_mul,awz,a5F]
  apply Finset.sum_eq_zero
  rintro ⟨b,c⟩ _
  let A:=((Q.coeff j).coeff k).coeff c
  have cap (l:Fin 2) (u:ℕ) (hu : ∀ d:Fin 2 →₀ ℕ,u<d l→A.coeff d=0) :
      u<e l→(Bg i r A).coeff e=0:= by
    intro hlt
    have hb:A.degreeOf l≤u:=MvPolynomial.degreeOf_le_iff.mpr fun d hd =>
      le_of_not_gt fun hd' => MvPolynomial.mem_support_iff.mp hd (hu d hd')
    exact MvPolynomial.notMem_support_iff.mp
      (MvPolynomial.notMem_support_of_degreeOf_lt l ((seedCoeff_axis i l r A).trans_lt
        (hb.trans_lt hlt)))
  change (D.block i^(2*r)).coeff b*(Bg i r A).coeff e=0
  rcases he with he | he
  · rw [cap 0 z (fun d hd=>hQ j k c d (Or.inl hd)) he,mul_zero]
  · rw [cap 1 t (fun d hd=>hQ j k c d (Or.inr hd)) he,mul_zero]
theorem rectShift {x :Input} (P:Poles x) (s :Rectangle) (W:ℕ) (g:Jet)
    (hg:g∈rectBank P s W) (i:Fin 2) (r :ℕ) :
    A5 i r g∈rectBank P s (W+2*x.h*r) := by
  let target :=rectBank P s (W+2*x.h*r)
  have hsub:rectBank P s W≤target.comap (aUq i r) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨Q,hQ,rfl⟩
      change aUq i r (U4 Q)∈target
      have hmem:BA P.D i r Q∈rectComplete P s (W+2*x.h*r) :=
        ⟨⟨⟨ds6 P.D hQ.1.1.1 i r,
          cyS.proof x.h P.D x.word s.box Q hQ.1.1.2 i r⟩,
          bay.proof x.h P.D P.crt s.box Q hQ.1.2 i r⟩,
          cleared_seedBox P.D hQ.2 i r⟩
      have hEval :U4 (BA P.D i r Q)∈target :=
        Submodule.subset_span ⟨_,hmem,rfl⟩
      rw [cEw] at hEval
      have hn:algebraMap L[X] FX (P.D.block i^(2*r))≠0:= by
        rw [← map_zero (algebraMap L[X] FX)]
        exact (zxb L[X] FX).ne (pow_ne_zero _ (P.D.monic i).ne_zero)
      exact (target.smul_mem_iff hn).mp hEval)
  rw [← cNg]
  exact hsub hg
end
end qqW9Gbd
end
section
set_option autoImplicit true
namespace qqW9Gbd
noncomputable section
open K1 (I)
open cu (L ku)
open DP (Source Aw aq7)
open P6_7_1 (Rectangle seedBox)
abbrev stock (s :Rectangle) :=(s.z+1)*(s.t+1)
def rectAmbient (h:ℕ) (s :Rectangle) (W:ℕ) :zpI L Source :=
  Aw h s.box W ⊓ seedBox s.z s.t
def rectContacted (h:ℕ) (word:I→L) (s :Rectangle) (W:ℕ) :zpI L Source :=
  aq7 h word s.box W ⊓ seedBox s.z s.t
def contactDebit (s :Rectangle) :ℕ :=
  stock s*262144*ku s.box (fun q j=>s.m+min q s.J-(q+2*j))
def iL (h:ℕ) (s :Rectangle) :ℕ :=
  stock s*(2*h)*ku s.box (fun q _=>s.B+s.J-q)
end
end qqW9Gbd
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qUlPTla
open Finset P6_7_1
open cu (ku)
open private crN from ProximityPrize.SubmissionLower.D9
def stock (U v a :ℕ) :ℕ:=U+1-a*v
def aso (h:ℤ) (q j a :ℕ) :ℤ :=
  0x1013e9d4+j-(131071-h)*q - 2*h*((j:ℤ)+a)
def tailEnd (q a :ℕ) :ℕ:=(0x1013e9d4 - 128721*q - 29)/4699+1-a
def width (h:ℤ) (q j a :ℕ) :ℤ :=
  if q<2079∨j<tailEnd q a then aso h q j a else 0
def phase (h:ℤ) (U E v d:ℕ) :ℤ :=
  ∑ a∈range 30,(stock U v (a+d) :ℤ) *
    ∑ q∈range 2094,∑ j∈range (min q 441+1),
      if j+E*(a+d)≤q then width h q j a else 0
theorem phase_interp (h:ℤ) (U E v d:ℕ) :
    19*phase h U E v d=(2369-h)*phase 2350 U E v d+(h-2350)*phase 2369 U E v d:= by
  simp only [phase,mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j _
  by_cases hj:j+E*(a+d)≤q
  · by_cases hs :q<2079∨j<tailEnd q a <;>
      simp only [hj,hs,ite_true,ite_false,width,aso] <;> ring
  · simp [hj]
private theorem dma (h q j a :ℕ) (hh:h≤131071) :
    width h q j a≤((terminal.m*P6.dw+j-q*(131071-h)-2*h*(j+a) :ℕ) :ℤ) := by
  unfold width
  split
  · have sub_le (b c:ℕ) : (b:ℤ)-c≤((b-c:ℕ) :ℤ) := by omega
    rw [Nat.sub_sub]
    have hx :=sub_le (terminal.m*P6.dw+j) (q*(131071-h)+2*h*(j+a))
    push_cast [Nat.cast_sub hh] at hx
    change (0x1013e9d4 :ℤ)+j-((q:ℤ)*(131071-(h:ℤ))+2*h*((j:ℤ)+a))≤_ at hx
    unfold aso
    linarith only [hx]
  · exact zbO _
private def positionGain (h U E v q j:ℕ) :ℕ :=
  let g:=(q-j)/E
  let w:=terminal.m*P6.dw+j-q*(131071-h)
  (∑ a∈range g,(stock U v a-stock U v (a+1))*(w-2*h*(j+a))) +
    stock U v g*(w-2*h*(j+g))
private theorem position_bound (h U E v q j:ℕ) (hh:h≤131071)
    (he :0<E) (hq:q≤2093) (hj:j≤q)
    (hc:2093/E<30∨U+1≤30*v) :
    (∑ a∈range 30,if j+E*(a+0)≤q then
      (stock U v (a+0) :ℤ)*width h q j a else 0) -
    (∑ a∈range 30,if j+E*(a+1)≤q then
      (stock U v (a+1) :ℤ)*width h q j a else 0)≤(positionGain h U E v q j:ℤ) := by
  let g:=(q-j)/E
  let f := fun d a=>(stock U v (a+d) :ℤ)*width h q j a
  have hz (d a :ℕ) (ha :30≤a) (hg:a+d≤g) :f d a=0:= by
    rcases hc with hd | hv
    · have hg' : g≤2093/E :=Nat.div_le_div_right (by omega)
      omega
    · have hzero :stock U v (a+d)=0:=Nat.sub_eq_zero_of_le
        (hv.trans (ztf v (by omega)))
      simp [f,hzero]
  have reform (d L:ℕ) (hd : ∀ a,a<L↔a+d≤g) :
      (∑ a∈range 30,if j+E*(a+d)≤q then f d a else 0) =
      ∑ a∈range L,f d a := by
    have hdiv (a :ℕ) :j+E*(a+d)≤q↔a<L:= by
      rw [hd,z1g he,Nat.mul_comm (a+d) E]
      omega
    simp only [hdiv]
    exact (crN L 30 (fun a ha hb=>hz d a ha ((hd a).mp hb))).symm
  change (∑ a∈range 30,if j+E*(a+0)≤q then f 0 a else 0) -
    (∑ a∈range 30,if j+E*(a+1)≤q then f 1 a else 0)≤_
  rw [reform 0 (g+1) (fun a=> by omega),reform 1 g (fun a=> by omega),
    sum_range_succ,add_sub_right_comm,← sum_sub_distrib]
  simp only [positionGain,Nat.cast_add,Nat.cast_sum]
  apply add_le_add
  · apply sum_le_sum
    intro a _
    have hs :stock U v (a+1)≤ stock U v a :=
      Nat.sub_le_sub_left (ztf v (by omega)) (U+1)
    simp only [f,Nat.add_zero,← sub_mul,z2R,Nat.cast_sub hs]
    exact mul_le_mul_of_nonneg_left (dma h q j a hh) (sub_nonneg.mpr (Int.ofNat_le.mpr hs))
  · simp only [f,Nat.add_zero,z2R]
    exact mul_le_mul_of_nonneg_left (dma h q j g hh) (zbO _)
private theorem phase_swap (h:ℤ) (U E v d:ℕ) :
    phase h U E v d =
    ∑ q∈range 2094,∑ j∈range (min q 441+1),∑ a∈range 30,
      if j+E*(a+d)≤q then (stock U v (a+d) :ℤ)*width h q j a else 0:= by
  unfold phase
  simp only [mul_sum,mul_ite,mul_zero]
  rw [sum_comm]
  exact sum_congr rfl fun _ _=>sum_comm
def aV (U:ℕ) :Rectangle := {terminal with z :=U}
theorem phase_bound (h U E v :ℕ) (hh:h≤131071) (he :0<E)
    (hc:2093/E<30∨U+1≤30*v) :
    phase h U E v 0 - phase h U E v 1 ≤
      ((ku (aV U).box (positionGain h U E v) :ℕ) :ℤ) := by
  rw [phase_swap,phase_swap]
  simp only [ku,aV,Rectangle.box,Nat.cast_sum]
  rw [← sum_sub_distrib]
  apply sum_le_sum
  intro q hq
  rw [← sum_sub_distrib]
  apply sum_le_sum
  intro j hj
  exact position_bound h U E v q j hh he
    (Nat.lt_succ_iff.mp (mem_range.mp hq))
    ((Nat.lt_succ_iff.mp (mem_range.mp hj)).trans (min_le_left _ _)) hc
theorem gain_eq (h U E v :ℕ) :
    (rectGain h (aV U) 0 E v :ℤ) =
    60837*((ku (aV U).box (positionGain h U E v) :ℕ) :ℤ) := by
  simp only [rectGain,aV,amv,ku,positionGain,stock,z2R]
  rfl
theorem reflected_gain (h U E v :ℕ) :
    rectGain h {terminal with t:=U} 1 E v=rectGain h (aV U) 0 E v := by
  simp only [rectGain,aV,amv,ku,ite_eq_right (by decide : (1 :Fin 2)≠0)]
  rfl
end qUlPTla
end
