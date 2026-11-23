import ProximityPrize.SubmissionLower.ZffaUPa
set_option Elab.async false
section
set_option autoImplicit true
namespace qNRjwze
noncomputable section
open P6 (K p)
open P6_7 (RectTail)
open P6_7_2
open P6_7_2_3
open cu (Jet rD)
open DP (Source complete U4)
open gT (Ambient)
open pI (xN oU)
open P5_7_1 (wD)
open akZ (btm)
abbrev anchorRow {b:RectTail} {h rows} (pick :Picks (b:=b) h rows) :=pick.freeRow 0
def Mark {b:RectTail} (x :Input b) (f :Jet) (γ:K) :Prop :=
  rD f (x.M.label γ) (x.F.scalar γ)=0
abbrev aV {b:RectTail} {x :Input b} (P:Poles x) (i:Aux) :=
  P.rows (auxiliary b i) (cutoff x.h 0 (auxiliary b i))
structure Reference {b:RectTail} {x :Input b} (P:Poles x) where
  raw:Source
  mem:raw∈complete P.crt x.word (auxiliary b 9) (cutoff x.h 0 (auxiliary b 9))
  nonzero :U4 raw≠0
abbrev LineRow :=MvPolynomial (Fin 3) cu.FX
def LineCaps (f :Jet) (g:LineRow) :Prop :=
  ∀ e∈g.support,e 1+e 2≤wD f 0∧e 2≤wD f 1∧e 0≤wD f 2
def LineRoot {b:RectTail} (x :Input b) (g:LineRow) (γ:K) :Prop :=
  ∃ z :cu.L,
    let v := ![algebraMap cu.L cu.FX z,cu.kr (x.F.scalar γ),
      cu.kr (x.F.scalar γ).derivative]
    MvPolynomial.eval v g=0∧MvPolynomial.eval v (MvPolynomial.pderiv 2 g)≠0
structure LastCut {b:RectTail} (x :Input b) (gH :Finset K) (f :Jet) where
  cut:Jet
  proper : ¬ f∣cut
  line :Bool
  row:LineRow
  caps :oU cut (if line then btm f else topCut b (wD f))
  separant:line=true→cut=f.derivative
  line_caps :line=true→LineCaps f row
  line_pos :line=true→0<wD f 2
  Eh : ∀ γ∈x.Γ,Mark x f γ →
    γ∈gH∨Mark x cut γ∨(line=true∧LineRoot x row γ)
def massCap:RectTail→Fin 4→ℕ
  | .pruned => ![8395,142162,679177,5128992]
  | .tailOne => ![8395,130972,622854,4359826]
  | .tailTwo => ![8395,123306,584565,3862406]
  | .tailThree => ![8395,117001,553229,3471117]
def projectionFee (b:RectTail) :ℕ:=(p+1)*massCap b 2+massCap b 3+massCap b 0
abbrev akj:ℕ:=0x471c0984879
def eHB:RectTail→ℕ
  | .pruned=>0xb9722833796c
  | .tailOne=>0xb584edae171a
  | .tailTwo=>0xb2e5be7ea8ed
  | .tailThree=>0xb0461a8c6f29
def au1 (b:RectTail) :ℕ:=ee3 b-(eHB b+akj+projectionFee b)
structure Parents {b:RectTail} (x :Input b) (D:Finset Jet) (cut:Jet→Jet) where
  parents :Jet→Finset (Ideal Ambient)
  gH :Finset K
  paid_bound:gH.card≤projectionFee b
  geometric : ∀ f∈D,∀ q∈parents f,
    xN q∧q.height=2∧gT.iJ f∈q∧gT.iJ (cut f)∈q
  disjoint : ∀ f∈D,∀ g∈D,f≠g→Disjoint (parents f) (parents g)
  Eh : ∀ f∈D,∀ γ∈x.Γ,Mark x f γ→Mark x (cut f) γ →
    γ∈gH ∨ ∃ g∈D,∃ q∈parents g,gT.IZ q (x.M.label γ) (x.F.scalar γ)
end
end qNRjwze
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace q7Huoga
noncomputable section
open Finset
open P6_7 (RectTail)
open P6_7_2 P6_7_2_3
open cu (Jet Shape)

open pI (oU)
open TD (auN arC J2)
open akZ (bCj btm bKa caQ aHP cfi)
open P5_7_1 (wD)
open scoped Classical
open private a8m from ProximityPrize.SubmissionLower.CR
open private b6z from ProximityPrize.SubmissionLower.D7
variable {b:RectTail} {x :Input b} {P:Poles x} {pick} (O:OriginCover P pick)
theorem spend_cap {f :Jet} (hf :f∈O.factors) (j:Fin 3) :
    wD f j≤ introCap b (O.origin f) j :=
  (single_le_sum (f := fun g=>wD g j) (fun _ _=>Nat.zero_le _)
    (show f∈O.factors.filter (fun g=>O.origin f≤O.origin g) from
      mem_filter.mpr ⟨hf,le_rfl⟩)).trans (O.nested _ j)
theorem origin_J (b:RectTail) (o:Origin) : (originShape b o).J≤(originShape b o).B:= by
  cases b <;> fin_cases o <;> decide
theorem ref_J (b:RectTail) (o:Origin) : (refShape b o).J≤(refShape b o).B:= by
  have h:introCap b o 1≤ introCap b o 0:= by cases b <;> fin_cases o <;> decide
  exact max_le_max (origin_J b o) h
theorem cut_origin {f :Jet} (hf :f∈O.factors) :
    oU (O.cut f) (originShape b (O.origin f)) := by
  have h:=O.cut_caps f hf
  by_cases hl:O.line f=true
  · have ho:=(O.line_pos f hf hl).1
    have hc (j:Fin 3) :introCap b last j≤auN (originShape b last) j:= by
      have he :originShape b last=topCut b (introCap b last) :=rfl
      rw [he]
      fin_cases j
      · change introCap b last 0≤164+19*(introCap b last 0-1)
        omega
      · change introCap b last 1≤50+19*(introCap b last 1-1)
        omega
      · change introCap b last 2≤ strongWidth b+19*introCap b last 2
        omega
    rw [anZ,ite_eq_left hl] at h
    refine (bCj _ _).mpr fun j=>((bCj _ _).mp h j).trans ?_
    exact (spend_cap O hf j).trans (ho.symm ▸ hc j)
  · rwa [anZ,ite_eq_right hl] at h
theorem spend_ref {o:Origin} {F:Jet} (h : ∀ j,wD F j≤ introCap b o j) :
    oU F (refShape b o) :=
  (bCj _ _).mpr fun j=>(h j).trans (by fin_cases j <;> exact le_max_right _ _)
theorem cut_ref {o:Origin} {G:Jet} (h:oU G (originShape b o)) :
    oU G (refShape b o) :=
  (bCj _ _).mpr fun j=>((bCj _ _).mp h j).trans (by fin_cases j <;> exact le_max_left _ _)
theorem tD {a c:Fin 3→ℕ} (h : ∀ j,a j≤ c j) (s :Shape) (k :Fin 4) :
    kK a s k≤kK c s k :=
  sum_le_sum fun j _=>mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (h j)) (Nat.cast_nonneg _)
theorem b9i (a :Fin 3→ℕ) (s :Shape) (k :Fin 4) :0≤kK a s k :=
  sum_nonneg fun _ _=>mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
theorem mass_cut {f :Jet} (hf :f∈O.factors) (k :Fin 4)
    {s :Shape} (hs :s.J≤ s.B) (hc:oU (O.cut f) s) :
    pI.mass (O.parents f) k≤aHP s k f := by
  have hp:=O.proper f hf
  obtain ⟨_,hm⟩:=a8m f (O.cut f) (b6z hp.1 hp.2.2)
    (btm f) s (caQ hp.1.ne_zero) hs (bKa f) hc (O.parents f) (fun Q hQ=> by
      obtain ⟨ha,_,hp,hq⟩:=O.geometric f hf Q hQ
      exact ⟨ha.prime,ha.dimension,hp,hq⟩)
  exact (hm k).trans_eq (cfi f s hs k)
theorem mass_cut_rat {f :Jet} (hf :f∈O.factors) (k :Fin 4)
    {s :Shape} (hs :s.J≤ s.B) (hc:oU (O.cut f) s) :
    J2 (O.parents f) k≤kK (wD f) s k := by
  simpa only [kK,J2,aHP,wD,akZ.yE,
    Nat.cast_sum,Nat.cast_mul,mul_comm] using (Nat.cast_le (α:=ℚ)).mpr (mass_cut O hf k hs hc)
private def weight (b:RectTail) (k :Fin 4) (j:Fin 3) (i:ℕ) :ℕ :=
  if h:i<14 then arC (originShape b ⟨i,h⟩) k j else 0
private def running (w:ℕ→ℕ) :ℕ→ℕ
  | 0=>0
  | n+1=>max (running w n) (w n)
private def a4Q (w:ℕ→ℕ) (n:ℕ) :ℕ:=running w (n+1) - running w n
private theorem sum_jump (w:ℕ→ℕ) (n:ℕ) :
    (∑ i∈range n,a4Q w i)=running w n:= by
  induction n with
  | zero=>rfl
  | succ n ih =>
    rw [sum_range_succ,ih,a4Q]
    exact Nat.add_sub_of_le (le_max_left _ _)
private theorem dlP (w:ℕ→ℕ) (o:Origin) :
    w o.val ≤ ∑ i:Origin,if i≤o then a4Q w i.val else 0:= by
  rw [← sum_filter]
  have he : (univ.filter fun i:Origin=>i≤o)=Iic o:= by ext i; simp
  rw [he]
  change w o.val ≤ ∑ i∈Iic o,a4Q w (Fin.valEmbedding i)
  rw [← sum_map (Iic o) Fin.valEmbedding (a4Q w),Fin.map_valEmbedding_Iic,
    ← Nat.range_succ_eq_Iic,sum_jump]
  exact le_max_right _ _
private def Ya (b:RectTail) (k :Fin 4) :ℕ :=
  ∑ j:Fin 3,∑ i:Origin,a4Q (weight b k j) i.val*introCap b i j
private theorem blT (b:RectTail) (k :Fin 4) : (Ya b k :ℚ)≤BC b k := by
  cases b <;> fin_cases k <;> apply (Nat.cast_le (α:=ℚ)).mpr <;> decide
theorem bAW (k :Fin 4) :
    (∑ f∈O.factors,J2 (O.parents f) k)≤BC b k := by
  have h: (∑ f∈O.factors,aHP (originShape b (O.origin f)) k f)≤Ya b k := by
    change (∑ f∈O.factors,∑ j:Fin 3,arC (originShape b (O.origin f)) k j*wD f j)≤_
    rw [sum_comm]
    apply sum_le_sum
    intro j _
    let w:=weight b k j
    calc
      _ ≤ ∑ f∈O.factors,(∑ i:Origin,if i≤O.origin f then a4Q w i.val else 0)*wD f j :=
        sum_le_sum fun f _=>Nat.mul_le_mul_right _ (by
          simpa only [w,weight,dite_eq_left (O.origin f).isLt] using dlP w (O.origin f))
      _ = ∑ i:Origin,a4Q w i.val * ∑ f∈O.factors.filter (fun f=>i≤O.origin f),wD f j:= by
        simp only [sum_mul,mul_sum,sum_filter]
        rw [sum_comm]
        refine sum_congr rfl fun i _=>sum_congr rfl fun f _ => ?_
        by_cases h:i≤O.origin f <;> simp [h]
      _≤_:=sum_le_sum fun i _=>Nat.mul_le_mul_left _ (O.nested i j)
  have hm:=(sum_le_sum fun f hf=>mass_cut O hf k (origin_J b _) (cut_origin O hf)).trans h
  exact (by simpa only [J2,Nat.cast_sum] using (Nat.cast_le (α:=ℚ)).mpr hm :
    (∑ f∈O.factors,J2 (O.parents f) k)≤(Ya b k :ℚ)).trans (blT b k)
end
end q7Huoga
end
section
set_option autoImplicit true
namespace q6hAhQd
noncomputable section
open P6 (K p)
open P6_7_2 (Input)
open P6_7_2_3 (degree oldAgreement)
open cu (L)
open gT (kM bbt aSf pZ)
open YY (U7)
structure DescendedMarks {b} (x :Input b) (T:Finset K) (J:Ideal kM)
    (C:MvPolynomial (Fin 2) L) (g H :ℕ) :Prop where
  subset :T⊆x.Γ
  curve :bbt J g H
  irreducible :Irreducible C
  projection :J.comap pZ=Ideal.span {MvPolynomial.map U7 C}
  plane_pos :0<C.totalDegree
  seed_lt:C.totalDegree*g<p
  marks : ∀ γ∈T,aSf J (x.M.label γ) (x.F.scalar γ)
abbrev gap (b:P6_7.RectTail) :ℕ:=oldAgreement - degree b
abbrev linearRate (b:P6_7.RectTail) :ℚ:=1+3*262144/(gap b:ℚ)
abbrev quadraticRate (b:P6_7.RectTail) :ℚ:=13+8*262144/(gap b:ℚ)
abbrev nativeSlope (d:ℚ) (g:ℕ) :ℚ:=d/(3*(g:ℚ))+4*g+8
end
end q6hAhQd
end
section
set_option autoImplicit true
namespace qQCjxhb
noncomputable section
open Polynomial
open P6 (K p)
open cu (L FX jz kr)
open DP (jF Iy ad0)
open gT (Ambient)
open scoped Polynomial
abbrev inc:L[X] →+* FX:=algebraMap _ _
def point (z :K) (S:K[X]) :Fin 4→FX :=
  ![jz z,(jz z)^p,kr S,kr S.derivative]
def line (F:Ambient) (z :K) (S:K[X]) (y v :FX) :Polynomial FX :=
  MvPolynomial.eval₂Hom C
    ![C (point z S 0),C (point z S 1),
      C (point z S 2)+C y*Polynomial.X,C (point z S 3)+C v*Polynomial.X] F
def mL {h:ℕ} (D:jF h) (T:Finset P6.I) :L[X] :=
  Iy D *gR.mL ad0 T
end
end qQCjxhb
end
section
set_option autoImplicit true
namespace qu56FMb
noncomputable section
open P6 (p)
open P6_7 (RectTail)
open P6_7_2_3 (BlendOK degree oldAgreement persistentRate NativeOK nativeRate)
abbrev linearRate (b:RectTail) :ℚ:=1+3*262144/((oldAgreement-degree b:ℕ) :ℚ)
abbrev quadraticRate (b:RectTail) :ℚ:=13+8*262144/((oldAgreement-degree b:ℕ) :ℚ)
abbrev nativeSlope (d:ℚ) (g:ℕ) :ℚ:=d/(3*(g:ℚ))+4*g+8
private theorem mix {a a₀ q h v H T k E :ℚ} (h₀:a₀≤a) (hq:a<q)
    (hH :0≤H) (hE :0≤E) (direct :T≤q*v) (other :T≤a₀*v+k*H+E)
    (rate :k*(q-a)/(q-a₀)≤h) :T≤a*v+h*H+E := by
  let θ:=(q-a)/(q-a₀)
  have hd:0<q-a₀:=sub_pos.mpr (h₀.trans_lt hq)
  have hθ:0≤θ:=div_nonneg (sub_nonneg.mpr hq.le) hd.le
  have hθ₁:θ≤1 :=(div_le_one hd).mpr (sub_le_sub_left h₀ q)
  have hc:θ*(q-a₀)=q-a :=div_mul_cancel₀ _ hd.ne'
  have hs : (1-θ)*q+θ*a₀=a := by linarith only [hc]
  have hr :k*θ≤h:= by simpa only [θ,mul_div_assoc] using rate
  calc
    T=(1-θ)*T+θ*T:= by ring
    _≤(1-θ)*(q*v)+θ*(a₀*v+k*H+E) :=
      add_le_add (mul_le_mul_of_nonneg_left direct (sub_nonneg.mpr hθ₁))
        (mul_le_mul_of_nonneg_left other hθ)
    _=a*v+(k*θ)*H+θ*E := by rw [← hs]; ring
    _≤_:=add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hr hH))
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ₁ hE)
theorem constant_price (b:RectTail) {d z a h:ℚ} {m u v t g H :ℕ}
    (hg:0<g) (hz :2≤z) (ha :0<a) (hh:0≤h)
    (ht: (t:ℚ)≤d) (hplane :t≤u+v)
    (hb:a<(p:ℚ)/g→BlendOK b g ((p:ℚ)/g) d z a h)
    (direct :m≤u+p*v)
    (persistent: (m:ℚ)≤persistentRate b g*H+g)
    (linear :g=1→(m:ℚ)≤linearRate b*H+g)
    (quadratic:g=2→(m:ℚ)≤16*((t:ℚ)*g)+quadraticRate b*H+g)
    (native :3≤g → ∀ e c W M,NativeOK (degree b) g e c W M →
      (m:ℚ)≤nativeSlope t g*((t:ℚ)*g)+nativeRate (degree b) g e c W*H+g) :
    (m:ℚ)≤z*((u:ℚ)*g)+(a+1)*((v :ℚ)*g)+h*H := by
  let q:ℚ:=(p:ℚ)/g
  let U:ℚ:=(u:ℚ)*g
  let V:ℚ:=(v :ℚ)*g
  have hgq:0<(g:ℚ) :=Nat.cast_pos.mpr hg
  have hg₁ : (1 :ℚ)≤g:=Nat.cast_le.mpr hg
  have hU:0≤U:=mul_nonneg (Nat.cast_nonneg _) hgq.le
  have hV:0≤V:=mul_nonneg (Nat.cast_nonneg _) hgq.le
  have hH : (0:ℚ)≤H :=Nat.cast_nonneg _
  have hz₁:1≤z := by linarith only [hz]
  have hz₀:0≤z := by linarith only [hz]
  have hu: (u:ℚ)≤U:= by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hg₁ (Nat.cast_nonneg u)
  have hzu: (u:ℚ)≤z*U:=hu.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hz₁ hU)
  have heq :q*V=(p:ℚ)*v := by
    dsimp only [q,V]
    rw [mul_comm (v :ℚ),← mul_assoc,div_mul_cancel₀ _ hgq.ne']
  have hdir : (m:ℚ) - z*U≤q*V:= by
    have hd: (m:ℚ)≤(u:ℚ)+(p:ℚ)*v := by exact_mod_cast direct
    rw [heq]
    linarith only [hd,hzu]
  change (m:ℚ)≤z*U+(a+1)*V+h*H
  by_cases hv :v=0
  · have hzero :V=0:= by simp [V,hv]
    rw [hzero,mul_zero] at hdir ⊢
    linarith only [hdir,mul_nonneg hh hH]
  have hgV: (g:ℚ)≤V:= by
    have hv₁:1≤(v :ℚ) :=Nat.cast_le.mpr (Nat.pos_of_ne_zero hv)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hv₁ hgq.le
  by_cases hq:a<q
  · have blend {a₀ k :ℚ} (h₀:a₀≤a) (h₁:a₀≤z)
        (other : (m:ℚ)≤a₀*(U+V)+k*H+g)
        (rate :k*(q-a)/(q-a₀)≤h) : (m:ℚ)≤z*U+(a+1)*V+h*H := by
      have other' : (m:ℚ)-z*U≤a₀*V+k*H+g:= by
        linarith only [other,mul_le_mul_of_nonneg_right h₁ hU]
      have hm:=mix h₀ hq hH hgq.le hdir other' rate
      linarith only [hm,hgV]
    have base {k :ℚ} (other : (m:ℚ)≤k*H+g) (rate : (1-a/q)*k≤h) :
        (m:ℚ)≤z*U+(a+1)*V+h*H := by
      apply blend ha.le hz₀ (by simpa only [zero_mul,zero_add] using other)
      rw [sub_zero,mul_div_assoc,sub_div,div_self (ha.trans hq).ne',mul_comm]
      exact rate
    have htUV: (t:ℚ)*g≤U+V:= by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hplane) hgq.le
    rcases hb hq with hp | ⟨hg₁,hl⟩ | ⟨hg₂,hza,hrate⟩ |
      ⟨hg₃,e,c,W,M,hok,hza,hrate⟩
    · exact base persistent hp
    · exact base (linear hg₁) hl
    · apply blend ((le_min_iff.mp hza).2) ((le_min_iff.mp hza).1) _ hrate
      exact (quadratic hg₂).trans
        (add_le_add (add_le_add (mul_le_mul_of_nonneg_left htUV (by positivity)) le_rfl) le_rfl)
    · apply blend ((le_min_iff.mp hza).2) ((le_min_iff.mp hza).1) _ hrate
      have hs :nativeSlope t g≤nativeSlope d g:= by
        unfold nativeSlope
        gcongr
      have hs₀:0≤nativeSlope t g:= by unfold nativeSlope; positivity
      exact (native hg₃ e c W M hok).trans
        (add_le_add (add_le_add (mul_le_mul hs htUV (by positivity)
          (hs₀.trans hs)) le_rfl) le_rfl)
  · have hle :=mul_le_mul_of_nonneg_right (le_of_not_gt hq) hV
    linarith only [hdir,hle,hV,mul_nonneg hh hH]
end
end qu56FMb
end
section
set_option autoImplicit true
namespace qcYgGze
noncomputable section
open cu (FX)
open gT (Ambient aQ B4 Pp)
abbrev SliceRing:=MvPolynomial (Fin 4) aQ
abbrev sliceBase :Ambient →+* SliceRing:=MvPolynomial.map (algebraMap FX aQ)
abbrev To (k :Fin 4) (I:Ideal Ambient) :Ideal SliceRing :=
  I.map sliceBase ⊔ Ideal.span {(![Pp 1,Pp 0,Pp 2,B4 2 3] :
    Fin 4→SliceRing) k}
abbrev cutSlice (k :Fin 4) (Q:Ideal Ambient) (F:Ambient) :Ideal SliceRing :=
  To k Q ⊔ Ideal.span {sliceBase F}
abbrev CurveResidue (I:Ideal Ambient) [I.IsPrime] :=
  IsLocalRing.ResidueField (Localization.AtPrime I)
abbrev SlopedResidue (I:Ideal Ambient) [I.IsPrime] :=
  FractionRing (Polynomial (CurveResidue I))
def seedValue (I:Ideal Ambient) [I.IsPrime] (i:Fin 2) :CurveResidue I :=
  IsLocalRing.residue (Localization.AtPrime I)
    (algebraMap Ambient (Localization.AtPrime I) (MvPolynomial.X (i.castAdd 2)))
def slope (I:Ideal Ambient) [I.IsPrime] :SlopedResidue I :=
  algebraMap (Polynomial (CurveResidue I)) (SlopedResidue I) Polynomial.X
def seedOnSlope (I:Ideal Ambient) [I.IsPrime] :Polynomial (CurveResidue I) :=
  Polynomial.C (seedValue I 0)+Polynomial.X*Polynomial.C (seedValue I 1)
def aQa (I:Ideal Ambient) [I.IsPrime] :Fin 2→SlopedResidue I :=
  ![slope I,algebraMap (Polynomial (CurveResidue I)) (SlopedResidue I) (seedOnSlope I)]
abbrev SeedParameterField (I:Ideal Ambient) [I.IsPrime] :=
  IntermediateField.adjoin FX (Set.range (aQa I))
end
end qcYgGze
end
