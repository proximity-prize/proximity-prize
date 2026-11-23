import ProximityPrize.SubmissionLower.E
import ProximityPrize.SubmissionLower.ZE36Kga
set_option Elab.async false
set_option autoImplicit true
namespace qZqYIua
open aR (af Shape shape aO Dn gI)
open dN (GeoJets j8 bC)
open Dr aiK Kd bau
open ap8 (aES aQe)
open lB (bF)
open Filter
open private dEw from ProximityPrize.SubmissionLower.J
open private aWr eMC from ProximityPrize.SubmissionLower.J
open private gp0 from ProximityPrize.SubmissionLower.J
open private Q9 bwo bwp from ProximityPrize.SubmissionLower.T
private noncomputable abbrev principal (g:GeoJets) :Ideal GeoJets :=Ideal.span {g}
private theorem dim_principal {g:GeoJets} (hg:g≠0) :dimension (principal g)≤3:= by
  have h:=aCR (aPQ Ideal.isPrime_bot
    (show g∉(⊥ : Ideal GeoJets) by simpa using hg))
  simpa [bEk] using h
private theorem square_degree {g:GeoJets} (hg:g≠0) {q r h:Shape}
    (hb : ∀ a∈[q,r,h],bF a) :
    tW (principal (g^2)) [q,r,h] =
      tW (principal g) [q,r,h]+tW (principal g) [q,r,h] := by
  let J:=principal (g^2)
  have hle :J≤principal g:=Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self g (by decide))
  have hs :J ⊔ principal g=principal g:=sup_eq_right.mpr hle
  have hc:J.colon {g} = principal g:= by
    ext v
    rw [Submodule.mem_colon_singleton,smul_eq_mul,Ideal.mem_span_singleton,Ideal.mem_span_singleton]
    constructor
    · rintro ⟨u,hu⟩
      exact ⟨u,mul_right_cancel₀ hg (by linear_combination hu)⟩
    · rintro ⟨u,rfl⟩
      exact ⟨u,by ring⟩
  have he (a :Shape) (ha :ChamberBox a) :
      capCoeff J 3 a=capCoeff (principal g) 3 a+capCoeff (principal g) 3 a := by
    simpa only [hs,hc] using dEw J g ha (dim_principal (pow_ne_zero 2 hg))
  unfold tW
  change BE (capCoeff J 3) [q,r,h] _/_ = _
  rw [aWr he hb ⟨by decide,by decide,by decide⟩,eMC,add_div]
  rfl
private def count (b j t:ℚ) :ℚ :=
  (8*b*j^2*t - 24*b*j*t^2+24*b*t^3-4*j^3*t+14*j^2*t^2 - 20*j*t^3+9*t^4)/2 +
  (2*b*j^2+2*b*j*t - 3*b*t^2 - j^3+(3/2)*j^2*t - (11/2)*j*t^2+(13/2)*t^3) +
  (4*b*j - b*t - j^2+2*j*t - (5/2)*t^2)+(2*b+j - t/2)+1
private theorem count_eq (a :Shape) (ha :ChamberBox a) :
    ((capExponents a).ncard:ℚ)=count a.b a.j a.t:= by
  have he :a.scale 1=a := by cases a; simp [Shape.scale]
  conv_lhs=>rw [← he,← cWW a ha 1 (by decide)]
  simp only [aIp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_X,Dn,count]
  push_cast
  ring
private def Ya (p a :Shape) :ℚ :=
  count a.b a.j a.t - count ((a.b:ℚ) - p.b) ((a.j:ℚ) - p.j) ((a.t:ℚ) - p.t)
private theorem count_bill (g:GeoJets) (hg:g≠0) {a :Shape} (ha :ChamberBox a)
    (hb: (geoShape g).b+a.j≤a.b) (hj: (geoShape g).j+3*a.t≤a.j)
    (ht: (geoShape g).t<a.t) :
    (Sn (principal (g^2)) (capExponents a) :ℚ)=Ya (geoShape g) a := by
  let p:=geoShape g
  change p.b+a.j≤a.b at hb
  change p.j+3*a.t≤a.j at hj
  change p.t<a.t at ht
  let u:Shape :=⟨a.b - p.b,a.j - p.j,a.t - p.t⟩
  have h₁:p.b≤a.b:= by omega
  have h₂:p.j≤a.j:= by omega
  have hua :u.plus p=a := by cases a; simp [u,Shape.plus,Nat.sub_add_cancel,h₁,h₂,ht.le]
  have hu:ChamberBox u:= by
    change a.j - p.j≤a.b - p.b∧3*(a.t - p.t)≤a.j - p.j∧0<a.t - p.t
    omega
  have he :=rank_square g hg u
  rw [hua] at he
  have hc: (Sn (principal (g^2)) (capExponents a) :ℚ) +
      ((capExponents u).ncard:ℚ)=((capExponents a).ncard:ℚ) := by exact_mod_cast he
  rw [count_eq _ hu,count_eq _ ha] at hc
  change _=Ya p a
  rw [Ya,eq_sub_iff_add_eq]
  simpa only [u,Nat.cast_sub h₁,Nat.cast_sub h₂,Nat.cast_sub ht.le] using hc
private theorem square_bill (g:GeoJets) (hg:g≠0) (q r h:Shape)
    (hq:bF q) (hr :bF r) (hh:bF h) :
    tW (principal (g^2)) [q,r,h]=(Ds.wP (geoShape g) q r h:ℚ)/ 16:= by
  classical
  let J:=principal (g^2)
  let p:=geoShape g
  let s :Fin 5→Shape := ![⟨3,3,1⟩,⟨5,4,1⟩,q,r,h]
  let dirs :List (Fin 5) :=[2,3,4]
  have hs (i:Fin 5) :bF (s i) := by
    fin_cases i
    · change bF ⟨3,3,1⟩; exact ⟨by decide,by decide⟩
    · change bF ⟨5,4,1⟩; exact ⟨by decide,by decide⟩
    · exact hq
    · exact hr
    · exact hh
  have hbase :ChamberBox (s 0) := by
    change ChamberBox ⟨3,3,1⟩
    exact ⟨by decide,by decide,by decide⟩
  have hd:dimension J≤dirs.length:=dim_principal (pow_ne_zero 2 hg)
  have hnorm:=cNl s J 0 dirs hs hbase (by decide) hd
  let N :=p.b+p.j+p.t+1
  obtain ⟨a,ha,hlarge⟩:=(hnorm.and (eventually_ge_atTop (N•step (1 :Fin 5)))).exists
  have he (w:Fin 5→ℕ) (hw:a≤w) :
      lO (Fd s) (HW s J) w=Ya p (ku s w) := by
    rw [(aKs.proof s J).2 w,eOX s hs]
    let m:=w 1
    let v :=Function.update w 1 0
    have hm:N≤ m:= by
      have hm' := (hlarge.trans hw) 1
      simpa [m,step,Pi.smul_apply] using hm'
    have hwv :w=v+m•step 1 := by
      funext i
      by_cases hi:i=1
      · subst i; simp [v,m,step]
      · simp [v,step,hi]
    rw [hwv,aES,gp0,aQe,show s 1=⟨5,4,1⟩ from rfl]
    have hv :=awr s hs v
    have hj:=hv.1
    have ht:=hv.2
    dsimp only [N,p] at hm
    apply count_bill g hg <;> simp only [ChamberBox,Shape.plus,Shape.scale,Nat.mul_one] <;> omega
  rw [cKj dirs _ _ a he,dV2] at ha
  change BE (Ya p) [q,r,h] (ku s a) =
    BE (capCoeff J 3) [q,r,h] ⟨3,3,1⟩ at ha
  rw [show tW J [q,r,h]=BE (capCoeff J 3) [q,r,h] ⟨3,3,1⟩/8 by rfl,← ha]
  simp only [BE,Ya,count,Ds.wP,gI,Dn,Shape.plus,FI.oL]
  push_cast
  ring
theorem literal_bound (R:af 4) (a q r h:Shape) (hR:R≠0)
    (hbox :aO (shape R) a) (hq:bF q) (hr :bF r) (hh:bF h) :
    tW (principal (bC R)) [q,r,h]≤(Ds.wP a q r h:ℚ)/32 := by
  let g:=bC R
  have hg:g≠0:= fun h=>hR (lB.aFf (h.trans (map_zero _).symm))
  have hbox' : aO (geoShape g) a := by
    have hs :=MvPolynomial.support_map_subset j8 R
    refine ⟨(Finset.sup_mono hs).trans hbox.1,?_,?_⟩
    · have hj:=hbox.2.1
      change aR.qE R≤a.j at hj
      rw [Ex.C6] at hj
      exact (Finset.sup_mono hs).trans hj
    · have hb:=(Dr.bHn hbox)
      exact MvPolynomial.degreeOf_le_iff.mpr fun m hm=>(hb m hm).2.2
  have H :=square_bill g hg q r h hq hr hh
  rw [square_degree hg (by simp [hq,hr,hh])] at H
  let p:=geoShape g
  let d:Shape :=⟨a.b-p.b,a.j-p.j,a.t-p.t⟩
  have he :p.plus d=a := by
    obtain ⟨hb,hj,ht⟩:=hbox'
    cases a
    simp_all [p,d,Shape.plus]
  have hm:Ds.wP p q r h≤Ds.wP a q r h:= by
    rw [← he]
    change Q9 p q r h≤Q9 (p.plus d) q r h
    rw [bwo]
    exact le_add_of_nonneg_right (bwp d q r h hq hr hh)
  have hm' : (Ds.wP p q r h:ℚ)≤(Ds.wP a q r h:ℚ) := by exact_mod_cast hm
  linarith only [H,hm']
end qZqYIua
