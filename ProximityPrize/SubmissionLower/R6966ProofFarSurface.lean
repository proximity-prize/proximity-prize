import ProximityPrize.SubmissionLower.R6966ProofFarChart
import ProximityPrize.SubmissionLower.R6960RetainedSurfaceClass
import ProximityPrize.SubmissionLower.R6960RetainedCrossingLift

set_option Elab.async false

section Merged_R6960RetainedChartGluing
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedChartGluing
open ChartSections (Chart)
open MonicChart MonicFourChartDescent MonicScalarCorrection ChartGlobalTests
open RetainedCompression (Curve ordinate view height heightCap)
open Polynomial
open K1_14 (L)
open Lower6960.MonicFourChartDescent (finite_inclusion infinity_inclusion)
variable {E : Type*} [Field E] [Algebra ChartField E]
theorem common_correction_far (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164748 f≤heightCap (f.degreeOf ordinate) 164748)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (u : Chart→E) (compatible : Compatible a b u) :
    ∃ c : E, Correction a b u c := by
  obtain ⟨H,high⟩:=high_twist f ir lo hi basis root
  have large : H<K1.p^H := Nat.lt_pow_self KoalaBear.is_prime.one_lt
  have above {d : ℕ} (pos : 0<d) : H<d*K1.p^H :=
    large.trans_le (Nat.le_mul_of_pos_left _ pos)
  obtain ⟨c,hc⟩:=high _ _ (above ha) (above hb) _ (compatible_iterate a b u compatible H)
  obtain ⟨d,_,hd⟩ := descend_iterate_far f ir lo hi bounded basis root a b ha u H c hc
  exact ⟨d,hd⟩
#print axioms common_correction_far
theorem split_cocycle_far (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164748 f≤heightCap (f.degreeOf ordinate) 164748)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (g : Chart→Chart→E)
    (add : ∀ s t r, g s t+g t r=g s r)
    (regular : ∀ s t, IsIntegral (MonicChartLaurent.overlapRing s t)
      (algebraMap ChartField E (frame a b s)*g s t)) :
    ∃ w : Chart→E, (∀ s, IsIntegral (baseChart s) (algebraMap ChartField E (frame a b s)*w s)) ∧
      ∀ s t, g s t=w s-w t := by
  let u (s : Chart):=g s (false,false)
  have diff (s t) : u s-u t=g s t := sub_eq_of_eq_add (add s t (false,false)).symm
  obtain ⟨c,hc⟩:=common_correction_far f ir lo hi bounded basis root a b ha hb u
    (fun s t=> by rw [diff]; exact regular s t)
  exact ⟨fun s=>u s-c,hc,fun s t=>by rw [←diff]; ring⟩
#print axioms split_cocycle_far
end Lower6960.RetainedChartGluing

end
end Merged_R6960RetainedChartGluing

section Merged_R6960RetainedLineRestriction
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedLineRestriction
open MonicFourChartDescent ChartSections MonicChart RetainedChartGluing
open ChartGlobalTests (frame_ne)
open MonicChartLaurent (overlapRing)
open MonicChartProbes (planeMap planeMap_injective)
open RetainedCompression (Curve ordinate view height heightCap)
open Polynomial
open K1_14 (L)
private theorem lines_ne (x z : L) : lines x z≠0 := by
  let m := planeMap (false,false)
  have a : (Polynomial.X (R:=(Polynomial L)))-C (C x)≠0 := X_sub_C_ne_zero _
  have b : (C (Polynomial.X (R:=L)) : (Polynomial (Polynomial L)))-C (C z)≠0 := by
    rw [←map_sub]; exact C_ne_zero.mpr (X_sub_C_ne_zero _)
  have good := (map_ne_zero_iff m (planeMap_injective _)).mpr (mul_ne_zero a b)
  simpa only [m,map_mul,map_sub,MonicChartProbes.planeMap_constants,MonicChartProbes.planeMap_scalar,
    MonicChartProbes.planeMap_abscissa,chartCoordinate,Bool.false_eq_true,ite_false,lines] using good
variable {E : Type*} [Field E] [Algebra ChartField E]
theorem split_of_split_on_lines_far (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164748 f≤heightCap (f.degreeOf ordinate) 164748)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (x z : L) (g : Chart→Chart→E) (add : ∀ s t r, g s t+g t r=g s r)
    (v : Chart→E) (localV : ∀ s, IsIntegral (baseChart s) (v s))
    (restricted : ∀ s t, ∃ r : E, IsIntegral (overlapRing s t) r ∧
      g s t-(v s-v t)=algebraMap ChartField E (lines x z / frame 1 1 s)*r) :
    ∃ w : Chart→E, (∀ s,IsIntegral (baseChart s) (w s)) ∧ ∀ s t,g s t=w s-w t := by
  let ι:=algebraMap ChartField E
  let P:=ι (lines x z)
  have pn : P≠0 := (map_ne_zero_iff ι ι.injective).mpr (lines_ne x z)
  let h (s t:Chart):=(g s t-(v s-v t))/P
  have coc (s t r) : h s t+h t r=h s r := by
    dsimp [h]
    rw [←add_div]
    congr 1
    linear_combination add s t r
  have twist (s t) : IsIntegral (overlapRing s t) (ι (frame 1 1 s)*h s t) := by
    obtain ⟨r,hr,eq⟩:=restricted s t
    have nz := (map_ne_zero_iff ι ι.injective).mpr (frame_ne 1 1 s)
    have recover : ι (frame 1 1 s)*h s t=r := by
      dsimp only [h]; rw [eq,map_div₀]
      change ι (frame 1 1 s)*(P/ι (frame 1 1 s)*r/P)=r
      field_simp
    rwa [recover]
  obtain ⟨w,localW,diff⟩:=split_cocycle_far f ir lo hi bounded basis root 1 1 (by decide) (by decide) h coc twist
  refine ⟨fun s=>v s+P*w s,fun s=>(localV s).add ?_,fun s t=>?_⟩
  · have integral : IsIntegral (baseChart s) (ι (lines x z/frame 1 1 s)) :=
      isIntegral_algebraMap (x:=(⟨_, local_equation x z s⟩ : baseChart s))
    have eq : ι (lines x z / frame 1 1 s)*(ι (frame 1 1 s)*w s)=P*w s := by
      rw [map_div₀,←mul_assoc,div_mul_cancel₀ _ ((map_ne_zero_iff ι ι.injective).mpr (frame_ne _ _ _))]
    exact eq ▸ integral.mul (localW s)
  · have eq := (div_eq_iff pn).mp (diff s t)
    linear_combination eq
#print axioms split_of_split_on_lines_far
end Lower6960.RetainedLineRestriction

end
end Merged_R6960RetainedLineRestriction

section Merged_R6960RetainedPairedResidues

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace Lower6960.RetainedRestrictionTorus
open MonicChart (ChartField)
open K1_14 (L)
open MonicFourChartDescent ChartSections MonicChartLaurent ChartOverlapTests Polynomial
open RetainedCompression (Curve ordinate view height heightCap)
open scoped Polynomial
variable {E : Type*} [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

private theorem base_x (s : Chart) (x:L) : algebraMap (baseChart s) E (xcut s x) =
    ι (divisor false x)/ι (localFrame s false) := by
  change ι ((xcut s x):ChartField)=_
  rw [xcut_value,map_div₀]
private theorem base_z (s : Chart) (z:L) : algebraMap (baseChart s) E (zcut s z) =
    ι (divisor true z)/ι (localFrame s true) := by
  change ι ((zcut s z):ChartField)=_
  rw [zcut_value,map_div₀]

private theorem glue (s : Chart) (x z:L) (nx:x≠0) (nz:z≠0) (u v:E)
    (hu:IsIntegral (baseChart s) u) (hv:IsIntegral (baseChart s) v) (h:Matched x z u v) :
    ∃ y:E,IsIntegral (baseChart s) y ∧ Congruent false x u y ∧ Congruent true z v y := by
  obtain ⟨a,b,ia,ib,eq⟩:=h
  have fn (j : Bool) : (ι (localFrame s j) : E)≠0 :=
    (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s j)
  have m:=lift_on_chart s x z nx nz u v hu hv ⟨ι (localFrame s false)*a,ι (localFrame s true)*b,
    (frame_integral s false).1.mul ia,(frame_integral s true).1.mul ib,by
      rw [base_x,base_z,eq]; field_simp [fn]⟩
  obtain ⟨y,a',b',hy,ia',ib',dx,dz⟩:=m
  refine ⟨y,hy,⟨ι ((localFrame s false)⁻¹)*a',
    (frame_integral s false).2.mul (order_mono (base_torus s) ia'),?_⟩,Congruent.symm
      ⟨ι ((localFrame s true)⁻¹)*b',(frame_integral s true).2.mul (order_mono (base_torus s) ib'),?_⟩⟩
  · rw [dx,base_x,map_inv₀,div_eq_mul_inv,mul_assoc]
  · rw [dz,base_z,map_inv₀,div_eq_mul_inv,mul_assoc]

private theorem product_residue [FiniteDimensional ChartField E]
    (s t : Chart) (x z:L) (nx:x≠0) (nz:z≠0) (v:E)
    (reg : IsIntegral (overlapRing s t) v) (vx : Congruent false x v 0) (vz : Congruent true z v 0) :
    ∃ r:E, IsIntegral (overlapRing s t) r ∧
      v=ι (RetainedLineRestriction.lines x z / frame 1 1 s)*r := by
  obtain ⟨a,ia,ea⟩:=vx; obtain ⟨b,ib,eb⟩:=vz
  rw [sub_zero] at ea eb
  let Xv:=ι (divisor false x)
  let Zv:=ι (divisor true z)
  let P:=ι (localFrame s false)
  let Q:=ι (localFrame s true)
  have mne (p:ChartField) (pn:p≠0) : (ι p:E)≠0 := (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr pn
  have xn : Xv≠0:=mne _ (divisor_ne false x)
  have zn : Zv≠0:=mne _ (divisor_ne true z)
  have pn : P≠0:=mne _ (localFrame_ne s false)
  have qn : Q≠0:=mne _ (localFrame_ne s true)
  let r:=P*Q*v/(Xv*Zv)
  have xeq : algebraMap (baseChart s) E (xcut s x)*r=Q*b := by
    rw [base_x]; change Xv/P*(P*Q*v/(Xv*Zv))=Q*b
    change v=Zv*b at eb
    rw [eb]; field_simp
  have zeq : algebraMap (baseChart s) E (zcut s z)*r=P*a := by
    rw [base_z]; change Zv/Q*(P*Q*v/(Xv*Zv))=P*a
    change v=Xv*a at ea
    rw [ea]; field_simp
  have both : algebraMap (baseChart s) E (xcut s x*zcut s z)*r=v := by
    rw [map_mul,base_x,base_z]; change Xv/P*(Zv/Q)*(P*Q*v/(Xv*Zv))=v
    field_simp
  refine ⟨r,cancel_both s t x z nx nz r (both ▸ reg)
    (xeq ▸ (frame_integral s true).1.mul ib) (zeq ▸ (frame_integral s false).1.mul ia),?_⟩
  have e : frame 1 1 s=localFrame s false*localFrame s true := by simp [frame,localFrame,axisBit,coordinate]
  rw [e,map_div₀,map_mul]
  rw [RetainedLineRestriction.lines,map_mul]
  change v=(Xv*Zv)/(P*Q)*(P*Q*v/(Xv*Zv))
  field_simp

private theorem lift_axis (j : Bool) (c:L) (nc:c≠0) (u:Chart→E) (v:Bool→E)
    (reg : ∀ s t, IsIntegral (overlapRing s t) (u s-u t)) (data : LineData j c u v) (s:Chart) :
    ∃ w:E,IsIntegral (baseChart s) w ∧ Congruent j c (u s-(u (false,false)-v false)) w := by
  let bit:=axisBit s (!j)
  let t:=reference j bit
  have parallel : axisBit s (!j)=axisBit t (!j) := by cases j <;> simp [bit,t,reference,axisBit]
  have r := (reg s t).add (order_mono (chart_cover s t) (data.1 bit))
  obtain ⟨w,hw,cw⟩:=line_representative j c nc s t parallel (u s-u t+v bit) r
  refine ⟨w,hw,Congruent.trans ?_ cw⟩
  have shared : Congruent j c (u (false,false)-u t) (v false-v bit) := by
    cases h:bit with
    | false => have t0:t=(false,false) := by cases j <;> simp [t,h,reference]
               rw [t0,sub_self,sub_self]; exact Congruent.refl j c 0
    | true => simpa only [t,h] using data.2
  obtain ⟨d,id,eq⟩:=shared.symm
  exact ⟨d,id,by rw [←eq]; abel⟩

/-- Only two transition differences and one crossing value are needed to detect an
untwisted obstruction on the original four normalized charts. -/
theorem split_of_paired_data_far (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164748 f≤heightCap (f.degreeOf ordinate) 164748)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) (u:Chart→E)
    (reg : ∀ s t, IsIntegral (overlapRing s t) (u s-u t)) (v w:Bool→E)
    (dv : LineData false x u v) (dw : LineData true z u w) (joined : Matched x z (v false) (w false)) :
    ∃ c:E, Correction 0 0 u c := by
  let : FiniteDimensional ChartField E := basis.finite
  choose a ia ca using lift_axis false x nx u v reg dv
  choose b ib cb using lift_axis true z nz u w reg dw
  obtain ⟨h₁,h₂,ih₁,ih₂,joint⟩:=joined
  have m (s:Chart) : Matched x z (a s) (b s) := by
    obtain ⟨p,ip,ep⟩:=ca s
    obtain ⟨q,iq,eq⟩:=cb s
    refine ⟨h₁-p,h₂+q,ih₁.sub ip,ih₂.add iq,?_⟩
    rw [mul_sub,mul_add]
    linear_combination joint-ep+eq
  choose l il ax az using fun s=>glue s x z nx nz (a s) (b s) (ia s) (ib s) (m s)
  have residual (s t : Chart) (j:Bool) (d:L) (y:E) (lift:∀ i,Congruent j d (u i-y) (l i)) :
      Congruent j d ((u s-u t)-(l s-l t)) 0 := by
    obtain ⟨r,hr,eq⟩:=(lift s).sub (lift t)
    refine ⟨r,hr,?_⟩
    rw [sub_zero,←eq]; abel
  have restriction (s t : Chart) := product_residue s t x z nx nz ((u s-u t)-(l s-l t))
    ((reg s t).sub ((order_mono (into_cleared _ (edge s t)) (il s)).sub (order_mono (chart_cover s t) (il t))))
    (residual s t _ _ _ (fun i=>(ca i).trans (ax i))) (residual s t _ _ _ (fun i=>(cb i).trans (az i)))
  obtain ⟨p,ip,eq⟩:=RetainedLineRestriction.split_of_split_on_lines_far f ir lo hi bounded basis root x z
    (fun s t=>u s-u t) (fun _ _ _=>by abel) l il restriction
  refine ⟨u (false,false)-p (false,false),fun s=>?_⟩
  have id : u s-(u (false,false)-p (false,false))=p s := by linear_combination eq s (false,false)
  simpa [id,frame] using ip s

#print axioms split_of_paired_data_far
end Lower6960.RetainedRestrictionTorus

end
end Merged_R6960RetainedPairedResidues

section Merged_R6960RetainedSurfaceClass

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedSurfaceClass
open ChartSections (Chart)
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests
open Module Submodule LinearMap Polynomial
open scoped Polynomial Lower6960.MonicChartLaurent

variable (E : Type) [Field E] [Algebra ChartField E]
open scoped Lower6960.RetainedSurfaceClass

private theorem raw_zero (x z:L) (u:potentials E) : rawMap E x z u=0 ↔
    ∃ v:Bool→Tor E, ∃ w:Bool→Tor E,
      (∀ b,IsIntegral (baseChart (reference false b)) (v b:E)) ∧
      (∀ b,IsIntegral (baseChart (reference true b)) (w b:E)) ∧
      red E false x (u.1 (false,false)-u.1 (reference false true))=red E false x (v false-v true) ∧
      red E true z (u.1 (false,false)-u.1 (reference true true))=red E true z (w false-w true) ∧
      (Ideal.Quotient.mk (axisIdeal E false x⊔axisIdeal E true z)) (v false) =
        Ideal.Quotient.mk _ (w false) := by
  rw [show rawMap E x z u=0 ↔ _ from Submodule.Quotient.mk_eq_zero _]
  constructor
  · rintro ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,eq,edge⟩
    obtain ⟨v0,iv0,h0⟩:=a.property
    obtain ⟨v1,iv1,h1⟩:=b.property
    obtain ⟨w0,iw0,g0⟩:=c.property
    obtain ⟨w1,iw1,g1⟩:=d.property
    let v (i:Bool):Tor E:=if i then v1 else v0
    let w (i:Bool):Tor E:=if i then w1 else w0
    refine ⟨v,w,(fun i=>by cases i <;> first | exact iv0 | exact iv1),
      (fun i=>by cases i <;> first | exact iw0 | exact iw1),?_,?_,?_⟩
    · change _=red E false x (v0-v1)
      rw [map_sub (red E false x) v0 v1,h0,h1]
      have e:= (congrArg Prod.fst edge).symm
      change red E false x (u.1 (false,false)-u.1 (reference false true))=a.1+ -b.1 at e
      simpa only [sub_eq_add_neg] using e
    · change _=red E true z (w0-w1)
      rw [map_sub (red E true z) w0 w1,g0,g1]
      have e:= (congrArg Prod.snd edge).symm
      change red E true z (u.1 (false,false)-u.1 (reference true true))=c.1+ -d.1 at e
      simpa only [sub_eq_add_neg] using e
    · change crossingX E x z a.1+ -(crossingZ E x z c.1)=0 at eq
      rw [←h0,←g0] at eq
      change (Ideal.Quotient.mk _ v0)+ -(Ideal.Quotient.mk _ w0)=0 at eq
      rw [←sub_eq_add_neg] at eq
      exact sub_eq_zero.mp eq
  · rintro ⟨v,w,iv,iw,ex,ez,node⟩
    let a (i:Bool): chartImage E false x i:=⟨_,⟨v i,iv i,rfl⟩⟩
    let b (i:Bool): chartImage E true z i:=⟨_,⟨w i,iw i,rfl⟩⟩
    refine ⟨((a false,a true),(b false,b true)),?_,?_⟩
    · change Ideal.Quotient.mk _ (v false)+ -Ideal.Quotient.mk _ (w false)=0
      rw [node,add_neg_cancel]
    · apply Prod.ext
      · change red E false x (v false)+ -(red E false x (v true))=_
        rw [←sub_eq_add_neg,←map_sub]; exact ex.symm
      · change red E true z (w false)+ -(red E true z (w true))=_
        rw [←sub_eq_add_neg,←map_sub]; exact ez.symm

private theorem matched_of_eq (x z:L) (a b:Tor E)
    (eq : Ideal.Quotient.mk (axisIdeal E false x⊔axisIdeal E true z) a=Ideal.Quotient.mk _ b) :
    Matched x z (a:E) (b:E) := by
  obtain ⟨u,hu,v,hv,l⟩:=Submodule.mem_sup.mp (Ideal.Quotient.eq.mp eq)
  obtain ⟨r,rfl⟩:=Ideal.mem_span_singleton.mp hu
  obtain ⟨t,rfl⟩:=Ideal.mem_span_singleton.mp hv
  exact ⟨r,t,r.property,t.property,congrArg Subtype.val l.symm⟩

open RetainedCompression (Curve ordinate view height heightCap)

/-- The actual bounded cover's untwisted obstruction space embeds in the quotient
formed by the two torus fibres and a single shared crossing. -/
theorem restriction_kernel_far (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164748 f≤heightCap (f.degreeOf ordinate) 164748)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) :
    (rawMap E x z).ker=coboundaries E := by
    ext u
    change rawMap E x z u=0 ↔ ∃ c:E,∀ s,IsIntegral (baseChart s) ((u.1 s:E)-c)
    rw [raw_zero]
    constructor
    · rintro ⟨v,w,iv,iw,ex,ez,node⟩
      have r:=split_of_paired_data_far f ir lo hi bounded basis root x z nx nz
        (fun s=>(u.1 s:E)) u.property (fun b=>(v b:E)) (fun b=>(w b:E))
        ⟨iv,congr_of_eq E false x _ _ ex⟩ ⟨iw,congr_of_eq E true z _ _ ez⟩
        (matched_of_eq E x z _ _ node)
      obtain ⟨c,hc⟩:=r
      exact ⟨c,fun s=>by simpa [frame] using hc s⟩
    · rintro ⟨c,hc⟩
      have ic : IsIntegral torus c := by
        have ii:=(u.1 (false,false)).property.sub (order_mono (base_torus (false,false)) (hc (false,false)))
        simpa only [sub_sub_cancel] using ii
      let ct : Tor E:=⟨c,ic⟩
      let v (j b:Bool):Tor E:=u.1 (reference j b)-ct
      have start (j:Bool) : reference j false=(false,false) := by cases j <;> rfl
      refine ⟨v false,v true,(fun b=>hc _),(fun b=>hc _),?_,?_,?_⟩
      · apply congrArg (red E false x); simp only [v,start]; abel
      · apply congrArg (red E true z); simp only [v,start]; abel
      · rfl
#print axioms restriction_kernel_far
end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedSurfaceClass
