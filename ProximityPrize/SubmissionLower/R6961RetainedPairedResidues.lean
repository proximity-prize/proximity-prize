import ProximityPrize.SubmissionLower.R6961RetainedAxisResidues

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace Lower6961.RetainedRestrictionTorus
open Lower6961.MonicChart (ChartField)
open K1_14 (L)
open MonicFourChartDescent Lower6960.ChartSections MonicChartLaurent ChartOverlapTests Polynomial
open RetainedCompression (Curve ordinate view height heightCap MarkedBand)
open scoped Polynomial
variable {E : Type*} [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

def Matched (x z : L) (u v:E) : Prop := ∃ a b:E,IsIntegral torus a ∧ IsIntegral torus b ∧
  u-v=ι (divisor false x)*a+ι (divisor true z)*b

theorem frame_integral (s : Chart) (j : Bool) :
    IsIntegral torus (ι (localFrame s j) : E) ∧ IsIntegral torus (ι (localFrame s j)⁻¹ : E) := by
  have p:=torus_frame s j
  exact ⟨isIntegral_algebraMap (x:=(⟨_,p.1⟩:torus)),isIntegral_algebraMap (x:=(⟨_,p.2⟩:torus))⟩

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

def reference (j bit : Bool) : Chart := if j then (bit,false) else (false,bit)

def LineData (j : Bool) (c:L) (u:Chart→E) (v:Bool→E) : Prop :=
  (∀ b, IsIntegral (baseChart (reference j b)) (v b)) ∧
  Congruent j c (u (false,false)-u (reference j true)) (v false-v true)

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
theorem split_of_paired_data (B : MarkedBand) (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<B.maxOrd) (bounded : height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree)
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
  obtain ⟨p,ip,eq⟩:=RetainedLineRestriction.split_of_split_on_lines B f ir lo hi bounded basis root x z
    (fun s t=>u s-u t) (fun _ _ _=>by abel) l il restriction
  refine ⟨u (false,false)-p (false,false),fun s=>?_⟩
  have id : u s-(u (false,false)-p (false,false))=p s := by linear_combination eq s (false,false)
  simpa [id,frame] using ip s

#print axioms split_of_paired_data
end Lower6961.RetainedRestrictionTorus
