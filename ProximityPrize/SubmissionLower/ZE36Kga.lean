import ProximityPrize.SubmissionLower.M
import ProximityPrize.SubmissionLower.B4
import ProximityPrize.SubmissionLower.Zc9uAjc
set_option Elab.async false
open _root_ renaming Finsupp.degree_apply → zqc, Polynomial.C → z1z, Polynomial.mapRingHom → zhd, Polynomial.map_C → zrL, Polynomial.map_add → zS4, Polynomial.map_dvd → z36, Polynomial.map_mul → zNl
section
set_option autoImplicit true
namespace qZqYIua
noncomputable section
open aR (Shape)
open dN (GeoField GeoJets)
open Dr Kd MvPolynomial
def geoShape (g:GeoJets) :Shape :=
  ⟨g.totalDegree,weightedTotalDegree Fin.val g,g.degreeOf 3⟩
private theorem VB (m:Fin 4 →₀ ℕ) :
    Finsupp.weight Fin.val m = ∑ i:Fin 4,i.val*m i:= by
  rw [Finsupp.weight_apply,Finsupp.sum_fintype m (fun i c=>c•i.val) (fun i=>zero_smul ℕ i.val)]
  simp only [smul_eq_mul,Nat.mul_comm]
private theorem fits_cap (g:GeoJets) (a :Shape) :
    g∈restrictSupport GeoField (capExponents a) ↔
      (geoShape g).b≤2*a.b∧(geoShape g).j≤2*a.j∧(geoShape g).t≤2*a.t:= by
  classical
  change (g.support :Set _)⊆capExponents a↔_
  simp only [geoShape,capExponents,Set.subset_def,Finset.mem_coe,Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨Finset.sup_le fun m hm => ?_,Finset.sup_le fun m hm => ?_,?_⟩
    · simpa only [zqc,Finsupp.sum] using (h m hm).1
    · simpa only [VB] using (h m hm).2.1
    · exact degreeOf_le_iff.mpr (fun m hm=>(h m hm).2.2)
  · rintro ⟨hb,hj,ht⟩ m hm
    refine ⟨?_,?_,(monomial_le_degreeOf 3 hm).trans ht⟩
    · simpa only [zqc,Finsupp.sum] using (le_totalDegree hm).trans hb
    · simpa only [VB] using
        (le_weightedTotalDegree Fin.val hm).trans hj
private theorem geo_mul {g v :GeoJets} (hg:g≠0) (hv :v≠0) :
    geoShape (g*v)=(geoShape g).plus (geoShape v) := by
  simp only [geoShape,Shape.plus,← weightedTotalDegree_one,← weightedTotalDegree_piSingle,
    weightedTotalDegree_mul _ _ _ hg hv]
private theorem fits_square_mul {g:GeoJets} (hg:g≠0) (v :GeoJets) (a :Shape) :
    g^2*v∈restrictSupport GeoField (capExponents (a.plus (geoShape g))) ↔
      v∈restrictSupport GeoField (capExponents a) := by
  by_cases hv :v=0
  · simp [hv]
  rw [fits_cap,fits_cap,geo_mul (pow_ne_zero _ hg) hv,pow_two,geo_mul hg hg]
  dsimp [Shape.plus]
  omega
theorem rank_square (g:GeoJets) (hg:g≠0) (a :Shape) :
    Sn (Ideal.span {g^2}) (capExponents (a.plus (geoShape g))) +
      (capExponents a).ncard=(capExponents (a.plus (geoShape g))).ncard:= by
  classical
  let J:Ideal GeoJets :=Ideal.span {g^2}
  let S:=capExponents (a.plus (geoShape g))
  let T:=capExponents a
  let U:=restrictSupport GeoField S
  let V:=restrictSupport GeoField T
  let π:=(Ideal.Quotient.mkₐ GeoField J).toLinearMap.domRestrict U
  let μ:=((LinearMap.mulLeft GeoField (g^2)).domRestrict V).codRestrict U
    (fun v=>(fits_square_mul hg v.val a).mpr v.property)
  let:Module.Finite GeoField U:=restrictSupport_finite (Set.toFinite S)
  have hμ:Function.Injective μ:= fun x y h =>
    Subtype.ext (mul_left_cancel₀ (pow_ne_zero _ hg) (congrArg Subtype.val h))
  have hr :LinearMap.range μ=LinearMap.ker π:= by
    ext x
    rw [LinearMap.mem_range,LinearMap.mem_ker]
    change (∃ v,μ v=x)↔Ideal.Quotient.mk J x.val=0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · rintro ⟨v,rfl⟩
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro hx
      obtain ⟨v,hv⟩:=Ideal.mem_span_singleton.mp hx
      have hvu:g^2*v∈U:=hv ▸ x.property
      exact ⟨⟨v,(fits_square_mul hg v a).mp hvu⟩,Subtype.ext hv.symm⟩
  have hn:=π.finrank_range_add_finrank_ker
  rw [← hr,LinearMap.range_domRestrict,LinearMap.finrank_range_of_inj hμ] at hn
  have fin (W:Set (Fin 4 →₀ ℕ)) [Finite W] :
      Module.finrank GeoField (restrictSupport GeoField W)=W.ncard:= by
    rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport GeoField _),Nat.card_coe_set_eq]
  change Sn J S+Module.finrank GeoField V=Module.finrank GeoField U at hn
  exact (fin T ▸ fin S ▸ hn)
end
end qZqYIua
end
section
set_option autoImplicit true
namespace P6_7
noncomputable section
open Polynomial
open P6 (K p node twist)
open cu (L j9)
open DP (jF ad0 aKF)

theorem dsh {A h u del} (M:P1.FJ h u del) {Γ} (F:P1.bje A M Γ) :
    ∃ H,YQ M F H := by
  let φ:=algebraMap K L
  let σ:=frobenius L p
  have hsmall:M.iF.toNat≤(j9 M.E).natDegree := by
    rw [j9,natDegree_map]
    unfold P1.FJ.iF
    omega
  obtain ⟨H,hm,hdeg,hd⟩:=cu.trim _ _ hsmall
  have hd' : H.map σ∣j9 (M.E.map twist) := by
    change H.map σ∣j9 (M.E.map K1.twist)
    rw [cu.dio]
    exact z36 σ hd
  have hcop:IsCoprime H (H.map σ) := by
    have ha :=M.adjacent_coprime.map (zhd φ)
    exact (ha.of_isCoprime_of_dvd_left hd).of_isCoprime_of_dvd_right hd'
  have hunit :IsCoprime (j9 (M.Q*M.factor*M.A₀)) H :=
    (((M.offset_reduced.mul_left M.coprime_factor.symm).mul_left M.first_amplitude_unit).map
      (zhd φ)).of_isCoprime_of_dvd_right hd
  refine ⟨H,hm,hdeg,hd,hm.map σ,(natDegree_map σ).trans hdeg,hd',hcop,?_,
    hunit,hunit.map (zhd σ),?_⟩
  · intro i
    have h₀:H.eval (φ (node i))≠0:= by
      intro hz
      have hb: (j9 M.E).eval (φ (node i))=0:= by
        obtain ⟨J,hj⟩:=hd
        simp [hj,eval_mul,hz]
      exact M.aFF i (φ.injective (by simpa [j9,φ] using hb))
    have hx :σ (φ (node i))=φ (node i) := by
      change φ (node i)^p= _
      rw [← map_pow,gR.Native.ahU]
    refine ⟨h₀,?_⟩
    rw [← hx,eval_map_apply]
    exact (map_ne_zero σ).mpr h₀
  · intro γ hγ
    let z :=M.label γ
    let B:=F.mark γ hγ
    have ha :IsCoprime (j9 (M.factor*M.wK γ)) H :=
      ((M.coprime_factor.symm.mul_left B.pole_unit).map
        (zhd φ)).of_isCoprime_of_dvd_right hd
    have hid :M.E∣(M.factor*M.wK γ)*F.scalar γ+C z*M.Q :=
      ⟨P1.FJ.decoder M B.bad,by rw [← B.identity]; exact sub_add_cancel _ _⟩
    have hres :H∣j9 (M.factor*M.wK γ)*j9 (F.scalar γ) +
        C (φ z)*j9 M.Q:= by
      simpa only [j9,zS4,zNl,zrL]
        using hd.trans (z36 φ hid)
    have hfix : (j9 (F.scalar γ)).map σ=j9 (F.scalar γ) := by
      rw [← cu.dio]
      exact congrArg j9 B.scalar_fixed
    refine ⟨ha,ha.map (zhd σ),hres,?_⟩
    simpa only [zS4,zNl,zrL,hfix,
      σ,frobenius_def] using (z36 σ hres)
def weakenFamily {A B h u del} {M:P1.FJ h u del} {Γ} (F:P1.bje A M Γ)
    (h:B≤A) :P1.bje B M Γ :=
  ⟨F.scalar,fun γ hγ =>
    let m:=F.mark γ hγ
    { bad:=⟨m.bad.support,m.bad.decoder,h.trans m.bad.dw,m.bad.degree,
        m.bad.lg,m.bad.nonjoint⟩
      avoids_deleted:=m.avoids_deleted
      scalar_fixed:=m.scalar_fixed
      aic:=m.aic
      scalar_hits :=m.scalar_hits
      pole_unit :=m.pole_unit
      identity :=m.identity },F.distinct⟩
theorem bW4 {A₀ h u del} (M:P1.FJ h u del) {Γ} (F:P1.bje A₀ M Γ)
    (H :L[X]) (hH :YQ M F H) :
    ∃ D:jF M.iF.toNat,
      D.block 0=H∧D.block 1=H.map (frobenius L p) ∧
      (∀ i k,(D.block i).eval (ad0 k)≠0) ∧
      ∀ γ∈Γ,aKF D (M.label γ) (F.scalar γ) := by
  let σ:=frobenius L p
  rcases hH with ⟨hm,hd,_,hm',hd',_,hcop,hnode,hdet,hdet',hmarks⟩
  let A:=j9 (M.factor*M.A₀)
  let B:=j9 (M.factor*M.A₁)
  let Q:=j9 M.Q
  have hdet0:IsCoprime (Q*A) H := by
    simpa [Q,A,j9,mul_assoc] using hdet
  have hdet1 :IsCoprime (Q.map σ*A.map σ) (H.map σ) := by
    simpa [Q,A,j9,mul_assoc,σ,zNl] using hdet'
  let D:jF M.iF.toNat :=
    ⟨![H,H.map σ],![Q,Q.map σ],![A,A.map σ],![B,B.map σ],
      fun i=> by fin_cases i <;> first | exact hm | exact hm',
      fun i=> by fin_cases i <;> first | exact hd | exact hd',
      hcop,fun i=> by fin_cases i <;> first | exact hdet0 | exact hdet1⟩
  refine ⟨D,rfl,rfl,?_,?_⟩
  · intro i k
    fin_cases i
    · exact (hnode k).1
    · exact (hnode k).2
  · intro γ hγ i
    let z :=algebraMap K L (M.label γ)
    have hz :j9 (M.factor*M.wK γ)=A+(@z1z L _) z*B:= by
      simp [A,B,z,P1.FJ.wK,j9,mul_add,mul_left_comm]
    obtain ⟨h₀,h₁,hr₀,hr₁⟩:=hmarks γ hγ
    fin_cases i
    · change IsCoprime (A+(@z1z L _) z*B) H ∧
        H∣(A+(@z1z L _) z*B)*j9 (F.scalar γ)+(@z1z L _) z*Q
      rw [← hz]
      exact ⟨h₀,hr₀⟩
    · have hσ: (j9 (M.factor*M.wK γ)).map σ =
          A.map σ+(@z1z L _) (z^p)*B.map σ:= by
        rw [hz,zS4,zNl,zrL]
        rfl
      change IsCoprime (A.map σ+(@z1z L _) (z^p)*B.map σ) (H.map σ) ∧
        H.map σ∣(A.map σ+(@z1z L _) (z^p)*B.map σ)*j9 (F.scalar γ) +
          (@z1z L _) (z^p)*Q.map σ
      rw [← hσ]
      exact ⟨h₁,hr₁⟩
theorem aic {A h u del Γ} {M:P1.FJ h u del} (F:P1.bje A M Γ)
    {γ:K} (hγ:γ∈Γ) : (F.scalar γ).natDegree≤131071+M.iF.toNat := by
  rcases (F.mark γ hγ).aic with hz | hd
  · simp [hz]
  · change ((F.scalar γ).natDegree :ℤ)≤131071+M.iF at hd
    omega
end
end P6_7
end
