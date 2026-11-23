import ProximityPrize.SubmissionLower.D3
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.P6Front
import ProximityPrize.SubmissionLower.B6
set_option Elab.async false
open _root_ renaming Finset → zJe, Finset.mem_filter → zO0, Nat.le_of_not_gt → zqB, Polynomial.C → z1z, Polynomial.mapRingHom → zhd, Polynomial.map_dvd_map' → zw5, Polynomial.map_mul → zNl, Polynomial.map_zero → zgY, Polynomial.natDegree → zFA
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P6
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
open Aj (GC aAg aC8
  a5o bYN)
open private cEN from ProximityPrize.SubmissionLower.B
open private ari aCJ bFL from ProximityPrize.SubmissionLower.D3
private theorem bfx {u:e9} {T:qo u} (R:Relation T) (i:I) :
    i∈pJ R↔(y1 R).eval (C (node i))=0∧(zv R).eval (C (node i))=0:= by
  classical
  simp [pJ]
private theorem ecS {u:e9} {T:qo u} (R:Relation T)
    (hi : ¬ as1 R) (hf :aYI R) :
    ∀ H :kB[X],H∣sZ (y1 R)→H∣sZ (zv R) →
      H∣sZ (jH (mL node (pJ R))) := by
  classical
  obtain ⟨g,hg,hgu,hgv,hgmax⟩:=hf
  change g.map aCJ≠0 at hg
  change g.map aCJ∣ _ at hgu hgv
  change ∀ H :kB[X],H∣sZ (y1 R)→H∣sZ (zv R) →
    H∣g.map aCJ at hgmax
  have hg0:g≠0:= by
    intro hz
    exact hg (by rw [hz,zgY])
  let g₀:=g*C g.leadingCoeff⁻¹
  have hm:g₀.Monic:=monic_mul_leadingCoeff_inv hg0
  have hnorm (P:kB[X]) (hd:g.map aCJ∣P) :
      g₀.map aCJ∣P:= by
    apply ((zw5 aCJ).mpr ?_).trans hd
    exact (dvd_mul_leadingCoeff_inv hg0).mp dvd_rfl
  have hlift (P:nC) (hd:g.map aCJ∣sZ P) :
      jH g₀∣P:= by
    apply (Polynomial.map_dvd_map GC aAg (hm.map z1z)).mp
    change sZ (jH g₀)∣sZ P
    rw [bFL]
    exact hnorm _ hd
  have hu:=hlift _ hgu
  have hv :=hlift _ hgv
  have hdom:g₀∣mL node Finset.univ := by
    by_contra h
    exact hi (Or.inr ⟨g₀,hm.ne_zero,hu,hv,h⟩)
  obtain ⟨S,_,_,t,ht,hS⟩ :=
    kL.guf node IRSProfile.domain.injective Finset.univ g₀ hm.ne_zero hdom
  have hsub:S⊆pJ R:= by
    intro i his
    have hz :g₀.eval (node i)=0:= by
      rw [hS,eval_smul,arK node S i his,smul_zero]
    have hlzero : (jH g₀).eval (C (node i))=0:= by
      rw [ari,hz,C_0]
    obtain ⟨U,hU⟩:=hu
    obtain ⟨V,hV⟩:=hv
    exact (bfx R i).mpr ⟨by rw [hU,eval_mul,hlzero,zero_mul],
      by rw [hV,eval_mul,hlzero,zero_mul]⟩
  have hg₀dvd:g₀∣mL node (pJ R) := by
    rw [hS,Polynomial.smul_eq_C_mul,(isUnit_C.mpr (isUnit_iff_ne_zero.mpr ht)).mul_left_dvd]
    exact kL.bsf node IRSProfile.domain.injective S _
      (fun i his=>arK node _ i (hsub his))
  intro H hU hV
  rw [bFL]
  exact (hgmax H hU hV).trans
    ((zw5 aCJ).mpr
      ((dvd_mul_right g (C g.leadingCoeff⁻¹)).trans hg₀dvd))
theorem ecX {u:e9} {T:qo u} (R:Relation T)
    (hu:y1 R≠0) (hm : ¬ aSe R) (hi : ¬ as1 R) :
    aiE (sZ (jH (mL node (pJ R))))
      (sZ (y1 R)) (sZ (zv R)) := by
  classical
  let S:=pJ R
  let Δ:=jH (mL node S)
  let A:=sZ (y1 R)
  let B:=sZ (zv R)
  have hΔ:Δ.Monic:=(S8 node S).map z1z
  have hΔ0:sZ Δ≠0:=(hΔ.map GC).ne_zero
  have hA0:A≠0 :=
    fun h=>hu (aC8 (h.trans (zgY _).symm))
  have hΔA:sZ Δ∣A:= by
    exact _root_.map_dvd (zhd GC)
      (a5o S (y1 R) (fun i h=>((bfx R i).mp h).1))
  have hΔB:sZ Δ∣B:= by
    exact _root_.map_dvd (zhd GC)
      (a5o S (zv R) (fun i h=>((bfx R i).mp h).2))
  refine ⟨hΔ0,hΔA,hΔB,?_⟩
  by_cases hf :aYI R
  · exact ecS R hi hf
  let G:=EuclideanDomain.gcd A B
  have hGA:G∣A:=EuclideanDomain.gcd_dvd_left _ _
  have hGB:G∣B:=EuclideanDomain.gcd_dvd_right _ _
  have hG:G≠0:= fun hz=>hA0 (zero_dvd_iff.mp (hz ▸ hGA))
  have hGd:G.natDegree≤S.card:= by
    apply zqB
    exact fun h=>hm ⟨hf,G,hG,hGA,hGB,h⟩
  have hΔd: (sZ Δ).natDegree=S.card:= by
    rw [bFL,natDegree_map_eq_of_injective aCJ.injective,ZQ]
  obtain ⟨q,hq⟩:=EuclideanDomain.dvd_gcd hΔA hΔB
  change G=sZ Δ*q at hq
  have hq0:q≠0:= by intro h; exact hG (by rw [hq,h,mul_zero])
  have hd:=congrArg zFA hq
  rw [natDegree_mul hΔ0 hq0,hΔd] at hd
  have hqC:q=C (q.coeff 0) :=eq_C_of_natDegree_eq_zero (by omega)
  have hqU:IsUnit q:= by
    rw [hqC,isUnit_C,isUnit_iff_ne_zero]
    intro hz
    exact hq0 (by rwa [hz,C_0] at hqC)
  intro H hHA hHB
  have hHG:H∣G:=EuclideanDomain.dvd_gcd hHA hHB
  rwa [hq,hqU.dvd_mul_right] at hHG
theorem ePH {u:e9} {T:qo u} (R:Relation T)
    (hs :axB R) (hw : ∃ γ,Normal u γ∧Nonempty (B5 u γ))
    (hgcd:aiE (sZ (jH (mL node (pJ R))))
      (sZ (y1 R)) (sZ (zv R))) :Nonempty (Reduction u T R) := by
  classical
  obtain ⟨γ,hγ,⟨M⟩⟩:=hw
  have h:=hs γ hγ M
  let B:=pJ R
  let G:=jH (mL node B)
  have hG:G.Monic:=(S8 node B).map z1z
  have hGd:G.natDegree=B.card:= by
    change ((mL node B).map z1z).natDegree= _
    rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective,ZQ]
  obtain ⟨U,hU⟩:=a5o B (y1 R)
    (fun i hi=>(bfx R i |>.mp hi).1)
  obtain ⟨V,hV⟩:=a5o B (zv R)
    (fun i hi=>(bfx R i |>.mp hi).2)
  obtain ⟨W,hW⟩:=a5o B R.output (fun i hi=> by
    have hroot :=(bfx R i).mp hi
    exact cEN R i hroot.1 hroot.2)
  have hu:U≠0:= by
    intro hz
    apply h.U_ne
    rw [hU,hz,mul_zero,vn,zgY]
  have hv :V≠0:= by
    intro hz
    apply h.V_ne
    rw [hV,hz,mul_zero,vn,zgY]
  have hdeg:max (y1 R).natDegree (zv R).natDegree=T.height:= by
    apply le_antisymm (max_le (R.x_degree 0) (R.x_degree 1))
    exact zqB fun hlt=>h.valid (Or.inl hlt)
  have hdu:=congrArg zFA hU
  have hdv :=congrArg zFA hV
  change (y1 R).natDegree=(G*U).natDegree at hdu
  change (zv R).natDegree=(G*V).natDegree at hdv
  rw [natDegree_mul hG.ne_zero hu,hGd] at hdu
  rw [natDegree_mul hG.ne_zero hv,hGd] at hdv
  let H :=max U.natDegree V.natDegree
  have hH :H+B.card=T.height:= by
    dsimp [H]
    omega
  have hout:W.degree<(k+H :ℕ) := by
    by_cases hzero :W=0
    · rw [hzero,degree_zero]
      exact WithBot.bot_lt_coe _
    have hRout:R.output≠0:= by rw [hW]; exact mul_ne_zero hG.ne_zero hzero
    have hd:=(natDegree_lt_iff_degree_lt hRout).mpr R.output_degree
    rw [hW] at hd
    change (G*W).natDegree<_ at hd
    rw [natDegree_mul hG.ne_zero hzero,hGd] at hd
    exact (natDegree_lt_iff_degree_lt hzero).mp (by omega)
  have hcop:IsCoprime (sZ U) (sZ V) := by
    apply bYN (sZ G) _ _ hgcd.1
      (fun hz=>hu (aC8 (hz.trans (zgY _).symm)))
    intro Q hqu hqv
    apply hgcd.2.2.2 Q
    · rw [hU,sZ,zNl]
      exact hqu
    · rw [hV,sZ,zNl]
      exact hqv
  exact ⟨⟨U,V,W,H,hH,rfl,hu,hv,hcop,hU,hV,hW,hout,
    fun γ hn M=>(hs γ hn M).fixed_errors⟩⟩
end
end P6
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P6
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
open Aj (GC aAg aC8 Vf biW)
open private bPb from ProximityPrize.SubmissionLower.B
open private dhe dhf bYj c09 co8 cKB c5O c8n from ProximityPrize.SubmissionLower.B
open aSg (bxJ c73 bC4)
open private db1 cti from ProximityPrize.SubmissionLower.CQ
private theorem ceU {u:e9} {T:qo u} {R:Relation T}
    (D:Reduction u T R) (e :K[X]) :
    ake u (pJ R) (C e*D.U) (C e*D.V) (C e*D.output) := by
  let G:=jH (mL node (pJ R))
  have hG : ∀ i∉pJ R,G.eval (C (node i))≠0:= by
    intro i hi
    change (K1.jH (mL node (pJ R))).eval (C (node i))≠0
    rw [Aj.ari,C_ne_zero]
    exact fun hz=>hi ((Principal.aVH node
      ProximityPrize.Benchmark.IRSProfile.domain.injective _ i).mp hz)
  rw [c73]
  exact @bPb u K1.p k T.height R (pJ R) G D.U D.V D.output
    hG D.U_factor D.V_factor D.output_factor e
private theorem go5 {u:e9} {T:qo u} {R:Relation T}
    (D:Reduction u T R) (P Q:nC) (hcross :Z4 D.U D.V P Q)
    (hp:P.natDegree≤D.height) (hq:Q.natDegree≤D.height) :
    ∃ e :K[X],P=C e*D.U∧Q=C e*D.V:= by
  have hext (F:nC) : (Vf F).natDegree=F.natDegree :=
    natDegree_map_eq_of_injective aAg F
  have hne (F:nC) (hF:F≠0) :Vf F≠0 :=
    fun hz=>hF (aC8 (hz.trans (zgY _).symm))
  have hxy :Vf D.U*Vf Q=Vf D.V*Vf P:= by
    have h:=congrArg Vf hcross
    simpa only [map_mul] using h
  have hcop:IsCoprime (Vf D.U) (Vf D.V) :=D.coprime
  obtain ⟨E,heP,heQ⟩:=bYj hcop hxy
  have hEd:=c09 (hne _ D.U_ne) (hne _ D.V_ne) heP heQ
    (by simpa only [hext] using D.max_degree)
    (by simpa only [hext] using hp) (by simpa only [hext] using hq)
  let s :=E.coeff 0
  have hE :E=C s :=eq_C_of_natDegree_eq_zero hEd
  rw [hE] at heP heQ
  let G:=jH (mL node (pJ R))
  have hLeftU:Vf (G*P)=C s*Vf (y1 R) := by
    rw [D.U_factor]
    change Vf (G*P)=C s*Vf (G*D.U)
    rw [map_mul,map_mul,heP]
    ac_rfl
  have hLeftV:Vf (G*Q)=C s*Vf (zv R) := by
    rw [D.V_factor]
    change Vf (G*Q)=C s*Vf (G*D.V)
    rw [map_mul,map_mul,heQ]
    ac_rfl
  let F:Fin 2→nC := ![G*P,G*Q]
  let A:Fin 2×Fin (T.height+1)→K[X] :=
    fun j=>(F j.1).coeff j.2.val
  have hA : ∀ j,GC (A j)=s*GC (R.coefficients j) := by
    rintro ⟨i,j⟩
    fin_cases i
    · have hc:=co8 j.val hLeftU
      rw [y1,Principal.ahe] at hc
      exact hc
    · have hc:=co8 j.val hLeftV
      rw [zv,Principal.ahe] at hc
      exact hc
  obtain ⟨e,he⟩:=cKB R.coefficients A R.primitive s hA
  have hmapC:Vf (C e)=C s := by
    change (C e).map GC=C s
    rw [Polynomial.map_C,he]
  refine ⟨e,aC8 ?_,aC8 ?_⟩
  · change Vf P=Vf (C e*D.U)
    rw [map_mul,hmapC,heP]
  · change Vf Q=Vf (C e*D.V)
    rw [map_mul,hmapC,heQ]
private theorem dEs {u:e9} {T:qo u} {R:Relation T}
    (D:Reduction u T R) (P Q:nC) (hcross :Z4 D.U D.V P Q)
    (hp:P.natDegree≤D.height) (hq:Q.natDegree≤D.height) :
    ∃ W:nC,W.degree<(k+D.height:ℕ)∧ake u (pJ R) P Q W:= by
  obtain ⟨e,rfl,rfl⟩:=go5 D P Q hcross hp hq
  refine ⟨C e*D.output,?_,?_⟩
  · have hdeg: (C e*D.output).degree≤D.output.degree := by
      simpa only [smul_eq_C_mul] using degree_smul_le e D.output
    exact hdeg.trans_lt D.output_degree
  · exact ceU D e
theorem fTr {u:e9} {T:qo u} {R:Relation T}
    (D:Reduction u T R) (hr :Xb D.U D.V=3) (S:biW D.U D.V)
    (ha :S.a.natDegree+uO (S.β 0) (S.β 1)≤D.height)
    (hb:S.b.natDegree+uO (S.α 0) (S.α 1)≤D.height) :
    ∃ B:KJ u T R D,baQ B∨Parallel B:= by
  have hdir :Z4 D.U D.V (JO S.a S.β) (J9 S.b S.α) := by
    rw [bxJ,cti,db1]
    exact S.direction
  have hUdeg: (JO S.a S.β).natDegree≤D.height:= by
    rw [bxJ]
    exact (dhe _ _).trans ha
  have hVdeg: (J9 S.b S.α).natDegree≤D.height:= by
    rw [cti]
    exact (dhf _ _).trans hb
  obtain ⟨W,hW,hnodes⟩:=dEs D _ _ hdir hUdeg hVdeg
  by_cases hd:S.α 0*S.β 1 - S.α 1*S.β 0=0
  · obtain ⟨t,ht,htβ⟩:=c5O S.α_primitive S.β_primitive (sub_eq_zero.mp hd)
    have htσ:twist t≠0:= fun hz=>ht (twist.injective (hz.trans (map_zero twist).symm))
    let a :=S.a*C (twist t)
    have heq (i:Fin 2) : (S.β i).map twist=C (twist t)*(S.α i).map twist:= by
      rw [htβ i,zNl,Polynomial.map_C]
    have hU:JO a S.α=JO S.a S.β :=
      (bxJ _ _).trans ((c8n S.a S.α S.β (twist t) heq).trans (bxJ _ _).symm)
    have hdeg (i:Fin 2) : (S.β i).natDegree=(S.α i).natDegree := by
      rw [htβ i,natDegree_C_mul ht]
    have ha' : a.natDegree+uO (S.α 0) (S.α 1)≤D.height:= by
      simpa only [a,natDegree_mul_C htσ,uO,hdeg] using ha
    have hdir' : Z4 D.U D.V (JO a S.α) (J9 S.b S.α) := by
      rw [hU]
      exact hdir
    have hn:ake u (pJ R) (JO a S.α) (J9 S.b S.α) W:= by
      rw [hU]
      exact hnodes
    exact ⟨⟨hr,S.α,S.α,a,S.b,mul_ne_zero S.a_ne (C_ne_zero.mpr htσ),S.b_ne,
      S.α_primitive,S.α_primitive,ha',hb,hdir',W,hW,hn⟩,Or.inr rfl⟩
  · exact ⟨⟨hr,S.α,S.β,S.a,S.b,S.a_ne,S.b_ne,
      S.α_primitive,S.β_primitive,ha,hb,hdir,W,hW,hnodes⟩,Or.inl hd⟩
theorem dLq {u:e9} (hfront:abC u) (T:qo u)
    (R:Relation T) (hmove : ¬ aSe R) (hinvalid : ¬ as1 R)
    (hsat :axB R) (hw : ∃ γ,Normal u γ∧Nonempty (B5 u γ)) :
    ∃ D:Reduction u T R,Xb D.U D.V=4 ∨
      ∃ B:KJ u T R D,baQ B∨Parallel B:= by
  have hu:y1 R≠0:= by
    obtain ⟨γ,hγ,⟨M⟩⟩:=hw
    intro hz
    exact (hsat γ hγ M).U_ne (by rw [vn,hz,zgY])
  obtain ⟨D⟩:=ePH R hsat hw (ecX R hu hmove hinvalid)
  refine ⟨D,?_⟩
  rcases Aj.fS5 D.U D.V D.U_ne D.V_ne with hfour | hthree
  · exact Or.inl ((bC4 _ _).trans hfour)
  · obtain ⟨S⟩:=czK.proof D.U D.V D.U_ne D.V_ne hthree
    have hsmall:=(dd8 D hfront).2.2
    obtain ⟨ha,hb⟩:=czL.proof D.U D.V D.height D.U_ne D.V_ne D.coprime D.max_degree hsmall S
    exact Or.inr (fTr D ((bC4 _ _).trans hthree) S ha hb)
end
end P6
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P6
open Polynomial Matrix gR ProximityPrize.Benchmark
open private cEO from ProximityPrize.SubmissionLower.S
open private cXI cqo a3F c8U cHb from ProximityPrize.SubmissionLower.T
private theorem dHz {u:e9} {T:qo u} (R:Relation T)
    (s :ℕ) (hL:T.height+s=L) :
    (Mc.Sm (fun b=>Principal.assemble (fun j=>R.coefficients (b,j))) L s).transpose *
      So u=0:= by
  have hsize :k+(48754+1)+t≤Fintype.card I:= by
    rw [IRSProfile.card_index]
    decide
  exact cEO p node (u 0) (u 1) IRSProfile.domain.injective
    Native.ahU (algebraMap K[X] kB) (IsFractionRing.injective K[X] kB)
    k T.height 48754 t s hL hsize R _ (fun _=>rfl)
private theorem eD3 {u:e9} {T:qo u} (R:Relation T)
    (hMoving:aSe R) {γ:K} {M:B5 u γ} (hSat :aSC R M) :
    ∃ i∉pJ R,
      (vn (y1 R) γ).eval (node i)=0∧(vn (zv R) γ).eval (node i)=0:= by
  classical
  obtain ⟨G,hG,hGU,hGV,hg⟩:=hMoving.2
  obtain ⟨D,hD,hd,hDU,hDV⟩:=cXI hG hGU hGV
  obtain ⟨A,hA⟩:=hDU
  obtain ⟨B,hB⟩:=hDV
  obtain ⟨hAU,hAUdeg⟩:=cqo hD hA hSat.U_ne
  obtain ⟨hBV,hBVdeg⟩:=cqo hD hB hSat.V_ne
  change vn (y1 R) γ=vn D γ*vn A γ at hAU
  change vn (zv R) γ=vn D γ*vn B γ at hBV
  change (vn (y1 R) γ).natDegree+D.natDegree ≤
    (y1 R).natDegree+(vn D γ).natDegree at hAUdeg
  change (vn (zv R) γ).natDegree+D.natDegree ≤
    (zv R).natDegree+(vn D γ).natDegree at hBVdeg
  have hdeg:D.natDegree≤(vn D γ).natDegree := by
    have hU:=R.x_degree 0
    have hV:=R.x_degree 1
    change (y1 R).natDegree≤T.height at hU
    change (zv R).natDegree≤T.height at hV
    have hMax :=hSat.degree_eq
    rcases le_total (vn (y1 R) γ).natDegree (vn (zv R) γ).natDegree with h | h
    · rw [max_eq_right h] at hMax
      omega
    · rw [max_eq_left h] at hMax
      omega
  obtain ⟨errors,_,hGCD⟩:=hSat.gcd_errors
  have hDvd:=hGCD.2.2.2 (vn D γ) ⟨vn A γ,hAU⟩ ⟨vn B γ,hBV⟩
  have hCard: (pJ R).card<(vn D γ).natDegree := by omega
  obtain ⟨i,hiFixed,hi⟩:=c8U (F:=K) (ι:=I)
    node IRSProfile.domain.injective errors (pJ R) (vn D γ) hDvd hCard
  exact ⟨i,hiFixed,by rw [hAU,eval_mul,hi,zero_mul],by rw [hBV,eval_mul,hi,zero_mul]⟩
open private cIp from ProximityPrize.SubmissionLower.D3
private theorem eFe {u:e9} {T:qo u} (R:Relation T)
    (hHeight : ∀ i,(R.coefficients i).natDegree≤0x197858f67)
    (hMoving:aSe R) (hSat :axB R) (Γ:zJe K)
    (hBad:Tt u Γ) (hNormal : ∀ γ∈Γ,Normal u γ) :
    Γ.card≤0x65e163d9c0000:= by
  classical
  let U (i:I) :=(y1 R).eval (C (node i))
  let V (i:I) :=(zv R).eval (C (node i))
  have hU (i) : (U i).natDegree≤0x197858f67:= by
    dsimp only [U,y1]
    rw [kL.bA7]
    exact Principal.bsZ _ (fun j=>hHeight (0,j)) _
  have hV (i) : (V i).natDegree≤0x197858f67:= by
    dsimp only [V,zv]
    rw [kL.bA7]
    exact Principal.bsZ _ (fun j=>hHeight (1,j)) _
  have hNew (γ:K) (hγ:γ∈Γ) :
      ∃ i,¬ (U i=0∧V i=0)∧(U i).eval γ=0∧(V i).eval γ=0:= by
    refine (P6.aCl u Γ hBad γ hγ).elim (fun M => ?_)
    obtain ⟨i,hi,hu,hv⟩:=eD3 R hMoving (hSat γ (hNormal γ hγ) M)
    have hNZ : ¬ (U i=0∧V i=0) := by
      simpa only [pJ,zO0,Finset.mem_univ,true_and] using hi
    exact ⟨i,hNZ,(a3F (y1 R) γ (node i)).symm.trans hu,
      (a3F (zv R) γ (node i)).symm.trans hv⟩
  exact cIp (c:=Γ.card) (n:=Fintype.card I) (n' := 262144)
    (H :=0x197858f67) (b:=0x65e163d9c0000) IRSProfile.card_index
    (cHb U V 0x197858f67 Γ hU hV hNew) rfl
theorem b9u (u:e9) (front:abC u) (T:qo u)
    (R:Relation T) (moving:aSe R) (saturated:axB R)
    (Γ:zJe K) (bad:Tt u Γ) (normal : ∀ γ∈Γ,Normal u γ) :
    Γ.card≤0x65e163d9c0000:= by
  let P (b:Fin 2) :nC:=Principal.assemble (fun j=>R.coefficients (b,j))
  let s :=L - T.height
  have hP : ∀ b,(P b).natDegree≤T.height:=R.x_degree
  have hBalance :=a7J T
  have hHeight:=aEz front T
  change T.height≤33561 at hHeight
  have hsDef :s=48755 - T.height:=rfl
  have hSum:T.height+s=L:= by change T.height+s=48755; omega
  have hs :15194≤ s := by omega
  have hRank :Bx.adJ (So u)+s=2*L:= by
    change Vv u+s= _
    rw [aSO u]
    change 48755+T.height+R5 u=82318 at hBalance
    change 82318 - R5 u+s=97510
    omega
  have hCoordinates :Mc.a6n P T.height=R.coefficients := by
    funext i
    exact Principal.ahe (fun j=>R.coefficients (i.1,j)) i.2
  have hPrim:M4.IsPrimitive (Mc.a6n P T.height) := by
    rw [hCoordinates]
    exact R.primitive
  have hKernel:=dHz R s hSum
  obtain ⟨hMinors,H,hH,rows,hRows⟩ :=
    czJ.proof K T.height L s P hSum (by omega) hP hPrim
  have hBound:=bz5.proof K L (t+1) s p (So u) (Mc.Sm P L s)
    (by decide) hRank hKernel (a8L p node (u 0) (u 1) L t) hMinors rows
  rw [hRows] at hBound
  have hProduct :15194*H≤ s*H :=Nat.mul_le_mul_right H hs
  have hCeiling:L*(p+1)=0x5e7b0d017ce6:=rfl
  rw [hCeiling] at hBound
  have hCap:H≤0x197858f67:= by omega
  apply eFe R _ moving saturated Γ bad normal
  intro i
  rw [← hCoordinates]
  exact (hH i.1 i.2.val).trans hCap
end P6
end
section
set_option autoImplicit true
namespace P6
theorem emJ (w:ℤ) (hlo:ajO<w) (hhi:w≤(DY:ℤ)) :
    ∃ b:gJ,(b.lo:ℤ)≤w∧w≤(b.hi:ℤ) := by
  change 2354<w at hlo
  by_cases hrectTight:w≤2359
  · exact ⟨.rectTight,by change 2355≤w; omega,hrectTight⟩
  by_cases hrectPruned:w≤2367
  · exact ⟨.rectPruned,by change 2360≤w; omega,hrectPruned⟩
  by_cases hrectTailOne :w≤2374
  · exact ⟨.rectTailOne,by change 2368≤w; omega,hrectTailOne⟩
  by_cases hrectTailTwo:w≤2381
  · exact ⟨.rectTailTwo,by change 2375≤w; omega,hrectTailTwo⟩
  by_cases hrectTailThree :w≤2406
  · exact ⟨.rectTailThree,by change 2382≤w; omega,hrectTailThree⟩
  by_cases hgraph:w≤2534
  · exact ⟨.graph,by change 2407≤w; omega,hgraph⟩
  by_cases hnear :w≤2703
  · exact ⟨.near,by change 2535≤w; omega,hnear⟩
  by_cases hmiddle :w≤3599
  · exact ⟨.middle,by change 2704≤w; omega,hmiddle⟩
  exact ⟨.far,by change 3600≤w; omega,hhi⟩
theorem emS (b:gJ) :
    b.regular+aCe+aEu+1≤0x3c366c9e63c20c6:= by
  cases b <;> decide
end P6
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P6
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
def c1 :Prop :=
  ∀ u,abC u → ∀ (T:qo u) (R:Relation T),axB R
def c2 :Prop :=
  ∀ u,abC u → ∀ (T:qo u) (R:Relation T)
    (D:Reduction u T R) (B:KJ u T R D),
    axB R→Parallel B → ¬ aSM B →
    ∀ Γ,Tt u Γ→(∀ γ∈Γ,Normal u γ)→Γ.card≤t+1
def c3:Prop :=
  ∀ u,abC u → ∀ (T:qo u) (R:Relation T)
    (D:Reduction u T R) (B:KJ u T R D),
    axB R→baQ B →
    ∀ Γ,Tt u Γ→(∀ γ∈Γ,Normal u γ)→Γ.card≤0x26edb227db20730
def c4 :Prop :=
  ∀ u,abC u → ∀ (T:qo u) (R:Relation T) (D:Reduction u T R),
    axB R→Xb D.U D.V=4 →
    ∀ Γ,Tt u Γ→(∀ γ∈Γ,Normal u γ)→Γ.card≤0x1f0d2ea082df883
def c5:Prop :=
  ∀ u,abC u → ∀ (T:qo u) (R:Relation T)
    (D:Reduction u T R) (B:KJ u T R D),
    axB R→Parallel B→aSM B →
    ∀ Γ,Tt u Γ→(∀ γ∈Γ,Normal u γ) →
    Γ.card≤aCe ∨
      ∃ book :zJe K,book⊆Γ∧book.card≤aCe ∧
        ∃ M:jG u (pJ R),Nonempty (mJ M (Γ \ book))
def c6:Prop :=
  ∀ u deleted (M:jG u deleted) Γ,mJ M Γ →
    M.shift∉Γ→1≤M.iF→M.iF≤ajO →
    Γ.card≤lowRegular
def c7:Prop :=
  ∀ (b:gJ) u deleted (M:jG u deleted) Γ,mJ M Γ →
    M.shift∉Γ→(b.lo:ℤ)≤M.iF→M.iF≤(b.hi:ℤ) →
    Γ.card≤b.regular
def c8:Prop :=i4.axW dw LM
theorem bJa {u:e9} {Γ:zJe K} {γ:K} :
    γ∈aOW u Γ↔γ∈Γ∧Normal u γ:= by
  classical exact zO0
theorem c1E {u:e9} {Γ:zJe K} (hΓ:Tt u Γ) :
    Tt u (aOW u Γ) :=
  fun γ hγ=>hΓ γ (bJa.mp hγ).1
theorem c1G {u:e9} {Γ:zJe K} :
    ∀ γ∈aOW u Γ,Normal u γ :=
  fun _ hγ=>(bJa.mp hγ).2
theorem a1l (u:e9) (hu:abC u) (Γ:zJe K)
    (b:ℕ) (hb: (aOW u Γ).card≤b) :
    Γ.card≤b+aEu:= by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s :=Γ) (p:=Normal u)]
  exact Nat.add_le_add hb (fS8 u hu Γ)
theorem eyy :
    lowRegular+aCe+aEu+1 =
      NG:= by
  decide
theorem eE8:LM+aCe+aEu+1=0xa7844e5f1cc5:= by
  decide
private theorem structural_le_scalar :structuralCap≤NG:= by decide
private theorem structural_bound {n:ℕ} (h:n≤ structuralCap) :n≤NG :=
  h.trans structural_le_scalar
private theorem dNg (h5:c5) (h6:c6) (h7:c7) (hlist:i4.axW dw LM)
    (u:e9) (hu:abC u) (T:qo u) (R:Relation T)
    (D:Reduction u T R) (B:KJ u T R D) (hsat :axB R)
    (hp:Parallel B) (hn:aSM B) (Γ:zJe K) (hΓ:Tt u Γ) :
    Γ.card≤NG:= by
  classical
  let N :=aOW u Γ
  rcases h5 u hu T R D B hsat hp hn N (c1E hΓ) c1G with
    hcheap | ⟨book,hs,hb,M,⟨F⟩⟩
  · exact structural_bound ((a1l u hu Γ _ hcheap).trans (by decide))
  · have htotal:Γ.card≤(N \ book).card+book.card+aEu :=
      a1l u hu Γ _ (Finset.card_sdiff_add_card_eq_card hs).ge
    let regular :=(N \ book).erase M.shift
    have hsub:regular⊆N \ book :=Finset.erase_subset _ _
    have hshift:M.shift∉regular :=Finset.notMem_erase _ _
    let G:mJ M regular :=
      ⟨F.scalar,fun γ hγ=>F.mark γ (hsub hγ),F.distinct.mono hsub⟩
    have hchart: (N \ book).card - 1≤ regular.card:=Finset.pred_card_le_card_erase
    have hreserve (b:ℕ) (h:regular.card≤b) :
        Γ.card≤b+aCe+aEu+1 := by omega
    have hwmax :M.iF≤(DY:ℤ) := by
      have hh:=M.aVi
      change (M.E.natDegree :ℤ)-M.factor.natDegree - uO M.A₀ M.A₁≤DY
      omega
    by_cases hw₀:M.iF≤0
    · exact (hreserve _ (P1.dth hlist M _ G hw₀)).trans
        (eE8.le.trans (by decide))
    by_cases hwL:M.iF≤ajO
    · exact (hreserve _ (h6 u _ M _ G hshift (by omega) hwL)).trans eyy.le
    · obtain ⟨b,hlo,hhi⟩:=emJ M.iF (by omega) hwmax
      exact (hreserve _ (h7 b u _ M _ G hshift hlo hhi)).trans
        ((emS b).trans (by decide))
private theorem glX (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4)
    (h5:c5) (h6:c6) (h7:c7) (hlist:i4.axW dw LM)
    (u:e9) (Γ:zJe K) (hΓ:Tt u Γ) :Γ.card≤NG:= by
  classical
  by_cases hdef :aDf u<L
  · exact structural_bound ((dU4 u Γ hdef hΓ).trans (by decide))
  have hfirst:=Nat.le_antisymm (ebt u) (zqB hdef)
  by_cases hz :R5 u=0
  · exact structural_bound ((eex u Γ hfirst hz hΓ).trans (by decide))
  by_cases htype :aB8 u
  · exact structural_bound ((gE2 u htype Γ hΓ).trans (by decide))
  by_cases hprincipal:aKm u
  · exact structural_bound ((eOt u Γ hprincipal hΓ).trans (by decide))
  by_cases hconstant:aYx u
  · exact structural_bound ((dO2 u Γ hconstant hΓ).trans (by decide))
  obtain ⟨T⟩:=gEU u (Nat.pos_of_ne_zero hz) htype hprincipal
  have hu:abC u:=⟨gET T,hfirst,htype,hprincipal,hconstant⟩
  let R:=c78 hu T
  have hsat :=h1 u hu T R
  let N :=aOW u Γ
  have hN :=c1E hΓ
  have hnormal := @c1G u Γ
  by_cases hmoving:aSe R
  · exact structural_bound ((a1l u hu Γ _ (b9u u hu T R hmoving hsat N hN hnormal)).trans
      (by decide))
  have hnone (he :N = ∅) :Γ.card≤NG :=
    structural_bound ((a1l u hu Γ 0 (by rw [show aOW u Γ = ∅ from he]; simp)).trans
      (by decide))
  by_cases hinvalid :as1 R
  · apply hnone
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro γ hγ
    obtain ⟨hγΓ,hnγ⟩:=bJa.mp hγ
    obtain ⟨M⟩:=aCl u Γ hΓ γ hγΓ
    exact (hsat γ hnγ M).valid hinvalid
  by_cases hne :N.Nonempty
  · obtain ⟨γ,hγ⟩:=hne
    obtain ⟨hγΓ,hnγ⟩:=bJa.mp hγ
    obtain ⟨D,hfour | ⟨B,hnp | hpar⟩⟩:=dLq hu T R hmoving hinvalid hsat
      ⟨γ,hnγ,aCl u Γ hΓ γ hγΓ⟩
    · exact structural_bound ((a1l u hu Γ _ (h4 u hu T R D hsat hfour N hN hnormal)).trans
        (by decide))
    · exact structural_bound ((a1l u hu Γ _ (h3 u hu T R D B hsat hnp N hN hnormal)).trans
        (by decide))
    · by_cases hn:aSM B
      · exact dNg h5 h6 h7 hlist u hu T R D B hsat hpar hn Γ hΓ
      · exact structural_bound ((a1l u hu Γ _ (h2 u hu T R D B hsat hpar hn N hN hnormal)).trans
          (by decide))
  · exact hnone (Finset.not_nonempty_iff_eq_empty.mp hne)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4)
    (h5:c5) (h6:c6) (h7:c7) (h8:c8) :
    ProtocolClaim 6960 0x1418d040 0x40000000:= by
  have hlist:i4.axW dw LM:=h8
  exact c5P hlist (glX h1 h2 h3 h4 h5 h6 h7 hlist)
end
end P6
end
