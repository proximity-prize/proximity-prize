import ProximityPrize.SubmissionLower.ZtdrOue
set_option Elab.async false
open _root_ renaming Function.Injective → zq4, LinearMap.mulLeft → zzN, LinearMap.range → zWl, Module.finrank → zsE, MvPolynomial.monomial → ztt, Nat.add_comm → zg2, Nat.add_right_comm → zRL, Nat.cast_sub → zjK, Nat.mul_le_mul_left → zBI, Nat.sub_add_cancel → zxt, Polynomial.C → z1z, Polynomial.map_injective → zTo, Submodule.finrank_mono → zFM, Submodule.finrank_sup_add_finrank_inf_eq → z61
section
namespace qj0Yp9c
noncomputable section
open qrKC9pb
open cu (L)
def c1 :Prop :=
  ∀ (J:Input) (ι:Type) [Fintype ι] (a x :ι→L) (r :ι→Bool) (D : ∀ i,GraphPrime J (r i)),
    Nonempty ι→(∀ i,Over J (D i) (a i) (x i)) →
    ∃ C:Cut J,∀ i,qg C.toChart (D i)
def c2 :Prop :=
  ∀ (J:Input) (C:Cut J),∃ b₀ h₀:ℕ,b₀≤J.b∧h₀≤J.h ∧
    ∀ a b c:ℕ,2*J.l≤a→b₀+J.b+J.s≤b→h₀+J.h≤ c →
      2*(zsE C.base (dO C.toChart a b c) :ℤ) ≤
        cutDifference J.s J.l J.b J.h b₀ h₀ a b c
private theorem difference_slope (s l b h b₀ h₀ a x z n:ℤ) :
    cutDifference s l b h b₀ h₀ (a+n*(l-2)) (x+n*(b+s)) (z+n*h) =
      cutDifference s l b h b₀ h₀ a x z+2*n*
        (((6*l-4)*b+(3*l*l-2)*s)*h -
          (b-b₀)*(2*l-2)*h -
          (h-h₀)*((2*l-2)*(b+s)+s*l*(l-2))) := by
  unfold cutDifference twiceCount
  ring
private theorem stage {J:Input} (C:Chart J) (hp:relativePolar C≠0)
  {V W T:Submodule C.base (EC J)}
  [FiniteDimensional C.base V] [FiniteDimensional C.base W] [FiniteDimensional C.base T]
  (hV:V≤T) (hW:W.map (nY C)≤T) (hR:W≤(aho C).toSubmodule)
  (hd:Disjoint V ((aho C).toSubmodule.map (nY C))) :
  zsE C.base W+Module.finrank C.base V≤zsE C.base T:= by
 let U:=W.map (nY C)
 have hdis :Disjoint U V:=(hd.mono_right (Submodule.map_mono hR)).symm
 have hdim:zsE C.base U=zsE C.base W :=
  (W.equivMapOfInjective (nY C) (fun x y h=>mul_left_cancel₀ hp h)).finrank_eq.symm
 have hr :=z61 U V
 rw [hdis.eq_bot,finrank_bot,add_zero,hdim] at hr
 rw [← hr]
 exact zFM (sup_le hW hV)
theorem of_children (cut:c1) (rank :c2) :qrKC9pb.c4 := by
  intro J ι _ a x r D hi ho
  rcases isEmpty_or_nonempty ι with hempty | hι
  · let _:=hempty
    simp
  obtain ⟨C,hC⟩:=cut J ι a x r D hι ho
  let S:=C.toChart
  obtain ⟨b₀,h₀,hb,hh,hupper⟩:=rank J C
  obtain ⟨V,hfd,hV,hd,hcharge⟩:=polar_classes S a x r D hi ho hC
  let _:=hfd
  obtain ⟨N,hN⟩:=piece_cofinal S V hV
  let A:=N+2*J.l+(b₀+J.b+J.s)+(h₀+J.h)+1
  let dA:=J.l-2
  let dB:=J.b+J.s
  let W (n:ℕ) :=dO S (A+n*dA) (A+n*dB) (A+n*J.h)
  let m := ∑ i,polarOrder (D i)
  have hstep (n:ℕ) :zsE S.base (W n)+m≤zsE S.base (W (n+1)) := by
    refine (Nat.add_le_add_left hcharge _).trans ?_
    have hmul' : (W n).map (nY S)≤W (n+1) := by
      dsimp only [W]
      simp only [Nat.add_mul,one_mul,← Nat.add_assoc]
      exact polar_mul_piece S _ _ _ (by dsimp [A]; omega)
    exact stage S (relativePolar_ne S) (hN _ _ _ (by dsimp [A]; omega)
      (by dsimp [A]; omega) (by dsimp [A]; omega)) hmul' (piece_le_ring _ _ _ _) hd
  have hlower (n:ℕ) :n*m≤zsE S.base (W n) := by
    induction n with
    | zero=>simp
    | succ n ih =>
      rw [Nat.succ_mul]
      exact (Nat.add_le_add_right ih _).trans (hstep n)
  let offset :=cutDifference J.s J.l J.b J.h b₀ h₀ A A A
  have htwo:2≤J.l:=J.Ca.two_le
  have hslope (n:ℕ) :
      2*(n:ℤ)*m≤offset+2*(n:ℤ)*polarBudget J:= by
    have hu:=hupper (A+n*dA) (A+n*dB) (A+n*J.h)
      (by dsimp [A]; omega) (by dsimp [A]; omega) (by dsimp [A]; omega)
    have hlow:2*(n:ℤ)*m≤2*(zsE S.base (W n) :ℤ) := by
      rw [mul_assoc]
      exact_mod_cast zBI 2 (hlower n)
    refine hlow.trans (hu.trans ?_)
    dsimp [dA,dB]
    push_cast [zjK htwo]
    rw [difference_slope]
    have h₁: (0:ℤ)≤(J.b:ℤ)-b₀:=sub_nonneg.mpr (by exact_mod_cast hb)
    have h₂: (0:ℤ)≤(J.h:ℤ)-h₀:=sub_nonneg.mpr (by exact_mod_cast hh)
    have h₃: (0:ℤ)≤(J.l:ℤ)-2 :=sub_nonneg.mpr (by exact_mod_cast htwo)
    have h₄: (0:ℤ)≤2*(J.l:ℤ)-2 := by omega
    have hmain: (4 :ℕ)≤6*J.l:= by omega
    have hmain' : (2 :ℕ)≤3*J.l*J.l:= by
      have :=zBI (3*J.l) htwo
      omega
    have hd₁:0≤((J.b:ℤ)-b₀)*(2*(J.l:ℤ)-2)*J.h:= by positivity
    have hd₂:0≤((J.h:ℤ)-h₀)*
        ((2*(J.l:ℤ)-2)*((J.b:ℤ)+J.s)+(J.s :ℤ)*J.l*((J.l:ℤ)-2)) := by positivity
    unfold offset polarBudget
    push_cast [zjK hmain,zjK hmain']
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_
      (show (0:ℤ)≤2*(n:ℤ) by positivity))
    omega
  by_contra! h
  have hdiff : (polarBudget J:ℤ)+1≤ m:= by exact_mod_cast Nat.succ_le_of_lt h
  let n:=offset.natAbs+1
  have hn:offset<(n:ℤ) := by
    dsimp [n]
    have :=Int.le_natAbs (a :=offset)
    omega
  have hm:=mul_le_mul_of_nonneg_left hdiff (show (0:ℤ)≤2*(n:ℤ) by positivity)
  have he :=hslope n
  rw [mul_add,mul_one] at hm
  omega
end
end qj0Yp9c
end
section
namespace qO4AyGb
noncomputable section
open Polynomial qrKC9pb
open cu (L)
open P5_7_7 (Dg)
def constMap (J:Input) :L →+* EC J :=
 (((a7W J).comp z1z).comp z1z).comp z1z
def gauge (J:Input) (τ:L) :EC J :=
 1+constant J τ*jU J false
def qW (J:Input) (τ b:L) :EC J :=
 constant J b*(jU J false/gauge J τ)+jet J false/gauge J τ^2
def extend {E :Type} [CommRing E] (e :L →+* E) :Dg →+* E[X][X][X] :=
 mapRingHom (mapRingHom (mapRingHom e))
def liftedEquation (J:Input) : (RatFunc L)[X][X][X] :=
 extend RatFunc.C J.F
def independentParameter : (RatFunc L)[X][X][X] :=
 z1z (z1z (z1z RatFunc.X))
def liftedCutter (G H :Dg) : (RatFunc L)[X][X][X] :=
 extend RatFunc.C G - independentParameter*extend RatFunc.C H
end
end qO4AyGb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qBTXDtb
noncomputable section
variable {K V:Type} [Field K] [AddCommGroup V] [Module K V]
private abbrev multiples (F:Multi K) (S:Submodule K (Multi K)) :=
 S.map (zzN K F)
private theorem rank_multiples {F:Multi K} (hF:F≠0) (S:Submodule K (Multi K)) :
   zsE K (multiples F S)=zsE K S :=
 (S.equivMapOfInjective (zzN K F) (fun _ _ h=>mul_left_cancel₀ hF h)).finrank_eq.symm
theorem rank_cut (e :Multi K →ₗ[K] V) (s l B H b₀ h₀ a b c:ℕ) {F G:Multi K}
   (hF:Prime F) (hd : ¬ F∣G) (hG:G∈space K s l B H)
   (ho:deg 1 0 0 F=l) (hz :deg 0 1 0 F=h₀) (hw:deg s 0 1 F=b₀+l*s)
   (hkillF : ∀ P,e (F*P)=0) (hkillG : ∀ P,e (G*P)=0) :
   zsE K (zWl (e.domRestrict (space K s (a+l+l) (b+B+b₀) (c+H+h₀)))) +
     zsE K (space K s (a+l) (b+B) (c+H)) +
     zsE K (space K s (a+l) (b+b₀) (c+h₀)) ≤
   zsE K (space K s (a+l+l) (b+B+b₀) (c+H+h₀)) +
     zsE K (space K s a b c) := by
 let T:=space K s (a+l+l) (b+B+b₀) (c+H+h₀)
 let S₁:=space K s (a+l) (b+B) (c+H)
 let S₂:=space K s (a+l) (b+b₀) (c+h₀)
 let S₀:=space K s a b c
 let U:=multiples F S₁
 let W:=multiples G S₂
 have hf :F∈space K s l b₀ h₀:=mem_space.mpr ⟨ho.le,hz.le,hw.le⟩
 have hu:U≤T:= by
   rintro _ ⟨P,hP,rfl⟩
   change F*P∈T
   rw [mul_comm]
   exact space_mul hP hf
 have hw' : W≤T:= by
   rintro _ ⟨P,hP,rfl⟩
   change G*P∈space K s (a+l+l) (b+B+b₀) (c+H+h₀)
   rw [mul_comm,zRL b B b₀,zRL c H h₀]
   exact space_mul hP hG
 have hk :U ⊔ W≤LinearMap.ker e := by
   apply sup_le
   · rintro _ ⟨P,_,rfl⟩
     exact hkillF P
   · rintro _ ⟨P,_,rfl⟩
     exact hkillG P
 have hk' : (U ⊔ W).comap T.subtype≤LinearMap.ker (e.domRestrict T) := by
   rw [LinearMap.ker_domRestrict]
   exact Submodule.comap_mono hk
 have hi:U ⊓ W≤ multiples (F*G) S₀:= by
   rintro x ⟨⟨P,_,hP⟩,⟨Q,hQ,hx⟩⟩
   change F*P=x at hP
   change G*Q=x at hx
   obtain ⟨R,hR⟩:=(hF.dvd_mul.mp (show F∣G*Q from ⟨P,hx.trans hP.symm⟩)).resolve_left hd
   have hr :F*R∈space K s (l+a) (b₀+b) (h₀+c) := by
     rw [← hR,zg2 l a,zg2 b₀ b,zg2 h₀ c]
     exact hQ
   refine ⟨R,space_cancel hF.ne_zero ho hz hw hr,?_⟩
   change (F*G)*R=x
   rw [mul_comm F G,mul_assoc,← hR,hx]
 have hsd:=zFM hk'
 rw [(Submodule.comapSubtypeEquivOfLe (sup_le hu hw')).finrank_eq] at hsd
 have hid :=zFM hi
 have hg:G≠0:= fun h=>hd (h.symm ▸ dvd_zero F)
 rw [rank_multiples (mul_ne_zero hF.ne_zero hg)] at hid
 have hsum:=z61 U W
 change _+_=zsE K (multiples F S₁)+Module.finrank K (multiples G S₂) at hsum
 rw [rank_multiples hF.ne_zero,rank_multiples hg] at hsum
 have hr :=(e.domRestrict T).finrank_range_add_finrank_ker
 change zsE K (zWl (e.domRestrict T)) +
   zsE K S₁+Module.finrank K S₂≤zsE K T+Module.finrank K S₀
 omega
end
end qBTXDtb
end
section
set_option maxHeartbeats 600000
namespace qBTXDtb
noncomputable section
open Polynomial qrKC9pb qj0Yp9c
private theorem exp_zero :exponent 0 0 0=0:= by
 ext v
 cases v with
 | none=>simp
 | some v =>
   cases v with
   | none=>simp
   | some v=>cases v; simp
private def evalMulti {J:Input} (C:Chart J) :Multi C.base →ₐ[C.base] EC J where
 toRingHom:=(m8 C).comp expand.symm.toRingHom
 commutes' d:= by
  change m8 C (expand.symm (MvPolynomial.C d))=(d:EC J)
  have hm:=expand_monomial 0 0 0 d
  simp only [exp_zero,Polynomial.monomial_zero_left,MvPolynomial.monomial_zero'] at hm
  rw [← hm,RingEquiv.symm_apply_apply]
  simp [m8,coe_eval₂RingHom,eval₂_C]
private theorem evalMulti_apply {J:Input} (C:Chart J) (P:Multi C.base) :
 evalMulti C P=m8 C (expand.symm P) :=rfl
private def scaledEval {J:Input} (C:Chart J) (a :ℕ) :Multi C.base →ₗ[C.base] EC J where
 toFun P:=evalMulti C P/denominator C ^a
 map_add' P Q:= by rw [map_add,add_div]
 map_smul' r P:= by
  change evalMulti C (r•P)/denominator C ^a=r•(evalMulti C P/denominator C ^a)
  rw [map_smul,smul_div_assoc]
private theorem scaledEval_apply {J:Input} (C:Chart J) (a :ℕ) (P:Multi C.base) :
 scaledEval C a P=evalMulti C P/denominator C ^a :=rfl
private theorem range_eval {J:Input} (C:Chart J) (a b c:ℕ) :
   zWl ((scaledEval C a).domRestrict (space C.base J.s a b c))=dO C a b c:= by
 apply le_antisymm
 · rintro _ ⟨P,rfl⟩
   change scaledEval C a P.val∈dO C a b c
   rw [scaledEval_apply,evalMulti_apply]
   apply scaled_eval_mem
   apply fits_expand.mpr
   rw [RingEquiv.apply_symm_apply]
   exact P.property
 · apply Submodule.span_le.mpr
   rintro _ ⟨m,rfl⟩
   let N :=gradeIndex m
   have hN :ztt N.val (1 :C.base)∈space C.base J.s a b c :=
    (MvPolynomial.monomial_mem_restrictSupport C.base).mpr (Or.inl N.property)
   refine ⟨⟨_,hN⟩,?_⟩
   change scaledEval C a (ztt (exponent m.1.val m.2.2.val m.2.1.val) 1) =
    pieceMono C m
   rw [← expand_monomial,scaledEval_apply,evalMulti_apply,RingEquiv.symm_apply_apply]
   simp only [m8,coe_eval₂RingHom,eval₂_monomial,map_one,one_mul,pieceMono,mono]
   have hp:denominator C ^a=denominator C ^(a-m.1.val)*denominator C ^m.1.val := by
    rw [← pow_add,zxt (Nat.le_of_lt_succ m.1.isLt)]
   rw [hp]
   simp only [numeratorU,numeratorV,div_eq_mul_inv,mul_inv_rev,inv_pow,mul_pow]
   ring
private theorem equation_bounds {J:Input} (C:Chart J) :
   (equation C).natDegree=J.l∧fits J.s J.l J.b J.h (equation C) := by
 have h₁:zq4 (mapRingHom C.scalar) :=zTo _ C.scalar.injective
 have h₂:zq4 (mapRingHom (mapRingHom C.scalar)) :=zTo _ h₁
 have ho: (equation C).natDegree=J.l:= by
   simpa only [equation,coe_mapRingHom,natDegree_map_eq_of_injective h₂] using J.Ca.jU
 refine ⟨ho,ho.le,fun k => ?_,fun k j hj => ?_⟩
 · simpa only [equation,coe_mapRingHom,coeff_map,natDegree_map_eq_of_injective h₁]
     using J.Ca.height k
 · simp only [equation,coe_mapRingHom,coeff_map,
     natDegree_map_eq_of_injective C.scalar.injective] at hj ⊢
   exact J.weight k j (fun hz=>hj (by rw [hz,Polynomial.map_zero]))
theorem proof :qj0Yp9c.c2 := by
 intro J C
 let F:=expand (equation C.toChart)
 let G:=expand C.an1
 have hf :Prime F:=comap_prime (expand (K:=C.base)).symm.toRingHom expand.toRingHom
  expand.apply_symm_apply (by simpa [F] using C.prime_eq)
 have hd : ¬ F∣G:= fun h=>C.proper ((map_dvd_iff (expand (K:=C.base))).mp h)
 have hG:G∈space C.base J.s J.l (J.b+J.s) J.h:=fits_expand.mp C.fits_cutter
 obtain ⟨ho,hf'⟩:=equation_bounds C.toChart
 have hbds :=mem_space.mp (fits_expand.mp hf')
 have hlead:=leading_bounds C.prime_eq.ne_zero J.s
 rw [ho] at hlead
 let b₀:=deg J.s 0 1 F-J.l*J.s
 let h₀:=deg 0 1 0 F
 have hF₁:deg 1 0 0 F=J.l:=le_antisymm hbds.1 hlead.1
 have hF₂:deg J.s 0 1 F=b₀+J.l*J.s :=(zxt hlead.2).symm
 have hb₀:b₀≤J.b:= by
  have h:deg J.s 0 1 F≤J.b+J.l*J.s :=hbds.2.2
  omega
 refine ⟨b₀,h₀,hb₀,hbds.2.1,?_⟩
 intro a b c ha hb hc
 let B:=J.b+J.s
 let u:=a-(J.l+J.l)
 let v :=b-(B+b₀)
 let w:=c-(J.h+h₀)
 have ha' : u+J.l+J.l=a := by dsimp [u]; omega
 have hb' : v+B+b₀=b:= by dsimp [v,B]; omega
 have hc' : w+J.h+h₀=c:= by dsimp [w]; omega
 have hzeroF:evalMulti C.toChart F=0:= by
  dsimp only [F]
  rw [evalMulti_apply,RingEquiv.symm_apply_apply,equation_vanish]
 have hzeroG:evalMulti C.toChart G=0:= by
  dsimp only [G]
  rw [evalMulti_apply,RingEquiv.symm_apply_apply,C.vanish]
 have hr :=rank_cut (scaledEval C.toChart a) J.s J.l B J.h b₀ h₀ u v w
  hf hd hG hF₁ rfl hF₂
  (fun P=> by rw [scaledEval_apply,map_mul,hzeroF,zero_mul,zero_div])
  (fun P=> by rw [scaledEval_apply,map_mul,hzeroG,zero_mul,zero_div])
 rw [ha',hb',hc',range_eval] at hr
 have ht:=twice_finrank C.base J.s a b c
 have h1 :=twice_finrank C.base J.s (u+J.l) (v+B) (w+J.h)
 have h2 :=twice_finrank C.base J.s (u+J.l) (v+b₀) (w+h₀)
 have h0:=twice_finrank C.base J.s u v w
 have ha₁: ((u+J.l:ℕ) :ℤ)=(a :ℤ)-J.l:= by omega
 have ha₂: (u:ℤ)=(a :ℤ)-2*J.l:= by omega
 have hb₁: ((v+B:ℕ) :ℤ)=(b:ℤ)-b₀:= by omega
 have hb₂: ((v+b₀:ℕ) :ℤ)=(b:ℤ)-J.b-J.s := by dsimp [B] at hb'; omega
 have hb₃: (v :ℤ)=(b:ℤ)-b₀-J.b-J.s := by dsimp [B] at hb'; omega
 have hc₁: ((w+J.h:ℕ) :ℤ)=(c:ℤ)-h₀:= by omega
 have hc₂: ((w+h₀:ℕ) :ℤ)=(c:ℤ)-J.h:= by omega
 have hc₃: (w:ℤ)=(c:ℤ)-h₀-J.h:= by omega
 unfold cutDifference
 rw [← ha₂,← ha₁,← hb₃,← hb₁,← hb₂,← hc₃,← hc₁,← hc₂,← ht,← h1,← h2,← h0]
 omega
end
end qBTXDtb
end
