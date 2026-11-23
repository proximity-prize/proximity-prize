import ProximityPrize.SubmissionLower.ZoOOLsc
import ProximityPrize.SubmissionLower.Zi7X5ad
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace qwQWGra
noncomputable section
open IsLocalRing WithZero
open scoped WithZero
open P5 (p)
variable {K M:Type} [Field K] [Field M] [Algebra K M]
variable (v :Valuation K ℤᵐ⁰) (w:Valuation M ℤᵐ⁰)
local notation "O" => v.valuationSubring
local notation "V" => w.valuationSubring
private theorem small_iff {a :ℤᵐ⁰} : a<1↔a≤exp (-1 :ℤ) := by
 simpa only [← exp_add,neg_add_cancel,exp_zero] using
  (lt_mul_exp_iff_le (x :=a) (y :=exp (-1 :ℤ)) exp_ne_zero)
private theorem unit_nat [CharP M p] {e :ℕ} (he :0<e) (hp:e<p) :
  w (e :M)=1 := by
 let:CharP V p:=(ValuationSubring.subtype V).charP Subtype.val_injective p
 let:CharP (ResidueField V) p :=
  CharP.of_ringHom_of_ne_zero (residue V) p (he.trans hp).ne'
 have hn: (e :ResidueField V)≠0:= fun hz =>
  hp.not_ge (Nat.le_of_dvd he ((CharP.cast_eq_zero_iff _ _ _).mp hz))
 have hu:IsUnit (e :V) :=(residue_ne_zero_iff_isUnit _).mp (by rwa [map_natCast])
 exact (Valuation.valuationSubring.integers w).one_of_isUnit hu
private theorem residue_zero [v.HasExtension w] [Algebra.IsSeparable (ResidueField O) (ResidueField V)]
    (D:Derivation ℤ M M) (hreg : ∀ x,w x≤1→w (D x)≤1)
    (hideal : ∀ x,w x<1→w (D x)<1)
    (hbase : ∀ x :O,w (D (algebraMap K M (x :K)))<1) :
    ∀ x,w x≤1→w (D x)<1 := by
  let d:Derivation ℤ V V:=Derivation.mk'
    { toFun:= fun x=>⟨D x,hreg x x.property⟩
      map_add' := fun x y=>Subtype.ext (D.map_add (x :M) y)
      map_smul' := fun n x=>Subtype.ext (D.map_smul n (x :M)) }
    (fun x y=>Subtype.ext (D.leibniz (x :M) y))
  let ρ:=(residue V).toIntAlgHom
  have hker (x :V) (hx :ρ x=0) :ρ (d x)=0 :=
    (residue_eq_zero_iff _).mpr (w.mem_maximalIdeal_iff.mpr
      (hideal x (w.mem_maximalIdeal_iff.mp ((residue_eq_zero_iff _).mp hx))))
  let dr :=Derivation.liftOfSurjective (f :=ρ) residue_surjective hker
  have hdr (x :V) :dr (residue V x)=residue V (d x) :=
    Derivation.liftOfSurjective_apply (f :=ρ) residue_surjective hker x
  have hk (a :ResidueField O) :dr (algebraMap (ResidueField O) (ResidueField V) a)=0:= by
    obtain ⟨b,rfl⟩:=residue_surjective a
    rw [Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap,hdr,residue_eq_zero_iff,
      w.mem_maximalIdeal_iff]
    exact hbase b
  let dr' : Derivation (ResidueField O) (ResidueField V) (ResidueField V) :=
    Derivation.mk'
      { toFun:=dr
        map_add' := dr.map_add
        map_smul' := fun a b=> by
          simp only [Algebra.smul_def,dr.leibniz,hk,mul_zero,add_zero,
            Algebra.algebraMap_self,RingHom.id_apply] }
      dr.leibniz
  let:Algebra.FormallyUnramified (ResidueField O) (ResidueField V) :=
    Algebra.FormallyUnramified.of_isSeparable _ _
  let E :=KaehlerDifferential.linearMapEquivDerivation (ResidueField O) (ResidueField V)
    (M:=ResidueField V)
  have hzero :dr' = 0:=E.symm.injective (Subsingleton.elim _ _)
  intro x hx
  let a :V:=⟨x,hx⟩
  have hr :residue V (d a)=0:= by
    rw [← hdr]
    exact DFunLike.congr_fun hzero (residue V a)
  exact w.mem_maximalIdeal_iff.mp ((residue_eq_zero_iff _).mp hr)
private theorem tangent_uniformizer (D:Derivation ℤ M M) {t a :M} {e :ℕ}
  (ht:0<w t) (ha :w a=w t^e) (he :0<e) (he' : w (e :M)=1)
  (hreg : ∀ x,w x≤1→w (D x)≤1) (hD:w (D a)≤w t^e) :
  w (D t)≤w t:= by
 have ht0:t≠0:=w.ne_zero_iff.mp ht.ne'
 let b:=a/t^e
 have hb:w b=1 := by
  rw [show b= _ from rfl,map_div₀,map_pow,ha,div_self (pow_ne_zero _ ht.ne')]
 have hab:t^e*b=a := by
  rw [mul_comm]
  exact div_mul_cancel₀ a (pow_ne_zero _ ht0)
 have hh: (e :M)*b*(t^(e - 1)*D t)=D a - t^e*D b:= by
  rw [← hab,D.leibniz,D.leibniz_pow]
  simp only [smul_eq_mul,nsmul_eq_mul,add_sub_cancel_left]
  ring
 have hle :=w.map_sub_le hD (show w (t^e*D b)≤w t^e by
  rw [map_mul,map_pow]
  exact mul_le_of_le_one_right' (hreg b hb.le))
 have hpow:w t^e=w t^(e - 1)*w t:= by
  conv_lhs=>rw [← Nat.sub_add_cancel he,pow_succ]
 rw [← hh,map_mul,map_mul,he',hb,one_mul,map_mul,map_pow,hpow] at hle
 exact (mul_le_mul_iff_right₀ (pow_pos ht (e - 1))).mp (by simpa only [one_mul] using hle)
private theorem tangent_ideal {t:M} (ht:w t=exp (-1 :ℤ))
   (D:Derivation ℤ M M) (hreg : ∀ x,w x≤1→w (D x)≤1)
   (hDt:w (D t)≤w t) (x :M) (hx :w x<1) :w (D x)<1 := by
 have htpos :0<w t:= by rw [ht]; exact exp_pos
 have htlt:w t<1 := by rw [ht,← exp_zero,exp_lt_exp]; decide
 let a :=x/t
 have ha :w a≤1 := by
   rw [show a= _ from rfl,map_div₀,div_le_one₀ htpos,ht]
   exact small_iff.mp hx
 have hxt:a*t=x :=div_mul_cancel₀ x (w.ne_zero_iff.mp htpos.ne')
 rw [← hxt,D.leibniz,smul_eq_mul,smul_eq_mul]
 refine (w.map_add_le ?_ ?_).trans_lt htlt
 · rw [map_mul]
   exact (mul_le_mul' ha hDt).trans_eq (one_mul _)
 · rw [map_mul]
   exact mul_le_of_le_one_right' (hreg a ha)
private theorem log_of_tangent {t x :M} (ht:w t=exp (-1 :ℤ)) (hx :x≠0)
    (D:Derivation ℤ M M) (hreg : ∀ z,w z≤1→w (D z)≤1)
    (hDt:w (D t)≤w t) :w (D x/x)≤1 := by
  have htpos :0<w t:= by rw [ht]; exact exp_pos
  have hxpos :0<w x :=pos_iff_ne_zero.mpr (w.ne_zero_iff.mpr hx)
  let n := -log (w x)
  let b:=t^n
  have hb:w b=w x := by
    change w (t^n)=w x
    rw [map_zpow₀,ht,← exp_zsmul,show n•(-1 :ℤ)=log (w x) by simp [n],
      exp_log hxpos.ne']
  let c:=x/b
  have hc:w c=1 := by
    rw [show c= _ from rfl,map_div₀,hb,div_self hxpos.ne']
  have hbc:c*b=x :=div_mul_cancel₀ x (w.ne_zero_iff.mp (hb.symm ▸ hxpos.ne'))
  have hDb:w (D b)≤w b:= by
    change w (D (t^n))≤w (t^n)
    rw [D.leibniz_zpow,zsmul_eq_mul,smul_eq_mul,map_mul,map_mul,map_zpow₀,map_zpow₀]
    have hn:w (n:M)≤1 :=((n:V)).property
    calc
      _≤1*(w t^(n - 1)*w t) :=mul_le_mul' hn (mul_le_mul' le_rfl hDt)
      _=w t^n:= by
        rw [one_mul,← zpow_add_one₀ htpos.ne',sub_add_cancel]
  rw [map_div₀,div_le_one₀ hxpos,← hbc,D.leibniz,smul_eq_mul,smul_eq_mul,map_mul,hc,one_mul]
  apply w.map_add_le
  · rw [map_mul,hc,one_mul]; exact hDb
  · rw [map_mul]; exact mul_le_of_le_one_right' (hreg c hc.le)
theorem proof :qoGY3we.c1 := by
  intro K M _ _ _ _ _ hd v w e D₀ D hv hw he hval hD hreg x hx hcase
  let:v.HasExtension w:=extension v w e he hval
  let:CharP M p:=charP_of_injective_ringHom (algebraMap K M).injective p
  have hm (z :K) (hz :v z≤1) :w (D (algebraMap K M z))≤1 := by
    rw [hD,hval]
    exact pow_le_one₀ zero_le (hreg z hz)
  obtain ⟨hp,hsep,B,hB,hb⟩:=local_data v w e he hv hw hval hd D hm
  let:Algebra.IsSeparable (ResidueField v.valuationSubring)
      (ResidueField w.valuationSubring) :=hsep
  obtain ⟨π,hπ⟩:=hv (exp (-1 :ℤ))
  obtain ⟨τ,hτ⟩:=hw (exp (-1 :ℤ))
  have hτpos :0<w τ:= by rw [hτ]; exact exp_pos
  have hτlt:w τ<1 := by rw [hτ,← exp_zero,exp_lt_exp]; decide
  have hπτ:v π=w τ:=hπ.trans hτ.symm
  let a :=algebraMap K M π
  have ha :w a=w τ^e :=(hval π).trans (congrArg (· ^ e) hπτ)
  have heunit :w (e :M)=1 :=unit_nat w he hp
  have htang (h : ∀ z,v z<1→v (D₀ z)<1) :w (D a)≤w τ^e := by
    change w (D (algebraMap K M π))≤_
    rw [hD,hval]
    apply pow_le_pow_left₀ zero_le
    rw [hτ]
    exact small_iff.mp (h π (hπτ.trans_lt hτlt))
  let S (n:ℕ) :=τ^n•D
  let good (n:ℕ) := ∀ z,w z≤1→w (S n z)≤1
  have hex : ∃ n,good n:= by
    have hBp:0<B:=zero_lt_one.trans_le hB
    obtain ⟨n,hn⟩:=exists_exp_neg_natCast_lt (inv_ne_zero hBp.ne')
    have hs :w τ^n≤B⁻¹:= by
      rw [hτ,← exp_nsmul]
      simpa using hn.le
    refine ⟨n,fun z hz => ?_⟩
    change w (τ^n*D z)≤1
    rw [map_mul,map_pow]
    exact (mul_le_mul' hs (hb z hz)).trans_eq (inv_mul_cancel₀ hBp.ne')
  classical
  have hu:good 0:= by
    let n:=Nat.find hex
    have hn:good n:=Nat.find_spec hex
    by_cases hn0:n=0
    · exact hn0 ▸ hn
    have hs :w τ^n≤w τ:= by
      obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero hn0
      rw [hk,pow_succ]
      exact mul_le_of_le_one_left' (pow_le_one₀ zero_le hτlt.le)
    have hs' (z :M) :w (S n z)=w τ^n*w (D z) := by
      change w (τ^n*D z)= _
      rw [map_mul,map_pow]
    have hstay :w (S n a)≤w τ^e := by
      rw [hs']
      rcases hcase with ht | ⟨rfl,_⟩
      · exact (mul_le_mul' (hs.trans hτlt.le) (htang ht)).trans_eq (one_mul _)
      · simpa only [pow_one,mul_one] using
          mul_le_mul' hs (hm π (hπτ.trans_le hτlt.le))
    have hSt:w (S n τ)≤w τ :=
      tangent_uniformizer w (S n) hτpos ha he heunit hn hstay
    have hz :=residue_zero v w (S n) hn (tangent_ideal w hτ (S n) hn hSt) (by
      intro b
      rw [hs']
      exact ((mul_le_mul' hs (hm b b.property)).trans_eq (mul_one _)).trans_lt hτlt)
    have hn1 :n - 1+1=n:=Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)
    have hg:good (n - 1) := by
      intro z hzr
      have hh:=small_iff.mp (hz z hzr)
      rw [hs',hτ] at hh
      have heq :w τ^n*w (D z)=w τ*w (S (n - 1) z) := by
        change _=w τ*w (τ^(n - 1)*D z)
        rw [map_mul,map_pow,← mul_assoc,← pow_succ',hn1]
      rw [← hτ,heq] at hh
      exact (mul_le_mul_iff_right₀ hτpos).mp (by simpa only [mul_one] using hh)
    exact (Nat.find_min hex (show n - 1<n by omega) hg).elim
  have hUp (z :M) (hz :w z≤1) :w (D z)≤1 := by
    have hh:=hu z hz
    change w ((τ^0:M)*D z)≤1 at hh
    simpa only [pow_zero,one_mul] using hh
  rcases hcase with ht | ⟨_,hx'⟩
  · exact log_of_tangent w hτ hx D hUp (tangent_uniformizer w D hτpos ha he heunit hUp (htang ht))
  · rw [map_div₀,hx',div_one]
    exact hUp x hx'.le
end
end qwQWGra
