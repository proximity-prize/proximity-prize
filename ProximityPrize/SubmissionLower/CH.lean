import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower.ContactTwoTailDVRExact6731Research
open IsLocalRing
variable {K R:Type*} [CommRing K] [CommRing R] [Algebra K R]
private theorem prime_dvd_factorial:∀ {n p:ℕ},p.Prime → (p∣n.factorial ↔ p ≤ n)
 | 0,_,hp => iff_of_false hp.not_dvd_one (not_le_of_gt hp.pos)
 | n+1,p,hp => by
     rw [Nat.factorial_succ,hp.dvd_mul,prime_dvd_factorial hp]
     exact ⟨fun h => h.elim (Nat.le_of_dvd (Nat.succ_pos _)) Nat.le_succ_of_le,
       fun h => (_root_.lt_or_eq_of_le h).elim
         (Or.inr ∘ Nat.le_of_lt_succ) fun h => Or.inl <| by rw [h]⟩
theorem derivation_pow_mul (D:Derivation K R R) (pi u:R) (mu:ℕ)
   (hmu:1 ≤ mu):
   D (pi^mu*u)=
     pi^(mu-1)*((mu:R)*u*D pi+pi*D u):=by
 rw [D.leibniz,Derivation.leibniz_pow]
 simp only [nsmul_eq_mul,smul_eq_mul]
 have hpow:pi^mu=pi^(mu-1)*pi:=by
   obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hmu
   simp [Nat.add_comm,pow_succ]
 rw [hpow]
 ring
theorem tangent_pow_mul (D:Derivation K R R) (pi u a:R) (mu:ℕ)
   (hmu:1 ≤ mu) (htangent:D pi=pi*a):
   D (pi^mu*u)=pi^mu*((mu:R)*a*u+D u):=by
 rw [derivation_pow_mul D pi u mu hmu,htangent]
 have hpow:pi^mu=pi^(mu-1)*pi:=by
   obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hmu
   simp [Nat.add_comm,pow_succ]
 rw [hpow]
 ring
theorem tangent_preserves_divisibility (D:Derivation K R R) (pi a:R) (mu:ℕ)
   (hmu:1 ≤ mu) (htangent:D pi=pi*a) (f:R) (hf:pi^mu∣f):
   pi^mu∣D f:=by
 obtain ⟨u,rfl⟩:=hf
 rw [tangent_pow_mul D pi u a mu hmu htangent]
 exact dvd_mul_right _ _
theorem tangent_iterate_preserves_divisibility
   (D:Derivation K R R) (pi a:R) (mu:ℕ)
   (hmu:1 ≤ mu) (htangent:D pi=pi*a) (f:R) (hf:pi^mu∣f):
   ∀ r,pi^mu∣(D:R → R)^[r] f:=by
 intro r
 induction r with
 | zero => simpa using hf
 | succ r ih =>
     rw [Function.iterate_succ_apply']
     exact tangent_preserves_divisibility D pi a mu hmu htangent _ ih
theorem iterate_pow_mul_expansion (D:Derivation K R R) (pi u:R)
   (mu r:ℕ) (hr:r ≤ mu):
   ∃ error:R,
     (D:R → R)^[r] (pi^mu*u)=
       (mu.descFactorial r:R)*pi^(mu-r)*u*(D pi)^r+
         pi^(mu-r+1)*error:=by
 induction r with
 | zero =>
     refine ⟨0,?_⟩
     simp
 | succ r ih =>
     have hr0:r ≤ mu:=le_trans (Nat.le_succ r) hr
     obtain ⟨error,herror⟩:=ih hr0
     obtain ⟨k,hk⟩:∃ k,mu-r=k+1:=by
       have hpos:0 < mu-r:=Nat.sub_pos_of_lt (Nat.lt_of_succ_le hr)
       exact Nat.exists_eq_succ_of_ne_zero hpos.ne'
     have hnext:mu-(r+1)=k:=by omega
     let q:=D pi
     let nextError:R:=
       (mu.descFactorial r:R)*D u*q^r+
       (mu.descFactorial r:R)*u*(r:R)*q^(r-1)*D q+
       (k+2:R)*q*error+pi*D error
     refine ⟨nextError,?_⟩
     rw [Function.iterate_succ_apply',herror,map_add]
     simp only [D.leibniz,Derivation.leibniz_pow,D.map_natCast,
       nsmul_eq_mul,smul_eq_mul]
     rw [hk,hnext,Nat.descFactorial_succ]
     have hmur:mu-r=k+1:=hk
     push_cast [hmur]
     dsimp only [q,nextError]
     ring
theorem isUnit_add_of_isUnit_of_not_isUnit [IsLocalRing R]
   {a b:R} (ha:IsUnit a) (hb:¬ IsUnit b):IsUnit (a+b):=by
 by_contra hab
 have hnb:¬ IsUnit (-b):=by simpa using hb
 have hs:=IsLocalRing.nonunits_add hab hnb
 apply hs
 simpa [add_assoc] using ha
section DVR
variable [IsDomain R] [IsDiscreteValuationRing R]
theorem addVal_iterate_eq_sub_of_transverse
   (D:Derivation K R R) (pi u:R) (mu r p:ℕ)
   [CharP R p] (hp:p.Prime) (hmu:mu < p) (hr:r ≤ mu)
   (hpi:Irreducible pi) (hu:IsUnit u) (htrans:IsUnit (D pi)):
   IsDiscreteValuationRing.addVal R ((D:R → R)^[r] (pi^mu*u))=mu-r:=by
 obtain ⟨error,herror⟩:=iterate_pow_mul_expansion D pi u mu r hr
 have hdescDvd:mu.descFactorial r∣mu.factorial:=by
   refine ⟨(mu-r).factorial,?_⟩
   rw [mul_comm,Nat.factorial_mul_descFactorial hr]
 have hnot:¬p∣mu.descFactorial r:=by
   intro hd
   have hpf:p∣mu.factorial:=hd.trans hdescDvd
   rw [prime_dvd_factorial hp] at hpf
   omega
 have hc:IsUnit (mu.descFactorial r:R):=
   (CharP.isUnit_natCast_iff hp).2 hnot
 have hlead:IsUnit ((mu.descFactorial r:R)*u*(D pi)^r):=
   (hc.mul hu).mul (htrans.pow r)
 let lead:R:=(mu.descFactorial r:R)*u*(D pi)^r
 have hpiError:¬IsUnit (pi*error):=
   not_isUnit_of_not_isUnit_dvd hpi.not_isUnit (dvd_mul_right pi error)
 have hbracket:IsUnit (lead+pi*error):=
   isUnit_add_of_isUnit_of_not_isUnit hlead hpiError
 have hfactor:
     (D:R → R)^[r] (pi^mu*u)=pi^(mu-r)*(lead+pi*error):=by
   rw [herror]
   simp only [lead]
   ring
 rw [hfactor,IsDiscreteValuationRing.addVal_mul,
   IsDiscreteValuationRing.addVal_pow,
   IsDiscreteValuationRing.addVal_uniformizer hpi,
   IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hbracket]
 simp
end DVR
theorem isDiscreteValuationRing_of_isRegularLocalRing_of_dimension_one
   [IsDomain R] [IsRegularLocalRing R] (hdim:ringKrullDim R=1):
   IsDiscreteValuationRing R:=by
 have hfin':=(IsRegularLocalRing.iff_finrank_cotangentSpace R).mp
   (inferInstance:IsRegularLocalRing R)
 rw [hdim] at hfin'
 have hfin:Module.finrank (ResidueField R) (CotangentSpace R)=1:=by
   exact_mod_cast hfin'
 exact IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp hfin
end ProximityPrize.SubmissionLower.ContactTwoTailDVRExact6731Research
