import ProximityPrize.SubmissionLower.Z6Xnfpd
import ProximityPrize.SubmissionLower.ZPNuIWc
set_option Elab.async false
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qd4jtSc
open qMHqmcc (GG receipt)
private theorem vQc0 :GG b2 96 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQc1 :GG b2 97 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQc2 :GG b2 98 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQc3 :GG b2 99 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQc4 :GG b2 100 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQc5 :GG b2 101 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQc6 :GG b2 102 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQc7 :GG b2 103 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem r1 :GG b2 96 8:=qMHqmcc.appendGrades (qMHqmcc.appendGrades (qMHqmcc.appendGrades (qMHqmcc.appendGrades (qMHqmcc.appendGrades (qMHqmcc.appendGrades (qMHqmcc.appendGrades vQc0 vQc1) vQc2) vQc3) vQc4) vQc5) vQc6) vQc7
theorem p2_6:GG b2 96 8:=r1
end qd4jtSc
end
section
set_option autoImplicit true
namespace qe6nVeb
private theorem square_mix (t a b:ℚ) (ht:0≤t) (ht' : t≤1) :
  (t*a+(1-t)*b)^2≤t*a^2+(1-t)*b^2 := by
 have h:=mul_nonneg (mul_nonneg ht (sub_nonneg.mpr ht')) (sq_nonneg (a-b))
 apply sub_nonneg.mp
 convert h using 1
 ring
private theorem charge_rat (t u r a b den cap:ℚ) (ht:0≤t) (ht' : t≤1)
    (h₀:den*(u*r)+10*a^2≤den*cap) (h₁:10*(u*b+a)^2≤den*cap) :
    den*((t*u)*r)+10*((u-t*u)*b+a)^2≤den*cap:= by
  have he : (u-t*u)*b+a=t*a+(1-t)*(u*b+a) := by ring
  have hsq:=square_mix t a (u*b+a) ht ht'
  rw [← he] at hsq
  calc
    _≤den*((t*u)*r)+10*(t*a^2+(1-t)*(u*b+a)^2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq (show (0:ℚ)≤10 by decide))
    _=t*(den*(u*r)+10*a^2)+(1-t)*(10*(u*b+a)^2) := by ring
    _≤t*(den*cap)+(1-t)*(den*cap) :=
      add_le_add (mul_le_mul_of_nonneg_left h₀ ht)
        (mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr ht'))
    _ = _:= by ring
theorem charge_mix {u s r a b den cap:ℕ} (hu:0< u) (hs :s≤u)
  (h₀:den*(u*r)+10*a^2≤den*cap) (h₁:10*(u*b+a)^2≤den*cap) :
  den*(s*r)+10*((u-s)*b+a)^2≤den*cap:= by
 have hu' : (0:ℚ)< u:= by exact_mod_cast hu
 have hs' : (s :ℚ)≤u:= by exact_mod_cast hs
 let t:ℚ:=(s :ℚ)/(u:ℚ)
 have ht:0≤t:=div_nonneg (Nat.cast_nonneg _) hu'.le
 have ht' : t≤1 :=(div_le_iff₀ hu').mpr (by simpa only [one_mul] using hs')
 have htU:t*(u:ℚ)=s :=div_mul_cancel₀ _ hu'.ne'
 have h:=charge_rat t u r a b den cap ht ht'
  (by exact_mod_cast h₀) (by exact_mod_cast h₁)
 rw [htU,← Nat.cast_sub hs] at h
 exact_mod_cast h
theorem ceil_bounds (n q:ℕ) (hq:0<q) :
  n≤q*((n+q-1)/q)∧q*((n+q-1)/q)≤n+q:= by
 have h:=Nat.mod_add_div (n+q-1) q
 have hm:=Nat.mod_lt (n+q-1) hq
 omega
end qe6nVeb
end
section
set_option autoImplicit true
namespace qe6nVeb
open P5 (k)
open P5_7_2 (A fO aKj jX row seedCap)
private def packed (b:fO) :ℕ:= match b.val with
 | 0=>0x24d0498092c72510492490511cb2318453488690ce211c41388059f8b3e167a2cf059d8b3a1661290851f0a37946428b6514c932126224c0417882e142d285848ac91512292050409c7130e251c48308c6110a211440287c50f081d1038206c30d02190430085c10b02150428084c10902110420083c107020d040008001000200040008001000200040008000000000
 | 1=>0x127024d0498092c82512492890591cc2318453488710ce211c41388059f8b3e167a2cf059d8b3a1661290851f0a36146328b44998932126224c0417882e142d285848ac91510292050409c7130e251848308c6110a211440287c40f081d1038206c30d02190430085c10b02150428084c10902110420083c107020d040008001000200040008001000200040008000000000
 | 2=>0x119c533106528c8698cf3122614cc0a97d62f305d64b8d16db2d385974b0a2b945628aa5150aa995522aa25540aa7937526e74dc89b0535aa4e1499c92e9255a2cf459892191422282450081f903e1e7a3cf079d8e3a1c724c7090dd11b2235406878ccf191c31346068bcc17162d2c5850aca1512292450409c8130e251c48308c6110c211440287c10f021d0438086c10d02190430085c10b02150428084c10902110420083c1000200040008001000200040008001000200040008000000000
 | 3=>0x29ac835166938d0819d2332a655cc8c18da31386174c0f17df2f405d84b8b2d965a2eb25d60bab97562eaa5d50ba9957b2af355e0abb5567a8fa51c8a359462a6db4db09b55269288a4d109a192422482450089f903e207a3cf079d951d28394c7090dd21b2235406880ccf191c31386068bcc17182d2c5850aca1512292450409c8130e251c48388c6110c211440087c10f021d0438086c10d02190430085c10b02150428084c10902110420083c1000200040008001000200040008001000200040008000000000
 | 4=>0x3390e7128e069bd037246d54d8b9ad935366970d0f19df33426588c9198e43130c26180caf995e32ba6570cad995a32b26560bc157812cff59f8b3e567b2ce859b0abb55752ae751c8a38546f2a925520a239446268a4d1092192422282450081f903e2c3d5478a8ed41d2639487090dd11b2035406878cce191a31346060bcc17162d285850ac91512292050409c7130e251c48308c61102210440087c10f021d0438086c10d02190430085c10b02150428084c10902110420083c1000200040008001000200040008001000200040008000000000
 | 5=>0xcf031dca3b1a7544e8a1cd63932716ce0f1be037446d8cd929ae6354e69a4d0db39b6638ca7190e319d623ac27580eaf9d5e35176a28d445a87330b6610cc1598132f46246c3e587b2ef35de0bbb56752ce76130ba5974a2c925920aa39546288a51109a1934224824900c8fd81f2e3d5878a8ed51d28394c7090dd11b2235406878ccf191c31346068bcc17162d2c5850aca1512292450409c8130e251c48308c11102210440087c10f021d0438086c10d02190430085c10b02150428084c1090211042008001000200040008001000200040008001000200040008000000000
 | 6=>0x4b8096c12d125928b0615cd2b1c553ca8814d129245148a0993d327264d39307258e4a1c9239207238e461c8a356a6aa0d4d1a8e350669e4c4f987a30f061d8b3a16722ce059b8a36146a346860ccc1916312c6050bca17142d245848ac81510291c50389c7130c251848308c5110a211440207c40f021d0438086c10d02190430085c10b02150428084c10902110420083c1070200040008001000200040008001000200040008000000000
 | 7=>0x10f041dcb3b1e7548e8a9cd739347170e0f1be037446d8cd929ae6354e69a0d0db39b6636ca7190e319c6238c27580eaf9d5e33176628cc45987330b6610c4cd897b11261f8c3ad77b2ef35de0b3b56752ae75d30ba5964a2c925520aa39446288a4d109a1924224826480c0fd71f2e3d5878a8ed41d2639487090dd11b2035406878cce191a31346060bcc17162d285850ac91512292050409c7130e251c48308c11102210440087c10f021d0438086c10d02190430085c10b02150428084c1090211042008001000200040008001000200040008001000200040008000000000
 | 8=>0x4390e7128e069bd037246d50d8b1ad83534696cd0e99de333e6580c9098e2312ec25d80baf985e30ba6170c2d985a30b26160b4155812aff55f8abe557b2ae255a4a3b547528e74dc89b8536f289251209a39346248a49108a191422082410081f961f2a3d507898ed31d2439447088dd01b1e353c6870ccd191a31306060bcb17142d285848ac91510292050389c7130e251848308c61102210440087c10f021d0438086c10d02190430085c10b02150428084c10902110420083c1000200040008001000200040008001000200040008000000000
 | 9=>0x11f023d047808ec11d0239047008dc11b0235046808cc6190c31186030bc6170c2d185830ac6150a291450289c51302250448088c11102210440087c10f021d0438086c10d02190430085c10b02150428084c1090211042008001000200040008001000200040008001000200040008000000000
 | 10=>0x490091c12302450488090c1210241048008fc11f103d207840ec81d1039207040dc81b1035206840cc7190e311c6038bc7170c2d185830ac11502290450089c11302250448088c11102210440087c10f021d0438086c10d02190430085c10b02150428084c1090211040008001000200040008001000200040008001000200040008000000000
 | 11=>0x24d0498092c12502490490091c12302450488090c1211041248048fc91f123d247848ec91d1239247040dc81b1035206840cc8190e311c6038bc7170c2d045808ac11502290450089c11302250448088c11102210440087c10f021d0438086c10d02190430085c10b02150428084c1090211040008001000200040008001000200040008001000200040008000000000
 | 12=>0x1190231046008bc117022d045808ac11502290450089c11302250448088c11102210440087c10f021d0438086c10d02190430085c10b02150428084c10902110420083c1000200040008001000200040008001000200040008000000000
 | _=>0x1190231046008bc117022d045808ac11502290450089c11302250448088c11102210440087c10f021d0438086c10d02190430085c10b02150428084c10902110420083c1070200040008001000200040008001000200040008000000000
def gradeWitness (b:fO) (i:ℕ) :Witness :=
 let n:=packed b >>> (15*i)
 ⟨n &&& 0x1ff,(n >>> 9) &&& 0x3f⟩
private def aYP (b:fO) (i:ℕ) :Prop :=
 let D:=131071+(jX b).hi
 let e :=i+1
 let u:=((row b).Kw >>> (12*i)) &&& 0xfff
 let x :=gradeWitness b i
 3≤e→0< u →
   weightOK D e (switch D e u x)∧filterOK D e u x∧feeOK D e u (row b).Z1 x
private instance (b:fO) (i:ℕ) :Decidable (aYP b i) := by
 unfold aYP
 infer_instance
private def Prefix (b:fO) :ℕ→Prop
 | 0=>True
 | i+1=>Prefix b i∧decide (aYP b i)=true
private theorem prefix_get {b:fO} {n:ℕ} (h:Prefix b n) {i:ℕ} (hi:i<n) :
   aYP b i:= by
 induction n with
 | zero=>omega
 | succ n ih =>
   rcases (show Prefix b n∧decide (aYP b n)=true from h) with ⟨h,hn⟩
   by_cases hh:i=n
   · subst i
     exact of_decide_eq_true hn
   · exact ih h (by omega)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
private theorem checked_prefix (b:fO) :Prefix b (row b).bDZ:= by
 fin_cases b <;> (repeat' apply And.intro) <;> first | exact True.intro | rfl
theorem band_guards (b:fO) :
  0<(jX b).lo∧k≤131071+(jX b).hi∧131071+(jX b).hi<A:= by
 fin_cases b <;> decide
theorem checked_grade (b:fO) (i:aKj b) (he :3≤ i.val+1) (hu:0<seedCap b i) :
   let D:=131071+(jX b).hi
   let e :=i.val+1
   let u:=seedCap b i
   ∃ x,weightOK D e (switch D e u x)∧filterOK D e u x∧feeOK D e u (row b).Z1 x :=
 ⟨gradeWitness b i,prefix_get (checked_prefix b) i.isLt he hu⟩
end qe6nVeb
end
section
set_option autoImplicit true
namespace q7YMR4d
noncomputable section
open P5 (K)
open cu (L)
open qe6nVeb (SeedPlane)
open MvPolynomial
def SmoothAt (q:SeedPlane) (a :Fin 2→L) :Prop :=
 eval a q=0 ∧ ∃ i,eval a (pderiv i q)≠0
def smoothMarks (q:SeedPlane) (z :K→Fin 2→L) (T:Finset K) :Finset K:= by
 classical exact T.filter fun γ=>SmoothAt q (z γ)
def quadraticAt (q:SeedPlane) (a :Fin 2→L) :SeedPlane :=
 homogeneousComponent 2 (aeval (fun i=>MvPolynomial.X i+C (a i)) q)
def simpleQuadratic (q:SeedPlane) (a :Fin 2→L) :Prop :=
 ∃ v :Fin 2→L,(∃ i,v i≠0)∧SmoothAt (quadraticAt q a) v
abbrev oF (a :Fin 2→L) :Ideal SeedPlane :=RingHom.ker (eval a)
def ke (q g:SeedPlane) :Ideal SeedPlane :=
 Ideal.span {q} ⊔ Ideal.span {g}
end
end q7YMR4d
end
