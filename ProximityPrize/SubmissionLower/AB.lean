import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower.ContactRecursiveGCDResearch
noncomputable section
section Quotients
variable {A:Type*} [CommMonoidWithZero A] [GCDMonoid A]
def leftGCDQuotient (a b:A):A:=Classical.choose (gcd_dvd_left a b)
def rightGCDQuotient (a b:A):A:=Classical.choose (gcd_dvd_right a b)
theorem left_eq_gcd_mul_leftGCDQuotient (a b:A):
   a=gcd a b*leftGCDQuotient a b:=
 Classical.choose_spec (gcd_dvd_left a b)
theorem right_eq_gcd_mul_rightGCDQuotient (a b:A):
   b=gcd a b*rightGCDQuotient a b:=
 Classical.choose_spec (gcd_dvd_right a b)
theorem gcdQuotients_isRelPrime {a b:A} (ha:a≠0):
   IsRelPrime (leftGCDQuotient a b) (rightGCDQuotient a b):=by
 intro d hdleft hdright
 have hg:gcd a b≠0:=gcd_ne_zero_of_left ha
 have hda:gcd a b*d∣a:=by
   calc
     gcd a b*d∣gcd a b*leftGCDQuotient a b:=
       mul_dvd_mul_left (gcd a b) hdleft
     _=a:=(left_eq_gcd_mul_leftGCDQuotient a b).symm
 have hdb:gcd a b*d∣b:=by
   calc
     gcd a b*d∣gcd a b*rightGCDQuotient a b:=
       mul_dvd_mul_left (gcd a b) hdright
     _=b:=(right_eq_gcd_mul_rightGCDQuotient a b).symm
 have hdg:gcd a b*d∣gcd a b:=dvd_gcd hda hdb
 apply isUnit_iff_dvd_one.mpr
 apply (mul_dvd_mul_iff_left hg).mp
 simpa only [mul_one] using hdg
end Quotients
section RecursiveDefinitions
variable {A:Type*} [CommMonoidWithZero A] [GCDMonoid A]
def gcd12 (a b:A):A:=gcd a b
def gcd123 (a b c:A):A:=gcd (gcd12 a b) c
def quotientA (a b:A):A:=leftGCDQuotient a b
def quotientB (a b:A):A:=rightGCDQuotient a b
def middleQuotient (a b c:A):A:=leftGCDQuotient (gcd12 a b) c
def quotientC (a b c:A):A:=rightGCDQuotient (gcd12 a b) c
theorem a_eq_gcd12_mul_quotientA (a b:A):
   a=gcd12 a b*quotientA a b:=
 left_eq_gcd_mul_leftGCDQuotient a b
theorem b_eq_gcd12_mul_quotientB (a b:A):
   b=gcd12 a b*quotientB a b:=
 right_eq_gcd_mul_rightGCDQuotient a b
theorem gcd12_eq_gcd123_mul_middleQuotient (a b c:A):
   gcd12 a b=gcd123 a b c*middleQuotient a b c:=
 left_eq_gcd_mul_leftGCDQuotient (gcd12 a b) c
theorem c_eq_gcd123_mul_quotientC (a b c:A):
   c=gcd123 a b c*quotientC a b c:=
 right_eq_gcd_mul_rightGCDQuotient (gcd12 a b) c
theorem firstQuotients_isRelPrime {a b:A} (ha:a≠0):
   IsRelPrime (quotientA a b) (quotientB a b):=
 gcdQuotients_isRelPrime ha
theorem secondQuotients_isRelPrime {a b c:A} (ha:a≠0):
   IsRelPrime (middleQuotient a b c) (quotientC a b c):=
 gcdQuotients_isRelPrime (gcd_ne_zero_of_left ha)
end RecursiveDefinitions
section Normalization
variable {A:Type*} [CommMonoidWithZero A] [NormalizedGCDMonoid A]
theorem gcd12_normalized (a b:A):normalize (gcd12 a b)=gcd12 a b:=
 normalize_gcd a b
theorem gcd123_normalized (a b c:A):
   normalize (gcd123 a b c)=gcd123 a b c:=
 normalize_gcd (gcd12 a b) c
end Normalization
section ThreeBranchCover
variable {A B:Type*} [CommRing A] [GCDMonoid A]
variable [CommRing B] [IsDomain B]
theorem recursive_three_branch_cover
   (phi:A →+*B) (a b c:A)
   (ha:phi a=0) (hb:phi b=0) (hc:phi c=0):
   (phi (gcd12 a b)≠0∧
       phi (quotientA a b)=0∧phi (quotientB a b)=0)∨
     (phi (gcd12 a b)=0∧phi (gcd123 a b c)≠0∧
       phi (middleQuotient a b c)=0∧phi (quotientC a b c)=0)∨
     (phi (gcd123 a b c)=0∧phi (gcd12 a b)=0):=by
 rcases eq_or_ne (phi (gcd12 a b)) 0 with h12 | h12
 · rcases eq_or_ne (phi (gcd123 a b c)) 0 with h123 | h123
   · exact Or.inr (Or.inr ⟨h123,h12⟩)
   · have hm:phi (middleQuotient a b c)=0:=by
       rw [gcd12_eq_gcd123_mul_middleQuotient,map_mul] at h12
       exact (mul_eq_zero.mp h12).resolve_left h123
     have hqC:phi (quotientC a b c)=0:=by
       rw [c_eq_gcd123_mul_quotientC a b c,map_mul] at hc
       exact (mul_eq_zero.mp hc).resolve_left h123
     exact Or.inr (Or.inl ⟨h12,h123,hm,hqC⟩)
 · have hqA:phi (quotientA a b)=0:=by
     rw [a_eq_gcd12_mul_quotientA a b,map_mul] at ha
     exact (mul_eq_zero.mp ha).resolve_left h12
   have hqB:phi (quotientB a b)=0:=by
     rw [b_eq_gcd12_mul_quotientB a b,map_mul] at hb
     exact (mul_eq_zero.mp hb).resolve_left h12
   exact Or.inl ⟨h12,hqA,hqB⟩
end ThreeBranchCover
end
end ProximityPrize.SubmissionLower.ContactRecursiveGCDResearch
