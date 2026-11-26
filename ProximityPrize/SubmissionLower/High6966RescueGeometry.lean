import ProximityPrize.SubmissionLower.R6960ExceptionalStage

set_option Elab.async false

-- merged module High6966RescueData
section Merged_High6966RescueData

set_option Elab.async false
namespace Lower6960.Rescue6966Source
open K1_14 (Shape)
open P1_7 (Bank)
open K1_14_2_2_4 (pairCap)
structure Step where
  source : Bank
  order : ℕ
  safe : 0<source.shape.J ∧ source.shape.J≤source.shape.B ∧ source.shape.B<K1.p ∧
    source.shape.U<K1.p ∧ source.shape.m*179769<K1.p
  small : order<K1.p
  room : 2*2499*order<source.shape.m*179769
structure Route where
  degree : ℕ
  upper : ℕ
  stages : Fin 17 → Step
  pos : 1≤degree
  zero : (stages 0).order=0
  small : ∀ k : Fin 4, pairCap (⟨0,degree,1,upper⟩:Shape) ((stages 0).source.shape) k<K1.p
  pivot : Fin 2 → Fin 17
  bound : Fin 2 → ℕ
  tight : ∀ k : Fin 2, pairCap (⟨0,degree,1,upper⟩:Shape) ((stages (pivot k)).source.shape)
      (Fin.castLE (by decide : 2≤4) k) < ((stages (pivot k)).order+1)*(bound k+1)
  degree_cap : bound 0≤154

private def s0 : Step := ⟨⟨⟨170,237,51,1879⟩,150975545344,89126689⟩,0,by decide,by decide,by decide⟩
private def s1 : Step := ⟨⟨⟨170,237,51,2113⟩,150975545344,89126689⟩,0,by decide,by decide,by decide⟩
private def s2 : Step := ⟨⟨⟨170,237,53,1671⟩,155362000896,91783289⟩,0,by decide,by decide,by decide⟩
private def s3 : Step := ⟨⟨⟨170,237,53,2113⟩,155362000896,91783289⟩,0,by decide,by decide,by decide⟩
private def s4 : Step := ⟨⟨⟨210,293,62,1879⟩,279710269440,204151930⟩,0,by decide,by decide,by decide⟩
private def s5 : Step := ⟨⟨⟨210,293,62,3807⟩,279710269440,204151930⟩,0,by decide,by decide,by decide⟩
private def s6 : Step := ⟨⟨⟨210,293,63,1671⟩,283090354176,206678784⟩,0,by decide,by decide,by decide⟩
private def s7 : Step := ⟨⟨⟨210,293,63,2113⟩,283090354176,206678784⟩,0,by decide,by decide,by decide⟩
private def s8 : Step := ⟨⟨⟨210,293,63,2377⟩,283090354176,206678784⟩,0,by decide,by decide,by decide⟩
private def s9 : Step := ⟨⟨⟨210,293,63,2674⟩,283090354176,206678784⟩,0,by decide,by decide,by decide⟩
private def s10 : Step := ⟨⟨⟨210,293,63,3008⟩,283090354176,206678784⟩,0,by decide,by decide,by decide⟩
private def s11 : Step := ⟨⟨⟨210,293,65,1879⟩,289785774080,211692234⟩,0,by decide,by decide,by decide⟩
private def s12 : Step := ⟨⟨⟨210,293,65,2113⟩,289785774080,211692234⟩,0,by decide,by decide,by decide⟩
private def s13 : Step := ⟨⟨⟨210,293,65,2377⟩,289785774080,211692234⟩,0,by decide,by decide,by decide⟩
private def s14 : Step := ⟨⟨⟨210,293,65,3807⟩,289785774080,211692234⟩,0,by decide,by decide,by decide⟩
private def s15 : Step := ⟨⟨⟨210,293,65,4282⟩,289785774080,211692234⟩,0,by decide,by decide,by decide⟩
private def s16 : Step := ⟨⟨⟨250,349,74,4282⟩,471125196800,409695834⟩,0,by decide,by decide,by decide⟩
private def s17 : Step := ⟨⟨⟨250,349,76,2377⟩,480667500544,418199213⟩,0,by decide,by decide,by decide⟩
private def s18 : Step := ⟨⟨⟨250,349,76,3807⟩,480667500544,418199213⟩,0,by decide,by decide,by decide⟩
private def s19 : Step := ⟨⟨⟨250,349,76,4282⟩,480667500544,418199213⟩,0,by decide,by decide,by decide⟩
private def s20 : Step := ⟨⟨⟨250,349,76,4817⟩,480667500544,418199213⟩,0,by decide,by decide,by decide⟩
private def s21 : Step := ⟨⟨⟨250,349,76,5419⟩,480667500544,418199213⟩,0,by decide,by decide,by decide⟩
private def s22 : Step := ⟨⟨⟨250,349,78,2113⟩,490108092416,426627288⟩,0,by decide,by decide,by decide⟩
private def s23 : Step := ⟨⟨⟨250,349,78,2377⟩,490108092416,426627288⟩,0,by decide,by decide,by decide⟩
private def s24 : Step := ⟨⟨⟨250,349,78,2674⟩,490108092416,426627288⟩,0,by decide,by decide,by decide⟩
private def s25 : Step := ⟨⟨⟨294,410,89,3807⟩,777085255680,791788817⟩,0,by decide,by decide,by decide⟩
private def s26 : Step := ⟨⟨⟨294,410,89,5419⟩,777085255680,791788817⟩,0,by decide,by decide,by decide⟩
private def s27 : Step := ⟨⟨⟨294,410,89,6858⟩,777085255680,791788817⟩,0,by decide,by decide,by decide⟩
private def s28 : Step := ⟨⟨⟨294,410,91,2674⟩,790165454848,805457011⟩,0,by decide,by decide,by decide⟩
private def s29 : Step := ⟨⟨⟨294,410,91,3008⟩,790165454848,805457011⟩,0,by decide,by decide,by decide⟩
private def s30 : Step := ⟨⟨⟨294,410,91,3807⟩,790165454848,805457011⟩,0,by decide,by decide,by decide⟩
private def s31 : Step := ⟨⟨⟨294,410,91,7715⟩,790165454848,805457011⟩,0,by decide,by decide,by decide⟩
private def s32 : Step := ⟨⟨⟨350,488,106,4817⟩,1308168290304,1584729438⟩,0,by decide,by decide,by decide⟩
private def s33 : Step := ⟨⟨⟨350,488,106,7715⟩,1308168290304,1584729438⟩,0,by decide,by decide,by decide⟩
private def s34 : Step := ⟨⟨⟨350,488,106,8679⟩,1308168290304,1584729438⟩,0,by decide,by decide,by decide⟩
private def s35 : Step := ⟨⟨⟨350,488,108,7715⟩,1326705278976,1607754763⟩,0,by decide,by decide,by decide⟩
private def s36 : Step := ⟨⟨⟨420,586,124,13899⟩,2212364288000,3219706108⟩,0,by decide,by decide,by decide⟩
private def s37 : Step := ⟨⟨⟨420,586,127,12355⟩,2252760678400,3279920952⟩,0,by decide,by decide,by decide⟩
private def s38 : Step := ⟨⟨⟨420,586,127,13899⟩,2252760678400,3279920952⟩,0,by decide,by decide,by decide⟩
private def s39 : Step := ⟨⟨⟨420,586,130,6096⟩,2292767784960,3339653140⟩,0,by decide,by decide,by decide⟩
private def s40 : Step := ⟨⟨⟨520,726,157,9763⟩,4261264752640,7692905725⟩,0,by decide,by decide,by decide⟩
private def s41 : Step := ⟨⟨⟨630,879,186,19788⟩,7438337572864,16221345781⟩,0,by decide,by decide,by decide⟩
private def s42 : Step := ⟨⟨⟨630,879,186,25043⟩,7438337572864,16221345781⟩,0,by decide,by decide,by decide⟩
private def s43 : Step := ⟨⟨⟨630,879,186,28173⟩,7438337572864,16221345781⟩,0,by decide,by decide,by decide⟩
private def s44 : Step := ⟨⟨⟨630,879,190,6858⟩,7559493713920,16491913877⟩,0,by decide,by decide,by decide⟩
private def s45 : Step := ⟨⟨⟨630,879,190,12355⟩,7559493713920,16491913877⟩,0,by decide,by decide,by decide⟩
private def s46 : Step := ⟨⟨⟨750,1047,222,45124⟩,12559140782080,32653699308⟩,0,by decide,by decide,by decide⟩
private def s47 : Step := ⟨⟨⟨750,1047,226,50764⟩,12730741817344,33110613849⟩,0,by decide,by decide,by decide⟩
private def s48 : Step := ⟨⟨⟨900,1256,272,19788⟩,22024701870080,68653176066⟩,0,by decide,by decide,by decide⟩
private def s49 : Step := ⟨⟨⟨900,1256,272,31694⟩,22024701870080,68653176066⟩,0,by decide,by decide,by decide⟩
private def s50 : Step := ⟨⟨⟨900,1256,272,45124⟩,22024701870080,68653176066⟩,0,by decide,by decide,by decide⟩
private def s51 : Step := ⟨⟨⟨170,237,53,2113⟩,155362000896,91783289⟩,1,by decide,by decide,by decide⟩
private def s52 : Step := ⟨⟨⟨210,293,62,2113⟩,279710269440,204151930⟩,1,by decide,by decide,by decide⟩
private def s53 : Step := ⟨⟨⟨210,293,62,2377⟩,279710269440,204151930⟩,1,by decide,by decide,by decide⟩
private def s54 : Step := ⟨⟨⟨210,293,63,1879⟩,283090354176,206678784⟩,1,by decide,by decide,by decide⟩
private def s55 : Step := ⟨⟨⟨210,293,63,2113⟩,283090354176,206678784⟩,1,by decide,by decide,by decide⟩
private def s56 : Step := ⟨⟨⟨210,293,63,5419⟩,283090354176,206678784⟩,1,by decide,by decide,by decide⟩
private def s57 : Step := ⟨⟨⟨210,293,65,1879⟩,289785774080,211692234⟩,1,by decide,by decide,by decide⟩
private def s58 : Step := ⟨⟨⟨210,293,65,2377⟩,289785774080,211692234⟩,1,by decide,by decide,by decide⟩
private def s59 : Step := ⟨⟨⟨210,293,65,2674⟩,289785774080,211692234⟩,1,by decide,by decide,by decide⟩
private def s60 : Step := ⟨⟨⟨210,293,65,4282⟩,289785774080,211692234⟩,1,by decide,by decide,by decide⟩
private def s61 : Step := ⟨⟨⟨250,349,76,2377⟩,480667500544,418199213⟩,1,by decide,by decide,by decide⟩
private def s62 : Step := ⟨⟨⟨250,349,76,2674⟩,480667500544,418199213⟩,1,by decide,by decide,by decide⟩
private def s63 : Step := ⟨⟨⟨250,349,76,3008⟩,480667500544,418199213⟩,1,by decide,by decide,by decide⟩
private def s64 : Step := ⟨⟨⟨250,349,76,3807⟩,480667500544,418199213⟩,1,by decide,by decide,by decide⟩
private def s65 : Step := ⟨⟨⟨250,349,76,4282⟩,480667500544,418199213⟩,1,by decide,by decide,by decide⟩
private def s66 : Step := ⟨⟨⟨250,349,76,4817⟩,480667500544,418199213⟩,1,by decide,by decide,by decide⟩
private def s67 : Step := ⟨⟨⟨250,349,78,3008⟩,490108092416,426627288⟩,1,by decide,by decide,by decide⟩
private def s68 : Step := ⟨⟨⟨294,410,89,3008⟩,777085255680,791788817⟩,1,by decide,by decide,by decide⟩
private def s69 : Step := ⟨⟨⟨294,410,89,6096⟩,777085255680,791788817⟩,1,by decide,by decide,by decide⟩
private def s70 : Step := ⟨⟨⟨294,410,91,3384⟩,790165454848,805457011⟩,1,by decide,by decide,by decide⟩
private def s71 : Step := ⟨⟨⟨294,410,91,4282⟩,790165454848,805457011⟩,1,by decide,by decide,by decide⟩
private def s72 : Step := ⟨⟨⟨350,488,106,3384⟩,1308168290304,1584729438⟩,1,by decide,by decide,by decide⟩
private def s73 : Step := ⟨⟨⟨350,488,106,8679⟩,1308168290304,1584729438⟩,1,by decide,by decide,by decide⟩
private def s74 : Step := ⟨⟨⟨350,488,108,4817⟩,1326705278976,1607754763⟩,1,by decide,by decide,by decide⟩
private def s75 : Step := ⟨⟨⟨350,488,108,5419⟩,1326705278976,1607754763⟩,1,by decide,by decide,by decide⟩
private def s76 : Step := ⟨⟨⟨350,488,108,8679⟩,1326705278976,1607754763⟩,1,by decide,by decide,by decide⟩
private def s77 : Step := ⟨⟨⟨420,586,127,6858⟩,2252760678400,3279920952⟩,1,by decide,by decide,by decide⟩
private def s78 : Step := ⟨⟨⟨420,586,127,8679⟩,2252760678400,3279920952⟩,1,by decide,by decide,by decide⟩
private def s79 : Step := ⟨⟨⟨420,586,127,15636⟩,2252760678400,3279920952⟩,1,by decide,by decide,by decide⟩
private def s80 : Step := ⟨⟨⟨420,586,130,5419⟩,2292767784960,3339653140⟩,1,by decide,by decide,by decide⟩
private def s81 : Step := ⟨⟨⟨420,586,130,7715⟩,2292767784960,3339653140⟩,1,by decide,by decide,by decide⟩
private def s82 : Step := ⟨⟨⟨520,726,154,13899⟩,4199390904320,7578534004⟩,1,by decide,by decide,by decide⟩
private def s83 : Step := ⟨⟨⟨520,726,157,10983⟩,4261264752640,7692905725⟩,1,by decide,by decide,by decide⟩
private def s84 : Step := ⟨⟨⟨520,726,157,13899⟩,4261264752640,7692905725⟩,1,by decide,by decide,by decide⟩
private def s85 : Step := ⟨⟨⟨520,726,161,6096⟩,4343013310464,7844248211⟩,1,by decide,by decide,by decide⟩
private def s86 : Step := ⟨⟨⟨630,879,186,22261⟩,7438337572864,16221345781⟩,1,by decide,by decide,by decide⟩
private def s87 : Step := ⟨⟨⟨630,879,186,28173⟩,7438337572864,16221345781⟩,1,by decide,by decide,by decide⟩
private def s88 : Step := ⟨⟨⟨630,879,190,13899⟩,7559493713920,16491913877⟩,1,by decide,by decide,by decide⟩
private def s89 : Step := ⟨⟨⟨630,879,190,31694⟩,7559493713920,16491913877⟩,1,by decide,by decide,by decide⟩
private def s90 : Step := ⟨⟨⟨630,879,195,7715⟩,7709474160640,16827402390⟩,1,by decide,by decide,by decide⟩
private def s91 : Step := ⟨⟨⟨750,1047,226,28173⟩,12730741817344,33110613849⟩,1,by decide,by decide,by decide⟩
private def s92 : Step := ⟨⟨⟨900,1256,266,50764⟩,21654240231424,67471047297⟩,1,by decide,by decide,by decide⟩
private def s93 : Step := ⟨⟨⟨900,1256,266,57109⟩,21654240231424,67471047297⟩,1,by decide,by decide,by decide⟩
private def s94 : Step := ⟨⟨⟨900,1256,272,22261⟩,22024701870080,68653176066⟩,1,by decide,by decide,by decide⟩
private def s95 : Step := ⟨⟨⟨900,1256,272,35655⟩,22024701870080,68653176066⟩,1,by decide,by decide,by decide⟩
private def s96 : Step := ⟨⟨⟨900,1256,272,50764⟩,22024701870080,68653176066⟩,1,by decide,by decide,by decide⟩
private def s97 : Step := ⟨⟨⟨210,293,63,2113⟩,283090354176,206678784⟩,2,by decide,by decide,by decide⟩
private def s98 : Step := ⟨⟨⟨210,293,63,2377⟩,283090354176,206678784⟩,2,by decide,by decide,by decide⟩
private def s99 : Step := ⟨⟨⟨210,293,65,2113⟩,289785774080,211692234⟩,2,by decide,by decide,by decide⟩
private def s100 : Step := ⟨⟨⟨210,293,65,2377⟩,289785774080,211692234⟩,2,by decide,by decide,by decide⟩
private def s101 : Step := ⟨⟨⟨210,293,65,2674⟩,289785774080,211692234⟩,2,by decide,by decide,by decide⟩
private def s102 : Step := ⟨⟨⟨250,349,74,3807⟩,471125196800,409695834⟩,2,by decide,by decide,by decide⟩
private def s103 : Step := ⟨⟨⟨250,349,76,2674⟩,480667500544,418199213⟩,2,by decide,by decide,by decide⟩
private def s104 : Step := ⟨⟨⟨250,349,76,3008⟩,480667500544,418199213⟩,2,by decide,by decide,by decide⟩
private def s105 : Step := ⟨⟨⟨250,349,76,4282⟩,480667500544,418199213⟩,2,by decide,by decide,by decide⟩
private def s106 : Step := ⟨⟨⟨250,349,76,5419⟩,480667500544,418199213⟩,2,by decide,by decide,by decide⟩
private def s107 : Step := ⟨⟨⟨250,349,78,2377⟩,490108092416,426627288⟩,2,by decide,by decide,by decide⟩
private def s108 : Step := ⟨⟨⟨294,410,89,2674⟩,777085255680,791788817⟩,2,by decide,by decide,by decide⟩
private def s109 : Step := ⟨⟨⟨294,410,89,3008⟩,777085255680,791788817⟩,2,by decide,by decide,by decide⟩
private def s110 : Step := ⟨⟨⟨294,410,91,2377⟩,790165454848,805457011⟩,2,by decide,by decide,by decide⟩
private def s111 : Step := ⟨⟨⟨294,410,91,2674⟩,790165454848,805457011⟩,2,by decide,by decide,by decide⟩
private def s112 : Step := ⟨⟨⟨294,410,91,3807⟩,790165454848,805457011⟩,2,by decide,by decide,by decide⟩
private def s113 : Step := ⟨⟨⟨294,410,91,4282⟩,790165454848,805457011⟩,2,by decide,by decide,by decide⟩
private def s114 : Step := ⟨⟨⟨294,410,91,4817⟩,790165454848,805457011⟩,2,by decide,by decide,by decide⟩
private def s115 : Step := ⟨⟨⟨294,410,91,5419⟩,790165454848,805457011⟩,2,by decide,by decide,by decide⟩
private def s116 : Step := ⟨⟨⟨294,410,91,6858⟩,790165454848,805457011⟩,2,by decide,by decide,by decide⟩
private def s117 : Step := ⟨⟨⟨350,488,106,3008⟩,1308168290304,1584729438⟩,2,by decide,by decide,by decide⟩
private def s118 : Step := ⟨⟨⟨350,488,106,3384⟩,1308168290304,1584729438⟩,2,by decide,by decide,by decide⟩
private def s119 : Step := ⟨⟨⟨350,488,106,5419⟩,1308168290304,1584729438⟩,2,by decide,by decide,by decide⟩
private def s120 : Step := ⟨⟨⟨350,488,106,6096⟩,1308168290304,1584729438⟩,2,by decide,by decide,by decide⟩
private def s121 : Step := ⟨⟨⟨350,488,108,3807⟩,1326705278976,1607754763⟩,2,by decide,by decide,by decide⟩
private def s122 : Step := ⟨⟨⟨350,488,108,6096⟩,1326705278976,1607754763⟩,2,by decide,by decide,by decide⟩
private def s123 : Step := ⟨⟨⟨350,488,108,9763⟩,1326705278976,1607754763⟩,2,by decide,by decide,by decide⟩
private def s124 : Step := ⟨⟨⟨420,586,127,6096⟩,2252760678400,3279920952⟩,2,by decide,by decide,by decide⟩
private def s125 : Step := ⟨⟨⟨420,586,127,7715⟩,2252760678400,3279920952⟩,2,by decide,by decide,by decide⟩
private def s126 : Step := ⟨⟨⟨420,586,127,8679⟩,2252760678400,3279920952⟩,2,by decide,by decide,by decide⟩
private def s127 : Step := ⟨⟨⟨420,586,127,9763⟩,2252760678400,3279920952⟩,2,by decide,by decide,by decide⟩
private def s128 : Step := ⟨⟨⟨420,586,130,5419⟩,2292767784960,3339653140⟩,2,by decide,by decide,by decide⟩
private def s129 : Step := ⟨⟨⟨520,726,154,15636⟩,4199390904320,7578534004⟩,2,by decide,by decide,by decide⟩
private def s130 : Step := ⟨⟨⟨520,726,157,8679⟩,4261264752640,7692905725⟩,2,by decide,by decide,by decide⟩
private def s131 : Step := ⟨⟨⟨520,726,157,12355⟩,4261264752640,7692905725⟩,2,by decide,by decide,by decide⟩
private def s132 : Step := ⟨⟨⟨520,726,157,15636⟩,4261264752640,7692905725⟩,2,by decide,by decide,by decide⟩
private def s133 : Step := ⟨⟨⟨520,726,161,6858⟩,4343013310464,7844248211⟩,2,by decide,by decide,by decide⟩
private def s134 : Step := ⟨⟨⟨630,879,190,15636⟩,7559493713920,16491913877⟩,2,by decide,by decide,by decide⟩
private def s135 : Step := ⟨⟨⟨750,1047,222,31694⟩,12559140782080,32653699308⟩,2,by decide,by decide,by decide⟩
private def s136 : Step := ⟨⟨⟨750,1047,226,8679⟩,12730741817344,33110613849⟩,2,by decide,by decide,by decide⟩
private def s137 : Step := ⟨⟨⟨750,1047,226,22261⟩,12730741817344,33110613849⟩,2,by decide,by decide,by decide⟩
private def s138 : Step := ⟨⟨⟨750,1047,226,28173⟩,12730741817344,33110613849⟩,2,by decide,by decide,by decide⟩
private def s139 : Step := ⟨⟨⟨900,1256,266,45124⟩,21654240231424,67471047297⟩,2,by decide,by decide,by decide⟩
private def s140 : Step := ⟨⟨⟨900,1256,266,57109⟩,21654240231424,67471047297⟩,2,by decide,by decide,by decide⟩
private def s141 : Step := ⟨⟨⟨900,1256,266,64247⟩,21654240231424,67471047297⟩,2,by decide,by decide,by decide⟩
private def s142 : Step := ⟨⟨⟨900,1256,272,25043⟩,22024701870080,68653176066⟩,2,by decide,by decide,by decide⟩
private def s143 : Step := ⟨⟨⟨900,1256,272,31694⟩,22024701870080,68653176066⟩,2,by decide,by decide,by decide⟩
private def s144 : Step := ⟨⟨⟨1100,1535,326,57109⟩,39579969388544,150663514795⟩,2,by decide,by decide,by decide⟩
private def s145 : Step := ⟨⟨⟨210,293,65,2377⟩,289785774080,211692234⟩,3,by decide,by decide,by decide⟩
private def s146 : Step := ⟨⟨⟨250,348,74,2377⟩,471125196800,405945859⟩,3,by decide,by decide,by decide⟩
private def s147 : Step := ⟨⟨⟨250,348,76,2377⟩,480667500544,414368386⟩,3,by decide,by decide,by decide⟩
private def s148 : Step := ⟨⟨⟨250,348,76,2674⟩,480667500544,414368386⟩,3,by decide,by decide,by decide⟩
private def s149 : Step := ⟨⟨⟨250,348,76,3008⟩,480667500544,414368386⟩,3,by decide,by decide,by decide⟩
private def s150 : Step := ⟨⟨⟨250,348,76,4282⟩,480667500544,414368386⟩,3,by decide,by decide,by decide⟩
private def s151 : Step := ⟨⟨⟨250,348,76,6096⟩,480667500544,414368386⟩,3,by decide,by decide,by decide⟩
private def s152 : Step := ⟨⟨⟨250,348,78,2113⟩,490108092416,422716393⟩,3,by decide,by decide,by decide⟩
private def s153 : Step := ⟨⟨⟨250,348,78,2674⟩,490108092416,422716393⟩,3,by decide,by decide,by decide⟩
private def s154 : Step := ⟨⟨⟨250,348,78,4817⟩,490108092416,422716393⟩,3,by decide,by decide,by decide⟩
private def s155 : Step := ⟨⟨⟨294,410,89,2674⟩,777085255680,791788817⟩,3,by decide,by decide,by decide⟩
private def s156 : Step := ⟨⟨⟨294,410,89,3008⟩,777085255680,791788817⟩,3,by decide,by decide,by decide⟩
private def s157 : Step := ⟨⟨⟨294,410,89,5419⟩,777085255680,791788817⟩,3,by decide,by decide,by decide⟩
private def s158 : Step := ⟨⟨⟨294,410,91,3008⟩,790165454848,805457011⟩,3,by decide,by decide,by decide⟩
private def s159 : Step := ⟨⟨⟨294,410,91,3384⟩,790165454848,805457011⟩,3,by decide,by decide,by decide⟩
private def s160 : Step := ⟨⟨⟨294,410,91,3807⟩,790165454848,805457011⟩,3,by decide,by decide,by decide⟩
private def s161 : Step := ⟨⟨⟨294,410,91,4282⟩,790165454848,805457011⟩,3,by decide,by decide,by decide⟩
private def s162 : Step := ⟨⟨⟨294,410,91,4817⟩,790165454848,805457011⟩,3,by decide,by decide,by decide⟩
private def s163 : Step := ⟨⟨⟨294,410,91,5419⟩,790165454848,805457011⟩,3,by decide,by decide,by decide⟩
private def s164 : Step := ⟨⟨⟨350,488,104,5419⟩,1289487646720,1561556019⟩,3,by decide,by decide,by decide⟩
private def s165 : Step := ⟨⟨⟨350,488,106,3384⟩,1308168290304,1584729438⟩,3,by decide,by decide,by decide⟩
private def s166 : Step := ⟨⟨⟨350,488,106,5419⟩,1308168290304,1584729438⟩,3,by decide,by decide,by decide⟩
private def s167 : Step := ⟨⟨⟨350,488,106,6096⟩,1308168290304,1584729438⟩,3,by decide,by decide,by decide⟩
private def s168 : Step := ⟨⟨⟨350,488,106,6858⟩,1308168290304,1584729438⟩,3,by decide,by decide,by decide⟩
private def s169 : Step := ⟨⟨⟨350,488,108,3807⟩,1326705278976,1607754763⟩,3,by decide,by decide,by decide⟩
private def s170 : Step := ⟨⟨⟨350,488,108,6858⟩,1326705278976,1607754763⟩,3,by decide,by decide,by decide⟩
private def s171 : Step := ⟨⟨⟨420,586,124,10983⟩,2212364288000,3219706108⟩,3,by decide,by decide,by decide⟩
private def s172 : Step := ⟨⟨⟨420,586,127,3807⟩,2252760678400,3279920952⟩,3,by decide,by decide,by decide⟩
private def s173 : Step := ⟨⟨⟨420,586,127,6858⟩,2252760678400,3279920952⟩,3,by decide,by decide,by decide⟩
private def s174 : Step := ⟨⟨⟨420,586,127,8679⟩,2252760678400,3279920952⟩,3,by decide,by decide,by decide⟩
private def s175 : Step := ⟨⟨⟨420,586,127,9763⟩,2252760678400,3279920952⟩,3,by decide,by decide,by decide⟩
private def s176 : Step := ⟨⟨⟨420,586,127,10983⟩,2252760678400,3279920952⟩,3,by decide,by decide,by decide⟩
private def s177 : Step := ⟨⟨⟨520,725,157,9763⟩,4261264752640,7658911630⟩,3,by decide,by decide,by decide⟩
private def s178 : Step := ⟨⟨⟨520,725,157,13899⟩,4261264752640,7658911630⟩,3,by decide,by decide,by decide⟩
private def s179 : Step := ⟨⟨⟨520,725,157,17590⟩,4261264752640,7658911630⟩,3,by decide,by decide,by decide⟩
private def s180 : Step := ⟨⟨⟨520,725,161,5419⟩,4343013310464,7809559934⟩,3,by decide,by decide,by decide⟩
private def s181 : Step := ⟨⟨⟨630,879,190,15636⟩,7559493713920,16491913877⟩,3,by decide,by decide,by decide⟩
private def s182 : Step := ⟨⟨⟨630,879,190,17590⟩,7559493713920,16491913877⟩,3,by decide,by decide,by decide⟩
private def s183 : Step := ⟨⟨⟨630,879,195,6858⟩,7709474160640,16827402390⟩,3,by decide,by decide,by decide⟩
private def s184 : Step := ⟨⟨⟨750,1047,222,35655⟩,12559140782080,32653699308⟩,3,by decide,by decide,by decide⟩
private def s185 : Step := ⟨⟨⟨750,1047,226,15636⟩,12730741817344,33110613849⟩,3,by decide,by decide,by decide⟩
private def s186 : Step := ⟨⟨⟨750,1047,226,25043⟩,12730741817344,33110613849⟩,3,by decide,by decide,by decide⟩
private def s187 : Step := ⟨⟨⟨750,1047,226,31694⟩,12730741817344,33110613849⟩,3,by decide,by decide,by decide⟩
private def s188 : Step := ⟨⟨⟨750,1047,226,35655⟩,12730741817344,33110613849⟩,3,by decide,by decide,by decide⟩
private def s189 : Step := ⟨⟨⟨750,1047,232,8679⟩,12985818152960,33790833671⟩,3,by decide,by decide,by decide⟩
private def s190 : Step := ⟨⟨⟨900,1256,266,50764⟩,21654240231424,67471047297⟩,3,by decide,by decide,by decide⟩
private def s191 : Step := ⟨⟨⟨900,1256,266,64247⟩,21654240231424,67471047297⟩,3,by decide,by decide,by decide⟩
private def s192 : Step := ⟨⟨⟨900,1256,266,72277⟩,21654240231424,67471047297⟩,3,by decide,by decide,by decide⟩
private def s193 : Step := ⟨⟨⟨1100,1535,326,64247⟩,39579969388544,150663514795⟩,3,by decide,by decide,by decide⟩
private def s194 : Step := ⟨⟨⟨1100,1535,332,25043⟩,40133103452160,152819743367⟩,3,by decide,by decide,by decide⟩
private def s195 : Step := ⟨⟨⟨250,348,76,2377⟩,480667500544,414368386⟩,4,by decide,by decide,by decide⟩
private def s196 : Step := ⟨⟨⟨250,348,76,2674⟩,480667500544,414368386⟩,4,by decide,by decide,by decide⟩
private def s197 : Step := ⟨⟨⟨250,348,76,3008⟩,480667500544,414368386⟩,4,by decide,by decide,by decide⟩
private def s198 : Step := ⟨⟨⟨250,348,76,3384⟩,480667500544,414368386⟩,4,by decide,by decide,by decide⟩
private def s199 : Step := ⟨⟨⟨250,348,78,2674⟩,490108092416,422716393⟩,4,by decide,by decide,by decide⟩
private def s200 : Step := ⟨⟨⟨250,348,78,4817⟩,490108092416,422716393⟩,4,by decide,by decide,by decide⟩
private def s201 : Step := ⟨⟨⟨294,410,89,3008⟩,777085255680,791788817⟩,4,by decide,by decide,by decide⟩
private def s202 : Step := ⟨⟨⟨294,410,89,3384⟩,777085255680,791788817⟩,4,by decide,by decide,by decide⟩
private def s203 : Step := ⟨⟨⟨294,410,89,6096⟩,777085255680,791788817⟩,4,by decide,by decide,by decide⟩
private def s204 : Step := ⟨⟨⟨294,410,91,3008⟩,790165454848,805457011⟩,4,by decide,by decide,by decide⟩
private def s205 : Step := ⟨⟨⟨294,410,91,3384⟩,790165454848,805457011⟩,4,by decide,by decide,by decide⟩
private def s206 : Step := ⟨⟨⟨294,410,91,4817⟩,790165454848,805457011⟩,4,by decide,by decide,by decide⟩
private def s207 : Step := ⟨⟨⟨294,410,91,5419⟩,790165454848,805457011⟩,4,by decide,by decide,by decide⟩
private def s208 : Step := ⟨⟨⟨294,410,91,6096⟩,790165454848,805457011⟩,4,by decide,by decide,by decide⟩
private def s209 : Step := ⟨⟨⟨350,488,106,3008⟩,1308168290304,1584729438⟩,4,by decide,by decide,by decide⟩
private def s210 : Step := ⟨⟨⟨350,488,106,3384⟩,1308168290304,1584729438⟩,4,by decide,by decide,by decide⟩
private def s211 : Step := ⟨⟨⟨350,488,106,6096⟩,1308168290304,1584729438⟩,4,by decide,by decide,by decide⟩
private def s212 : Step := ⟨⟨⟨350,488,106,6858⟩,1308168290304,1584729438⟩,4,by decide,by decide,by decide⟩
private def s213 : Step := ⟨⟨⟨350,488,106,7715⟩,1308168290304,1584729438⟩,4,by decide,by decide,by decide⟩
private def s214 : Step := ⟨⟨⟨350,488,108,3807⟩,1326705278976,1607754763⟩,4,by decide,by decide,by decide⟩
private def s215 : Step := ⟨⟨⟨350,488,108,4282⟩,1326705278976,1607754763⟩,4,by decide,by decide,by decide⟩
private def s216 : Step := ⟨⟨⟨350,488,108,7715⟩,1326705278976,1607754763⟩,4,by decide,by decide,by decide⟩
private def s217 : Step := ⟨⟨⟨420,586,127,3807⟩,2252760678400,3279920952⟩,4,by decide,by decide,by decide⟩
private def s218 : Step := ⟨⟨⟨420,586,127,4282⟩,2252760678400,3279920952⟩,4,by decide,by decide,by decide⟩
private def s219 : Step := ⟨⟨⟨420,586,127,5419⟩,2252760678400,3279920952⟩,4,by decide,by decide,by decide⟩
private def s220 : Step := ⟨⟨⟨420,586,127,9763⟩,2252760678400,3279920952⟩,4,by decide,by decide,by decide⟩
private def s221 : Step := ⟨⟨⟨420,586,130,6858⟩,2292767784960,3339653140⟩,4,by decide,by decide,by decide⟩
private def s222 : Step := ⟨⟨⟨420,586,130,10983⟩,2292767784960,3339653140⟩,4,by decide,by decide,by decide⟩
private def s223 : Step := ⟨⟨⟨520,725,157,10983⟩,4261264752640,7658911630⟩,4,by decide,by decide,by decide⟩
private def s224 : Step := ⟨⟨⟨520,725,161,6096⟩,4343013310464,7809559934⟩,4,by decide,by decide,by decide⟩
private def s225 : Step := ⟨⟨⟨520,725,161,6858⟩,4343013310464,7809559934⟩,4,by decide,by decide,by decide⟩
private def s226 : Step := ⟨⟨⟨520,725,161,9763⟩,4343013310464,7809559934⟩,4,by decide,by decide,by decide⟩
private def s227 : Step := ⟨⟨⟨630,879,186,17590⟩,7438337572864,16221345781⟩,4,by decide,by decide,by decide⟩
private def s228 : Step := ⟨⟨⟨630,879,186,19788⟩,7438337572864,16221345781⟩,4,by decide,by decide,by decide⟩
private def s229 : Step := ⟨⟨⟨630,879,190,13899⟩,7559493713920,16491913877⟩,4,by decide,by decide,by decide⟩
private def s230 : Step := ⟨⟨⟨630,879,195,7715⟩,7709474160640,16827402390⟩,4,by decide,by decide,by decide⟩
private def s231 : Step := ⟨⟨⟨630,879,195,17590⟩,7709474160640,16827402390⟩,4,by decide,by decide,by decide⟩
private def s232 : Step := ⟨⟨⟨750,1047,226,17590⟩,12730741817344,33110613849⟩,4,by decide,by decide,by decide⟩
private def s233 : Step := ⟨⟨⟨750,1047,226,28173⟩,12730741817344,33110613849⟩,4,by decide,by decide,by decide⟩
private def s234 : Step := ⟨⟨⟨900,1256,266,40111⟩,21654240231424,67471047297⟩,4,by decide,by decide,by decide⟩
private def s235 : Step := ⟨⟨⟨900,1256,272,9763⟩,22024701870080,68653176066⟩,4,by decide,by decide,by decide⟩
private def s236 : Step := ⟨⟨⟨900,1256,272,35655⟩,22024701870080,68653176066⟩,4,by decide,by decide,by decide⟩
private def s237 : Step := ⟨⟨⟨998,1387,302,31694⟩,30044628975616,102461756220⟩,4,by decide,by decide,by decide⟩
private def s238 : Step := ⟨⟨⟨998,1387,302,50764⟩,30044628975616,102461756220⟩,4,by decide,by decide,by decide⟩
private def s239 : Step := ⟨⟨⟨998,1387,302,72277⟩,30044628975616,102461756220⟩,4,by decide,by decide,by decide⟩
private def s240 : Step := ⟨⟨⟨1100,1535,326,64247⟩,39579969388544,150663514795⟩,4,by decide,by decide,by decide⟩
private def s241 : Step := ⟨⟨⟨1100,1535,326,72277⟩,39579969388544,150663514795⟩,4,by decide,by decide,by decide⟩
private def s242 : Step := ⟨⟨⟨1100,1535,332,28173⟩,40133103452160,152819743367⟩,4,by decide,by decide,by decide⟩
private def s243 : Step := ⟨⟨⟨250,348,76,2674⟩,480667500544,414368386⟩,5,by decide,by decide,by decide⟩
private def s244 : Step := ⟨⟨⟨250,348,76,3008⟩,480667500544,414368386⟩,5,by decide,by decide,by decide⟩
private def s245 : Step := ⟨⟨⟨250,348,78,2674⟩,490108092416,422716393⟩,5,by decide,by decide,by decide⟩
private def s246 : Step := ⟨⟨⟨250,348,78,3384⟩,490108092416,422716393⟩,5,by decide,by decide,by decide⟩
private def s247 : Step := ⟨⟨⟨294,410,89,2674⟩,777085255680,791788817⟩,5,by decide,by decide,by decide⟩
private def s248 : Step := ⟨⟨⟨294,410,89,4817⟩,777085255680,791788817⟩,5,by decide,by decide,by decide⟩
private def s249 : Step := ⟨⟨⟨294,410,89,6858⟩,777085255680,791788817⟩,5,by decide,by decide,by decide⟩
private def s250 : Step := ⟨⟨⟨294,410,91,3008⟩,790165454848,805457011⟩,5,by decide,by decide,by decide⟩
private def s251 : Step := ⟨⟨⟨294,410,91,3384⟩,790165454848,805457011⟩,5,by decide,by decide,by decide⟩
private def s252 : Step := ⟨⟨⟨294,410,91,5419⟩,790165454848,805457011⟩,5,by decide,by decide,by decide⟩
private def s253 : Step := ⟨⟨⟨350,488,104,3384⟩,1289487646720,1561556019⟩,5,by decide,by decide,by decide⟩
private def s254 : Step := ⟨⟨⟨350,488,106,3008⟩,1308168290304,1584729438⟩,5,by decide,by decide,by decide⟩
private def s255 : Step := ⟨⟨⟨350,488,106,3384⟩,1308168290304,1584729438⟩,5,by decide,by decide,by decide⟩
private def s256 : Step := ⟨⟨⟨350,488,106,3807⟩,1308168290304,1584729438⟩,5,by decide,by decide,by decide⟩
private def s257 : Step := ⟨⟨⟨350,488,108,3384⟩,1326705278976,1607754763⟩,5,by decide,by decide,by decide⟩
private def s258 : Step := ⟨⟨⟨350,488,108,4817⟩,1326705278976,1607754763⟩,5,by decide,by decide,by decide⟩
private def s259 : Step := ⟨⟨⟨350,488,108,5419⟩,1326705278976,1607754763⟩,5,by decide,by decide,by decide⟩
private def s260 : Step := ⟨⟨⟨350,488,108,6096⟩,1326705278976,1607754763⟩,5,by decide,by decide,by decide⟩
private def s261 : Step := ⟨⟨⟨350,488,108,8679⟩,1326705278976,1607754763⟩,5,by decide,by decide,by decide⟩
private def s262 : Step := ⟨⟨⟨420,586,127,3807⟩,2252760678400,3279920952⟩,5,by decide,by decide,by decide⟩
private def s263 : Step := ⟨⟨⟨420,586,127,4282⟩,2252760678400,3279920952⟩,5,by decide,by decide,by decide⟩
private def s264 : Step := ⟨⟨⟨420,586,127,6096⟩,2252760678400,3279920952⟩,5,by decide,by decide,by decide⟩
private def s265 : Step := ⟨⟨⟨420,586,127,6858⟩,2252760678400,3279920952⟩,5,by decide,by decide,by decide⟩
private def s266 : Step := ⟨⟨⟨420,586,127,7715⟩,2252760678400,3279920952⟩,5,by decide,by decide,by decide⟩
private def s267 : Step := ⟨⟨⟨420,586,127,10983⟩,2252760678400,3279920952⟩,5,by decide,by decide,by decide⟩
private def s268 : Step := ⟨⟨⟨420,586,127,13899⟩,2252760678400,3279920952⟩,5,by decide,by decide,by decide⟩
private def s269 : Step := ⟨⟨⟨420,586,130,7715⟩,2292767784960,3339653140⟩,5,by decide,by decide,by decide⟩
private def s270 : Step := ⟨⟨⟨520,725,154,12355⟩,4199390904320,7545064854⟩,5,by decide,by decide,by decide⟩
private def s271 : Step := ⟨⟨⟨520,725,157,4282⟩,4261264752640,7658911630⟩,5,by decide,by decide,by decide⟩
private def s272 : Step := ⟨⟨⟨520,725,157,6858⟩,4261264752640,7658911630⟩,5,by decide,by decide,by decide⟩
private def s273 : Step := ⟨⟨⟨520,725,157,7715⟩,4261264752640,7658911630⟩,5,by decide,by decide,by decide⟩
private def s274 : Step := ⟨⟨⟨520,725,157,10983⟩,4261264752640,7658911630⟩,5,by decide,by decide,by decide⟩
private def s275 : Step := ⟨⟨⟨520,725,161,12355⟩,4343013310464,7809559934⟩,5,by decide,by decide,by decide⟩
private def s276 : Step := ⟨⟨⟨630,879,190,9763⟩,7559493713920,16491913877⟩,5,by decide,by decide,by decide⟩
private def s277 : Step := ⟨⟨⟨630,879,190,15636⟩,7559493713920,16491913877⟩,5,by decide,by decide,by decide⟩
private def s278 : Step := ⟨⟨⟨630,879,190,19788⟩,7559493713920,16491913877⟩,5,by decide,by decide,by decide⟩
private def s279 : Step := ⟨⟨⟨750,1047,226,17590⟩,12730741817344,33110613849⟩,5,by decide,by decide,by decide⟩
private def s280 : Step := ⟨⟨⟨750,1047,226,19788⟩,12730741817344,33110613849⟩,5,by decide,by decide,by decide⟩
private def s281 : Step := ⟨⟨⟨900,1256,266,40111⟩,21654240231424,67471047297⟩,5,by decide,by decide,by decide⟩
private def s282 : Step := ⟨⟨⟨900,1256,272,17590⟩,22024701870080,68653176066⟩,5,by decide,by decide,by decide⟩
private def s283 : Step := ⟨⟨⟨900,1256,272,28173⟩,22024701870080,68653176066⟩,5,by decide,by decide,by decide⟩
private def s284 : Step := ⟨⟨⟨900,1256,272,35655⟩,22024701870080,68653176066⟩,5,by decide,by decide,by decide⟩
private def s285 : Step := ⟨⟨⟨900,1256,272,40111⟩,22024701870080,68653176066⟩,5,by decide,by decide,by decide⟩
private def s286 : Step := ⟨⟨⟨900,1256,279,9763⟩,22452680785920,70021105933⟩,5,by decide,by decide,by decide⟩
private def s287 : Step := ⟨⟨⟨1100,1535,332,72277⟩,40133103452160,152819743367⟩,5,by decide,by decide,by decide⟩
private def s288 : Step := ⟨⟨⟨1220,1696,370,50764⟩,54930349752320,229159736517⟩,5,by decide,by decide,by decide⟩
private def s289 : Step := ⟨⟨⟨1220,1696,370,64247⟩,54930349752320,229159736517⟩,5,by decide,by decide,by decide⟩
private def s290 : Step := ⟨⟨⟨1350,1884,400,72277⟩,73092385996800,341469310532⟩,5,by decide,by decide,by decide⟩
private def s291 : Step := ⟨⟨⟨1350,1884,408,28173⟩,74202776600576,346781832878⟩,5,by decide,by decide,by decide⟩
private def s292 : Step := ⟨⟨⟨294,410,87,3008⟩,763884470272,778016029⟩,7,by decide,by decide,by decide⟩
private def s293 : Step := ⟨⟨⟨294,410,89,3008⟩,777085255680,791788817⟩,7,by decide,by decide,by decide⟩
private def s294 : Step := ⟨⟨⟨294,410,89,3384⟩,777085255680,791788817⟩,7,by decide,by decide,by decide⟩
private def s295 : Step := ⟨⟨⟨294,410,89,3807⟩,777085255680,791788817⟩,7,by decide,by decide,by decide⟩
private def s296 : Step := ⟨⟨⟨294,410,91,3008⟩,790165454848,805457011⟩,7,by decide,by decide,by decide⟩
private def s297 : Step := ⟨⟨⟨294,410,91,3384⟩,790165454848,805457011⟩,7,by decide,by decide,by decide⟩
private def s298 : Step := ⟨⟨⟨294,410,91,3807⟩,790165454848,805457011⟩,7,by decide,by decide,by decide⟩
private def s299 : Step := ⟨⟨⟨350,488,104,7715⟩,1289487646720,1561556019⟩,7,by decide,by decide,by decide⟩
private def s300 : Step := ⟨⟨⟨350,488,106,3807⟩,1308168290304,1584729438⟩,7,by decide,by decide,by decide⟩
private def s301 : Step := ⟨⟨⟨350,488,106,4282⟩,1308168290304,1584729438⟩,7,by decide,by decide,by decide⟩
private def s302 : Step := ⟨⟨⟨350,488,106,6096⟩,1308168290304,1584729438⟩,7,by decide,by decide,by decide⟩
private def s303 : Step := ⟨⟨⟨350,488,108,3384⟩,1326705278976,1607754763⟩,7,by decide,by decide,by decide⟩
private def s304 : Step := ⟨⟨⟨350,488,108,4817⟩,1326705278976,1607754763⟩,7,by decide,by decide,by decide⟩
private def s305 : Step := ⟨⟨⟨420,586,127,3807⟩,2252760678400,3279920952⟩,7,by decide,by decide,by decide⟩
private def s306 : Step := ⟨⟨⟨420,586,127,4282⟩,2252760678400,3279920952⟩,7,by decide,by decide,by decide⟩
private def s307 : Step := ⟨⟨⟨420,586,127,5419⟩,2252760678400,3279920952⟩,7,by decide,by decide,by decide⟩
private def s308 : Step := ⟨⟨⟨420,586,127,6858⟩,2252760678400,3279920952⟩,7,by decide,by decide,by decide⟩
private def s309 : Step := ⟨⟨⟨420,586,127,8679⟩,2252760678400,3279920952⟩,7,by decide,by decide,by decide⟩
private def s310 : Step := ⟨⟨⟨420,586,127,9763⟩,2252760678400,3279920952⟩,7,by decide,by decide,by decide⟩
private def s311 : Step := ⟨⟨⟨420,586,130,3384⟩,2292767784960,3339653140⟩,7,by decide,by decide,by decide⟩
private def s312 : Step := ⟨⟨⟨420,586,130,3807⟩,2292767784960,3339653140⟩,7,by decide,by decide,by decide⟩
private def s313 : Step := ⟨⟨⟨420,586,130,6096⟩,2292767784960,3339653140⟩,7,by decide,by decide,by decide⟩
private def s314 : Step := ⟨⟨⟨420,586,130,6858⟩,2292767784960,3339653140⟩,7,by decide,by decide,by decide⟩
private def s315 : Step := ⟨⟨⟨520,725,157,4282⟩,4261264752640,7658911630⟩,7,by decide,by decide,by decide⟩
private def s316 : Step := ⟨⟨⟨520,725,157,4817⟩,4261264752640,7658911630⟩,7,by decide,by decide,by decide⟩
private def s317 : Step := ⟨⟨⟨520,725,157,8679⟩,4261264752640,7658911630⟩,7,by decide,by decide,by decide⟩
private def s318 : Step := ⟨⟨⟨520,725,157,13899⟩,4261264752640,7658911630⟩,7,by decide,by decide,by decide⟩
private def s319 : Step := ⟨⟨⟨520,725,161,4817⟩,4343013310464,7809559934⟩,7,by decide,by decide,by decide⟩
private def s320 : Step := ⟨⟨⟨520,725,161,6096⟩,4343013310464,7809559934⟩,7,by decide,by decide,by decide⟩
private def s321 : Step := ⟨⟨⟨520,725,161,8679⟩,4343013310464,7809559934⟩,7,by decide,by decide,by decide⟩
private def s322 : Step := ⟨⟨⟨520,725,161,10983⟩,4343013310464,7809559934⟩,7,by decide,by decide,by decide⟩
private def s323 : Step := ⟨⟨⟨520,725,161,12355⟩,4343013310464,7809559934⟩,7,by decide,by decide,by decide⟩
private def s324 : Step := ⟨⟨⟨630,879,190,13899⟩,7559493713920,16491913877⟩,7,by decide,by decide,by decide⟩
private def s325 : Step := ⟨⟨⟨750,1047,222,17590⟩,12559140782080,32653699308⟩,7,by decide,by decide,by decide⟩
private def s326 : Step := ⟨⟨⟨750,1047,226,22261⟩,12730741817344,33110613849⟩,7,by decide,by decide,by decide⟩
private def s327 : Step := ⟨⟨⟨750,1047,232,9763⟩,12985818152960,33790833671⟩,7,by decide,by decide,by decide⟩
private def s328 : Step := ⟨⟨⟨900,1256,272,19788⟩,22024701870080,68653176066⟩,7,by decide,by decide,by decide⟩
private def s329 : Step := ⟨⟨⟨900,1256,272,22261⟩,22024701870080,68653176066⟩,7,by decide,by decide,by decide⟩
private def s330 : Step := ⟨⟨⟨900,1256,272,35655⟩,22024701870080,68653176066⟩,7,by decide,by decide,by decide⟩
private def s331 : Step := ⟨⟨⟨1100,1535,326,45124⟩,39579969388544,150663514795⟩,7,by decide,by decide,by decide⟩
private def s332 : Step := ⟨⟨⟨1100,1535,332,40111⟩,40133103452160,152819743367⟩,7,by decide,by decide,by decide⟩
private def s333 : Step := ⟨⟨⟨1100,1535,332,45124⟩,40133103452160,152819743367⟩,7,by decide,by decide,by decide⟩
private def s334 : Step := ⟨⟨⟨1100,1535,341,10983⟩,40955142733824,156029238110⟩,7,by decide,by decide,by decide⟩
private def s335 : Step := ⟨⟨⟨1350,1884,400,57109⟩,73092385996800,341469310532⟩,7,by decide,by decide,by decide⟩
private def s336 : Step := ⟨⟨⟨1350,1884,400,72277⟩,73092385996800,341469310532⟩,7,by decide,by decide,by decide⟩
private def s337 : Step := ⟨⟨⟨1350,1884,400,81311⟩,73092385996800,341469310532⟩,7,by decide,by decide,by decide⟩
private def s338 : Step := ⟨⟨⟨1350,1884,408,81311⟩,74202776600576,346781832878⟩,7,by decide,by decide,by decide⟩
private def s339 : Step := ⟨⟨⟨1650,2303,498,31694⟩,135254251667456,772776530256⟩,7,by decide,by decide,by decide⟩
private def s340 : Step := ⟨⟨⟨350,488,106,3384⟩,1308168290304,1584729438⟩,10,by decide,by decide,by decide⟩
private def s341 : Step := ⟨⟨⟨350,488,106,3807⟩,1308168290304,1584729438⟩,10,by decide,by decide,by decide⟩
private def s342 : Step := ⟨⟨⟨350,488,108,3384⟩,1326705278976,1607754763⟩,10,by decide,by decide,by decide⟩
private def s343 : Step := ⟨⟨⟨350,488,108,3807⟩,1326705278976,1607754763⟩,10,by decide,by decide,by decide⟩
private def s344 : Step := ⟨⟨⟨350,488,108,4282⟩,1326705278976,1607754763⟩,10,by decide,by decide,by decide⟩
private def s345 : Step := ⟨⟨⟨350,488,108,4817⟩,1326705278976,1607754763⟩,10,by decide,by decide,by decide⟩
private def s346 : Step := ⟨⟨⟨420,586,127,4282⟩,2252760678400,3279920952⟩,10,by decide,by decide,by decide⟩
private def s347 : Step := ⟨⟨⟨420,586,127,4817⟩,2252760678400,3279920952⟩,10,by decide,by decide,by decide⟩
private def s348 : Step := ⟨⟨⟨420,586,127,6096⟩,2252760678400,3279920952⟩,10,by decide,by decide,by decide⟩
private def s349 : Step := ⟨⟨⟨420,586,127,8679⟩,2252760678400,3279920952⟩,10,by decide,by decide,by decide⟩
private def s350 : Step := ⟨⟨⟨420,586,130,4282⟩,2292767784960,3339653140⟩,10,by decide,by decide,by decide⟩
private def s351 : Step := ⟨⟨⟨420,586,130,4817⟩,2292767784960,3339653140⟩,10,by decide,by decide,by decide⟩
private def s352 : Step := ⟨⟨⟨420,586,130,6858⟩,2292767784960,3339653140⟩,10,by decide,by decide,by decide⟩
private def s353 : Step := ⟨⟨⟨420,586,130,7715⟩,2292767784960,3339653140⟩,10,by decide,by decide,by decide⟩
private def s354 : Step := ⟨⟨⟨420,586,130,8679⟩,2292767784960,3339653140⟩,10,by decide,by decide,by decide⟩
private def s355 : Step := ⟨⟨⟨520,725,157,4282⟩,4261264752640,7658911630⟩,10,by decide,by decide,by decide⟩
private def s356 : Step := ⟨⟨⟨520,725,157,4817⟩,4261264752640,7658911630⟩,10,by decide,by decide,by decide⟩
private def s357 : Step := ⟨⟨⟨520,725,157,5419⟩,4261264752640,7658911630⟩,10,by decide,by decide,by decide⟩
private def s358 : Step := ⟨⟨⟨520,725,157,10983⟩,4261264752640,7658911630⟩,10,by decide,by decide,by decide⟩
private def s359 : Step := ⟨⟨⟨520,725,161,4282⟩,4343013310464,7809559934⟩,10,by decide,by decide,by decide⟩
private def s360 : Step := ⟨⟨⟨520,725,161,6096⟩,4343013310464,7809559934⟩,10,by decide,by decide,by decide⟩
private def s361 : Step := ⟨⟨⟨520,725,161,7715⟩,4343013310464,7809559934⟩,10,by decide,by decide,by decide⟩
private def s362 : Step := ⟨⟨⟨630,879,190,15636⟩,7559493713920,16491913877⟩,10,by decide,by decide,by decide⟩
private def s363 : Step := ⟨⟨⟨630,879,195,5419⟩,7709474160640,16827402390⟩,10,by decide,by decide,by decide⟩
private def s364 : Step := ⟨⟨⟨630,879,195,8679⟩,7709474160640,16827402390⟩,10,by decide,by decide,by decide⟩
private def s365 : Step := ⟨⟨⟨630,879,195,9763⟩,7709474160640,16827402390⟩,10,by decide,by decide,by decide⟩
private def s366 : Step := ⟨⟨⟨630,879,195,12355⟩,7709474160640,16827402390⟩,10,by decide,by decide,by decide⟩
private def s367 : Step := ⟨⟨⟨630,879,195,15636⟩,7709474160640,16827402390⟩,10,by decide,by decide,by decide⟩
private def s368 : Step := ⟨⟨⟨750,1046,226,15636⟩,12730741817344,33009058589⟩,10,by decide,by decide,by decide⟩
private def s369 : Step := ⟨⟨⟨750,1046,232,9763⟩,12985818152960,33687112323⟩,10,by decide,by decide,by decide⟩
private def s370 : Step := ⟨⟨⟨750,1046,232,13899⟩,12985818152960,33687112323⟩,10,by decide,by decide,by decide⟩
private def s371 : Step := ⟨⟨⟨750,1046,232,28173⟩,12985818152960,33687112323⟩,10,by decide,by decide,by decide⟩
private def s372 : Step := ⟨⟨⟨900,1256,266,25043⟩,21654240231424,67471047297⟩,10,by decide,by decide,by decide⟩
private def s373 : Step := ⟨⟨⟨900,1256,272,19788⟩,22024701870080,68653176066⟩,10,by decide,by decide,by decide⟩
private def s374 : Step := ⟨⟨⟨900,1256,272,25043⟩,22024701870080,68653176066⟩,10,by decide,by decide,by decide⟩
private def s375 : Step := ⟨⟨⟨900,1256,279,10983⟩,22452680785920,70021105933⟩,10,by decide,by decide,by decide⟩
private def s376 : Step := ⟨⟨⟨1100,1535,326,40111⟩,39579969388544,150663514795⟩,10,by decide,by decide,by decide⟩
private def s377 : Step := ⟨⟨⟨1100,1535,326,50764⟩,39579969388544,150663514795⟩,10,by decide,by decide,by decide⟩
private def s378 : Step := ⟨⟨⟨1100,1535,332,25043⟩,40133103452160,152819743367⟩,10,by decide,by decide,by decide⟩
private def s379 : Step := ⟨⟨⟨1100,1535,332,57109⟩,40133103452160,152819743367⟩,10,by decide,by decide,by decide⟩
private def s380 : Step := ⟨⟨⟨1100,1535,341,13899⟩,40955142733824,156029238110⟩,10,by decide,by decide,by decide⟩
private def s381 : Step := ⟨⟨⟨1350,1884,408,50764⟩,74202776600576,346781832878⟩,10,by decide,by decide,by decide⟩
private def s382 : Step := ⟨⟨⟨1644,2285,498,40111⟩,134156626165760,753510622290⟩,10,by decide,by decide,by decide⟩
private def s383 : Step := ⟨⟨⟨1644,2285,498,64247⟩,134156626165760,753510622290⟩,10,by decide,by decide,by decide⟩
private def s384 : Step := ⟨⟨⟨1644,2285,498,91474⟩,134156626165760,753510622290⟩,10,by decide,by decide,by decide⟩
private def s385 : Step := ⟨⟨⟨1644,2285,498,102908⟩,134156626165760,753510622290⟩,10,by decide,by decide,by decide⟩
private def s386 : Step := ⟨⟨⟨1650,2303,488,91474⟩,133179773812736,760643620838⟩,10,by decide,by decide,by decide⟩
private def s387 : Step := ⟨⟨⟨420,585,127,4817⟩,2252760678400,3261978232⟩,16,by decide,by decide,by decide⟩
private def s388 : Step := ⟨⟨⟨420,585,130,5419⟩,2292767784960,3321371304⟩,16,by decide,by decide,by decide⟩
private def s389 : Step := ⟨⟨⟨520,725,154,4817⟩,4199390904320,7545064854⟩,16,by decide,by decide,by decide⟩
private def s390 : Step := ⟨⟨⟨520,725,157,4282⟩,4261264752640,7658911630⟩,16,by decide,by decide,by decide⟩
private def s391 : Step := ⟨⟨⟨520,725,157,5419⟩,4261264752640,7658911630⟩,16,by decide,by decide,by decide⟩
private def s392 : Step := ⟨⟨⟨520,725,157,6096⟩,4261264752640,7658911630⟩,16,by decide,by decide,by decide⟩
private def s393 : Step := ⟨⟨⟨520,725,157,6858⟩,4261264752640,7658911630⟩,16,by decide,by decide,by decide⟩
private def s394 : Step := ⟨⟨⟨520,725,157,9763⟩,4261264752640,7658911630⟩,16,by decide,by decide,by decide⟩
private def s395 : Step := ⟨⟨⟨520,725,161,4282⟩,4343013310464,7809559934⟩,16,by decide,by decide,by decide⟩
private def s396 : Step := ⟨⟨⟨520,725,161,4817⟩,4343013310464,7809559934⟩,16,by decide,by decide,by decide⟩
private def s397 : Step := ⟨⟨⟨520,725,161,7715⟩,4343013310464,7809559934⟩,16,by decide,by decide,by decide⟩
private def s398 : Step := ⟨⟨⟨520,725,161,10983⟩,4343013310464,7809559934⟩,16,by decide,by decide,by decide⟩
private def s399 : Step := ⟨⟨⟨630,879,190,5419⟩,7559493713920,16491913877⟩,16,by decide,by decide,by decide⟩
private def s400 : Step := ⟨⟨⟨630,879,190,8679⟩,7559493713920,16491913877⟩,16,by decide,by decide,by decide⟩
private def s401 : Step := ⟨⟨⟨630,879,190,9763⟩,7559493713920,16491913877⟩,16,by decide,by decide,by decide⟩
private def s402 : Step := ⟨⟨⟨630,879,190,10983⟩,7559493713920,16491913877⟩,16,by decide,by decide,by decide⟩
private def s403 : Step := ⟨⟨⟨630,879,195,5419⟩,7709474160640,16827402390⟩,16,by decide,by decide,by decide⟩
private def s404 : Step := ⟨⟨⟨630,879,195,6096⟩,7709474160640,16827402390⟩,16,by decide,by decide,by decide⟩
private def s405 : Step := ⟨⟨⟨630,879,195,12355⟩,7709474160640,16827402390⟩,16,by decide,by decide,by decide⟩
private def s406 : Step := ⟨⟨⟨630,879,195,13899⟩,7709474160640,16827402390⟩,16,by decide,by decide,by decide⟩
private def s407 : Step := ⟨⟨⟨750,1046,226,6858⟩,12730741817344,33009058589⟩,16,by decide,by decide,by decide⟩
private def s408 : Step := ⟨⟨⟨750,1046,226,9763⟩,12730741817344,33009058589⟩,16,by decide,by decide,by decide⟩
private def s409 : Step := ⟨⟨⟨750,1046,226,13899⟩,12730741817344,33009058589⟩,16,by decide,by decide,by decide⟩
private def s410 : Step := ⟨⟨⟨750,1046,232,6858⟩,12985818152960,33687112323⟩,16,by decide,by decide,by decide⟩
private def s411 : Step := ⟨⟨⟨750,1046,232,7715⟩,12985818152960,33687112323⟩,16,by decide,by decide,by decide⟩
private def s412 : Step := ⟨⟨⟨750,1046,232,9763⟩,12985818152960,33687112323⟩,16,by decide,by decide,by decide⟩
private def s413 : Step := ⟨⟨⟨750,1046,232,13899⟩,12985818152960,33687112323⟩,16,by decide,by decide,by decide⟩
private def s414 : Step := ⟨⟨⟨750,1046,232,19788⟩,12985818152960,33687112323⟩,16,by decide,by decide,by decide⟩
private def s415 : Step := ⟨⟨⟨900,1256,272,12355⟩,22024701870080,68653176066⟩,16,by decide,by decide,by decide⟩
private def s416 : Step := ⟨⟨⟨900,1256,272,19788⟩,22024701870080,68653176066⟩,16,by decide,by decide,by decide⟩
private def s417 : Step := ⟨⟨⟨900,1256,272,22261⟩,22024701870080,68653176066⟩,16,by decide,by decide,by decide⟩
private def s418 : Step := ⟨⟨⟨900,1256,279,15636⟩,22452680785920,70021105933⟩,16,by decide,by decide,by decide⟩
private def s419 : Step := ⟨⟨⟨900,1256,279,19788⟩,22452680785920,70021105933⟩,16,by decide,by decide,by decide⟩
private def s420 : Step := ⟨⟨⟨1100,1535,326,35655⟩,39579969388544,150663514795⟩,16,by decide,by decide,by decide⟩
private def s421 : Step := ⟨⟨⟨1100,1535,332,15636⟩,40133103452160,152819743367⟩,16,by decide,by decide,by decide⟩
private def s422 : Step := ⟨⟨⟨1100,1535,332,31694⟩,40133103452160,152819743367⟩,16,by decide,by decide,by decide⟩
private def s423 : Step := ⟨⟨⟨1100,1535,341,25043⟩,40955142733824,156029238110⟩,16,by decide,by decide,by decide⟩
private def s424 : Step := ⟨⟨⟨1350,1884,400,35655⟩,73092385996800,341469310532⟩,16,by decide,by decide,by decide⟩
private def s425 : Step := ⟨⟨⟨1350,1884,400,57109⟩,73092385996800,341469310532⟩,16,by decide,by decide,by decide⟩
private def s426 : Step := ⟨⟨⟨1350,1884,418,19788⟩,75578221264896,353372556299⟩,16,by decide,by decide,by decide⟩
private def s427 : Step := ⟨⟨⟨1650,2303,488,64247⟩,133179773812736,760643620838⟩,16,by decide,by decide,by decide⟩
private def s428 : Step := ⟨⟨⟨1650,2303,488,72277⟩,133179773812736,760643620838⟩,16,by decide,by decide,by decide⟩
private def s429 : Step := ⟨⟨⟨1927,2678,584,64247⟩,216034207334400,1421525065183⟩,16,by decide,by decide,by decide⟩
private def s430 : Step := ⟨⟨⟨1927,2678,584,91474⟩,216034207334400,1421525065183⟩,16,by decide,by decide,by decide⟩
private def s431 : Step := ⟨⟨⟨1927,2678,584,115771⟩,216034207334400,1421525065183⟩,16,by decide,by decide,by decide⟩
private def s432 : Step := ⟨⟨⟨1927,2678,584,130242⟩,216034207334400,1421525065183⟩,16,by decide,by decide,by decide⟩
private def s433 : Step := ⟨⟨⟨2000,2792,592,130242⟩,237206388080640,1642878192099⟩,16,by decide,by decide,by decide⟩
private def s434 : Step := ⟨⟨⟨2000,2792,604,50764⟩,240862397726720,1668809144914⟩,16,by decide,by decide,by decide⟩
private def s435 : Step := ⟨⟨⟨520,725,157,5419⟩,4261264752640,7658911630⟩,20,by decide,by decide,by decide⟩
private def s436 : Step := ⟨⟨⟨520,725,157,6096⟩,4261264752640,7658911630⟩,20,by decide,by decide,by decide⟩
private def s437 : Step := ⟨⟨⟨520,725,161,4817⟩,4343013310464,7809559934⟩,20,by decide,by decide,by decide⟩
private def s438 : Step := ⟨⟨⟨520,725,161,5419⟩,4343013310464,7809559934⟩,20,by decide,by decide,by decide⟩
private def s439 : Step := ⟨⟨⟨520,725,161,6096⟩,4343013310464,7809559934⟩,20,by decide,by decide,by decide⟩
private def s440 : Step := ⟨⟨⟨520,725,161,7715⟩,4343013310464,7809559934⟩,20,by decide,by decide,by decide⟩
private def s441 : Step := ⟨⟨⟨630,878,190,6096⟩,7559493713920,16431687757⟩,20,by decide,by decide,by decide⟩
private def s442 : Step := ⟨⟨⟨630,878,190,7715⟩,7559493713920,16431687757⟩,20,by decide,by decide,by decide⟩
private def s443 : Step := ⟨⟨⟨630,878,190,8679⟩,7559493713920,16431687757⟩,20,by decide,by decide,by decide⟩
private def s444 : Step := ⟨⟨⟨630,878,190,10983⟩,7559493713920,16431687757⟩,20,by decide,by decide,by decide⟩
private def s445 : Step := ⟨⟨⟨630,878,195,4817⟩,7709474160640,16765904450⟩,20,by decide,by decide,by decide⟩
private def s446 : Step := ⟨⟨⟨630,878,195,5419⟩,7709474160640,16765904450⟩,20,by decide,by decide,by decide⟩
private def s447 : Step := ⟨⟨⟨630,878,195,6096⟩,7709474160640,16765904450⟩,20,by decide,by decide,by decide⟩
private def s448 : Step := ⟨⟨⟨630,878,195,6858⟩,7709474160640,16765904450⟩,20,by decide,by decide,by decide⟩
private def s449 : Step := ⟨⟨⟨630,878,195,7715⟩,7709474160640,16765904450⟩,20,by decide,by decide,by decide⟩
private def s450 : Step := ⟨⟨⟨630,878,195,8679⟩,7709474160640,16765904450⟩,20,by decide,by decide,by decide⟩
private def s451 : Step := ⟨⟨⟨630,878,195,10983⟩,7709474160640,16765904450⟩,20,by decide,by decide,by decide⟩
private def s452 : Step := ⟨⟨⟨630,878,195,12355⟩,7709474160640,16765904450⟩,20,by decide,by decide,by decide⟩
private def s453 : Step := ⟨⟨⟨750,1046,226,6858⟩,12730741817344,33009058589⟩,20,by decide,by decide,by decide⟩
private def s454 : Step := ⟨⟨⟨750,1046,226,10983⟩,12730741817344,33009058589⟩,20,by decide,by decide,by decide⟩
private def s455 : Step := ⟨⟨⟨750,1046,226,12355⟩,12730741817344,33009058589⟩,20,by decide,by decide,by decide⟩
private def s456 : Step := ⟨⟨⟨750,1046,232,7715⟩,12985818152960,33687112323⟩,20,by decide,by decide,by decide⟩
private def s457 : Step := ⟨⟨⟨750,1046,232,12355⟩,12985818152960,33687112323⟩,20,by decide,by decide,by decide⟩
private def s458 : Step := ⟨⟨⟨750,1046,232,13899⟩,12985818152960,33687112323⟩,20,by decide,by decide,by decide⟩
private def s459 : Step := ⟨⟨⟨750,1046,232,15636⟩,12985818152960,33687112323⟩,20,by decide,by decide,by decide⟩
private def s460 : Step := ⟨⟨⟨900,1256,272,15636⟩,22024701870080,68653176066⟩,20,by decide,by decide,by decide⟩
private def s461 : Step := ⟨⟨⟨900,1256,272,19788⟩,22024701870080,68653176066⟩,20,by decide,by decide,by decide⟩
private def s462 : Step := ⟨⟨⟨900,1256,272,25043⟩,22024701870080,68653176066⟩,20,by decide,by decide,by decide⟩
private def s463 : Step := ⟨⟨⟨900,1256,279,7715⟩,22452680785920,70021105933⟩,20,by decide,by decide,by decide⟩
private def s464 : Step := ⟨⟨⟨900,1256,279,8679⟩,22452680785920,70021105933⟩,20,by decide,by decide,by decide⟩
private def s465 : Step := ⟨⟨⟨900,1256,279,15636⟩,22452680785920,70021105933⟩,20,by decide,by decide,by decide⟩
private def s466 : Step := ⟨⟨⟨900,1256,279,22261⟩,22452680785920,70021105933⟩,20,by decide,by decide,by decide⟩
private def s467 : Step := ⟨⟨⟨1100,1535,326,25043⟩,39579969388544,150663514795⟩,20,by decide,by decide,by decide⟩
private def s468 : Step := ⟨⟨⟨1100,1535,341,22261⟩,40955142733824,156029238110⟩,20,by decide,by decide,by decide⟩
private def s469 : Step := ⟨⟨⟨1100,1535,341,31694⟩,40955142733824,156029238110⟩,20,by decide,by decide,by decide⟩
private def s470 : Step := ⟨⟨⟨1350,1884,400,40111⟩,73092385996800,341469310532⟩,20,by decide,by decide,by decide⟩
private def s471 : Step := ⟨⟨⟨1350,1884,408,17590⟩,74202776600576,346781832878⟩,20,by decide,by decide,by decide⟩
private def s472 : Step := ⟨⟨⟨1350,1884,408,35655⟩,74202776600576,346781832878⟩,20,by decide,by decide,by decide⟩
private def s473 : Step := ⟨⟨⟨1350,1884,408,40111⟩,74202776600576,346781832878⟩,20,by decide,by decide,by decide⟩
private def s474 : Step := ⟨⟨⟨1650,2303,498,57109⟩,135254251667456,772776530256⟩,20,by decide,by decide,by decide⟩
private def s475 : Step := ⟨⟨⟨1650,2303,498,81311⟩,135254251667456,772776530256⟩,20,by decide,by decide,by decide⟩
private def s476 : Step := ⟨⟨⟨2000,2791,592,72277⟩,237206388080640,1640986809111⟩,20,by decide,by decide,by decide⟩
private def s477 : Step := ⟨⟨⟨2000,2791,592,81311⟩,237206388080640,1640986809111⟩,20,by decide,by decide,by decide⟩
private def s478 : Step := ⟨⟨⟨2000,2791,592,115771⟩,237206388080640,1640986809111⟩,20,by decide,by decide,by decide⟩
private def s479 : Step := ⟨⟨⟨2000,2791,592,146522⟩,237206388080640,1640986809111⟩,20,by decide,by decide,by decide⟩
private def s480 : Step := ⟨⟨⟨2000,2791,592,164837⟩,237206388080640,1640986809111⟩,20,by decide,by decide,by decide⟩
private def s481 : Step := ⟨⟨⟨2000,2791,604,35655⟩,240862397726720,1666886727164⟩,20,by decide,by decide,by decide⟩
private def s482 : Step := ⟨⟨⟨2000,2791,620,19788⟩,245690786119680,1701147081935⟩,20,by decide,by decide,by decide⟩
private def s483 : Step := ⟨⟨⟨2500,3490,740,146522⟩,463070780456960,4008490505414⟩,20,by decide,by decide,by decide⟩
private def s484 : Step := ⟨⟨⟨2500,3490,755,57109⟩,470210689105920,4071783120217⟩,20,by decide,by decide,by decide⟩
private def s485 : Step := ⟨⟨⟨630,878,195,7715⟩,7709474160640,16765904450⟩,31,by decide,by decide,by decide⟩
private def s486 : Step := ⟨⟨⟨750,1046,226,6858⟩,12730741817344,33009058589⟩,31,by decide,by decide,by decide⟩
private def s487 : Step := ⟨⟨⟨750,1046,226,7715⟩,12730741817344,33009058589⟩,31,by decide,by decide,by decide⟩
private def s488 : Step := ⟨⟨⟨750,1046,226,8679⟩,12730741817344,33009058589⟩,31,by decide,by decide,by decide⟩
private def s489 : Step := ⟨⟨⟨750,1046,232,6858⟩,12985818152960,33687112323⟩,31,by decide,by decide,by decide⟩
private def s490 : Step := ⟨⟨⟨750,1046,232,7715⟩,12985818152960,33687112323⟩,31,by decide,by decide,by decide⟩
private def s491 : Step := ⟨⟨⟨750,1046,232,9763⟩,12985818152960,33687112323⟩,31,by decide,by decide,by decide⟩
private def s492 : Step := ⟨⟨⟨750,1046,232,19788⟩,12985818152960,33687112323⟩,31,by decide,by decide,by decide⟩
private def s493 : Step := ⟨⟨⟨900,1255,272,8679⟩,22024701870080,68477558806⟩,31,by decide,by decide,by decide⟩
private def s494 : Step := ⟨⟨⟨900,1255,272,9763⟩,22024701870080,68477558806⟩,31,by decide,by decide,by decide⟩
private def s495 : Step := ⟨⟨⟨900,1255,272,13899⟩,22024701870080,68477558806⟩,31,by decide,by decide,by decide⟩
private def s496 : Step := ⟨⟨⟨900,1255,272,15636⟩,22024701870080,68477558806⟩,31,by decide,by decide,by decide⟩
private def s497 : Step := ⟨⟨⟨900,1255,272,17590⟩,22024701870080,68477558806⟩,31,by decide,by decide,by decide⟩
private def s498 : Step := ⟨⟨⟨900,1255,272,22261⟩,22024701870080,68477558806⟩,31,by decide,by decide,by decide⟩
private def s499 : Step := ⟨⟨⟨900,1255,279,7715⟩,22452680785920,69841856233⟩,31,by decide,by decide,by decide⟩
private def s500 : Step := ⟨⟨⟨900,1255,279,8679⟩,22452680785920,69841856233⟩,31,by decide,by decide,by decide⟩
private def s501 : Step := ⟨⟨⟨900,1255,279,9763⟩,22452680785920,69841856233⟩,31,by decide,by decide,by decide⟩
private def s502 : Step := ⟨⟨⟨900,1255,279,10983⟩,22452680785920,69841856233⟩,31,by decide,by decide,by decide⟩
private def s503 : Step := ⟨⟨⟨900,1255,279,13899⟩,22452680785920,69841856233⟩,31,by decide,by decide,by decide⟩
private def s504 : Step := ⟨⟨⟨900,1255,279,17590⟩,22452680785920,69841856233⟩,31,by decide,by decide,by decide⟩
private def s505 : Step := ⟨⟨⟨900,1255,279,25043⟩,22452680785920,69841856233⟩,31,by decide,by decide,by decide⟩
private def s506 : Step := ⟨⟨⟨1100,1534,332,10983⟩,40133103452160,152499774767⟩,31,by decide,by decide,by decide⟩
private def s507 : Step := ⟨⟨⟨1100,1534,332,12355⟩,40133103452160,152499774767⟩,31,by decide,by decide,by decide⟩
private def s508 : Step := ⟨⟨⟨1100,1534,341,8679⟩,40955142733824,155702293064⟩,31,by decide,by decide,by decide⟩
private def s509 : Step := ⟨⟨⟨1100,1534,341,15636⟩,40955142733824,155702293064⟩,31,by decide,by decide,by decide⟩
private def s510 : Step := ⟨⟨⟨1100,1534,341,28173⟩,40955142733824,155702293064⟩,31,by decide,by decide,by decide⟩
private def s511 : Step := ⟨⟨⟨1100,1534,341,35655⟩,40955142733824,155702293064⟩,31,by decide,by decide,by decide⟩
private def s512 : Step := ⟨⟨⟨1350,1883,408,19788⟩,74202776600576,346190054868⟩,31,by decide,by decide,by decide⟩
private def s513 : Step := ⟨⟨⟨1350,1883,408,31694⟩,74202776600576,346190054868⟩,31,by decide,by decide,by decide⟩
private def s514 : Step := ⟨⟨⟨1350,1883,408,35655⟩,74202776600576,346190054868⟩,31,by decide,by decide,by decide⟩
private def s515 : Step := ⟨⟨⟨1350,1883,418,10983⟩,75578221264896,352769102024⟩,31,by decide,by decide,by decide⟩
private def s516 : Step := ⟨⟨⟨1350,1883,418,19788⟩,75578221264896,352769102024⟩,31,by decide,by decide,by decide⟩
private def s517 : Step := ⟨⟨⟨1650,2302,498,50764⟩,135254251667456,771697512616⟩,31,by decide,by decide,by decide⟩
private def s518 : Step := ⟨⟨⟨1650,2302,498,57109⟩,135254251667456,771697512616⟩,31,by decide,by decide,by decide⟩
private def s519 : Step := ⟨⟨⟨1650,2302,512,25043⟩,138129879859200,788519769358⟩,31,by decide,by decide,by decide⟩
private def s520 : Step := ⟨⟨⟨1650,2302,512,28173⟩,138129879859200,788519769358⟩,31,by decide,by decide,by decide⟩
private def s521 : Step := ⟨⟨⟨1650,2302,512,40111⟩,138129879859200,788519769358⟩,31,by decide,by decide,by decide⟩
private def s522 : Step := ⟨⟨⟨2000,2791,604,50764⟩,240862397726720,1666886727164⟩,31,by decide,by decide,by decide⟩
private def s523 : Step := ⟨⟨⟨2000,2791,604,57109⟩,240862397726720,1666886727164⟩,31,by decide,by decide,by decide⟩
private def s524 : Step := ⟨⟨⟨2000,2791,604,91474⟩,240862397726720,1666886727164⟩,31,by decide,by decide,by decide⟩
private def s525 : Step := ⟨⟨⟨2500,3489,740,115771⟩,463070780456960,4004797990029⟩,31,by decide,by decide,by decide⟩
private def s526 : Step := ⟨⟨⟨2500,3489,755,28173⟩,470210689105920,4068029992867⟩,31,by decide,by decide,by decide⟩
private def s527 : Step := ⟨⟨⟨2500,3489,755,102908⟩,470210689105920,4068029992867⟩,31,by decide,by decide,by decide⟩
private def s528 : Step := ⟨⟨⟨3000,4187,888,208621⟩,799929517735936,8302251431404⟩,31,by decide,by decide,by decide⟩
private def s529 : Step := ⟨⟨⟨3000,4187,906,81311⟩,812266433019904,8433369009268⟩,31,by decide,by decide,by decide⟩
private def s530 : Step := ⟨⟨⟨3048,4235,924,91474⟩,854327964467200,8883701072242⟩,31,by decide,by decide,by decide⟩
private def s531 : Step := ⟨⟨⟨3500,4886,1036,130242⟩,1269967213297664,15388297203643⟩,31,by decide,by decide,by decide⟩
private def s532 : Step := ⟨⟨⟨3500,4886,1036,185441⟩,1269967213297664,15388297203643⟩,31,by decide,by decide,by decide⟩
private def s533 : Step := ⟨⟨⟨3500,4886,1057,164837⟩,1289556817346560,15631374615265⟩,31,by decide,by decide,by decide⟩
private def s534 : Step := ⟨⟨⟨750,1046,226,6858⟩,12730741817344,33009058589⟩,32,by decide,by decide,by decide⟩
private def s535 : Step := ⟨⟨⟨750,1046,226,7715⟩,12730741817344,33009058589⟩,32,by decide,by decide,by decide⟩
private def s536 : Step := ⟨⟨⟨750,1046,232,6858⟩,12985818152960,33687112323⟩,32,by decide,by decide,by decide⟩
private def s537 : Step := ⟨⟨⟨750,1046,232,7715⟩,12985818152960,33687112323⟩,32,by decide,by decide,by decide⟩
private def s538 : Step := ⟨⟨⟨750,1046,232,8679⟩,12985818152960,33687112323⟩,32,by decide,by decide,by decide⟩
private def s539 : Step := ⟨⟨⟨750,1046,232,9763⟩,12985818152960,33687112323⟩,32,by decide,by decide,by decide⟩
private def s540 : Step := ⟨⟨⟨750,1046,232,13899⟩,12985818152960,33687112323⟩,32,by decide,by decide,by decide⟩
private def s541 : Step := ⟨⟨⟨900,1255,272,6858⟩,22024701870080,68477558806⟩,32,by decide,by decide,by decide⟩
private def s542 : Step := ⟨⟨⟨900,1255,272,8679⟩,22024701870080,68477558806⟩,32,by decide,by decide,by decide⟩
private def s543 : Step := ⟨⟨⟨900,1255,272,9763⟩,22024701870080,68477558806⟩,32,by decide,by decide,by decide⟩
private def s544 : Step := ⟨⟨⟨900,1255,272,17590⟩,22024701870080,68477558806⟩,32,by decide,by decide,by decide⟩
private def s545 : Step := ⟨⟨⟨900,1255,272,19788⟩,22024701870080,68477558806⟩,32,by decide,by decide,by decide⟩
private def s546 : Step := ⟨⟨⟨900,1255,279,8679⟩,22452680785920,69841856233⟩,32,by decide,by decide,by decide⟩
private def s547 : Step := ⟨⟨⟨900,1255,279,9763⟩,22452680785920,69841856233⟩,32,by decide,by decide,by decide⟩
private def s548 : Step := ⟨⟨⟨900,1255,279,10983⟩,22452680785920,69841856233⟩,32,by decide,by decide,by decide⟩
private def s549 : Step := ⟨⟨⟨900,1255,279,13899⟩,22452680785920,69841856233⟩,32,by decide,by decide,by decide⟩
private def s550 : Step := ⟨⟨⟨900,1255,279,15636⟩,22452680785920,69841856233⟩,32,by decide,by decide,by decide⟩
private def s551 : Step := ⟨⟨⟨900,1255,279,17590⟩,22452680785920,69841856233⟩,32,by decide,by decide,by decide⟩
private def s552 : Step := ⟨⟨⟨900,1255,279,22261⟩,22452680785920,69841856233⟩,32,by decide,by decide,by decide⟩
private def s553 : Step := ⟨⟨⟨1100,1534,332,9763⟩,40133103452160,152499774767⟩,32,by decide,by decide,by decide⟩
private def s554 : Step := ⟨⟨⟨1100,1534,332,10983⟩,40133103452160,152499774767⟩,32,by decide,by decide,by decide⟩
private def s555 : Step := ⟨⟨⟨1100,1534,332,17590⟩,40133103452160,152499774767⟩,32,by decide,by decide,by decide⟩
private def s556 : Step := ⟨⟨⟨1100,1534,332,22261⟩,40133103452160,152499774767⟩,32,by decide,by decide,by decide⟩
private def s557 : Step := ⟨⟨⟨1100,1534,332,31694⟩,40133103452160,152499774767⟩,32,by decide,by decide,by decide⟩
private def s558 : Step := ⟨⟨⟨1100,1534,341,12355⟩,40955142733824,155702293064⟩,32,by decide,by decide,by decide⟩
private def s559 : Step := ⟨⟨⟨1100,1534,341,22261⟩,40955142733824,155702293064⟩,32,by decide,by decide,by decide⟩
private def s560 : Step := ⟨⟨⟨1350,1883,408,12355⟩,74202776600576,346190054868⟩,32,by decide,by decide,by decide⟩
private def s561 : Step := ⟨⟨⟨1350,1883,408,22261⟩,74202776600576,346190054868⟩,32,by decide,by decide,by decide⟩
private def s562 : Step := ⟨⟨⟨1350,1883,408,31694⟩,74202776600576,346190054868⟩,32,by decide,by decide,by decide⟩
private def s563 : Step := ⟨⟨⟨1350,1883,418,19788⟩,75578221264896,352769102024⟩,32,by decide,by decide,by decide⟩
private def s564 : Step := ⟨⟨⟨1350,1883,418,31694⟩,75578221264896,352769102024⟩,32,by decide,by decide,by decide⟩
private def s565 : Step := ⟨⟨⟨1650,2302,498,31694⟩,135254251667456,771697512616⟩,32,by decide,by decide,by decide⟩
private def s566 : Step := ⟨⟨⟨1650,2302,498,57109⟩,135254251667456,771697512616⟩,32,by decide,by decide,by decide⟩
private def s567 : Step := ⟨⟨⟨1650,2302,512,50764⟩,138129879859200,788519769358⟩,32,by decide,by decide,by decide⟩
private def s568 : Step := ⟨⟨⟨2000,2791,604,40111⟩,240862397726720,1666886727164⟩,32,by decide,by decide,by decide⟩
private def s569 : Step := ⟨⟨⟨2000,2791,620,22261⟩,245690786119680,1701147081935⟩,32,by decide,by decide,by decide⟩
private def s570 : Step := ⟨⟨⟨2500,3489,740,81311⟩,463070780456960,4004797990029⟩,32,by decide,by decide,by decide⟩
private def s571 : Step := ⟨⟨⟨2500,3489,740,102908⟩,463070780456960,4004797990029⟩,32,by decide,by decide,by decide⟩
private def s572 : Step := ⟨⟨⟨2500,3489,740,115771⟩,463070780456960,4004797990029⟩,32,by decide,by decide,by decide⟩
private def s573 : Step := ⟨⟨⟨2500,3489,755,50764⟩,470210689105920,4068029992867⟩,32,by decide,by decide,by decide⟩
private def s574 : Step := ⟨⟨⟨2500,3489,775,28173⟩,479640131993600,4151672878537⟩,32,by decide,by decide,by decide⟩
private def s575 : Step := ⟨⟨⟨3000,4187,906,102908⟩,812266433019904,8433369009268⟩,32,by decide,by decide,by decide⟩
private def s576 : Step := ⟨⟨⟨3000,4187,906,185441⟩,812266433019904,8433369009268⟩,32,by decide,by decide,by decide⟩
private def s577 : Step := ⟨⟨⟨3000,4187,906,208621⟩,812266433019904,8433369009268⟩,32,by decide,by decide,by decide⟩
private def s578 : Step := ⟨⟨⟨3500,4886,1057,81311⟩,1289556817346560,15631374615265⟩,32,by decide,by decide,by decide⟩
private def s579 : Step := ⟨⟨⟨3500,4886,1057,130242⟩,1289556817346560,15631374615265⟩,32,by decide,by decide,by decide⟩
private def s580 : Step := ⟨⟨⟨3500,4886,1057,185441⟩,1289556817346560,15631374615265⟩,32,by decide,by decide,by decide⟩
private def s581 : Step := ⟨⟨⟨900,1255,272,9763⟩,22024701870080,68477558806⟩,44,by decide,by decide,by decide⟩
private def s582 : Step := ⟨⟨⟨900,1255,272,10983⟩,22024701870080,68477558806⟩,44,by decide,by decide,by decide⟩
private def s583 : Step := ⟨⟨⟨900,1255,279,10983⟩,22452680785920,69841856233⟩,44,by decide,by decide,by decide⟩
private def s584 : Step := ⟨⟨⟨900,1255,279,12355⟩,22452680785920,69841856233⟩,44,by decide,by decide,by decide⟩
private def s585 : Step := ⟨⟨⟨1100,1534,332,9763⟩,40133103452160,152499774767⟩,44,by decide,by decide,by decide⟩
private def s586 : Step := ⟨⟨⟨1100,1534,332,10983⟩,40133103452160,152499774767⟩,44,by decide,by decide,by decide⟩
private def s587 : Step := ⟨⟨⟨1100,1534,332,12355⟩,40133103452160,152499774767⟩,44,by decide,by decide,by decide⟩
private def s588 : Step := ⟨⟨⟨1100,1534,332,13899⟩,40133103452160,152499774767⟩,44,by decide,by decide,by decide⟩
private def s589 : Step := ⟨⟨⟨1100,1534,332,19788⟩,40133103452160,152499774767⟩,44,by decide,by decide,by decide⟩
private def s590 : Step := ⟨⟨⟨1100,1534,332,25043⟩,40133103452160,152499774767⟩,44,by decide,by decide,by decide⟩
private def s591 : Step := ⟨⟨⟨1100,1534,341,8679⟩,40955142733824,155702293064⟩,44,by decide,by decide,by decide⟩
private def s592 : Step := ⟨⟨⟨1100,1534,341,10983⟩,40955142733824,155702293064⟩,44,by decide,by decide,by decide⟩
private def s593 : Step := ⟨⟨⟨1100,1534,341,12355⟩,40955142733824,155702293064⟩,44,by decide,by decide,by decide⟩
private def s594 : Step := ⟨⟨⟨1100,1534,341,15636⟩,40955142733824,155702293064⟩,44,by decide,by decide,by decide⟩
private def s595 : Step := ⟨⟨⟨1100,1534,341,19788⟩,40955142733824,155702293064⟩,44,by decide,by decide,by decide⟩
private def s596 : Step := ⟨⟨⟨1100,1534,341,22261⟩,40955142733824,155702293064⟩,44,by decide,by decide,by decide⟩
private def s597 : Step := ⟨⟨⟨1350,1883,408,12355⟩,74202776600576,346190054868⟩,44,by decide,by decide,by decide⟩
private def s598 : Step := ⟨⟨⟨1350,1883,408,19788⟩,74202776600576,346190054868⟩,44,by decide,by decide,by decide⟩
private def s599 : Step := ⟨⟨⟨1350,1883,408,22261⟩,74202776600576,346190054868⟩,44,by decide,by decide,by decide⟩
private def s600 : Step := ⟨⟨⟨1350,1883,408,28173⟩,74202776600576,346190054868⟩,44,by decide,by decide,by decide⟩
private def s601 : Step := ⟨⟨⟨1350,1883,408,31694⟩,74202776600576,346190054868⟩,44,by decide,by decide,by decide⟩
private def s602 : Step := ⟨⟨⟨1350,1883,418,10983⟩,75578221264896,352769102024⟩,44,by decide,by decide,by decide⟩
private def s603 : Step := ⟨⟨⟨1350,1883,418,12355⟩,75578221264896,352769102024⟩,44,by decide,by decide,by decide⟩
private def s604 : Step := ⟨⟨⟨1350,1883,418,13899⟩,75578221264896,352769102024⟩,44,by decide,by decide,by decide⟩
private def s605 : Step := ⟨⟨⟨1350,1883,418,22261⟩,75578221264896,352769102024⟩,44,by decide,by decide,by decide⟩
private def s606 : Step := ⟨⟨⟨1350,1883,418,25043⟩,75578221264896,352769102024⟩,44,by decide,by decide,by decide⟩
private def s607 : Step := ⟨⟨⟨1350,1883,418,28173⟩,75578221264896,352769102024⟩,44,by decide,by decide,by decide⟩
private def s608 : Step := ⟨⟨⟨1350,1883,418,50764⟩,75578221264896,352769102024⟩,44,by decide,by decide,by decide⟩
private def s609 : Step := ⟨⟨⟨1650,2302,498,28173⟩,135254251667456,771697512616⟩,44,by decide,by decide,by decide⟩
private def s610 : Step := ⟨⟨⟨1650,2302,498,35655⟩,135254251667456,771697512616⟩,44,by decide,by decide,by decide⟩
private def s611 : Step := ⟨⟨⟨1650,2302,498,40111⟩,135254251667456,771697512616⟩,44,by decide,by decide,by decide⟩
private def s612 : Step := ⟨⟨⟨1650,2302,512,13899⟩,138129879859200,788519769358⟩,44,by decide,by decide,by decide⟩
private def s613 : Step := ⟨⟨⟨1650,2302,512,15636⟩,138129879859200,788519769358⟩,44,by decide,by decide,by decide⟩
private def s614 : Step := ⟨⟨⟨2000,2791,620,22261⟩,245690786119680,1701147081935⟩,44,by decide,by decide,by decide⟩
private def s615 : Step := ⟨⟨⟨2000,2791,620,40111⟩,245690786119680,1701147081935⟩,44,by decide,by decide,by decide⟩
private def s616 : Step := ⟨⟨⟨2500,3489,740,72277⟩,463070780456960,4004797990029⟩,44,by decide,by decide,by decide⟩
private def s617 : Step := ⟨⟨⟨2500,3489,755,64247⟩,470210689105920,4068029992867⟩,44,by decide,by decide,by decide⟩
private def s618 : Step := ⟨⟨⟨2500,3489,775,28173⟩,479640131993600,4151672878537⟩,44,by decide,by decide,by decide⟩
private def s619 : Step := ⟨⟨⟨2500,3489,775,50764⟩,479640131993600,4151672878537⟩,44,by decide,by decide,by decide⟩
private def s620 : Step := ⟨⟨⟨3000,4187,888,146522⟩,799929517735936,8302251431404⟩,44,by decide,by decide,by decide⟩
private def s621 : Step := ⟨⟨⟨3000,4187,906,64247⟩,812266433019904,8433369009268⟩,44,by decide,by decide,by decide⟩
private def s622 : Step := ⟨⟨⟨3000,4187,906,102908⟩,812266433019904,8433369009268⟩,44,by decide,by decide,by decide⟩
private def s623 : Step := ⟨⟨⟨3000,4187,906,130242⟩,812266433019904,8433369009268⟩,44,by decide,by decide,by decide⟩
private def s624 : Step := ⟨⟨⟨3000,4187,906,146522⟩,812266433019904,8433369009268⟩,44,by decide,by decide,by decide⟩
private def s625 : Step := ⟨⟨⟨3000,4187,930,35655⟩,828559354757120,8606810126747⟩,44,by decide,by decide,by decide⟩
private def s626 : Step := ⟨⟨⟨3500,4885,1036,297039⟩,1269967213297664,15378169933196⟩,44,by decide,by decide,by decide⟩
private def s627 : Step := ⟨⟨⟨3500,4885,1057,208621⟩,1289556817346560,15621081034380⟩,44,by decide,by decide,by decide⟩
private def s628 : Step := ⟨⟨⟨3500,4885,1057,264035⟩,1289556817346560,15621081034380⟩,44,by decide,by decide,by decide⟩
private def s629 : Step := ⟨⟨⟨4281,5949,1297,102908⟩,2364944629104640,34550690014738⟩,44,by decide,by decide,by decide⟩
private def s630 : Step := ⟨⟨⟨4281,5949,1297,264035⟩,2364944629104640,34550690014738⟩,44,by decide,by decide,by decide⟩
private def s631 : Step := ⟨⟨⟨1350,1882,408,15636⟩,74202776600576,345598963978⟩,73,by decide,by decide,by decide⟩
private def s632 : Step := ⟨⟨⟨1350,1882,418,13899⟩,75578221264896,352166349574⟩,73,by decide,by decide,by decide⟩
private def s633 : Step := ⟨⟨⟨1350,1882,418,17590⟩,75578221264896,352166349574⟩,73,by decide,by decide,by decide⟩
private def s634 : Step := ⟨⟨⟨1650,2301,498,13899⟩,135254251667456,770619519922⟩,73,by decide,by decide,by decide⟩
private def s635 : Step := ⟨⟨⟨1650,2301,498,17590⟩,135254251667456,770619519922⟩,73,by decide,by decide,by decide⟩
private def s636 : Step := ⟨⟨⟨1650,2301,498,22261⟩,135254251667456,770619519922⟩,73,by decide,by decide,by decide⟩
private def s637 : Step := ⟨⟨⟨1650,2301,498,25043⟩,135254251667456,770619519922⟩,73,by decide,by decide,by decide⟩
private def s638 : Step := ⟨⟨⟨1650,2301,512,13899⟩,138129879859200,787417379725⟩,73,by decide,by decide,by decide⟩
private def s639 : Step := ⟨⟨⟨1650,2301,512,15636⟩,138129879859200,787417379725⟩,73,by decide,by decide,by decide⟩
private def s640 : Step := ⟨⟨⟨1650,2301,512,17590⟩,138129879859200,787417379725⟩,73,by decide,by decide,by decide⟩
private def s641 : Step := ⟨⟨⟨1650,2301,512,19788⟩,138129879859200,787417379725⟩,73,by decide,by decide,by decide⟩
private def s642 : Step := ⟨⟨⟨1650,2301,512,28173⟩,138129879859200,787417379725⟩,73,by decide,by decide,by decide⟩
private def s643 : Step := ⟨⟨⟨1650,2301,512,31694⟩,138129879859200,787417379725⟩,73,by decide,by decide,by decide⟩
private def s644 : Step := ⟨⟨⟨1650,2301,512,35655⟩,138129879859200,787417379725⟩,73,by decide,by decide,by decide⟩
private def s645 : Step := ⟨⟨⟨2000,2790,604,19788⟩,240862397726720,1664965815864⟩,73,by decide,by decide,by decide⟩
private def s646 : Step := ⟨⟨⟨2000,2790,604,35655⟩,240862397726720,1664965815864⟩,73,by decide,by decide,by decide⟩
private def s647 : Step := ⟨⟨⟨2000,2790,604,40111⟩,240862397726720,1664965815864⟩,73,by decide,by decide,by decide⟩
private def s648 : Step := ⟨⟨⟨2000,2790,620,17590⟩,245690786119680,1699185179819⟩,73,by decide,by decide,by decide⟩
private def s649 : Step := ⟨⟨⟨2000,2790,620,19788⟩,245690786119680,1699185179819⟩,73,by decide,by decide,by decide⟩
private def s650 : Step := ⟨⟨⟨2000,2790,620,25043⟩,245690786119680,1699185179819⟩,73,by decide,by decide,by decide⟩
private def s651 : Step := ⟨⟨⟨2000,2790,620,35655⟩,245690786119680,1699185179819⟩,73,by decide,by decide,by decide⟩
private def s652 : Step := ⟨⟨⟨2000,2790,620,45124⟩,245690786119680,1699185179819⟩,73,by decide,by decide,by decide⟩
private def s653 : Step := ⟨⟨⟨2500,3488,755,22261⟩,470210689105920,4064279218567⟩,73,by decide,by decide,by decide⟩
private def s654 : Step := ⟨⟨⟨2500,3488,755,25043⟩,470210689105920,4064279218567⟩,73,by decide,by decide,by decide⟩
private def s655 : Step := ⟨⟨⟨2500,3488,775,19788⟩,479640131993600,4147842034257⟩,73,by decide,by decide,by decide⟩
private def s656 : Step := ⟨⟨⟨2500,3488,775,40111⟩,479640131993600,4147842034257⟩,73,by decide,by decide,by decide⟩
private def s657 : Step := ⟨⟨⟨2500,3488,775,64247⟩,479640131993600,4147842034257⟩,73,by decide,by decide,by decide⟩
private def s658 : Step := ⟨⟨⟨3000,4186,906,50764⟩,812266433019904,8426888829858⟩,73,by decide,by decide,by decide⟩
private def s659 : Step := ⟨⟨⟨3000,4186,906,64247⟩,812266433019904,8426888829858⟩,73,by decide,by decide,by decide⟩
private def s660 : Step := ⟨⟨⟨3000,4186,930,35655⟩,828559354757120,8600191575129⟩,73,by decide,by decide,by decide⟩
private def s661 : Step := ⟨⟨⟨3000,4186,930,40111⟩,828559354757120,8600191575129⟩,73,by decide,by decide,by decide⟩
private def s662 : Step := ⟨⟨⟨3000,4186,930,57109⟩,828559354757120,8600191575129⟩,73,by decide,by decide,by decide⟩
private def s663 : Step := ⟨⟨⟨3500,4884,1036,102908⟩,1269967213297664,15368047192365⟩,73,by decide,by decide,by decide⟩
private def s664 : Step := ⟨⟨⟨3500,4884,1036,115771⟩,1269967213297664,15368047192365⟩,73,by decide,by decide,by decide⟩
private def s665 : Step := ⟨⟨⟨3500,4884,1057,50764⟩,1289556817346560,15610792063730⟩,73,by decide,by decide,by decide⟩
private def s666 : Step := ⟨⟨⟨3500,4884,1057,81311⟩,1289556817346560,15610792063730⟩,73,by decide,by decide,by decide⟩
private def s667 : Step := ⟨⟨⟨3500,4884,1085,102908⟩,1315428062986240,15931892384151⟩,73,by decide,by decide,by decide⟩
private def s668 : Step := ⟨⟨⟨6623,9203,2007,164837⟩,8754949968101376,197823002949183⟩,73,by decide,by decide,by decide⟩
private def s669 : Step := ⟨⟨⟨1350,1882,408,15636⟩,74202776600576,345598963978⟩,76,by decide,by decide,by decide⟩
private def s670 : Step := ⟨⟨⟨1350,1882,418,15636⟩,75578221264896,352166349574⟩,76,by decide,by decide,by decide⟩
private def s671 : Step := ⟨⟨⟨1650,2301,498,15636⟩,135254251667456,770619519922⟩,76,by decide,by decide,by decide⟩
private def s672 : Step := ⟨⟨⟨1650,2301,498,17590⟩,135254251667456,770619519922⟩,76,by decide,by decide,by decide⟩
private def s673 : Step := ⟨⟨⟨1650,2301,498,40111⟩,135254251667456,770619519922⟩,76,by decide,by decide,by decide⟩
private def s674 : Step := ⟨⟨⟨1650,2301,512,13899⟩,138129879859200,787417379725⟩,76,by decide,by decide,by decide⟩
private def s675 : Step := ⟨⟨⟨1650,2301,512,17590⟩,138129879859200,787417379725⟩,76,by decide,by decide,by decide⟩
private def s676 : Step := ⟨⟨⟨1650,2301,512,19788⟩,138129879859200,787417379725⟩,76,by decide,by decide,by decide⟩
private def s677 : Step := ⟨⟨⟨1650,2301,512,22261⟩,138129879859200,787417379725⟩,76,by decide,by decide,by decide⟩
private def s678 : Step := ⟨⟨⟨1650,2301,512,25043⟩,138129879859200,787417379725⟩,76,by decide,by decide,by decide⟩
private def s679 : Step := ⟨⟨⟨1650,2301,512,31694⟩,138129879859200,787417379725⟩,76,by decide,by decide,by decide⟩
private def s680 : Step := ⟨⟨⟨2000,2789,604,17590⟩,240862397726720,1663046410409⟩,76,by decide,by decide,by decide⟩
private def s681 : Step := ⟨⟨⟨2000,2789,604,19788⟩,240862397726720,1663046410409⟩,76,by decide,by decide,by decide⟩
private def s682 : Step := ⟨⟨⟨2000,2789,604,22261⟩,240862397726720,1663046410409⟩,76,by decide,by decide,by decide⟩
private def s683 : Step := ⟨⟨⟨2000,2789,604,28173⟩,240862397726720,1663046410409⟩,76,by decide,by decide,by decide⟩
private def s684 : Step := ⟨⟨⟨2000,2789,604,31694⟩,240862397726720,1663046410409⟩,76,by decide,by decide,by decide⟩
private def s685 : Step := ⟨⟨⟨2000,2789,604,35655⟩,240862397726720,1663046410409⟩,76,by decide,by decide,by decide⟩
private def s686 : Step := ⟨⟨⟨2000,2789,604,45124⟩,240862397726720,1663046410409⟩,76,by decide,by decide,by decide⟩
private def s687 : Step := ⟨⟨⟨2000,2789,604,50764⟩,240862397726720,1663046410409⟩,76,by decide,by decide,by decide⟩
private def s688 : Step := ⟨⟨⟨2000,2789,620,17590⟩,245690786119680,1697224818404⟩,76,by decide,by decide,by decide⟩
private def s689 : Step := ⟨⟨⟨2000,2789,620,19788⟩,245690786119680,1697224818404⟩,76,by decide,by decide,by decide⟩
private def s690 : Step := ⟨⟨⟨2000,2789,620,35655⟩,245690786119680,1697224818404⟩,76,by decide,by decide,by decide⟩
private def s691 : Step := ⟨⟨⟨2000,2789,620,45124⟩,245690786119680,1697224818404⟩,76,by decide,by decide,by decide⟩
private def s692 : Step := ⟨⟨⟨2500,3488,755,22261⟩,470210689105920,4064279218567⟩,76,by decide,by decide,by decide⟩
private def s693 : Step := ⟨⟨⟨2500,3488,755,31694⟩,470210689105920,4064279218567⟩,76,by decide,by decide,by decide⟩
private def s694 : Step := ⟨⟨⟨2500,3488,775,22261⟩,479640131993600,4147842034257⟩,76,by decide,by decide,by decide⟩
private def s695 : Step := ⟨⟨⟨2500,3488,775,25043⟩,479640131993600,4147842034257⟩,76,by decide,by decide,by decide⟩
private def s696 : Step := ⟨⟨⟨2500,3488,775,45124⟩,479640131993600,4147842034257⟩,76,by decide,by decide,by decide⟩
private def s697 : Step := ⟨⟨⟨2500,3488,775,64247⟩,479640131993600,4147842034257⟩,76,by decide,by decide,by decide⟩
private def s698 : Step := ⟨⟨⟨3000,4186,906,40111⟩,812266433019904,8426888829858⟩,76,by decide,by decide,by decide⟩
private def s699 : Step := ⟨⟨⟨3000,4186,906,64247⟩,812266433019904,8426888829858⟩,76,by decide,by decide,by decide⟩
private def s700 : Step := ⟨⟨⟨3000,4186,906,72277⟩,812266433019904,8426888829858⟩,76,by decide,by decide,by decide⟩
private def s701 : Step := ⟨⟨⟨3000,4186,930,50764⟩,828559354757120,8600191575129⟩,76,by decide,by decide,by decide⟩
private def s702 : Step := ⟨⟨⟨3000,4186,930,64247⟩,828559354757120,8600191575129⟩,76,by decide,by decide,by decide⟩
private def s703 : Step := ⟨⟨⟨3500,4884,1036,115771⟩,1269967213297664,15368047192365⟩,76,by decide,by decide,by decide⟩
private def s704 : Step := ⟨⟨⟨3500,4884,1057,102908⟩,1289556817346560,15610792063730⟩,76,by decide,by decide,by decide⟩
private def s705 : Step := ⟨⟨⟨3500,4884,1057,115771⟩,1289556817346560,15610792063730⟩,76,by decide,by decide,by decide⟩
private def s706 : Step := ⟨⟨⟨3500,4884,1085,50764⟩,1315428062986240,15931892384151⟩,76,by decide,by decide,by decide⟩
private def s707 : Step := ⟨⟨⟨4500,6280,1395,81311⟩,2794932370145280,43531937415069⟩,76,by decide,by decide,by decide⟩
private def s708 : Step := ⟨⟨⟨6624,9204,2007,164837⟩,8757908515848192,197892215121891⟩,76,by decide,by decide,by decide⟩
private def s709 : Step := ⟨⟨⟨2000,2788,604,19788⟩,240862397726720,1661128510194⟩,103,by decide,by decide,by decide⟩
private def s710 : Step := ⟨⟨⟨2000,2788,604,25043⟩,240862397726720,1661128510194⟩,103,by decide,by decide,by decide⟩
private def s711 : Step := ⟨⟨⟨2000,2788,620,17590⟩,245690786119680,1695265997069⟩,103,by decide,by decide,by decide⟩
private def s712 : Step := ⟨⟨⟨2000,2788,620,19788⟩,245690786119680,1695265997069⟩,103,by decide,by decide,by decide⟩
private def s713 : Step := ⟨⟨⟨2000,2788,620,22261⟩,245690786119680,1695265997069⟩,103,by decide,by decide,by decide⟩
private def s714 : Step := ⟨⟨⟨2000,2788,620,25043⟩,245690786119680,1695265997069⟩,103,by decide,by decide,by decide⟩
private def s715 : Step := ⟨⟨⟨2000,2788,620,28173⟩,245690786119680,1695265997069⟩,103,by decide,by decide,by decide⟩
private def s716 : Step := ⟨⟨⟨2500,3487,755,25043⟩,470210689105920,4060530796561⟩,103,by decide,by decide,by decide⟩
private def s717 : Step := ⟨⟨⟨2500,3487,755,31694⟩,470210689105920,4060530796561⟩,103,by decide,by decide,by decide⟩
private def s718 : Step := ⟨⟨⟨2500,3487,755,40111⟩,470210689105920,4060530796561⟩,103,by decide,by decide,by decide⟩
private def s719 : Step := ⟨⟨⟨2500,3487,775,22261⟩,479640131993600,4144013596741⟩,103,by decide,by decide,by decide⟩
private def s720 : Step := ⟨⟨⟨2500,3487,775,25043⟩,479640131993600,4144013596741⟩,103,by decide,by decide,by decide⟩
private def s721 : Step := ⟨⟨⟨2500,3487,775,28173⟩,479640131993600,4144013596741⟩,103,by decide,by decide,by decide⟩
private def s722 : Step := ⟨⟨⟨2500,3487,775,31694⟩,479640131993600,4144013596741⟩,103,by decide,by decide,by decide⟩
private def s723 : Step := ⟨⟨⟨2500,3487,775,35655⟩,479640131993600,4144013596741⟩,103,by decide,by decide,by decide⟩
private def s724 : Step := ⟨⟨⟨2500,3487,775,40111⟩,479640131993600,4144013596741⟩,103,by decide,by decide,by decide⟩
private def s725 : Step := ⟨⟨⟨2500,3487,775,45124⟩,479640131993600,4144013596741⟩,103,by decide,by decide,by decide⟩
private def s726 : Step := ⟨⟨⟨3000,4185,906,45124⟩,812266433019904,8420412037186⟩,103,by decide,by decide,by decide⟩
private def s727 : Step := ⟨⟨⟨3000,4185,906,57109⟩,812266433019904,8420412037186⟩,103,by decide,by decide,by decide⟩
private def s728 : Step := ⟨⟨⟨3000,4185,930,28173⟩,828559354757120,8593576488693⟩,103,by decide,by decide,by decide⟩
private def s729 : Step := ⟨⟨⟨3000,4185,930,31694⟩,828559354757120,8593576488693⟩,103,by decide,by decide,by decide⟩
private def s730 : Step := ⟨⟨⟨3000,4185,930,50764⟩,828559354757120,8593576488693⟩,103,by decide,by decide,by decide⟩
private def s731 : Step := ⟨⟨⟨3000,4185,930,57109⟩,828559354757120,8593576488693⟩,103,by decide,by decide,by decide⟩
private def s732 : Step := ⟨⟨⟨3500,4883,1057,57109⟩,1289556817346560,15600507702257⟩,103,by decide,by decide,by decide⟩
private def s733 : Step := ⟨⟨⟨3500,4883,1057,72277⟩,1289556817346560,15600507702257⟩,103,by decide,by decide,by decide⟩
private def s734 : Step := ⟨⟨⟨3500,4883,1057,91474⟩,1289556817346560,15600507702257⟩,103,by decide,by decide,by decide⟩
private def s735 : Step := ⟨⟨⟨3500,4883,1085,31694⟩,1315428062986240,15921388386716⟩,103,by decide,by decide,by decide⟩
private def s736 : Step := ⟨⟨⟨3500,4883,1085,57109⟩,1315428062986240,15921388386716⟩,103,by decide,by decide,by decide⟩
private def s737 : Step := ⟨⟨⟨3500,4883,1085,81311⟩,1315428062986240,15921388386716⟩,103,by decide,by decide,by decide⟩
private def s738 : Step := ⟨⟨⟨4500,6279,1332,146522⟩,2698317932789760,41969435185037⟩,103,by decide,by decide,by decide⟩
private def s739 : Step := ⟨⟨⟨4500,6279,1332,164837⟩,2698317932789760,41969435185037⟩,103,by decide,by decide,by decide⟩
private def s740 : Step := ⟨⟨⟨4500,6279,1359,81311⟩,2739950258749440,42632508857204⟩,103,by decide,by decide,by decide⟩
private def s741 : Step := ⟨⟨⟨4500,6279,1359,115771⟩,2739950258749440,42632508857204⟩,103,by decide,by decide,by decide⟩
private def s742 : Step := ⟨⟨⟨4500,6279,1359,146522⟩,2739950258749440,42632508857204⟩,103,by decide,by decide,by decide⟩
private def s743 : Step := ⟨⟨⟨4500,6279,1395,72277⟩,2794932370145280,43509614052359⟩,103,by decide,by decide,by decide⟩
private def s744 : Step := ⟨⟨⟨9071,12604,2749,208621⟩,22490098892800000,695862530200649⟩,103,by decide,by decide,by decide⟩
private def r0 : Route := ⟨2,1,![s47,s93,s144,s193,s241,s290,s338,s385,s433,s385,s483,s577,s528,s630,s630,s630,s630],by decide,rfl,by intro k; fin_cases k <;> decide,![11,13],![154,5896],by intro k; fin_cases k <;> decide,by decide⟩
private def r1 : Route := ⟨2,3,![s50,s96,s141,s192,s239,s287,s337,s386,s432,s386,s480,s580,s532,s626,s626,s626,s626],by decide,rfl,by intro k; fin_cases k <;> decide,![13,11],![131,5715],by intro k; fin_cases k <;> decide,by decide⟩
private def r2 : Route := ⟨2,8,![s46,s92,s140,s191,s240,s289,s336,s384,s431,s384,s479,s576,s533,s628,s628,s628,s628],by decide,rfl,by intro k; fin_cases k <;> decide,![13,12],![132,5415],by intro k; fin_cases k <;> decide,by decide⟩
private def r3 : Route := ⟨2,15,![s49,s95,s139,s190,s238,s288,s335,s383,s430,s383,s478,s579,s531,s627,s627,s627,s627],by decide,rfl,by intro k; fin_cases k <;> decide,![13,11],![132,4427],by intro k; fin_cases k <;> decide,by decide⟩
private def r4 : Route := ⟨2,25,![s48,s94,s142,s194,s242,s291,s339,s382,s434,s382,s484,s578,s529,s629,s668,s708,s744],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![145,2666],by intro k; fin_cases k <;> decide,by decide⟩
private def r5 : Route := ⟨2,40,![s44,s90,s136,s189,s235,s286,s334,s380,s426,s380,s482,s574,s526,s625,s625,s625,s625],by decide,rfl,by intro k; fin_cases k <;> decide,![13,13],![113,1619],by intro k; fin_cases k <;> decide,by decide⟩
private def r6 : Route := ⟨2,50,![s29,s72,s121,s172,s218,s271,s319,s363,s411,s363,s464,s560,s515,s613,s654,s695,s735],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![55,826],by intro k; fin_cases k <;> decide,by decide⟩
private def r7 : Route := ⟨2,70,![s17,s67,s111,s160,s210,s256,s312,s359,s404,s359,s453,s553,s508,s597,s645,s689,s722],by decide,rfl,by intro k; fin_cases k <;> decide,![16,15],![40,820],by intro k; fin_cases k <;> decide,by decide⟩
private def r8 : Route := ⟨2,92,![s4,s55,s101,s147,s199,s247,s298,s344,s389,s344,s439,s537,s490,s585,s638,s671,s713],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![32,762],by intro k; fin_cases k <;> decide,by decide⟩
private def r9 : Route := ⟨3,1,![s43,s89,s143,s188,s234,s285,s333,s379,s428,s379,s477,s572,s525,s624,s624,s624,s624],by decide,rfl,by intro k; fin_cases k <;> decide,![13,13],![133,3276],by intro k; fin_cases k <;> decide,by decide⟩
private def r10 : Route := ⟨3,3,![s43,s91,s135,s184,s236,s281,s331,s381,s429,s381,s475,s575,s527,s620,s620,s620,s620],by decide,rfl,by intro k; fin_cases k <;> decide,![13,11],![132,3200],by intro k; fin_cases k <;> decide,by decide⟩
private def r11 : Route := ⟨3,8,![s42,s87,s138,s187,s237,s284,s332,s377,s427,s377,s476,s571,s530,s623,s623,s623,s623],by decide,rfl,by intro k; fin_cases k <;> decide,![13,13],![133,3055],by intro k; fin_cases k <;> decide,by decide⟩
private def r12 : Route := ⟨3,15,![s41,s86,s137,s186,s233,s283,s330,s376,s425,s376,s474,s570,s524,s622,s622,s622,s622],by decide,rfl,by intro k; fin_cases k <;> decide,![12,13],![124,2588],by intro k; fin_cases k <;> decide,by decide⟩
private def r13 : Route := ⟨3,25,![s45,s88,s134,s185,s232,s282,s329,s378,s424,s378,s481,s573,s523,s621,s621,s621,s621],by decide,rfl,by intro k; fin_cases k <;> decide,![12,13],![124,1931],by intro k; fin_cases k <;> decide,by decide⟩
private def r14 : Route := ⟨3,40,![s39,s85,s133,s183,s230,s276,s327,s375,s421,s375,s471,s569,s519,s618,s665,s706,s743],by decide,rfl,by intro k; fin_cases k <;> decide,![16,15],![87,1222],by intro k; fin_cases k <;> decide,by decide⟩
private def r15 : Route := ⟨3,50,![s28,s70,s118,s169,s217,s263,s316,s360,s410,s360,s463,s558,s507,s612,s653,s694,s729],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![58,751],by intro k; fin_cases k <;> decide,by decide⟩
private def r16 : Route := ⟨3,70,![s22,s62,s108,s158,s209,s255,s305,s355,s403,s355,s449,s547,s501,s602,s648,s681,s720],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![48,762],by intro k; fin_cases k <;> decide,by decide⟩
private def r17 : Route := ⟨3,92,![s3,s52,s100,s147,s196,s246,s297,s343,s395,s343,s436,s537,s487,s583,s638,s671,s712],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![38,738],by intro k; fin_cases k <;> decide,by decide⟩
private def r18 : Route := ⟨4,1,![s38,s79,s134,s182,s228,s280,s326,s371,s420,s371,s473,s566,s518,s616,s664,s705,s739],by decide,rfl,by intro k; fin_cases k <;> decide,![16,15],![98,1517],by intro k; fin_cases k <;> decide,by decide⟩
private def r19 : Route := ⟨4,3,![s36,s84,s132,s179,s231,s278,s326,s374,s420,s374,s470,s566,s522,s616,s667,s703,s742],by decide,rfl,by intro k; fin_cases k <;> decide,![16,14],![99,1434],by intro k; fin_cases k <;> decide,by decide⟩
private def r20 : Route := ⟨4,8,![s37,s82,s129,s181,s227,s279,s328,s372,s422,s372,s472,s567,s517,s617,s663,s704,s738],by decide,rfl,by intro k; fin_cases k <;> decide,![16,15],![98,1446],by intro k; fin_cases k <;> decide,by decide⟩
private def r21 : Route := ⟨4,15,![s40,s83,s131,s178,s229,s277,s325,s373,s423,s373,s469,s568,s521,s619,s666,s707,s741],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![99,1309],by intro k; fin_cases k <;> decide,by decide⟩
private def r22 : Route := ⟨4,25,![s34,s78,s130,s177,s223,s275,s324,s368,s417,s368,s467,s565,s514,s615,s659,s700,s740],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![89,1108],by intro k; fin_cases k <;> decide,by decide⟩
private def r23 : Route := ⟨4,40,![s32,s75,s128,s180,s224,s272,s321,s365,s415,s365,s465,s563,s512,s614,s660,s698,s732],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![77,955],by intro k; fin_cases k <;> decide,by decide⟩
private def r24 : Route := ⟨4,50,![s24,s68,s117,s165,s214,s262,s315,s357,s407,s357,s456,s554,s506,s604,s655,s692,s728],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![67,718],by intro k; fin_cases k <;> decide,by decide⟩
private def r25 : Route := ⟨4,70,![s13,s61,s104,s156,s202,s253,s301,s347,s399,s347,s448,s543,s500,s593,s641,s688,s716],by decide,rfl,by intro k; fin_cases k <;> decide,![14,16],![51,748],by intro k; fin_cases k <;> decide,by decide⟩
private def r26 : Route := ⟨4,92,![s1,s57,s98,s146,s196,s244,s294,s341,s388,s341,s438,s535,s489,s582,s633,s674,s712],by decide,rfl,by intro k; fin_cases k <;> decide,![14,16],![42,738],by intro k; fin_cases k <;> decide,by decide⟩
private def r27 : Route := ⟨5,1,![s35,s76,s127,s176,s223,s270,s318,s367,s419,s367,s468,s564,s513,s615,s657,s702,s734],by decide,rfl,by intro k; fin_cases k <;> decide,![16,15],![87,846],by intro k; fin_cases k <;> decide,by decide⟩
private def r28 : Route := ⟨5,3,![s33,s73,s123,s171,s222,s268,s318,s362,s416,s362,s462,s564,s511,s608,s657,s699,s734],by decide,rfl,by intro k; fin_cases k <;> decide,![13,15],![79,869],by intro k; fin_cases k <;> decide,by decide⟩
private def r29 : Route := ⟨5,8,![s31,s81,s126,s175,s226,s274,s323,s370,s414,s370,s466,s562,s520,s611,s662,s697,s737],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![85,865],by intro k; fin_cases k <;> decide,by decide⟩
private def r30 : Route := ⟨5,15,![s27,s77,s125,s174,s220,s267,s322,s366,s418,s366,s461,s557,s510,s610,s658,s701,s733],by decide,rfl,by intro k; fin_cases k <;> decide,![11,15],![86,840],by intro k; fin_cases k <;> decide,by decide⟩
private def r31 : Route := ⟨5,25,![s26,s80,s124,s173,s225,s273,s321,s369,s413,s369,s460,s561,s516,s609,s661,s696,s732],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![85,803],by intro k; fin_cases k <;> decide,by decide⟩
private def r32 : Route := ⟨5,40,![s25,s71,s115,s166,s211,s264,s320,s361,s408,s361,s457,s555,s509,s605,s651,s693,s726],by decide,rfl,by intro k; fin_cases k <;> decide,![14,16],![71,782],by intro k; fin_cases k <;> decide,by decide⟩
private def r33 : Route := ⟨5,50,![s23,s63,s109,s159,s210,s256,s306,s356,s404,s356,s450,s548,s502,s603,s649,s682,s721],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![63,643],by intro k; fin_cases k <;> decide,by decide⟩
private def r34 : Route := ⟨5,70,![s12,s61,s110,s155,s201,s254,s311,s346,s399,s346,s447,s542,s493,s592,s640,s680,s719],by decide,rfl,by intro k; fin_cases k <;> decide,![14,14],![58,722],by intro k; fin_cases k <;> decide,by decide⟩
private def r35 : Route := ⟨5,92,![s6,s54,s99,s152,s195,s245,s296,s342,s390,s342,s445,s541,s489,s591,s634,s674,s709],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![50,724],by intro k; fin_cases k <;> decide,by decide⟩
private def r36 : Route := ⟨6,1,![s26,s69,s116,s170,s216,s261,s310,s358,s409,s358,s465,s559,s505,s601,s652,s687,s736],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![75,559],by intro k; fin_cases k <;> decide,by decide⟩
private def r37 : Route := ⟨6,3,![s26,s69,s122,s170,s213,s269,s310,s358,s409,s358,s460,s556,s505,s607,s652,s687,s731],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![75,575],by intro k; fin_cases k <;> decide,by decide⟩
private def r38 : Route := ⟨6,8,![s21,s75,s120,s168,s221,s266,s317,s365,s406,s365,s459,s556,s516,s600,s656,s691,s727],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![76,618],by intro k; fin_cases k <;> decide,by decide⟩
private def r39 : Route := ⟨6,15,![s20,s74,s119,s167,s212,s265,s309,s364,s405,s364,s458,s552,s498,s606,s647,s686,s730],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![75,622],by intro k; fin_cases k <;> decide,by decide⟩
private def r40 : Route := ⟨6,25,![s30,s71,s114,s164,s219,s264,s314,s361,s412,s361,s455,s545,s504,s599,s646,s690,s726],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![76,651],by intro k; fin_cases k <;> decide,by decide⟩
private def r41 : Route := ⟨6,40,![s14,s64,s112,s161,s215,s258,s307,s360,s400,s360,s451,s558,s503,s595,s650,s683,s718],by decide,rfl,by intro k; fin_cases k <;> decide,![16,14],![69,673],by intro k; fin_cases k <;> decide,by decide⟩
private def r42 : Route := ⟨6,50,![s9,s62,s104,s156,s205,s257,s301,s351,s393,s351,s442,s547,s494,s588,s636,s677,s720],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![63,613],by intro k; fin_cases k <;> decide,by decide⟩
private def r43 : Route := ⟨6,70,![s7,s58,s107,s153,s198,s250,s303,s345,s391,s345,s441,s539,s499,s586,s635,s675,s714],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![56,658],by intro k; fin_cases k <;> decide,by decide⟩
private def r44 : Route := ⟨6,92,![s0,s54,s97,s145,s195,s243,s293,s340,s387,s340,s435,s536,s486,s581,s631,s670,s709],by decide,rfl,by intro k; fin_cases k <;> decide,![15,15],![51,702],by intro k; fin_cases k <;> decide,by decide⟩
private def r45 : Route := ⟨7,1,![s19,s66,s114,s163,s208,s260,s314,s354,s402,s354,s455,s551,s497,s590,s646,s685,s726],by decide,rfl,by intro k; fin_cases k <;> decide,![13,16],![78,442],by intro k; fin_cases k <;> decide,by decide⟩
private def r46 : Route := ⟨7,3,![s16,s66,s114,s157,s208,s260,s308,s361,s402,s361,s455,s551,s509,s599,s644,s685,s725],by decide,rfl,by intro k; fin_cases k <;> decide,![14,16],![72,456],by intro k; fin_cases k <;> decide,by decide⟩
private def r47 : Route := ⟨7,8,![s15,s56,s106,s151,s203,s249,s299,s349,s398,s349,s452,s544,s492,s596,s644,s673,s725],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![68,493],by intro k; fin_cases k <;> decide,by decide⟩
private def r48 : Route := ⟨7,15,![s18,s65,s113,s162,s207,s259,s313,s353,s401,s353,s454,s550,s496,s598,s643,s684,s724],by decide,rfl,by intro k; fin_cases k <;> decide,![14,16],![72,497],by intro k; fin_cases k <;> decide,by decide⟩
private def r49 : Route := ⟨7,25,![s5,s60,s105,s154,s206,s252,s302,s352,s394,s352,s444,s549,s495,s589,s642,s679,s723],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![69,529],by intro k; fin_cases k <;> decide,by decide⟩
private def r50 : Route := ⟨7,40,![s10,s67,s102,s150,s200,s248,s304,s348,s397,s348,s443,s540,s502,s594,s637,s678,s717],by decide,rfl,by intro k; fin_cases k <;> decide,![15,15],![69,591],by intro k; fin_cases k <;> decide,by decide⟩
private def r51 : Route := ⟨7,50,![s8,s59,s103,s149,s204,s251,s300,s350,s392,s350,s440,s546,s491,s587,s640,s676,s715],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![62,568],by intro k; fin_cases k <;> decide,by decide⟩
private def r52 : Route := ⟨7,70,![s11,s53,s101,s148,s197,s246,s295,s344,s396,s344,s446,s538,s488,s584,s639,s672,s710],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![61,647],by intro k; fin_cases k <;> decide,by decide⟩
private def r53 : Route := ⟨7,92,![s2,s51,s97,s145,s195,s243,s292,s340,s387,s340,s437,s534,s485,s581,s632,s669,s711],by decide,rfl,by intro k; fin_cases k <;> decide,![15,15],![56,690],by intro k; fin_cases k <;> decide,by decide⟩
def data : Fin 54 → Route := ![r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53]

def bank (r:Fin 54) (i:Fin 17) := ((data r).stages i).source
def reserve (r:Fin 54) (i:Fin 17) := ((data r).stages i).order
def jetCap (r:Fin 54) := (data r).degree
def seedCap (r:Fin 54) := (data r).upper
def cutoff (h:ℕ) (r:Fin 54) (i:Fin 17) := (bank r i).shape.m*179769-2*h*reserve r i-1
theorem shape_guards (r:Fin 54) (i:Fin 17) : 0<(bank r i).shape.J ∧ (bank r i).shape.J≤(bank r i).shape.B ∧ (bank r i).shape.B<K1.p ∧ (bank r i).shape.U<K1.p ∧ (bank r i).shape.m*179769<K1.p := ((data r).stages i).safe
theorem cutoff_fit {h:ℕ} (hi:h≤2499) (r:Fin 54) (i:Fin 17) :
    cutoff h r i+2*h*reserve r i<(bank r i).shape.m*179769 := by
  have bound : 2*2499*reserve r i<(bank r i).shape.m*179769 := ((data r).stages i).room
  have small := Nat.mul_le_mul_right (reserve r i) (Nat.mul_le_mul_left 2 hi)
  unfold cutoff
  omega
end Lower6960.Rescue6966Source

end Merged_High6966RescueData

-- merged module High6966RescueGeometry
section Merged_High6966RescueGeometry

set_option Elab.async false
-- merged module R6960Rescue6966
section Merged_R6960Rescue6966
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.Rescue6966
open Finset Polynomial
open K1 (I K)
open K1_14 (L FX Shape Jet jetAt atX liftPoly)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom UsesSeed ODE)
open K1_14_2_2 (RowCaps Active dual Fits mass sectionDegree ordinateIncl ODECaps fixedOn)
open K1_14_2_2_2 (FiniteSections residualBudget ordinate_eq length_le_mass)
open K1_14_2_2_2_1 (rowCaps_iff jetDegree seedDegree)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (SeedCover joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open Rescue6966Source (bank reserve cutoff jetCap seedCap)
open DifferentialContact (Native)
open scoped Classical
open K1_14_2_2_3 (shiftedWord)
open P0_10R_1 (seed_projection section_bound component_height)
open P1_7_4_1 (irreducible_cut)
abbrev Model (u : P1.Words) (deleted : Finset I) := P1.ModelAt 33677 u deleted
abbrev Family {u deleted} (M : Model u deleted) (Γ : Finset K) := P1.FamilyAt 179769 M Γ
def word {u deleted} (M : Model u deleted) : I→L := fun i => algebraMap K L (M.word i)
def OnMark {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (A : Ideal Ambient) (γ : K) : Prop := OnJet A (M.label γ) (F.scalar γ)
theorem label_injective {u deleted} (M : Model u deleted) : Function.Injective M.label :=
  fun _ _ h => sub_left_inj.mp h
def primeShape (rect : Fin 54) : Shape := ⟨0,jetCap rect,1,seedCap rect⟩
def initialCap (rect : Fin 54) : Fin 4 → ℕ := pairCap (primeShape rect) (bank rect 0).shape
theorem prime_shape_fit (rect : Fin 54) : (primeShape rect).J≤(primeShape rect).B :=
  (Rescue6966Source.data rect).pos
theorem initial_small (rect : Fin 54) (k : Fin 4) : initialCap rect k<K1.p :=
  (Rescue6966Source.data rect).small k
theorem reserve_small (rect : Fin 54) (i : Fin 17) : reserve rect i<K1.p :=
  ((Rescue6966Source.data rect).stages i).small
theorem contact_at_mark {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {s : Shape} {W r : ℕ} {P : Jet} (inside : P∈evaluated Crt (word M) s W)
    (width : W+2*M.overhead.toNat*r<s.m*179769)
    (γ : K) (hγ : γ∈Γ) :
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (r+1) P := by
  let B := F.mark γ hγ
  have degree : (liftPoly (F.scalar γ)).natDegree≤131071+M.overhead.toNat := by
    rw [liftPoly, Polynomial.natDegree_map]
    rcases B.scalar_degree with hzero | hd
    · simp [hzero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at hd
      omega
  refine PrefixRows.contact_of_crt Crt (word M) s P inside width noPole
    (M.label γ) (F.scalar γ) (residues γ hγ) degree B.bad.support B.bad.agreement ?_
  intro i hit
  rw [word,liftPoly,nodeL,Polynomial.eval_map,Polynomial.eval₂_hom]
  exact congrArg (algebraMap K L) (B.scalar_hits i hit)
theorem zero_of_contact {z : K} {S : (Polynomial K)} {P : Jet} {r : ℕ}
    (contact : Native (RingHom.ker (jetMarkHom z S)) (r+1) P) : jetAt P z S=0 := by
  have test := contact [] (by simp)
  change toJet P∈RingHom.ker (jetMarkHom z S) at test
  rwa [RingHom.mem_ker,K1_14_2.eval_toJet] at test
private theorem initial_sections {G Q : Jet} {s t : Shape} (irr : Irreducible G)
    (avoid : ¬G∣Q) (gs : RowCaps G s) (qs : RowCaps Q t) (js : s.J≤s.B) (jt : t.J≤t.B) :
    ∃ A : Finset (Ideal Ambient), P1_7_4_1.SectionGeometry A ∧ Fits A (pairCap s t) ∧
      (∀ J∈A,toJet G∈J ∧ toJet Q∈J) ∧
      ∀ z S,jetAt G z S=0 → jetAt Q z S=0 → ∃ J∈A,OnJet J z S := by
  have proper := irreducible_cut irr avoid
  obtain ⟨A,geom,cover⟩ := K1_14_2_2_2_3.proof _ _ proper
  obtain ⟨finite,fit⟩ := section_bound _ _ proper s t js jt gs qs A geom
  refine ⟨A,?_,fit,fun J mem=>(geom J mem).2.2,cover⟩
  intro J mem
  obtain ⟨prime,dim,g,q⟩ := geom J mem
  exact ⟨prime,dim,component_height proper prime dim g q,finite J mem⟩
structure Initial {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (G Q₀ : Jet) (rect : Fin 54) where
  seeds : SeedCover
  seed_degree : seeds.curve.totalDegree ≤ initialCap rect 2
  seed_points : seeds.points.card ≤ initialCap rect 3
  ordinates : Finset FX
  ordinate_card : ordinates.card ≤ initialCap rect 0
  rankExit : Finset (Ideal Ambient)
  parents : Finset (Ideal Ambient)
  rank_geom : ∀ J∈rankExit,Active J ∧ ¬dual J
  parent_geom : ∀ J∈parents,Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet Q₀∈J
  disjoint : Disjoint rankExit parents
  fits : Fits (rankExit∪parents) (initialCap rect)
  covers : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 →
    seeds.Covers (M.label γ) ∨ atX (F.scalar γ)∈ordinates ∨
      (∃ J∈rankExit,OnMark F J γ) ∨ ∃ J∈parents,OnMark F J γ
private theorem classify {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {rect : Fin 54} {A : Finset (Ideal Ambient)}
    (geom : P1_7_4_1.SectionGeometry A) (fit : Fits A (initialCap rect))
    (rows : ∀ J∈A,toJet G∈J ∧ toJet Q₀∈J)
    (cover : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → ∃ J∈A,OnMark F J γ) :
    Nonempty (Initial F G Q₀ rect) := by
  classical
  let noSeeds := A.filter (fun J=>sectionDegree J 0=0)
  let constY := A.filter (fun J=>0<sectionDegree J 0 ∧
    ¬Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let active := A.filter (fun J=>0<sectionDegree J 0 ∧
    Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let rank := active.filter (fun J=>¬dual J)
  let parents := active.filter dual
  have geomActive (J : Ideal Ambient) (mem : J∈active) : Active J ∧ J.height=2 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,height,finite⟩ := geom J hin
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (initial_small rect k))
    exact ⟨⟨prime,dim,finite.seeds,finite.ordinate,finite.mixed,finite.jets,
      ⟨seedPos,small 0⟩,small 2,small 3,ord⟩,height⟩
  have seed_exists (J : Ideal Ambient) (mem : J∈noSeeds) :
      ∃ C : SeedCover,C.curve.totalDegree≤sectionDegree J 2 ∧ C.points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → C.Covers z := by
    obtain ⟨hin,zero⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,_,finite⟩ := geom J hin
    exact seed_projection J prime dim finite zero
  let seedImage (J : Ideal Ambient) : SeedCover :=
    if mem : J∈noSeeds then Classical.choose (seed_exists J mem) else ⟨1,one_ne_zero,∅⟩
  have seed_spec (J : Ideal Ambient) (mem : J∈noSeeds) :
      (seedImage J).curve.totalDegree≤sectionDegree J 2 ∧
        (seedImage J).points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → (seedImage J).Covers z := by
    simpa only [seedImage,dite_eq_left mem] using Classical.choose_spec (seed_exists J mem)
  let onY (J : Ideal Ambient) := (Γ.filter (OnMark F J)).image fun γ=>atX (F.scalar γ)
  have ordinate_bound (J : Ideal Ambient) (mem : J∈constY) : (onY J).card≤sectionDegree J 0 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    apply le_trans (b:=1) _ seedPos
    apply card_le_one.mpr
    intro y hy z hz
    obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hy
    obtain ⟨δ,hδ,rfl⟩ := mem_image.mp hz
    exact ordinate_eq (geom J hin).1 ord (mem_filter.mp hγ).2 (mem_filter.mp hδ).2
  refine ⟨⟨joinCovers noSeeds seedImage,?_,?_,constY.biUnion onY,?_,rank,parents,?_,?_,?_,?_,?_⟩⟩
  · exact (joinCovers_degree _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 2).trans (fit 2)))
  · exact (joinCovers_points _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).2.1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 3).trans (fit 3)))
  · exact card_biUnion_le.trans ((sum_le_sum ordinate_bound).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 0).trans (fit 0)))
  · intro J mem
    exact ⟨(geomActive J (mem_filter.mp mem).1).1,(mem_filter.mp mem).2⟩
  · intro J mem
    obtain ⟨hin,d⟩ := mem_filter.mp mem
    obtain ⟨act,ht⟩ := geomActive J hin
    exact ⟨act,d,ht,rows J (mem_filter.mp hin).1⟩
  · exact disjoint_left.mpr fun _ a b=>(mem_filter.mp a).2 (mem_filter.mp b).2
  · apply K1_14_2_2.fits_mono _ fit
    exact union_subset ((filter_subset _ _).trans (filter_subset _ _))
      ((filter_subset _ _).trans (filter_subset _ _))
  · intro γ hγ zero
    obtain ⟨J,hin,on⟩ := cover γ hγ zero
    by_cases z : sectionDegree J 0=0
    · have mem : J∈noSeeds := mem_filter.mpr ⟨hin,z⟩
      exact Or.inl (joinCovers_covers mem ((seed_spec J mem).2.2 _ _ on))
    · by_cases ord : Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl)
      · have mem : J∈active := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
        by_cases d : dual J
        · exact Or.inr (Or.inr (Or.inr ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
      · have mem : J∈constY := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
        exact Or.inr (Or.inl (mem_biUnion.mpr ⟨J,mem,
          mem_image.mpr ⟨γ,mem_filter.mpr ⟨hγ,on⟩,rfl⟩⟩))
theorem initial_cover {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {rect : Fin 54} (irr : Irreducible G) (avoid : ¬G∣Q₀)
    (capsG : RowCaps G (primeShape rect)) (capsQ : RowCaps Q₀ (bank rect 0).shape)
    (zero : ∀ γ∈Γ,jetAt Q₀ (M.label γ) (F.scalar γ)=0) :
    Nonempty (Initial F G Q₀ rect) := by
  obtain ⟨A,geom,fit,rows,cover⟩ := initial_sections irr avoid capsG capsQ (prime_shape_fit rect)
    (Rescue6966Source.shape_guards rect 0).2.1
  exact classify F geom fit rows (fun γ hγ hG => cover _ _ hG (zero γ hγ))
theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 54} (initial : Initial F G Q₀ rect) :
    ∃ E : ODE, ODECaps E (mass initial.rankExit 2) (mass initial.rankExit 1) ∧
      ∀ γ∈Γ,(∃ J∈initial.rankExit,OnMark F J γ) → K1_14_2.fixedAt E (F.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation initial.rankExit initial.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))
end Lower6960.Rescue6966

end
end Merged_R6960Rescue6966

-- merged module R6960Rescue6966History
section Merged_R6960Rescue6966History
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.Rescue6966
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual Fits mass)
open K1_14_2_2_2_1 (rowCaps_iff jetDegree seedDegree)
open K1_14_2_2_4 (pairCap)
open Rescue6966Source (bank reserve cutoff jetCap seedCap)
open DifferentialContact (Native)
open scoped Classical
open K1_14_2_2_3 (shiftedWord)
theorem history_from_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G : Jet} {rect : Fin 54} (irr : Irreducible G) (capsG : RowCaps G (primeShape rect))
    (Q : Fin 17→Jet) (init : Initial F G (Q 0) rect) (avoid : ∀ i,¬G∣Q i)
    (caps : ∀ i,RowCaps (Q i) (bank rect i).shape)
    (contact : ∀ i γ,γ∈Γ → Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ)))
      (reserve rect i+1) (Q i)) :
    ∃ kept : ℕ→Finset (Ideal Ambient),
      kept 0=init.parents ∧ kept 1=init.parents ∧ Antitone kept ∧
      (∀ i : Fin 17,∀ n,i.val<n → ∀ J∈kept n,Native J (reserve rect i+1) (Q i)) ∧
      (∀ i : Fin 17,∀ n,i.val<n → ∀ c : Fin 4,
        (reserve rect i+1)*mass (kept n) c≤pairCap (primeShape rect) (bank rect i).shape c) ∧
      ∀ i : Fin 17,∀ J∈kept i.val,J∉kept (i.val+1) →
        ∃ C : Jet,RowCaps C (bank rect i).shape ∧ toJet C∉J ∧
          ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0 := by
  have on (J : Ideal Ambient) (mem : J∈init.parents) : Active J ∧ dual J ∧ toJet G∈J :=
    let h := init.parent_geom J mem
    ⟨h.1,h.2.1,h.2.2.2.1⟩
  choose S sub pass bound cut using fun i =>
    ExceptionalStage.filter irr (avoid i) capsG (caps i) (prime_shape_fit rect)
      (Rescue6966Source.shape_guards rect i).2.1 init.parents on (reserve rect i) (reserve_small rect i)
  let selected (i : Fin 17) := if i = 0 then init.parents else S i
  have first : selected 0=init.parents := by simp [selected]
  have rzero : reserve rect 0=0 := (Rescue6966Source.data rect).zero
  have contact_zero (J : Ideal Ambient) (mem : J∈init.parents) : Native J (reserve rect 0+1) (Q 0) := by
    intro w hw
    have hz : w.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp hz]
    exact (init.parent_geom J mem).2.2.2.2
  have sel_pass (i : Fin 17) (J : Ideal Ambient) (mem : J∈selected i) :
      Native J (reserve rect i+1) (Q i) := by
    by_cases zi : i = 0
    · subst i; exact contact_zero J (first ▸ mem)
    · exact pass i J (by simpa only [selected,ite_eq_right zi] using mem)
  have sel_bound (i : Fin 17) (c : Fin 4) :
      (reserve rect i+1)*mass (selected i) c≤pairCap (primeShape rect) (bank rect i).shape c := by
    by_cases zi : i = 0
    · subst i
      rw [rzero, Nat.zero_add, first, one_mul]
      exact K1_14_2_2.mass_mono (subset_union_right (s₁:=init.rankExit) (s₂:=init.parents)) c
        |>.trans (init.fits c)
    · simpa only [selected,ite_eq_right zi] using bound i c
  let kept (n : ℕ) := init.parents.filter (fun J=>∀ i : Fin 17,i.val<n → J∈selected i)
  have spec {J n} : J∈kept n ↔ J∈init.parents ∧ ∀ i : Fin 17,i.val<n → J∈selected i := mem_filter
  refine ⟨kept,?_,?_,?_,?_,?_,?_⟩
  · ext J; simp [kept]
  · ext J
    refine ⟨fun h=>(spec.mp h).1,fun h=>spec.mpr ⟨h,?_⟩⟩
    intro i hi
    have zi : i = 0 := Fin.ext (by omega)
    subst i
    exact first.symm ▸ h
  · intro n m h J mem
    exact spec.mpr ⟨(spec.mp mem).1,fun i hi=>(spec.mp mem).2 i (hi.trans_le h)⟩
  · intro i n hi J mem
    exact sel_pass i J ((spec.mp mem).2 i hi)
  · intro i n hi c
    have hsub : kept n⊆selected i := fun _ mem=>(spec.mp mem).2 i hi
    exact (Nat.mul_le_mul_left _ (K1_14_2_2.mass_mono hsub c)).trans (sel_bound i c)
  · intro i J prev lost
    obtain ⟨root,prior⟩ := spec.mp prev
    have fail : J∉selected i := by
      intro pass
      apply lost (spec.mpr ⟨root,?_⟩)
      intro j hj
      by_cases same : j=i
      · exact same ▸ pass
      · apply prior
        have diff : j.val≠i.val := fun h=>same (Fin.ext h)
        omega
    have nz : i ≠ 0 := by
      intro z
      subst i
      exact fail (first.symm ▸ root)
    obtain ⟨C,cap,proper,zero⟩ := cut i J root (by simpa only [selected,ite_eq_right nz] using fail)
    exact ⟨C,cap,proper,fun γ hγ=>zero _ _ (contact i γ hγ)⟩
structure Run {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (G : Jet) where
  rect : Fin 54
  row : Fin 17→Jet
  row_mem : ∀ i,row i∈evaluated Crt (word M) (bank rect i).shape (cutoff M.overhead.toNat rect i)
  avoids : ∀ i,¬G∣row i
  initial : Initial F G (row 0) rect
  kept : ℕ→Finset (Ideal Ambient)
  start : kept 0=initial.parents
  intro_pass : kept 1=initial.parents
  antitone : Antitone kept
  passed : ∀ i : Fin 17,∀ n,i.val<n → ∀ J∈kept n,Native J (reserve rect i+1) (row i)
  cap : ∀ i : Fin 17,∀ n,i.val<n → ∀ c : Fin 4,
    (reserve rect i+1)*mass (kept n) c≤pairCap (primeShape rect) (bank rect i).shape c
  cut : ∀ i : Fin 17,∀ J∈kept i.val,J∉kept (i.val+1) →
    ∃ C : Jet,RowCaps C (bank rect i).shape ∧ toJet C∉J ∧
      ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0
theorem prepare_from_rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (hi : M.overhead.toNat≤2499)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (rect : Fin 54) (irreducible : Irreducible G) (capsG : RowCaps G (primeShape rect))
    (rows : ∀ i,∃ Q∈evaluated Crt (word M) (bank rect i).shape (cutoff M.overhead.toNat rect i),¬G∣Q) :
    ∃ R : Run F Crt G, R.rect=rect := by
  choose Q inside avoid using rows
  have caps (i : Fin 17) : RowCaps (Q i) (bank rect i).shape :=
    evaluated_shape Crt (word M) (inside i)
  have contact (i : Fin 17) (γ : K) (hγ : γ∈Γ) :
      Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve rect i+1) (Q i) :=
    contact_at_mark F Crt noPole residues (inside i) (Rescue6966Source.cutoff_fit hi rect i) γ hγ
  obtain ⟨ini⟩ := initial_cover F irreducible (avoid 0) capsG (caps 0)
    (fun γ hγ=>zero_of_contact (contact 0 γ hγ))
  obtain ⟨kept,start,intro_pass,anti,passed,cap,cut⟩ :=
    history_from_initial irreducible capsG Q ini avoid caps contact
  exact ⟨⟨rect,Q,inside,avoid,ini,kept,start,intro_pass,anti,passed,cap,cut⟩,rfl⟩
theorem Run.parent_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈R.kept n) :
    Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet (R.row 0)∈J :=
  R.initial.parent_geom J (R.start ▸ R.antitone (Nat.zero_le n) mem)
end Lower6960.Rescue6966

end
end Merged_R6960Rescue6966History

-- merged module R6960Rescue6966Cuts
section Merged_R6960Rescue6966Cuts
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.Rescue6966
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt atX seedEmbedding)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom eval_toJet CoordinateRing)
open K1_14_2_2 (RowCaps Active dual mass sectionDegree CutCover weight dot emptyCut joinCuts
  joinCuts_cost sum_dot)
open K1_14_2_2_3 K1_14_2_2_7
open K1_14_3 (Surface Parent)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open Rescue6966Source (bank reserve)
open scoped Classical
open HighCore82258_3 (envelope_caps)
open K1_14_2_2_7 (seed_value_eq)
def terminalShape : Shape := ⟨4000,5585,1200,510000⟩
def terminalCutoff : ℕ := terminalShape.m*179769-1
def TerminalFits (s : Shape) : Prop :=
  0<s.m ∧ s.B≤terminalShape.B ∧ s.J≤terminalShape.J ∧ s.U≤terminalShape.U
def TerminalPass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (J : Ideal Ambient) : Prop :=
  ∀ s, TerminalFits s → ∀ P∈evaluated Crt w s (s.m*179769-1),toJet P∈J

/-- A parent that fails any terminal bank provides a proper row inside
the single envelope used by the geometric cut bill. -/
theorem terminal_failure {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L)
    {J : Ideal Ambient} (failed : ¬ TerminalPass Crt w J) :
    ∃ (s : Shape) (P : Jet), 0<s.m ∧ P∈evaluated Crt w s (s.m*179769-1) ∧
      RowCaps P terminalShape ∧ toJet P∉J := by
  classical
  unfold TerminalPass at failed
  push Not at failed
  obtain ⟨s,⟨sm,sb,sj,su⟩,P,inside,proper⟩ := failed
  refine ⟨s,P,sm,inside,?_,proper⟩
  intro j i nz
  obtain ⟨b,v,u⟩ := evaluated_shape Crt w inside j i nz
  exact ⟨b.trans sb,v.trans sj,u.trans su⟩

def Run.final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    Finset (Ideal Ambient) :=
  (R.kept 17).filter (TerminalPass Crt (word M))
def Run.live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) : Finset (Ideal Ambient) :=
  if n<17 then R.kept (n+1) else R.final
def Run.lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) : Finset (Ideal Ambient) :=
  R.live n \ R.live (n+1)
theorem Run.next_sub {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) : R.live (i+1)⊆R.live i := by
  by_cases hn : i+1<17
  · simp only [Run.live,ite_eq_left hi,ite_eq_left hn]
    exact R.antitone (by omega)
  · have eq : i+1=17 := by omega
    rw [Run.live,Run.live,ite_eq_right hn,ite_eq_left hi,eq]
    exact filter_subset _ _
theorem Run.live_active {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} {J : Ideal Ambient} (hi : i<17) (mem : J∈R.live i) : Active J := by
  rw [Run.live,ite_eq_left hi] at mem
  exact (R.parent_geom mem).1
theorem Run.live_start {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    R.live 0=R.initial.parents := by
  rw [Run.live,ite_eq_left (by decide : 0<17)]
  exact R.intro_pass
def rescueStage (rect : Fin 54) (i : Fin 17) : P1_7.Stage :=
  ⟨reserve rect i,⟨HelperPrefix.timesShape (reserve rect i+1) (primeShape rect),0,0⟩,bank rect i⟩
def cutShape (rect : Fin 54) (i : ℕ) : Shape :=
  if hi : i+1<17 then HighCore82258_3.envelope (rescueStage rect ⟨i+1,hi⟩) else terminalShape
theorem cutShape_fit (rect : Fin 54) (i : ℕ) : (cutShape rect i).J≤(cutShape rect i).B := by
  unfold cutShape
  split
  · exact Nat.le_add_left _ _
  · decide
theorem Run.marked_cutter {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} {J : Ideal Ambient} (hi : i<17) (mem : J∈R.lost i) :
    ∃ C : Jet, RowCaps C (cutShape R.rect i) ∧ toJet C∉J ∧
      ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0 := by
  obtain ⟨prev,lost⟩ := mem_sdiff.mp mem
  rw [Run.live,ite_eq_left hi] at prev
  by_cases hn : i+1<17
  · let j : Fin 17 := ⟨i+1,hn⟩
    rw [Run.live,ite_eq_left hn] at lost
    obtain ⟨C,cap,proper,zero⟩ := R.cut j J prev lost
    refine ⟨C,?_,proper,zero⟩
    rw [cutShape,dite_eq_left hn]
    apply envelope_caps (s:=rescueStage R.rect j)
    · exact Nat.mul_le_mul_left _ (prime_shape_fit R.rect)
    · exact (Rescue6966Source.shape_guards R.rect j).2.1
    · exact Or.inr cap
  · have eq : i+1=17 := by omega
    rw [Run.live,ite_eq_right hn] at lost
    have hf : ¬ TerminalPass Crt (word M) J := fun pass =>
      lost (mem_filter.mpr ⟨eq ▸ prev,pass⟩)
    obtain ⟨s,C,sm,inside,cap,proper⟩ := terminal_failure Crt (word M) hf
    rw [cutShape,dite_eq_right hn]
    refine ⟨C,cap,proper,?_⟩
    intro γ hγ
    apply zero_of_contact (r:=0)
    exact contact_at_mark F Crt noPole residues inside
      (by simpa only [Nat.mul_zero,Nat.add_zero] using Nat.sub_lt (Nat.mul_pos sm (by decide : 0<179769)) (by decide : 0<1)) γ hγ
private theorem mark_on_cut {J : Ideal Ambient} {P : Jet} {z : K} {S : (Polynomial K)}
    (on : OnJet J z S) (zero : jetAt P z S=0) :
    ∃ Q∈cutComponents J P,OnJet Q z S := by
  let e := jetMarkHom z S
  have incl : J ⊔ Ideal.span {toJet P} ≤ RingHom.ker e :=
    sup_le on ((Ideal.span_singleton_le_iff_mem _).mpr
      (RingHom.mem_ker.mpr ((eval_toJet _ _ _).trans zero)))
  have : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q,minimal,mark⟩ := Ideal.exists_minimalPrimes_le incl
  exact ⟨Q,Ideal.mem_minimalPrimesFinset.mpr minimal,mark⟩
theorem proper_cut {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (s : Shape) {J : Ideal Ambient} {P : Jet} (sl : s.J≤s.B) (act : Active J)
    (cap : RowCaps P s) (proper : toJet P∉J) (zero : ∀ γ∈Γ,jetAt P (M.label γ) (F.scalar γ)=0) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight s fee) (sectionDegree J)) ∧
      ∀ γ∈Γ,OnMark F J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
  let marked (Q : Ideal Ambient) := Γ.filter (OnMark F Q)
  let direct := (constantComponents J P).biUnion marked
  have card : direct.card≤(constantComponents J P).card := by
    have single (Q : Ideal Ambient) (mem : Q∈constantComponents J P) : (marked Q).card≤1 := by
      obtain ⟨comp,seed⟩ := mem_filter.mp mem
      let _ : Q.IsPrime := (cutComponent_curve act proper comp).1
      apply card_le_one.mpr
      intro γ hγ δ hδ
      apply label_injective M
      apply seedEmbedding.injective
      apply (algebraMap K1_14.FX (CoordinateRing Q)).injective
      exact (seed_value_eq seed (mem_filter.mp hγ).2).trans (seed_value_eq seed (mem_filter.mp hδ).2).symm
    calc
      _ ≤ ∑ Q∈constantComponents J P,(marked Q).card := card_biUnion_le
      _ ≤ ∑ _∈constantComponents J P,1 := sum_le_sum single
      _ = _ := by simp
  let C : CutCover := ⟨direct,movingComponents J P,by
    intro Q hQ
    obtain ⟨comp,moving⟩ := mem_filter.mp hQ
    obtain ⟨prime,dim⟩ := cutComponent_curve act proper comp
    exact ⟨prime,dim,K1_14_2_2_7_1.proof Q prime dim moving⟩⟩
  refine ⟨C,?_,?_⟩
  · intro fee
    fin_cases fee
    · exact P0_10R.Bridge.cut_seed_mass s J P sl act cap proper
    · exact P0_10R.Bridge.cut_ordinate_mass s J P sl act cap proper
    · exact card.trans (P0_10R.Bridge.cut_constant_count s J P sl act cap proper)
  · intro γ hγ on
    obtain ⟨Q,comp,mark⟩ := mark_on_cut on (zero γ hγ)
    by_cases c : ConstantSeed Q
    · exact Or.inl (mem_biUnion.mpr ⟨Q,mem_filter.mpr ⟨comp,c⟩,mem_filter.mpr ⟨hγ,mark⟩⟩)
    · exact Or.inr ⟨Q,mem_filter.mpr ⟨comp,c⟩,mark⟩
theorem Run.cutCover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} (hi : i<17) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape R.rect i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
  have oneCut (J : Ideal Ambient) (mem : J∈R.lost i) :
      ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape R.rect i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ,OnMark F J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
    obtain ⟨P,cap,proper,zero⟩ := R.marked_cutter noPole residues hi mem
    exact proper_cut F _ (cutShape_fit _ _) (R.live_active hi (mem_sdiff.mp mem).1) cap proper zero
  let C (J : Ideal Ambient) : CutCover :=
    if mem : J∈R.lost i then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈R.lost i) :
      (∀ fee,(C J).cost fee≤dot (weight (cutShape R.rect i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ,OnMark F J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves,OnMark F Q γ := by
    simpa only [C,dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts (R.lost i) C,?_,?_⟩
  · intro fee
    exact (joinCuts_cost _ _ _).trans ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J,mem,on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q,hQ,hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J,mem,point⟩)
    · exact Or.inr ⟨Q,mem_biUnion.mpr ⟨J,mem,hQ⟩,hmark⟩
theorem Run.retained_or_lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {J : Ideal Ambient} (mem : J∈R.initial.parents) :
    J∈R.final ∨ ∃ i<17,J∈R.lost i := by
  by_cases h : ∃ i<17,J∈R.lost i
  · exact Or.inr h
  · have live : ∀ n≤17,J∈R.live n := by
      intro n hn
      induction n with
      | zero => exact R.live_start.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n,by omega,mem_sdiff.mpr ⟨ih (by omega),absent⟩⟩
    exact Or.inl (by simpa [Run.live] using live 17 le_rfl)
def OnSurface {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (q : Surface) (γ : K) : Prop :=
  ∀ P∈q.asIdeal,jetAt P (M.label γ) (F.scalar γ)=0
def SurfacePass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (q : Surface) : Prop :=
  ∀ s, TerminalFits s → ∀ P∈evaluated Crt w s (s.m*179769-1),P∈q.asIdeal

theorem SurfacePass.original {h : ℕ} {D : PoleData h} {Crt : CRTLift D} {w : I→L}
    {q : Surface} (pass : SurfacePass Crt w q) :
    ∀ P∈evaluated Crt w terminalShape terminalCutoff,P∈q.asIdeal :=
  pass terminalShape ⟨by decide,le_rfl,le_rfl,le_rfl⟩
theorem Run.terminal_surfaces_with_origins {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S,∃ J∈R.final,q.asIdeal=J.comap K1_14_2.toJet) ∧
      ∀ γ∈Γ,(∃ J∈R.final,OnMark F J γ) → ∃ q∈S,OnSurface F q γ := by
  let getGeom (J : R.final) := R.parent_geom (mem_filter.mp J.property).1
  let surface (J : R.final) := surfaceOf J.val (getGeom J).1.prime
  let S := R.final.attach.image surface
  refine ⟨S,?_,?_,?_⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩ := mem_image.mp hq
    have hJ := getGeom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1,(mem_filter.mp J.property).2⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩:=mem_image.mp hq
    exact ⟨J.val,J.property,rfl⟩
  · rintro γ _ ⟨J,hJ,on⟩
    let q : R.final := ⟨J,hJ⟩
    refine ⟨surface q,mem_image.mpr ⟨q,mem_attach _ _,rfl⟩,?_⟩
    intro P mem
    rw [←eval_toJet]
    exact RingHom.mem_ker.mp (on mem)

theorem Run.terminal_surfaces {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,(∃ J∈R.final,OnMark F J γ) → ∃ q∈S,OnSurface F q γ := by
  obtain ⟨S,geom,_,marks⟩:=R.terminal_surfaces_with_origins
  exact ⟨S,geom,marks⟩
end Lower6960.Rescue6966

end
end Merged_R6960Rescue6966Cuts

-- merged module R6960Rescue6966Bills
section Merged_R6960Rescue6966Bills
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
namespace Lower6960.Rescue6966
open Finset Polynomial
open K1 (I K)
open K1_14 (Shape Jet atX jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass weight dot CutCover emptyCut mass_mono)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (Surface Parent)
open Rescue6966Source (bank reserve)
open P1_7_4 (Mass massQ dotQ massQ_mono weightedBill bill_bound)
open scoped Classical
def initialMass (rect : Fin 54) : Mass := fun k => initialCap rect k
def history (rect : Fin 54) : ℕ → Mass
  | 0 => initialMass rect
  | n+1 => fun k =>
    if hn : n+1<17 then
      let i : Fin 17 := ⟨n+1,hn⟩
      min (history rect n k)
        ((pairCap (primeShape rect) (bank rect i).shape k : ℚ)/(reserve rect i+1))
    else history rect n k
theorem Run.initial_cap {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) (k : Fin 4) : massQ (R.kept n) k ≤ initialMass R.rect k := by
  have sub : R.kept n ⊆ R.initial.parents := by
    simpa only [R.start] using (R.antitone (Nat.zero_le n) : R.kept n⊆R.kept 0)
  exact (Nat.cast_le (α:=ℚ)).mpr ((mass_mono (sub.trans subset_union_right) k).trans (R.initial.fits k))
theorem Run.history_cap {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i n : ℕ} (hi : i<17) (prior : i<n) (k : Fin 4) :
    massQ (R.kept n) k ≤ history R.rect i k := by
  induction i with
  | zero => exact R.initial_cap n k
  | succ i ih =>
    simp only [history,dite_eq_left hi]
    apply le_min (ih (by omega) (by omega))
    let j : Fin 17 := ⟨i+1,hi⟩
    change massQ (R.kept n) k ≤ (pairCap (primeShape R.rect) (bank R.rect j).shape k : ℚ) / (reserve R.rect j+1)
    have pos : (0 : ℚ)<reserve R.rect j+1 := by positivity
    apply (le_div_iff₀ pos).mpr
    have bound := R.cap j n prior k
    rw [Nat.mul_comm] at bound
    unfold massQ
    exact_mod_cast bound
theorem Run.live_history {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (R.live i) k ≤ history R.rect i k := by
  rw [Run.live,ite_eq_left hi]
  exact R.history_cap hi (Nat.lt_succ_self _) k
theorem Run.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (R.live i) k ≤ initialMass R.rect k := by
  rw [Run.live,ite_eq_left hi]
  exact R.initial_cap _ k
end Lower6960.Rescue6966
end
end Merged_R6960Rescue6966Bills

end Merged_High6966RescueGeometry
