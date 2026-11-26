import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic
import ProximityPrize.SubmissionLower.R6960HelperPrefix

set_option Elab.async false

-- Source: Research6969.TransitionBankChecks08
section Z6969Source0596
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem pole144 : momentEstimate 665 149 = 5571898574 := by
  refine moment_from_blocks [(128,203833760),(128,1047368465),(128,1605652800),(128,1535611200),(128,916630470),(128,257053969),(46,5747910)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank144 (u : ℕ) : P3_7_1.BankOK (bank144 u) :=
  P3_7_1.checked (bank144 u) (m:=480) (B:=665) (J:=149) (N:=3425114521600) (M:=5571898574) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole144
theorem free144_0 : TransitionSources.Free 2293 30 (bank144 4704) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 30 (bank144 4704)) 2293 = 13109567899755 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 30 (bank144 4704)) 2294 = 263377039605165 := by decide +kernel
  refine ⟨rank144 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free144_1 : TransitionSources.Free 2390 30 (bank144 3940) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 30 (bank144 3940)) 2390 = 1692798439955 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 30 (bank144 3940)) 2391 = 170159459656137 := by decide +kernel
  refine ⟨rank144 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole145 : momentEstimate 670 149 = 5707728199 := by
  refine moment_from_blocks [(128,205622560),(128,1058704165),(128,1629268800),(128,1571515200),(128,955538956),(128,279284498),(51,7794020)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank145 (u : ℕ) : P3_7_1.BankOK (bank145 u) :=
  P3_7_1.checked (bank145 u) (m:=483) (B:=670) (J:=149) (N:=3473185177600) (M:=5707728199) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole145
theorem free145_0 : TransitionSources.Free 2293 41 (bank145 7920) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank145 7920)) 2293 = 11620958396606 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank145 7920)) 2294 = 731601782957548 := by decide +kernel
  refine ⟨rank145 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free145_1 : TransitionSources.Free 2390 41 (bank145 5985) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank145 5985)) 2390 = 2022551954680 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank145 5985)) 2391 = 396530790940752 := by decide +kernel
  refine ⟨rank145 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole146 : momentEstimate 701 157 = 6873381450 := by
  refine moment_from_blocks [(128,216713120),(128,1149358751),(128,1839529536),(128,1869299264),(128,1273103352),(128,483286300),(90,42091127)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank146 (u : ℕ) : P3_7_1.BankOK (bank146 u) :=
  P3_7_1.checked (bank146 u) (m:=506) (B:=701) (J:=157) (N:=4009024552960) (M:=6873381450) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole146
theorem free146_0 : TransitionSources.Free 2293 40 (bank146 6858) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 40 (bank146 6858)) 2293 = 12984797249450 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 40 (bank146 6858)) 2294 = 632722538653290 := by decide +kernel
  refine ⟨rank146 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole147 : momentEstimate 740 166 = 8540674317 := by
  refine moment_from_blocks [(128,230665760),(128,1260185825),(128,2105610816),(128,2256097856),(128,1717901941),(128,817302159),(128,152817968),(10,91992)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank147 (u : ℕ) : P3_7_1.BankOK (bank147 u) :=
  P3_7_1.checked (bank147 u) (m:=534) (B:=740) (J:=166) (N:=4716471779328) (M:=8540674317) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole147
theorem free147_0 : TransitionSources.Free 2293 40 (bank147 6388) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 40 (bank147 6388)) 2293 = 20927474114742 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 40 (bank147 6388)) 2294 = 651416876899641 := by decide +kernel
  refine ⟨rank147 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free147_1 : TransitionSources.Free 2390 40 (bank147 5174) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 40 (bank147 5174)) 2390 = 1917425557800 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 40 (bank147 5174)) 2391 = 398788467976350 := by decide +kernel
  refine ⟨rank147 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free147_2 : TransitionSources.Free 2390 40 (bank147 6388) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 40 (bank147 6388)) 2390 = 61178399544249945 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 40 (bank147 6388)) 2391 = 61808888947034844 := by decide +kernel
  refine ⟨rank147 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole148 : momentEstimate 741 166 = 8577852024 := by
  refine moment_from_blocks [(128,231023520),(128,1262535636),(128,2110687616),(128,2263910784),(128,1727926398),(128,825423035),(128,156226464),(11,118571)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank148 (u : ℕ) : P3_7_1.BankOK (bank148 u) :=
  P3_7_1.checked (bank148 u) (m:=534) (B:=741) (J:=166) (N:=4716471779328) (M:=8577852024) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole148
theorem free148_0 : TransitionSources.Free 2293 41 (bank148 6656) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank148 6656)) 2293 = 19990525227309 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank148 6656)) 2294 = 706321995461481 := by decide +kernel
  refine ⟨rank148 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free148_1 : TransitionSources.Free 2390 41 (bank148 5351) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank148 5351)) 2390 = 33464663926068 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank148 5351)) 2391 = 459102118642980 := by decide +kernel
  refine ⟨rank148 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole149 : momentEstimate 751 169 = 9080555850 := by
  refine moment_from_blocks [(128,234601120),(128,1292202030),(128,2186200000),(128,2374206400),(128,1857131143),(128,931152299),(128,204042592),(24,1020266)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank149 (u : ℕ) : P3_7_1.BankOK (bank149 u) :=
  P3_7_1.checked (bank149 u) (m:=542) (B:=751) (J:=169) (N:=4942312243200) (M:=9080555850) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole149
theorem free149_0 : TransitionSources.Free 2293 40 (bank149 6281) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 40 (bank149 6281)) 2293 = 12698589290085 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 40 (bank149 6281)) 2294 = 650934195607125 := by decide +kernel
  refine ⟨rank149 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free149_1 : TransitionSources.Free 2390 40 (bank149 5119) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 40 (bank149 5119)) 2390 = 33346971532800 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 40 (bank149 5119)) 2391 = 440125533273600 := by decide +kernel
  refine ⟨rank149 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole150 : momentEstimate 755 169 = 9237048500 := by
  refine moment_from_blocks [(128,236032160),(128,1301648270),(128,2206741440),(128,2405888960),(128,1898428388),(128,966101400),(128,220622592),(28,1585290)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank150 (u : ℕ) : P3_7_1.BankOK (bank150 u) :=
  P3_7_1.checked (bank150 u) (m:=544) (B:=755) (J:=169) (N:=4983222435840) (M:=9237048500) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole150
theorem free150_0 : TransitionSources.Free 2293 41 (bank150 6517) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank150 6517)) 2293 = 2240395818445 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank150 6517)) 2294 = 696612559156595 := by decide +kernel
  refine ⟨rank150 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free150_1 : TransitionSources.Free 2390 41 (bank150 5281) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank150 5281)) 2390 = 16817502110285 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank150 5281)) 2391 = 454328022069735 := by decide +kernel
  refine ⟨rank150 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole151 : momentEstimate 765 172 = 9768274947 := by
  refine moment_from_blocks [(128,239609760),(128,1331163635),(128,2283146048),(128,2518403904),(128,2032267314),(128,1080170494),(128,278743312),(41,4770480)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank151 (u : ℕ) : P3_7_1.BankOK (bank151 u) :=
  P3_7_1.checked (bank151 u) (m:=552) (B:=765) (J:=172) (N:=5217441021952) (M:=9768274947) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole151
theorem free151_0 : TransitionSources.Free 2293 40 (bank151 6174) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 40 (bank151 6174)) 2293 = 30651141738750 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 40 (bank151 6174)) 2294 = 680927173150900 := by decide +kernel
  refine ⟨rank151 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free151_1 : TransitionSources.Free 2390 40 (bank151 5065) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 40 (bank151 5065)) 2390 = 1671719762727 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 40 (bank151 5065)) 2391 = 421592664365802 := by decide +kernel
  refine ⟨rank151 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole152 : momentEstimate 769 173 = 9978111377 := by
  refine moment_from_blocks [(128,241040800),(128,1342540827),(128,2312228928),(128,2561675328),(128,2084773232),(128,1125910256),(128,303266000),(46,6676006)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank152 (u : ℕ) : P3_7_1.BankOK (bank152 u) :=
  P3_7_1.checked (bank152 u) (m:=555) (B:=769) (J:=173) (N:=5304235851776) (M:=9978111377) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole152
theorem free152_0 : TransitionSources.Free 2293 41 (bank152 6378) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank152 6378)) 2293 = 4585712223892 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank152 6378)) 2294 = 709563708870206 := by decide +kernel
  refine ⟨rank152 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free152_1 : TransitionSources.Free 2390 41 (bank152 5208) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank152 5208)) 2390 = 41923435226465 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank152 5208)) 2391 = 492964593845439 := by decide +kernel
  refine ⟨rank152 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole153 : momentEstimate 769 174 = 10022613078 := by
  refine moment_from_blocks [(128,241040800),(128,1344381850),(128,2320483200),(128,2572796800),(128,2094799146),(128,1134055354),(128,307953472),(47,7102456)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank153 (u : ℕ) : P3_7_1.BankOK (bank153 u) :=
  P3_7_1.checked (bank153 u) (m:=555) (B:=769) (J:=174) (N:=5327303475200) (M:=10022613078) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole153
theorem free153_0 : TransitionSources.Free 2293 41 (bank153 6368) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank153 6368)) 2293 = 454787469873 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank153 6368)) 2294 = 707167361905059 := by decide +kernel
  refine ⟨rank153 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free153_1 : TransitionSources.Free 2390 41 (bank153 5200) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank153 5200)) 2390 = 27868448788635 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank153 5200)) 2391 = 480043473013629 := by decide +kernel
  refine ⟨rank153 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole154 : momentEstimate 772 170 = 9968090926 := by
  refine moment_from_blocks [(128,242114080),(128,1343834882),(128,2302584768),(128,2551932864),(128,2086306826),(128,1130030069),(128,304584659),(46,6702778)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank154 (u : ℕ) : P3_7_1.BankOK (bank154 u) :=
  P3_7_1.checked (bank154 u) (m:=556) (B:=772) (J:=170) (N:=5255817068544) (M:=9968090926) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole154
private theorem pole155 : momentEstimate 781 169 = 10299257375 := by
  refine moment_from_blocks [(128,245333920),(128,1363048830),(128,2340260800),(128,2611825600),(128,2171271272),(128,1209061940),(128,347686136),(54,10768877)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank155 (u : ℕ) : P3_7_1.BankOK (bank155 u) :=
  P3_7_1.checked (bank155 u) (m:=560) (B:=781) (J:=169) (N:=5316921262080) (M:=10299257375) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole155
private theorem pole156 : momentEstimate 781 172 = 10440670587 := by
  refine moment_from_blocks [(128,245333920),(128,1369124051),(128,2366230336),(128,2646839104),(128,2203058852),(128,1234517412),(128,362978262),(57,12588650)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank156 (u : ℕ) : P3_7_1.BankOK (bank156 u) :=
  P3_7_1.checked (bank156 u) (m:=560) (B:=781) (J:=172) (N:=5388141854720) (M:=10440670587) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole156
private theorem pole157 : momentEstimate 781 176 = 10627925923 := by
  refine moment_from_blocks [(128,245333920),(128,1376559796),(128,2400029376),(128,2692926144),(128,2245172681),(128,1268727256),(128,383862374),(61,15314376)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank157 (u : ℕ) : P3_7_1.BankOK (bank157 u) :=
  P3_7_1.checked (bank157 u) (m:=560) (B:=781) (J:=176) (N:=5482316038144) (M:=10627925923) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole157
private theorem pole158 : momentEstimate 780 179 = 10723114255 := by
  refine moment_from_blocks [(128,244976160),(128,1379264235),(128,2419436160),(128,2718771840),(128,2265519266),(128,1284401035),(128,393956295),(63,16789264)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank158 (u : ℕ) : P3_7_1.BankOK (bank158 u) :=
  P3_7_1.checked (bank158 u) (m:=563) (B:=780) (J:=179) (N:=5619261112320) (M:=10723114255) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole158
theorem free158_0 : TransitionSources.Free 2293 65 (bank158 51722) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 65 (bank158 51722)) 2293 = 42082435372950 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 65 (bank158 51722)) 2294 = 49348216454318460 := by decide +kernel
  refine ⟨rank158 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free158_1 : TransitionSources.Free 2390 65 (bank158 18445) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 65 (bank158 18445)) 2390 = 35789328924820 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 65 (bank158 18445)) 2391 = 6052514400841800 := by decide +kernel
  refine ⟨rank158 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole159 : momentEstimate 781 175 = 10581248240 := by
  refine moment_from_blocks [(128,245333920),(128,1374770236),(128,2391668224),(128,2681468416),(128,2234672603),(128,1260146337),(128,378588744),(60,14599760)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank159 (u : ℕ) : P3_7_1.BankOK (bank159 u) :=
  P3_7_1.checked (bank159 u) (m:=563) (B:=781) (J:=175) (N:=5524531707904) (M:=10581248240) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole159
theorem free159_0 : TransitionSources.Free 2293 40 (bank159 6076) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 40 (bank159 6076)) 2293 = 254540687224 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 40 (bank159 6076)) 2294 = 667132241646872 := by decide +kernel
  refine ⟨rank159 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free159_1 : TransitionSources.Free 2390 40 (bank159 5020) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 40 (bank159 5020)) 2390 = 38459723044760 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 40 (bank159 5020)) 2391 = 475262383325496 := by decide +kernel
  refine ⟨rank159 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole160 : momentEstimate 786 178 = 10943454095 := by
  refine moment_from_blocks [(128,247122720),(128,1391964886),(128,2443095104),(128,2756897856),(128,2321249629),(128,1337291253),(128,424725022),(68,21107625)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank160 (u : ℕ) : P3_7_1.BankOK (bank160 u) :=
  P3_7_1.checked (bank160 u) (m:=568) (B:=786) (J:=178) (N:=5707573493760) (M:=10943454095) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole160
theorem free160_0 : TransitionSources.Free 2293 65 (bank160 43523) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 65 (bank160 43523)) 2293 = 24714382207320 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 65 (bank160 43523)) 2294 = 35236525912880760 := by decide +kernel
  refine ⟨rank160 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free160_1 : TransitionSources.Free 2390 65 (bank160 17407) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 65 (bank160 17407)) 2390 = 24271792068608 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 65 (bank160 17407)) 2391 = 5428707160332288 := by decide +kernel
  refine ⟨rank160 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole161 : momentEstimate 787 177 = 10940615189 := by
  refine moment_from_blocks [(128,247480480),(128,1392638932),(128,2440046784),(128,2753554624),(128,2321576771),(128,1338865383),(128,425316625),(68,21135590)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank161 (u : ℕ) : P3_7_1.BankOK (bank161 u) :=
  P3_7_1.checked (bank161 u) (m:=568) (B:=787) (J:=177) (N:=5683410108416) (M:=10940615189) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole161
theorem free161_0 : TransitionSources.Free 2293 41 (bank161 6246) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank161 6246)) 2293 = 16065719863646 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank161 6246)) 2294 = 739228457340448 := by decide +kernel
  refine ⟨rank161 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free161_1 : TransitionSources.Free 2390 41 (bank161 5142) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank161 5142)) 2390 = 32617602362200 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank161 5142)) 2391 = 502896560095722 := by decide +kernel
  refine ⟨rank161 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
end Research6969.TransitionBanks
end Z6969Source0596

-- Source: Research6969.PrefixHelper
section Z6969Source0597
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
namespace Lower6960.Prefix6969Helper
open Research6969.FarProfileArithmetic (value value_eq)
open Research6966.FarSourceArithmetic (Request)
open Research6969.TransitionBanks (bank154 rank154)
open HelperSource
open Finset Polynomial
open K1_14 (FX L Jet)
open K1_14_1 (PoleData CRTLift evaluated evaluated_mono evaluated_shape)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree jetDegree_le)
open P1_7 (Bank debit)
abbrev bankAt (u : ℕ) : Bank := bank154 u
abbrev helperBank := bankAt 10007

theorem checked (u : ℕ) : P3_7_1.BankOK (bankAt u) := rank154 u

theorem helper_bank_checked : P3_7_1.BankOK helperBank := checked 10007

inductive HelperTest where
  | twoSlopes | seedBoundary | mixedBoundary | jetBoundary
def HelperTest.slope : HelperTest → ℕ
  | .twoSlopes => 2
  | _ => 1
def HelperTest.excess : HelperTest → ℕ
  | .mixedBoundary => 1
  | .jetBoundary => 7
  | _ => 0
def HelperTest.seed : HelperTest → ℕ
  | .seedBoundary => 62
  | .mixedBoundary => 57
  | _ => 1
abbrev HelperTest.cap (_ : HelperTest) : ℕ := 10007

private def helperRequest (test : HelperTest) : Request :=
  ⟨bankAt test.cap, 10, test.slope, test.excess, test.seed⟩

private abbrev compressedSurplus (h : ℕ) (test : HelperTest) : ℤ :=
  value (helperRequest test) h

private theorem compressedSurplus_eq (h : ℕ) (test : HelperTest) (hi : h ≤ 2294) :
    compressedSurplus h test = surplus (bankAt test.cap) 179740 h 10 test.slope test.excess test.seed :=
  value_eq (helperRequest test) h (by cases test <;> decide)
    (by change 170 < 131071 - h; omega)

private theorem twoSlopes_first : compressedSurplus 2293 .twoSlopes = 18657742651906 := by decide +kernel
private theorem twoSlopes_next : compressedSurplus 2294 .twoSlopes = 1741377828513512 := by decide +kernel
private theorem seedBoundary_first : compressedSurplus 2293 .seedBoundary = 16900402650256202 := by decide +kernel
private theorem seedBoundary_next : compressedSurplus 2294 .seedBoundary = 18630221563424000 := by decide +kernel
private theorem mixedBoundary_first : compressedSurplus 2293 .mixedBoundary = 14816851828953426 := by decide +kernel
private theorem mixedBoundary_next : compressedSurplus 2294 .mixedBoundary = 16546025553753672 := by decide +kernel
private theorem jetBoundary_first : compressedSurplus 2293 .jetBoundary = 88326333131993666 := by decide +kernel
private theorem jetBoundary_next : compressedSurplus 2294 .jetBoundary = 90087565069311592 := by decide +kernel

theorem helper_surplus (test : HelperTest) {h : ℕ} (lo : 2293≤h) (hi : h≤33735) :
    debit h (bankAt test.cap) < gain (bankAt test.cap).shape 179740 h 10 test.slope test.excess test.seed := by
  apply surplus_positive _ _ 2293 _ _ _ _ _ lo (by omega)
  · rw [← compressedSurplus_eq _ _ (by decide)]
    cases test
    · rw [twoSlopes_first]; decide
    · rw [seedBoundary_first]; decide
    · rw [mixedBoundary_first]; decide
    · rw [jetBoundary_first]; decide
  · change surplus (bankAt test.cap) 179740 2293 10 test.slope test.excess test.seed ≤
      surplus (bankAt test.cap) 179740 2294 10 test.slope test.excess test.seed
    rw [← compressedSurplus_eq 2293 test (by decide), ← compressedSurplus_eq 2294 test (by decide)]
    cases test
    · rw [twoSlopes_first, twoSlopes_next]; decide
    · rw [seedBoundary_first, seedBoundary_next]; decide
    · rw [mixedBoundary_first, mixedBoundary_next]; decide
    · rw [jetBoundary_first, jetBoundary_next]; decide
theorem helper_width {h : ℕ} (lo : 2293≤h) (hi : h≤33735) :
    WidthGuard helperBank 179740 h 10 :=
  width_at_height _ _ 2293 _ _ lo (by omega) (by decide) (by unfold WidthGuard; decide +kernel)
def helperCutoff (h : ℕ) : ℕ := cutoffCount helperBank.shape 179740 h 10-1
theorem helper_avoids {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2293≤h) (hi : h≤33735) (test : HelperTest) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : test.slope≤G.natDegree) (seed : test.seed≤seedDegree G)
    (excess : G.natDegree+test.excess≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), ¬ G∣Q := by
  obtain ⟨Q,inside,avoids⟩ := crt_avoiding_row Crt word (bankAt test.cap) 179740 10 test.slope test.excess test.seed
    (by omega) (by omega) (by cases test <;> decide)
    (checked test.cap).nodes (checked test.cap).moment.1 (checked test.cap).moment.2
    (by cases test <;> decide) (helper_width lo hi) (helper_surplus test lo hi) irr seeded slope seed excess
  exact ⟨Q, K1_14_1.evaluated_mono Crt word (s:=(bankAt test.cap).shape) (s':=helperBank.shape)
    rfl rfl rfl (by cases test <;> decide) le_rfl inside, avoids⟩
theorem helper_nonzero {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2293≤h) (hi : h≤33735) :
    ∃ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), P≠0 := by
  have sup := crt_supply Crt word helperBank 179740 10 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  exact nonzero_of_supply Crt word helperBank.shape _ (lt_of_le_of_lt (Nat.zero_le _) sup)
private theorem shape_lower_bound {G : Jet} (nz : G≠0) : G.natDegree≤jetDegree G := by
  have coeff : ((G.coeff G.natDegree).coeff G.leadingCoeff.natDegree) ≠ 0 := by
    rw [coeff_natDegree,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nz)
  have cap := (jetDegree_le G _).1 le_rfl _ _ coeff
  omega
theorem helper_common_caps {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2293≤h) (hi : h≤33735) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : 0<G.natDegree)
    (common : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q) :
    G.natDegree=1 ∧ 1≤jetDegree G ∧ jetDegree G≤7 ∧
      1≤seedDegree G ∧ seedDegree G≤61 ∧ (2≤jetDegree G → seedDegree G≤56) := by
  have sb : 1≤seedDegree G := by
    obtain ⟨j,i,hs⟩ := seeded
    have ge := (K1_14_2_2_2_1.seedDegree_le G _).1 le_rfl j i
    omega
  have jb := shape_lower_bound irr.ne_zero
  have not_test (test : HelperTest) (a : test.slope≤G.natDegree)
      (b : test.seed≤seedDegree G) (c : G.natDegree+test.excess≤jetDegree G) : False := by
    obtain ⟨Q,hQ,avoid⟩ := helper_avoids Crt word lo hi test irr seeded a b c
    exact avoid (common Q hQ)
  have linear : G.natDegree=1 := by
    by_contra! bad
    exact not_test .twoSlopes (by change 2≤G.natDegree; omega) sb (by simpa [HelperTest.excess] using jb)
  refine ⟨linear, by omega, ?_, sb, ?_, ?_⟩
  · by_contra! bad
    exact not_test .jetBoundary (by change 1≤G.natDegree; omega) sb
      (by change G.natDegree+7≤jetDegree G; omega)
  · by_contra! bad
    exact not_test .seedBoundary (by change 1≤G.natDegree; omega) (by change 62≤seedDegree G; omega)
      (by simpa [HelperTest.excess] using jb)
  · intro j
    by_contra! bad
    exact not_test .mixedBoundary (by change 1≤G.natDegree; omega) (by change 57≤seedDegree G; omega)
      (by change G.natDegree+1≤jetDegree G; omega)
theorem helper_not_two {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2293≤h) (hi : h≤33735) {G H : Jet} (g : Irreducible G) (i : Irreducible H)
    (cop : IsRelPrime G H) (gs : 0<G.natDegree) (hs : 0<H.natDegree)
    (gu : UsesSeed G) (hu : UsesSeed H)
    (allG : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q)
    (allH : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), H∣Q) : False := by
  have supply := crt_supply Crt word helperBank 179740 10 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  obtain ⟨P,hP,np⟩ := helper_nonzero Crt word lo hi
  have hpc (j i : ℕ) : ((P.coeff j).coeff i).totalDegree ≤ helperBank.shape.U := by
    by_cases zero : ((P.coeff j).coeff i)=0
    · simp [zero]
    · exact (evaluated_shape Crt word hP j i zero).2.2
  exact HelperPrefix.not_two_common helperBank.shape h (cutoffCount helperBank.shape 179740 h 10)
    (by omega) (evaluated Crt word helperBank.shape) G H P g i cop gs hs gu hu np hP
    (by decide) hpc (fun _ _ _ hR => evaluated_shape Crt word hR)
    (fun W _ R hR hnR => P0_10_1.leading_bound (by omega) (by omega) Crt word helperBank.shape W R hR hnR)
    (fun _ _ _ hR j a hshift => evaluated_mono Crt word rfl rfl rfl le_rfl hshift
      (P0_10_1.evaluated_shift Crt word hR j a))
    supply allG allH
end Lower6960.Prefix6969Helper
end Z6969Source0597

-- Source: Research6969.TransitionBankChecks09
section Z6969Source0598
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem pole162 : momentEstimate 789 179 = 11126431075 := by
  refine moment_from_blocks [(128,248196000),(128,1400821215),(128,2467336320),(128,2793214080),(128,2365212827),(128,1377478988),(128,449167563),(72,25004082)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank162 (u : ℕ) : P3_7_1.BankOK (bank162 u) :=
  P3_7_1.checked (bank162 u) (m:=570) (B:=789) (J:=179) (N:=5776980049920) (M:=11126431075) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole162
theorem free162_0 : TransitionSources.Free 2293 65 (bank162 40650) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 65 (bank162 40650)) 2293 = 36638064582730 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 65 (bank162 40650)) 2294 = 31150366655379920 := by decide +kernel
  refine ⟨rank162 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free162_1 : TransitionSources.Free 2390 65 (bank162 16965) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 65 (bank162 16965)) 2390 = 6929160152510 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 65 (bank162 16965)) 2391 = 5206764651226350 := by decide +kernel
  refine ⟨rank162 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole163 : momentEstimate 792 174 = 11019070253 := by
  refine moment_from_blocks [(128,249269280),(128,1399108395),(128,2440782400),(128,2759041600),(128,2343740636),(128,1364417924),(128,439572581),(70,23137437)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank163 (u : ℕ) : P3_7_1.BankOK (bank163 u) :=
  P3_7_1.checked (bank163 u) (m:=570) (B:=792) (J:=174) (N:=5654852403200) (M:=11019070253) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole163
private theorem pole164 : momentEstimate 804 181 = 11923349975 := by
  refine moment_from_blocks [(128,253562400),(128,1440063989),(128,2564184896),(128,2941393728),(128,2555443784),(128,1558608390),(128,562977081),(89,47115707)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank164 (u : ℕ) : P3_7_1.BankOK (bank164 u) :=
  P3_7_1.checked (bank164 u) (m:=580) (B:=804) (J:=181) (N:=6056834760704) (M:=11923349975) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole164
theorem free164_0 : TransitionSources.Free 2293 41 (bank164 6138) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank164 6138)) 2293 = 37386695827530 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank164 6138)) 2294 = 781416155546740 := by decide +kernel
  refine ⟨rank164 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free164_1 : TransitionSources.Free 2390 41 (bank164 5088) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank164 5088)) 2390 = 21869550532900 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank164 5088)) 2391 = 512414826958160 := by decide +kernel
  refine ⟨rank164 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole165 : momentEstimate 804 182 = 11974188965 := by
  refine moment_from_blocks [(128,253562400),(128,1441654989),(128,2572599360),(128,2953379904),(128,2566844226),(128,1568048663),(128,569434321),(90,48665102)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank165 (u : ℕ) : P3_7_1.BankOK (bank165 u) :=
  P3_7_1.checked (bank165 u) (m:=580) (B:=804) (J:=182) (N:=6082014740480) (M:=11974188965) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole165
theorem free165_0 : TransitionSources.Free 2293 41 (bank165 6130) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank165 6130)) 2293 = 3807925388866 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank165 6130)) 2294 = 749898963498326 := by decide +kernel
  refine ⟨rank165 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free165_1 : TransitionSources.Free 2390 41 (bank165 5082) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank165 5082)) 2390 = 25806784536026 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank165 5082)) 2391 = 517844881910226 := by decide +kernel
  refine ⟨rank165 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole166 : momentEstimate 818 185 = 12818954657 := by
  refine moment_from_blocks [(128,258571040),(128,1479933698),(128,2673465792),(128,3107723712),(128,2761856574),(128,1758632067),(128,696983158),(107,81788616)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank166 (u : ℕ) : P3_7_1.BankOK (bank166 u) :=
  P3_7_1.checked (bank166 u) (m:=590) (B:=818) (J:=185) (N:=6397599416320) (M:=12818954657) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole166
theorem free166_0 : TransitionSources.Free 2293 41 (bank166 6058) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank166 6058)) 2293 = 55964878333642 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank166 6058)) 2294 = 821662025870876 := by decide +kernel
  refine ⟨rank166 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free166_1 : TransitionSources.Free 2390 41 (bank166 5048) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 41 (bank166 5048)) 2390 = 52792672891860 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 41 (bank166 5048)) 2391 = 562934950560774 := by decide +kernel
  refine ⟨rank166 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole167 : momentEstimate 823 185 = 13072778317 := by
  refine moment_from_blocks [(128,260359840),(128,1491991978),(128,2700606912),(128,3150101952),(128,2819456903),(128,1818380487),(128,737930641),(112,93949604)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank167 (u : ℕ) : P3_7_1.BankOK (bank167 u) :=
  P3_7_1.checked (bank167 u) (m:=594) (B:=823) (J:=185) (N:=6495116984320) (M:=13072778317) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole167
theorem free167_0 : TransitionSources.Free 2293 65 (bank167 24691) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 65 (bank167 24691)) 2293 = 22802104901042 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 65 (bank167 24691)) 2294 = 12890194578654142 := by decide +kernel
  refine ⟨rank167 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free167_1 : TransitionSources.Free 2390 65 (bank167 13649) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 65 (bank167 13649)) 2390 = 30633120533925 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 65 (bank167 13649)) 2391 = 3803442252839775 := by decide +kernel
  refine ⟨rank167 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole168 : momentEstimate 824 185 = 13123950482 := by
  refine moment_from_blocks [(128,260717600),(128,1494403634),(128,2706035136),(128,3158577600),(128,2830979520),(128,1830444715),(128,746270707),(113,96521570)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank168 (u : ℕ) : P3_7_1.BankOK (bank168 u) :=
  P3_7_1.checked (bank168 u) (m:=594) (B:=824) (J:=185) (N:=6495116984320) (M:=13123950482) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole168
theorem free168_0 : TransitionSources.Free 2293 30 (bank168 4492) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 30 (bank168 4492)) 2293 = 52735959953704 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 30 (bank168 4492)) 2294 = 479889557038112 := by decide +kernel
  refine ⟨rank168 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free168_1 : TransitionSources.Free 2390 30 (bank168 3916) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 30 (bank168 3916)) 2390 = 37823826121760 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 30 (bank168 3916)) 2391 = 349309029184152 := by decide +kernel
  refine ⟨rank168 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole169 : momentEstimate 867 191 = 15843358730 := by
  refine moment_from_blocks [(128,276101280),(128,1606907472),(128,2993903616),(128,3605747712),(128,3412285440),(128,2452105648),(128,1207957022),(128,285179600),(34,3170940)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank169 (u : ℕ) : P3_7_1.BankOK (bank169 u) :=
  P3_7_1.checked (bank169 u) (m:=626) (B:=867) (J:=191) (N:=7482311180288) (M:=15843358730) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole169
theorem free169_0 : TransitionSources.Free 2293 76 (bank169 292467) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank169 292467)) 2293 = 5806074736 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank169 292467)) 2294 = 2066712364786833632 := by decide +kernel
  refine ⟨rank169 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free169_1 : TransitionSources.Free 2390 76 (bank169 29097) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank169 29097)) 2390 = 45802255571888 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank169 29097)) 2391 = 19673511819885864 := by decide +kernel
  refine ⟨rank169 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole170 : momentEstimate 870 191 = 16020316298 := by
  refine moment_from_blocks [(128,277174560),(128,1614184080),(128,3010492416),(128,3631773696),(128,3447748608),(128,2493361562),(128,1240451495),(128,301076656),(37,4053225)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank170 (u : ℕ) : P3_7_1.BankOK (bank170 u) :=
  P3_7_1.checked (bank170 u) (m:=626) (B:=870) (J:=191) (N:=7482311180288) (M:=16020316298) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole170
theorem free170_0 : TransitionSources.Free 2293 76 (bank170 227095) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank170 227095)) 2293 = 34873921844128 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank170 227095)) 2294 = 1255066476690084800 := by decide +kernel
  refine ⟨rank170 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free170_1 : TransitionSources.Free 2390 76 (bank170 28384) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank170 28384)) 2390 = 1499222353160 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank170 28384)) 2391 = 18813415617476340 := by decide +kernel
  refine ⟨rank170 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole171 : momentEstimate 869 188 = 15766391116 := by
  refine moment_from_blocks [(128,276816800),(128,1607541487),(128,2977950528),(128,3581782848),(128,3392891712),(128,2444089043),(128,1201344129),(128,281055824),(33,2918745)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank171 (u : ℕ) : P3_7_1.BankOK (bank171 u) :=
  P3_7_1.checked (bank171 u) (m:=627) (B:=869) (J:=188) (N:=7419528216576) (M:=15766391116) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole171
theorem free171_0 : TransitionSources.Free 2293 75 (bank171 201573) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 75 (bank171 201573)) 2293 = 8904979750576 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 75 (bank171 201573)) 2294 = 975690631704592433 := by decide +kernel
  refine ⟨rank171 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free171_1 : TransitionSources.Free 2390 75 (bank171 27879) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 75 (bank171 27879)) 2390 = 36560117784260 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 75 (bank171 27879)) 2391 = 17944458764132040 := by decide +kernel
  refine ⟨rank171 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free171_2 : TransitionSources.Free 2390 75 (bank171 201573) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 75 (bank171 201573)) 2390 = 94641136397289410705 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 75 (bank171 201573)) 2391 = 95616818124014252562 := by decide +kernel
  refine ⟨rank171 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole172 : momentEstimate 869 199 = 16475620761 := by
  refine moment_from_blocks [(128,276816800),(128,1621206050),(128,3073900800),(128,3730899200),(128,3549036800),(128,2574309626),(128,1306057613),(128,336734912),(44,6658960)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank172 (u : ℕ) : P3_7_1.BankOK (bank172 u) :=
  P3_7_1.checked (bank172 u) (m:=627) (B:=869) (J:=199) (N:=7745044480000) (M:=16475620761) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole172
theorem free172_0 : TransitionSources.Free 2293 75 (bank172 88577) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 75 (bank172 88577)) 2293 = 63097192268712 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 75 (bank172 88577)) 2294 = 197906152954525596 := by decide +kernel
  refine ⟨rank172 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free172_1 : TransitionSources.Free 2390 75 (bank172 23613) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 75 (bank172 23613)) 2390 = 42749549879380 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 75 (bank172 23613)) 2391 = 13533258862031872 := by decide +kernel
  refine ⟨rank172 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole173 : momentEstimate 872 192 = 16204478458 := by
  refine moment_from_blocks [(128,277890080),(128,1620362192),(128,3030464384),(128,3662886784),(128,3485808512),(128,2532955534),(128,1271947032),(128,317083200),(40,5080740)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank173 (u : ℕ) : P3_7_1.BankOK (bank173 u) :=
  P3_7_1.checked (bank173 u) (m:=630) (B:=872) (J:=192) (N:=7619678044160) (M:=16204478458) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole173
theorem free173_0 : TransitionSources.Free 2293 76 (bank173 184768) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank173 184768)) 2293 = 48561958986788 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank173 184768)) 2294 = 838806552183406924 := by decide +kernel
  refine ⟨rank173 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free173_1 : TransitionSources.Free 2390 76 (bank173 27639) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank173 27639)) 2390 = 58714760278320 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank173 27639)) 2391 = 18067094010348000 := by decide +kernel
  refine ⟨rank173 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole174 : momentEstimate 876 192 = 16444710190 := by
  refine moment_from_blocks [(128,279321120),(128,1630072656),(128,3052648576),(128,3697719424),(128,3533289600),(128,2588703286),(128,1316515235),(128,339726432),(44,6713861)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank174 (u : ℕ) : P3_7_1.BankOK (bank174 u) :=
  P3_7_1.checked (bank174 u) (m:=630) (B:=876) (J:=192) (N:=7619678044160) (M:=16444710190) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole174
theorem free174_0 : TransitionSources.Free 2293 76 (bank174 148759) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank174 148759)) 2293 = 6071931862160 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank174 148759)) 2294 = 548856683244382840 := by decide +kernel
  refine ⟨rank174 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free174_1 : TransitionSources.Free 2390 76 (bank174 26788) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank174 26788)) 2390 = 7055425091470 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank174 26788)) 2391 = 17084163859861980 := by decide +kernel
  refine ⟨rank174 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole175 : momentEstimate 878 193 = 16632572003 := by
  refine moment_from_blocks [(128,280036640),(128,1636225520),(128,3072680640),(128,3729040064),(128,3571704512),(128,2628937635),(128,1348950316),(128,356858720),(47,8137956)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank175 (u : ℕ) : P3_7_1.BankOK (bank175 u) :=
  P3_7_1.checked (bank175 u) (m:=634) (B:=878) (J:=193) (N:=7758708736000) (M:=16632572003) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole175
theorem free175_0 : TransitionSources.Free 2293 76 (bank175 125592) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank175 125592)) 2293 = 51018917457716 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank175 125592)) 2294 = 394857040159544768 := by decide +kernel
  refine ⟨rank175 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free175_1 : TransitionSources.Free 2390 76 (bank175 25973) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank175 25973)) 2390 = 63043921631340 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank175 25973)) 2391 = 16264373976622746 := by decide +kernel
  refine ⟨rank175 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole176 : momentEstimate 882 194 = 16945191716 := by
  refine moment_from_blocks [(128,281467680),(128,1647208290),(128,3103863360),(128,3777983040),(128,3634213440),(128,2697828556),(128,1404897745),(128,386783904),(52,10945701)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank176 (u : ℕ) : P3_7_1.BankOK (bank176 u) :=
  P3_7_1.checked (bank176 u) (m:=636) (B:=882) (J:=194) (N:=7844154572800) (M:=16945191716) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole176
theorem free176_0 : TransitionSources.Free 2293 76 (bank176 98699) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank176 98699)) 2293 = 2433116275800 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank176 98699)) 2294 = 247117281062345400 := by decide +kernel
  refine ⟨rank176 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free176_1 : TransitionSources.Free 2390 76 (bank176 24684) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank176 24684)) 2390 = 34746577859100 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank176 24684)) 2391 = 14865068189114580 := by decide +kernel
  refine ⟨rank176 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole177 : momentEstimate 885 194 = 17131221716 := by
  refine moment_from_blocks [(128,282540960),(128,1654503045),(128,3120599040),(128,3804303360),(128,3670118400),(128,2740588370),(128,1439954097),(128,405697344),(55,12917100)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank177 (u : ℕ) : P3_7_1.BankOK (bank177 u) :=
  P3_7_1.checked (bank177 u) (m:=638) (B:=885) (J:=194) (N:=7899413217280) (M:=17131221716) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole177
theorem free177_0 : TransitionSources.Free 2293 76 (bank177 92547) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank177 92547)) 2293 = 64167766774482 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank177 92547)) 2294 = 218937707954035146 := by decide +kernel
  refine ⟨rank177 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free177_1 : TransitionSources.Free 2390 76 (bank177 24344) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank177 24344)) 2390 = 24283754918325 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank177 24344)) 2391 = 14555377098277785 := by decide +kernel
  refine ⟨rank177 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole178 : momentEstimate 888 195 = 17387809020 := by
  refine moment_from_blocks [(128,283614240),(128,1663032623),(128,3146292352),(128,3844742272),(128,3721108608),(128,2796194301),(128,1485759778),(128,431183616),(59,15881230)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank178 (u : ℕ) : P3_7_1.BankOK (bank178 u) :=
  P3_7_1.checked (bank178 u) (m:=640) (B:=888) (J:=195) (N:=7985899765760) (M:=17387809020) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole178
theorem free178_0 : TransitionSources.Free 2293 76 (bank178 80371) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank178 80371)) 2293 = 18343455231264 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank178 80371)) 2294 = 166947140772707448 := by decide +kernel
  refine ⟨rank178 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free178_1 : TransitionSources.Free 2390 76 (bank178 23472) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank178 23472)) 2390 = 26788644532204 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank178 23472)) 2391 = 13687663034116272 := by decide +kernel
  refine ⟨rank178 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole179 : momentEstimate 891 195 = 17577396586 := by
  refine moment_from_blocks [(128,284687520),(128,1670333051),(128,3163076224),(128,3871159936),(128,3757160064),(128,2839489948),(128,1521804891),(128,451287440),(62,18397512)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank179 (u : ℕ) : P3_7_1.BankOK (bank179 u) :=
  P3_7_1.checked (bank179 u) (m:=642) (B:=891) (J:=195) (N:=8041801449472) (M:=17577396586) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole179
theorem free179_0 : TransitionSources.Free 2293 76 (bank179 76613) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank179 76613)) 2293 = 38425762349346 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank179 76613)) 2294 = 152841848474365998 := by decide +kernel
  refine ⟨rank179 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free179_1 : TransitionSources.Free 2390 76 (bank179 23197) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank179 23197)) 2390 = 41487096946582 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank179 23197)) 2391 = 13482673843571058 := by decide +kernel
  refine ⟨rank179 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
end Research6969.TransitionBanks
end Z6969Source0598

-- Source: Research6969.TransitionBankChecks10
section Z6969Source0599
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem pole180 : momentEstimate 896 197 = 18038668599 := by
  refine moment_from_blocks [(128,286476320),(128,1684878241),(128,3209000256),(128,3943773504),(128,3848074560),(128,2938062298),(128,1604184795),(128,498989168),(69,25229457)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank180 (u : ℕ) : P3_7_1.BankOK (bank180 u) :=
  P3_7_1.checked (bank180 u) (m:=646) (B:=896) (J:=197) (N:=8217479086080) (M:=18038668599) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole180
theorem free180_0 : TransitionSources.Free 2293 76 (bank180 62680) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank180 62680)) 2293 = 61985028912858 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank180 62680)) 2294 = 104396803445286576 := by decide +kernel
  refine ⟨rank180 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free180_1 : TransitionSources.Free 2390 76 (bank180 21819) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank180 21819)) 2390 = 2891807698440 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank180 21819)) 2391 = 12133595176430040 := by decide +kernel
  refine ⟨rank180 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole181 : momentEstimate 897 197 = 18103487397 := by
  refine moment_from_blocks [(128,286834080),(128,1687315317),(128,3214626624),(128,3952643904),(128,3860188992),(128,2952731164),(128,1616614341),(128,506198288),(70,26334687)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank181 (u : ℕ) : P3_7_1.BankOK (bank181 u) :=
  P3_7_1.checked (bank181 u) (m:=646) (B:=897) (J:=197) (N:=8217479086080) (M:=18103487397) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole181
theorem free181_0 : TransitionSources.Free 2293 76 (bank181 61748) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank181 61748)) 2293 = 24605369976267 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank181 61748)) 2294 = 101519918135851311 := by decide +kernel
  refine ⟨rank181 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free181_1 : TransitionSources.Free 2390 76 (bank181 21723) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank181 21723)) 2390 = 76264034404110 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank181 21723)) 2391 = 12129008039163954 := by decide +kernel
  refine ⟨rank181 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole182 : momentEstimate 900 198 = 18370859424 := by
  refine moment_from_blocks [(128,287907360),(128,1695762649),(128,3240433216),(128,3993589312),(128,3912078912),(128,3010027213),(128,1665065993),(128,534946945),(74,31047824)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank182 (u : ℕ) : P3_7_1.BankOK (bank182 u) :=
  P3_7_1.checked (bank182 u) (m:=650) (B:=900) (J:=198) (N:=8363671289856) (M:=18370859424) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole182
theorem free182_0 : TransitionSources.Free 2293 76 (bank182 57760) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank182 57760)) 2293 = 55335602671536 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank182 57760)) 2294 = 89903973164709363 := by decide +kernel
  refine ⟨rank182 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free182_1 : TransitionSources.Free 2390 76 (bank182 21248) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank182 21248)) 2390 = 46782332918595 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank182 21248)) 2391 = 11713233486939318 := by decide +kernel
  refine ⟨rank182 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole183 : momentEstimate 903 198 = 18568500055 := by
  refine moment_from_blocks [(128,288980640),(128,1703079010),(128,3257359360),(128,4020296704),(128,3948567552),(128,3054464893),(128,1703204376),(128,557584470),(77,34963050)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank183 (u : ℕ) : P3_7_1.BankOK (bank183 u) :=
  P3_7_1.checked (bank183 u) (m:=650) (B:=903) (J:=198) (N:=8363671289856) (M:=18568500055) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole183
theorem free183_0 : TransitionSources.Free 2293 76 (bank183 54742) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank183 54742)) 2293 = 17670462204434 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank183 54742)) 2294 = 81266721139370884 := by decide +kernel
  refine ⟨rank183 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free183_1 : TransitionSources.Free 2390 76 (bank183 20877) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank183 20877)) 2390 = 43035607567524 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank183 20877)) 2391 = 11381612888266049 := by decide +kernel
  refine ⟨rank183 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole184 : momentEstimate 906 199 = 18841034461 := by
  refine moment_from_blocks [(128,290053920),(128,1711502330),(128,3283232000),(128,4061472000),(128,4000851200),(128,3112514597),(128,1752913429),(128,587856569),(81,40638416)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank184 (u : ℕ) : P3_7_1.BankOK (bank184 u) :=
  P3_7_1.checked (bank184 u) (m:=654) (B:=906) (J:=199) (N:=8511579750400) (M:=18841034461) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole184
theorem free184_0 : TransitionSources.Free 2293 76 (bank184 51224) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank184 51224)) 2293 = 58000902336150 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank184 51224)) 2294 = 72011590431146700 := by decide +kernel
  refine ⟨rank184 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free184_1 : TransitionSources.Free 2390 76 (bank184 20384) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank184 20384)) 2390 = 78516590978700 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank184 20384)) 2391 = 11011283626607730 := by decide +kernel
  refine ⟨rank184 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole185 : momentEstimate 908 200 = 19048970063 := by
  refine moment_from_blocks [(128,290769440),(128,1717454658),(128,3303449472),(128,4093813632),(128,4041122688),(128,3155966873),(128,1790189243),(128,610937570),(84,45266487)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank185 (u : ℕ) : P3_7_1.BankOK (bank185 u) :=
  P3_7_1.checked (bank185 u) (m:=656) (B:=908) (J:=200) (N:=8602464026624) (M:=19048970063) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole185
theorem free185_0 : TransitionSources.Free 2293 76 (bank185 48641) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank185 48641)) 2293 = 69799259528856 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank185 48641)) 2294 = 65532000881455218 := by decide +kernel
  refine ⟨rank185 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free185_1 : TransitionSources.Free 2390 76 (bank185 19986) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank185 19986)) 2390 = 62269161918920 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank185 19986)) 2391 = 10666588666321962 := by decide +kernel
  refine ⟨rank185 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole186 : momentEstimate 910 200 = 19184229663 := by
  refine moment_from_blocks [(128,291484960),(128,1722338730),(128,3314795520),(128,4111746048),(128,4065641472),(128,3186053050),(128,1816500465),(128,627091603),(86,48577815)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank186 (u : ℕ) : P3_7_1.BankOK (bank186 u) :=
  P3_7_1.checked (bank186 u) (m:=656) (B:=910) (J:=200) (N:=8602464026624) (M:=19184229663) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole186
theorem free186_0 : TransitionSources.Free 2293 76 (bank186 46700) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank186 46700)) 2293 = 58435103160612 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank186 46700)) 2294 = 60648993906103269 := by decide +kernel
  refine ⟨rank186 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free186_1 : TransitionSources.Free 2390 76 (bank186 19684) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank186 19684)) 2390 = 45688563996705 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank186 19684)) 2391 = 10374324579773910 := by decide +kernel
  refine ⟨rank186 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole187 : momentEstimate 918 206 = 20188806092 := by
  refine moment_from_blocks [(128,294347040),(128,1747612533),(128,3412910016),(128,4270956480),(128,4260782016),(128,3390916902),(128,1993958856),(128,741367524),(100,75954725)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank187 (u : ℕ) : P3_7_1.BankOK (bank187 u) :=
  P3_7_1.checked (bank187 u) (m:=662) (B:=918) (J:=206) (N:=8977766154240) (M:=20188806092) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole187
theorem free187_0 : TransitionSources.Free 2293 75 (bank187 32183) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 75 (bank187 32183)) 2293 = 14724110740032 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 75 (bank187 32183)) 2294 = 30061454732926416 := by decide +kernel
  refine ⟨rank187 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free187_1 : TransitionSources.Free 2390 75 (bank187 16602) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 75 (bank187 16602)) 2390 = 17852956058056 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 75 (bank187 16602)) 2391 = 7689868372083576 := by decide +kernel
  refine ⟨rank187 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole188 : momentEstimate 920 202 = 20024299600 := by
  refine moment_from_blocks [(128,295062560),(128,1748824670),(128,3389469888),(128,4230935744),(128,4220957888),(128,3365663585),(128,1974441190),(128,727150800),(98,71793275)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank188 (u : ℕ) : P3_7_1.BankOK (bank188 u) :=
  P3_7_1.checked (bank188 u) (m:=664) (B:=920) (J:=202) (N:=8905622290432) (M:=20024299600) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole188
theorem free188_0 : TransitionSources.Free 2293 76 (bank188 40375) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank188 40375)) 2293 = 62363187022304 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank188 40375)) 2294 = 46804923058159588 := by decide +kernel
  refine ⟨rank188 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free188_1 : TransitionSources.Free 2390 76 (bank188 18578) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank188 18578)) 2390 = 67782988755570 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank188 18578)) 2391 = 9563557560797460 := by decide +kernel
  refine ⟨rank188 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole189 : momentEstimate 924 203 = 20383503144 := by
  refine moment_from_blocks [(128,296493600),(128,1759587057),(128,3421200768),(128,4281852288),(128,4286865792),(128,3441328255),(128,2041817143),(128,771029879),(103,83328362)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank189 (u : ℕ) : P3_7_1.BankOK (bank189 u) :=
  P3_7_1.checked (bank189 u) (m:=666) (B:=924) (J:=203) (N:=8999288700928) (M:=20383503144) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole189
theorem free189_0 : TransitionSources.Free 2293 76 (bank189 37687) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank189 37687)) 2293 = 44521979662944 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank189 37687)) 2294 = 41298415588524528 := by decide +kernel
  refine ⟨rank189 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free189_1 : TransitionSources.Free 2390 76 (bank189 18034) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank189 18034)) 2390 = 90876791915160 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank189 18034)) 2391 = 9154699106091120 := by decide +kernel
  refine ⟨rank189 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole190 : momentEstimate 927 203 = 20597080434 := by
  refine moment_from_blocks [(128,297566880),(128,1766926533),(128,3438356352),(128,4309034880),(128,4324075392),(128,3487658161),(128,2084014306),(128,798569287),(106,90878643)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank190 (u : ℕ) : P3_7_1.BankOK (bank190 u) :=
  P3_7_1.checked (bank190 u) (m:=668) (B:=927) (J:=203) (N:=9059825090560) (M:=20597080434) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole190
theorem free190_0 : TransitionSources.Free 2293 76 (bank190 37026) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank190 37026)) 2293 = 5416869112024 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank190 37026)) 2294 = 40107368452677476 := by decide +kernel
  refine ⟨rank190 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free190_1 : TransitionSources.Free 2390 76 (bank190 17912) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank190 17912)) 2390 = 56071467529266 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank190 17912)) 2391 = 9061095633249618 := by decide +kernel
  refine ⟨rank190 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole191 : momentEstimate 930 204 = 20891646965 := by
  refine moment_from_blocks [(128,298640160),(128,1775219585),(128,3464440960),(128,4351143040),(128,4378012800),(128,3548683927),(128,2138835832),(128,835134219),(110,101536442)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank191 (u : ℕ) : P3_7_1.BankOK (bank191 u) :=
  P3_7_1.checked (bank191 u) (m:=670) (B:=930) (J:=204) (N:=9154580971520) (M:=20891646965) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole191
theorem free191_0 : TransitionSources.Free 2293 76 (bank191 35220) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank191 35220)) 2293 = 27162902934880 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank191 35220)) 2294 = 36703186697883125 := by decide +kernel
  refine ⟨rank191 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free191_1 : TransitionSources.Free 2390 76 (bank191 17509) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank191 17509)) 2390 = 46371151186475 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank191 17509)) 2391 = 8743394323497300 := by decide +kernel
  refine ⟨rank191 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole192 : momentEstimate 962 208 = 23645774460 := by
  refine moment_from_blocks [(128,310088480),(128,1857168788),(128,3684713472),(128,4705141760),(128,4848960512),(128,4116311184),(128,2675051808),(128,1209222293),(128,238529328),(18,586835)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank192 (u : ℕ) : P3_7_1.BankOK (bank192 u) :=
  P3_7_1.checked (bank192 u) (m:=690) (B:=962) (J:=208) (N:=9921631092736) (M:=23645774460) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole192
private theorem pole193 : momentEstimate 962 212 = 23997864317 := by
  refine moment_from_blocks [(128,310088480),(128,1860225107),(128,3720200064),(128,4767137664),(128,4920688512),(128,4181145468),(128,2729359010),(128,1250460165),(128,257533232),(22,1026615)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank193 (u : ℕ) : P3_7_1.BankOK (bank193 u) :=
  P3_7_1.checked (bank193 u) (m:=690) (B:=962) (J:=212) (N:=10065769922560) (M:=23997864317) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole193
private theorem pole194 : momentEstimate 962 217 = 24434817260 := by
  refine moment_from_blocks [(128,310088480),(128,1863329882),(128,3762707904),(128,4843150784),(128,5009235392),(128,4261558346),(128,2797670533),(128,1302808995),(128,282438208),(27,1828736)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank194 (u : ℕ) : P3_7_1.BankOK (bank194 u) :=
  P3_7_1.checked (bank194 u) (m:=690) (B:=962) (J:=217) (N:=10244384358400) (M:=24434817260) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole194
private theorem pole195 : momentEstimate 963 208 = 23724874690 := by
  refine moment_from_blocks [(128,310446240),(128,1859621660),(128,3690505280),(128,4714357824),(128,4861600832),(128,4132348229),(128,2691041452),(128,1220795242),(128,243475296),(19,682635)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank195 (u : ℕ) : P3_7_1.BankOK (bank195 u) :=
  P3_7_1.checked (bank195 u) (m:=690) (B:=963) (J:=208) (N:=9921631092736) (M:=23724874690) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole195
private theorem pole196 : momentEstimate 963 212 = 24078187611 := by
  refine moment_from_blocks [(128,310446240),(128,1862682213),(128,3726048192),(128,4776475584),(128,4933516224),(128,4197417732),(128,2745503490),(128,1262226848),(128,262706688),(23,1164400)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank196 (u : ℕ) : P3_7_1.BankOK (bank196 u) :=
  P3_7_1.checked (bank196 u) (m:=690) (B:=963) (J:=212) (N:=10065769922560) (M:=24078187611) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole196
private theorem pole197 : momentEstimate 963 217 = 24516657294 := by
  refine moment_from_blocks [(128,310446240),(128,1865791298),(128,3768623552),(128,4852638144),(128,5022294464),(128,4278115958),(128,2814006983),(128,1314816501),(128,287894784),(28,2029370)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank197 (u : ℕ) : P3_7_1.BankOK (bank197 u) :=
  P3_7_1.checked (bank197 u) (m:=690) (B:=963) (J:=217) (N:=10244384358400) (M:=24516657294) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole197
end Research6969.TransitionBanks
end Z6969Source0599

-- Source: Research6969.TransitionBankChecks11
section Z6969Source0600
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem pole198 : momentEstimate 1079 242 = 38464827595 := by
  refine moment_from_blocks [(128,351946400),(128,2159171779),(128,4670421120),(128,6390347904),(128,7091058816),(128,6772553856),(128,5446417777),(128,3502766654),(128,1666942787),(128,406423248),(41,6777254)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank198 (u : ℕ) : P3_7_1.BankOK (bank198 u) :=
  P3_7_1.checked (bank198 u) (m:=777) (B:=1079) (J:=242) (N:=14510937341952) (M:=38464827595) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole198
theorem free198_0 : TransitionSources.Free 2293 65 (bank198 9780) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 65 (bank198 9780)) 2293 = 106936096624891 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 65 (bank198 9780)) 2294 = 4565552825133260 := by decide +kernel
  refine ⟨rank198 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free198_1 : TransitionSources.Free 2390 65 (bank198 7884) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 65 (bank198 7884)) 2390 = 144154520710220 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 65 (bank198 7884)) 2391 = 2924243702035665 := by decide +kernel
  refine ⟨rank198 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole199 : momentEstimate 1139 255 = 47675541672 := by
  refine moment_from_blocks [(128,373412000),(128,2307825824),(128,5137965056),(128,7228825600),(128,8245944320),(128,8189321216),(128,7059059664),(128,5035185818),(128,2863339848),(128,1095209040),(114,139453286)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank199 (u : ℕ) : P3_7_1.BankOK (bank199 u) :=
  P3_7_1.checked (bank199 u) (m:=820) (B:=1139) (J:=255) (N:=17030719733760) (M:=47675541672) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole199
theorem free199_0 : TransitionSources.Free 2293 65 (bank199 9241) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 65 (bank199 9241)) 2293 = 99242915076576 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 65 (bank199 9241)) 2294 = 4759594010025408 := by decide +kernel
  refine ⟨rank199 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free199_1 : TransitionSources.Free 2390 65 (bank199 7608) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 65 (bank199 7608)) 2390 = 137358945094560 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 65 (bank199 7608)) 2391 = 3168194097773264 := by decide +kernel
  refine ⟨rank199 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole200 : momentEstimate 1150 248 = 48121815022 := by
  refine moment_from_blocks [(128,377347360),(128,2334934774),(128,5157782016),(128,7222067712),(128,8241971712),(128,8217494016),(128,7148634624),(128,5155905316),(128,2957634817),(128,1152294320),(118,155748355)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank200 (u : ℕ) : P3_7_1.BankOK (bank200 u) :=
  P3_7_1.checked (bank200 u) (m:=825) (B:=1150) (J:=248) (N:=16903818182656) (M:=48121815022) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole200
private theorem pole201 : momentEstimate 1150 253 = 48873782027 := by
  refine moment_from_blocks [(128,377347360),(128,2335006499),(128,5193848896),(128,7309989952),(128,8360777792),(128,8346212416),(128,7266293824),(128,5256098130),(128,3042419258),(128,1210035136),(123,175752764)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank201 (u : ℕ) : P3_7_1.BankOK (bank201 u) :=
  P3_7_1.checked (bank201 u) (m:=825) (B:=1150) (J:=253) (N:=17161575202816) (M:=48873782027) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole201
private theorem pole202 : momentEstimate 1150 260 = 49918096074 := by
  refine moment_from_blocks [(128,377347360),(128,2335010080),(128,5239886695),(128,7429304448),(128,8524017792),(128,8524017792),(128,7429318448),(128,5397111024),(128,3162592170),(128,1293013808),(128,206473008),(2,3449)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank202 (u : ℕ) : P3_7_1.BankOK (bank202 u) :=
  P3_7_1.checked (bank202 u) (m:=825) (B:=1150) (J:=260) (N:=17518948515840) (M:=49918096074) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole202
private theorem pole203 : momentEstimate 1151 248 = 48256472894 := by
  refine moment_from_blocks [(128,377705120),(128,2337405986),(128,5164044864),(128,7232410176),(128,8256393792),(128,8235995712),(128,7171215936),(128,5179630887),(128,2977028765),(128,1164872576),(119,159769080)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank203 (u : ℕ) : P3_7_1.BankOK (bank203 u) :=
  P3_7_1.checked (bank203 u) (m:=825) (B:=1151) (J:=248) (N:=16903818182656) (M:=48256472894) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole203
private theorem pole204 : momentEstimate 1151 253 = 49010625289 := by
  refine moment_from_blocks [(128,377705120),(128,2337477791),(128,5200156224),(128,7320458816),(128,8375408192),(128,8365004352),(128,7289247296),(128,5280051138),(128,3062077002),(128,1222929792),(124,180109566)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank204 (u : ℕ) : P3_7_1.BankOK (bank204 u) :=
  P3_7_1.checked (bank204 u) (m:=825) (B:=1151) (J:=253) (N:=17161575202816) (M:=49010625289) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole204
private theorem pole205 : momentEstimate 1151 260 = 50057971890 := by
  refine moment_from_blocks [(128,377705120),(128,2337481376),(128,5246250929),(128,7439944896),(128,8538934464),(128,8543210688),(128,7452781839),(128,5421370860),(128,3182616403),(128,1306349024),(128,211318240),(3,8051)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank205 (u : ℕ) : P3_7_1.BankOK (bank205 u) :=
  P3_7_1.checked (bank205 u) (m:=825) (B:=1151) (J:=260) (N:=17518948515840) (M:=50057971890) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole205
private theorem pole206 : momentEstimate 1201 269 = 58933082332 := by
  refine moment_from_blocks [(128,395593120),(128,2461046176),(128,5619582979),(128,8129678400),(128,9507654720),(128,9753168960),(128,8866221120),(128,6897200651),(128,4445945515),(128,2205893739),(128,626087760),(62,25009192)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank206 (u : ℕ) : P3_7_1.BankOK (bank206 u) :=
  P3_7_1.checked (bank206 u) (m:=865) (B:=1201) (J:=269) (N:=19985667194880) (M:=58933082332) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole206
theorem free206_0 : TransitionSources.Free 2293 65 (bank206 8864) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 65 (bank206 8864)) 2293 = 248759818155945 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 65 (bank206 8864)) 2294 = 5262646130869185 := by decide +kernel
  refine ⟨rank206 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free206_1 : TransitionSources.Free 2390 65 (bank206 7419) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 65 (bank206 7419)) 2390 = 233119831900550 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 65 (bank206 7419)) 2391 = 3603226746694470 := by decide +kernel
  refine ⟨rank206 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole207 : momentEstimate 1217 272 = 62028176139 := by
  refine moment_from_blocks [(128,401317280),(128,2500586912),(128,5739277084),(128,8355232704),(128,9826794432),(128,10153311168),(128,9334782912),(128,7403030173),(128,4896417276),(128,2547145051),(128,815093840),(81,55187307)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank207 (u : ℕ) : P3_7_1.BankOK (bank207 u) :=
  P3_7_1.checked (bank207 u) (m:=877) (B:=1217) (J:=272) (N:=20785262231552) (M:=62028176139) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole207
theorem free207_0 : TransitionSources.Free 2293 76 (bank207 11435) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank207 11435)) 2293 = 48725902154508 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank207 11435)) 2294 = 8706495101065266 := by decide +kernel
  refine ⟨rank207 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free207_1 : TransitionSources.Free 2390 76 (bank207 9165) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank207 9165)) 2390 = 140682595862239 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank207 9165)) 2391 = 5476939122968652 := by decide +kernel
  refine ⟨rank207 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole208 : momentEstimate 1229 274 = 64382650838 := by
  refine moment_from_blocks [(128,405610400),(128,2530242464),(128,5827524561),(128,8520934400),(128,10061849600),(128,10449331200),(128,9683379200),(128,7785172146),(128,5242642745),(128,2815103370),(128,972127424),(95,88733328)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank208 (u : ℕ) : P3_7_1.BankOK (bank208 u) :=
  P3_7_1.checked (bank208 u) (m:=886) (B:=1229) (J:=274) (N:=21383938048000) (M:=64382650838) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole208
theorem free208_0 : TransitionSources.Free 2293 76 (bank208 11310) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank208 11310)) 2293 = 50175332815652 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank208 11310)) 2294 = 8749028275379216 := by decide +kernel
  refine ⟨rank208 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free208_1 : TransitionSources.Free 2390 76 (bank208 9103) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank208 9103)) 2390 = 49607827302440 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank208 9103)) 2391 = 5456410476092136 := by decide +kernel
  refine ⟨rank208 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole209 : momentEstimate 1229 276 = 64746366769 := by
  refine moment_from_blocks [(128,405610400),(128,2530242464),(128,5838001641),(128,8555195968),(128,10111856192),(128,10506694208),(128,9739710016),(128,7833908835),(128,5286241607),(128,2850345829),(128,994267984),(97,94291625)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank209 (u : ℕ) : P3_7_1.BankOK (bank209 u) :=
  P3_7_1.checked (bank209 u) (m:=886) (B:=1229) (J:=276) (N:=21501770989568) (M:=64746366769) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole209
theorem free209_0 : TransitionSources.Free 2293 76 (bank209 11249) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank209 11249)) 2293 = 2287786185000 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank209 11249)) 2294 = 8664096101596875 := by decide +kernel
  refine ⟨rank209 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free209_1 : TransitionSources.Free 2390 76 (bank209 9062) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank209 9062)) 2390 = 71283722080536 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank209 9062)) 2391 = 5464716916939974 := by decide +kernel
  refine ⟨rank209 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole210 : momentEstimate 1250 280 = 69141668633 := by
  refine moment_from_blocks [(128,413123360),(128,2582139680),(128,5994182670),(128,8855537408),(128,10540566272),(128,11046995712),(128,10374825728),(128,8534167027),(128,5933298837),(128,3364260267),(128,1315251568),(122,187320104)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank210 (u : ℕ) : P3_7_1.BankOK (bank210 u) :=
  P3_7_1.checked (bank210 u) (m:=901) (B:=1250) (J:=280) (N:=22569516007424) (M:=69141668633) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole210
theorem free210_0 : TransitionSources.Free 2293 76 (bank210 11036) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank210 11036)) 2293 = 199542452055024 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank210 11036)) 2294 = 8942984302079451 := by decide +kernel
  refine ⟨rank210 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free210_1 : TransitionSources.Free 2390 76 (bank210 8954) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank210 8954)) 2390 = 219708783483390 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank210 8954)) 2391 = 5742132552225630 := by decide +kernel
  refine ⟨rank210 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole211 : momentEstimate 1267 284 = 73012155113 := by
  refine moment_from_blocks [(128,419205280),(128,2624151712),(128,6123682923),(128,9113123520),(128,10910857920),(128,11513215680),(128,10920196800),(128,9136231668),(128,6501351016),(128,3826799122),(128,1621485184),(128,301385344),(15,468944)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank211 (u : ℕ) : P3_7_1.BankOK (bank211 u) :=
  P3_7_1.checked (bank211 u) (m:=912) (B:=1267) (J:=284) (N:=23441086873600) (M:=73012155113) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole211
theorem free211_0 : TransitionSources.Free 2293 75 (bank211 10626) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 75 (bank211 10626)) 2293 = 61667005568574 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 75 (bank211 10626)) 2294 = 8504263017549552 := by decide +kernel
  refine ⟨rank211 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free211_1 : TransitionSources.Free 2390 75 (bank211 8704) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 75 (bank211 8704)) 2390 = 141677803827650 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 75 (bank211 8704)) 2391 = 5576817704582220 := by decide +kernel
  refine ⟨rank211 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free211_2 : TransitionSources.Free 2390 75 (bank211 10626) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 75 (bank211 10626)) 2390 = 818993480167723440 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 75 (bank211 10626)) 2391 = 827436076179704418 := by decide +kernel
  refine ⟨rank211 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole212 : momentEstimate 1275 287 = 75115353358 := by
  refine moment_from_blocks [(128,422067360),(128,2643922080),(128,6189258408),(128,9253684224),(128,11115168768),(128,11768693760),(128,11214259200),(128,9454864145),(128,6804374453),(128,4077871091),(128,1794123920),(128,374881424),(26,2184525)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank212 (u : ℕ) : P3_7_1.BankOK (bank212 u) :=
  P3_7_1.checked (bank212 u) (m:=919) (B:=1275) (J:=287) (N:=24035953999872) (M:=75115353358) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole212
theorem free212_0 : TransitionSources.Free 2293 76 (bank212 10770) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank212 10770)) 2293 = 1840548006076 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank212 10770)) 2294 = 8869910185046504 := by decide +kernel
  refine ⟨rank212 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free212_1 : TransitionSources.Free 2390 76 (bank212 8810) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank212 8810)) 2390 = 9991603441512 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank212 8810)) 2391 = 5703537779444340 := by decide +kernel
  refine ⟨rank212 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole213 : momentEstimate 1288 286 = 77398939333 := by
  refine moment_from_blocks [(128,426718240),(128,2676048928),(128,6269693391),(128,9382649920),(128,11296448576),(128,12006481984),(128,11512750144),(128,9815953404),(128,7162937194),(128,4374740908),(128,2000352947),(128,467644272),(38,6519425)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank213 (u : ℕ) : P3_7_1.BankOK (bank213 u) :=
  P3_7_1.checked (bank213 u) (m:=928) (B:=1288) (J:=286) (N:=24501513093120) (M:=77398939333) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole213
theorem free213_0 : TransitionSources.Free 2293 76 (bank213 10766) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank213 10766)) 2293 = 30465472655154 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank213 10766)) 2294 = 9050514154458036 := by decide +kernel
  refine ⟨rank213 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free213_1 : TransitionSources.Free 2390 76 (bank213 8827) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank213 8827)) 2390 = 97275588673006 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank213 8827)) 2391 = 5915112131678916 := by decide +kernel
  refine ⟨rank213 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole214 : momentEstimate 1317 296 = 85393696802 := by
  refine moment_from_blocks [(128,437093280),(128,2747716512),(128,6500673246),(128,9881099712),(128,12027026880),(128,12927245760),(128,12581756352),(128,10990560840),(128,8318125554),(128,5361927401),(128,2724113855),(128,844710160),(77,51647250)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank214 (u : ℕ) : P3_7_1.BankOK (bank214 u) :=
  P3_7_1.checked (bank214 u) (m:=949) (B:=1317) (J:=296) (N:=26438419611648) (M:=85393696802) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole214
theorem free214_0 : TransitionSources.Free 2293 76 (bank214 10456) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank214 10456)) 2293 = 270941445155914 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank214 10456)) 2294 = 9455198019168149 := by decide +kernel
  refine ⟨rank214 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free214_1 : TransitionSources.Free 2390 76 (bank214 8650) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 76 (bank214 8650)) 2390 = 120414121625258 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 76 (bank214 8650)) 2391 = 6151219029420900 := by decide +kernel
  refine ⟨rank214 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
private theorem pole215 : momentEstimate 1337 299 = 90341964896 := by
  refine moment_from_blocks [(128,444248480),(128,2797142432),(128,6643067413),(128,10160457600),(128,12433737600),(128,13448726400),(128,13205424000),(128,11703830400),(128,9052014142),(128,6002010468),(128,3211545701),(128,1127300160),(100,112460100)] ?_ rfl rfl
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,True.intro⟩
theorem rank215 (u : ℕ) : P3_7_1.BankOK (bank215 u) :=
  P3_7_1.checked (bank215 u) (m:=962) (B:=1337) (J:=299) (N:=27464892416000) (M:=90341964896) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) pole215
theorem free215_0 : TransitionSources.Free 2293 75 (bank215 10166) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 75 (bank215 10166)) 2293 = 348508435295448 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 75 (bank215 10166)) 2294 = 9386778540952584 := by decide +kernel
  refine ⟨rank215 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
theorem free215_1 : TransitionSources.Free 2390 75 (bank215 8473) := by
  have left : FarProfileArithmetic.value (TransitionSources.request 75 (bank215 8473)) 2390 = 3019320053630 := by decide +kernel
  have right : FarProfileArithmetic.value (TransitionSources.request 75 (bank215 8473)) 2391 = 6027006834418722 := by decide +kernel
  refine ⟨rank215 _,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard; decide +kernel,?_,?_⟩
  · rw [left]; decide
  · rw [left,right]; decide
end Research6969.TransitionBanks
end Z6969Source0600

-- Source: Research6969.PrefixWideSchedule
section Z6969Source0601
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000

namespace Lower6960.Prefix6969Wide

open Research6969
open Research6969.TransitionBanks
open K1_14 (L)
open K1_14_1 (PoleData CRTLift evaluated)
open Lower6960.HelperSource
open P1_7_4 (Mass)

abbrev count : ℕ := 21
abbrev firstHeight : ℕ := 2293
abbrev lastHeight : ℕ := 2389
abbrev agreement : ℕ := 179740

def reserve (i : Fin count) : ℕ := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 14, 21, 21, 36, 41, 41, 65, 76, 76, 76, 76] i
def bank (i : Fin count) : P1_7.Bank :=
  ![bank2 1529, bank8 1694, bank14 1831, bank21 1963, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank61 2536, bank73 5660, bank85 2903, bank74 6544, bank116 3644, bank132 9317, bank148 6656, bank117 49199, bank198 9780, bank207 11435, bank179 76613, bank173 184768, bank169 292467] i

theorem free_checked (i : Fin count) : TransitionSources.Free firstHeight (reserve i) (bank i) := by
  fin_cases i
  · exact free2_0
  · exact free8_0
  · exact free14_0
  · exact free21_0
  · exact free32_0
  · exact free41_0
  · exact free42_2
  · exact free48_0
  · exact free61_0
  · exact free73_0
  · exact free85_0
  · exact free74_2
  · exact free116_1
  · exact free132_0
  · exact free148_0
  · exact free117_0
  · exact free198_0
  · exact free207_0
  · exact free179_0
  · exact free173_0
  · exact free169_0

def cutoff (h : ℕ) (i : Fin count) : ℕ :=
  cutoffCount (bank i).shape agreement h (reserve i) - 1

theorem cutoff_fit {h : ℕ} (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) (i : Fin count) :
    cutoff h i + 2 * h * reserve i < (bank i).shape.m * agreement := by
  have cert := free_checked i
  have hw := width_at_height _ _ _ _ _ lo (hi.trans (by decide)) cert.reserve_fit cert.width
  exact Lower6960.FreeSource.buffered_fit (bank i) agreement h (reserve i) hw

theorem free_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) (i : Fin count) :
    ∃ P ∈ evaluated Crt word (bank i).shape (cutoff h i), P ≠ 0 :=
  (free_checked i).row Crt word ((by decide : 0 < firstHeight).trans_le lo) lo (hi.trans (by decide))

def suppliedHistory : List Mass :=
  [![13965, 178234, 835524, 4738040],
   ![23965/2, 638225/4, 1444437/2, 8475929/2],
   ![17372/3, 230512/3, 629864, 3352561],
   ![7059/2, 743997/16, 376305, 19643741/9],
   ![16211/9, 851639/36, 482245/2, 5031049/4],
   ![24292/27, 12821, 524355/4, 29910923/36],
   ![73478/121, 1314218/121, 5925831/49, 29910923/36],
   ![73478/121, 1314218/121, 5925831/49, 6160324/9],
   ![73478/121, 1141617/121, 99855, 401956],
   ![77324/147, 3687442/441, 8102131/98, 401956],
   ![77324/147, 3687442/441, 8102131/98, 401956],
   ![61324/121, 3687442/441, 5856386/75, 401956],
   ![61324/121, 923839/121, 1790408/25, 9116377/32],
   ![61324/121, 923839/121, 1790408/25, 9116377/32],
   ![61324/121, 11170728/1681, 58368, 9116377/32],
   ![1322245/3362, 11170728/1681, 58368, 9116377/32],
   ![1322245/3362, 8168588/1323, 55043139/1058, 95648400/361],
   ![1322245/3362, 16330489/2738, 49014791/972, 160202063/605],
   ![470505/1369, 16330489/2738, 49014791/972, 160202063/605],
   ![461692/1369, 16330489/2738, 49014791/972, 160202063/605],
   ![459151/1369, 16330489/2738, 49014791/972, 160202063/605]]

def suppliedDegreeRates : List ℕ := [389083703, 388126102, 388260904, 388304270, 386845787, 389010179, 388311592, 388691591, 162716559, 163566869, 163638726, 163457698, 87370845, 87370845, 80626634, 107152128, 115478646, 115428840, 148643765, 183775545, 243003640]
def suppliedHeightRates : List ℕ := [880149, 882774, 882404, 882285, 886282, 880351, 882265, 881224, 2355449, 2341311, 2340116, 2343126, 4547911, 4547911, 4944769, 3676880, 3389896, 3391288, 2589427, 2066153, 1505721]
def retainedCredit (i : Fin 4) : ℕ := ![128991192184800, 1597290774980, 218703276000, 4035632720] i
abbrev prefixCap : ℕ := 222663779244259824

end Lower6960.Prefix6969Wide
end Z6969Source0601

-- Source: Research6969.PrefixWideGeometry
section Z6969Source0602
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960MainGeometry

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969Wide
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt seedHasse)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual orderOn FixedPart)
open K1_14_2_2R (chainCompatible)
open HelperPrefix (timesShape)
open Prefix6969Helper (helperBank helperCutoff)
open MainPrefixSource (hasse_at_mark)
open Far6969RescueGeometry (Model Family word OnMark contact_at_mark zero_of_contact)
open DifferentialContact (Native)
open PrefixRows (Prepared)
open P1_7_4 (ODEGuard degreeVector introJump introWeight)
open scoped Classical

def terminalShape : Shape := ⟨3000, 4184, 900, 530820⟩

def copies (i : Fin count) : ℕ := (reserve i + 11) / 11

theorem reserve_small (i : Fin count) : reserve i < K1.p := by
  fin_cases i <;> decide +kernel

def freeShape (i : Fin 21) : Shape := (bank i).shape

def movingShape (i : Fin 21) : Shape := timesShape (copies i) helperBank.shape

def stage (i : Fin 21) : P1_7.Stage := ⟨reserve i,bank i,⟨movingShape i,0,0⟩⟩

def cutShape (i : ℕ) : Shape :=
  if hi : i+1<21 then HighCore82258_3.envelope (stage ⟨i+1,hi⟩) else terminalShape

theorem cutShape_fit (i : ℕ) : (cutShape i).J≤(cutShape i).B := by
  unfold cutShape
  split
  · exact Nat.le_add_left _ _
  · decide

def introIndices : List (Fin 21) := [1,2,3,4,5,6,7,8,9,10,11,12,13,14]

def introAccount (k : Fin 4) : List (Fin 21) → (Fin 3→ℕ) → (Fin 3→ℕ) → ℕ
  | [], cap, old =>
      introJump cap old (movingShape 0) k +
        K1_14_2_2_2.ordinaryBudget (cap 2) (cap 0) k
  | i::rest, cap, old =>
      let s := freeShape i
      introJump cap old s k + introAccount k rest
        (fun j=>min (cap j) (degreeVector s j/(reserve i+1)))
        (fun j=>max (old j) (introWeight s k j))

def initialCap (k : Fin 4) : ℕ :=
  introAccount k introIndices (degreeVector (freeShape 0)) (fun _=>0)

theorem initial_small (k : Fin 4) : initialCap k < K1.p := by
  fin_cases k <;> decide +kernel

theorem free_ode_guard (i : Fin 21) : ODEGuard (freeShape i).B (freeShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩

theorem moving_ode_guard (i : Fin 21) : ODEGuard (movingShape i).B (movingShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩

theorem free_seed_small (i : Fin 21) : (freeShape i).U<K1.p := by
  fin_cases i <;> decide +kernel

theorem moving_seed_small (i : Fin 21) : (movingShape i).U<K1.p := by
  fin_cases i <;> decide +kernel

theorem reserve_pos {i : Fin 21} (hi : 0 < i.val) : 0<reserve i := by
  have checks (j : Fin 21) : (j.val=0) ∨ 0<reserve j := by
    fin_cases j <;> decide +kernel
  exact (checks i).resolve_left (by omega)

/-- The main branch retains the single preparation object, including the
original helper, its one possible exception, and the 21 stripped free rows. -/
structure Rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) where
  source : Fin 21→Jet
  out : Prepared source freeShape copies
    (evaluated Crt (word M) helperBank.shape (helperCutoff M.overhead.toNat)) helperBank.shape
  contact : ∀ i γ, γ∈Γ → jetAt out.exception (M.label γ) (F.scalar γ)≠0 →
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (out.helper^copies i)
  fixedFree : ∀ i, FixedPart (out.free i) (freeShape i)
  fixedMoving : ∀ i, FixedPart (out.helper^copies i) (movingShape i)

theorem rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293≤M.overhead.toNat) (hi : M.overhead.toNat≤2389)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Nonempty (Rows F Crt) := by
  have hiAll : M.overhead.toNat ≤ 33735 := hi.trans (by decide)
  choose P inside nz using free_rows Crt (word M) lo hi
  obtain ⟨out⟩ := PrefixRows.prepare P freeShape copies _ _ nz
    (fun i => evaluated_shape Crt (word M) (inside i))
    (Prefix6969Helper.helper_nonzero Crt (word M) lo hiAll)
    (fun Q hQ => evaluated_shape Crt (word M) hQ)
    (fun _ _ g h cop => Prefix6969Helper.helper_not_two Crt (word M) lo hiAll
      g.1 h.1 cop g.2.1 h.2.1 g.2.2.1 h.2.2.1 g.2.2.2 h.2.2.2)
  refine ⟨⟨P,out,?_,?_,?_⟩⟩
  · intro i γ mem regular
    have fit : reserve i+1 ≤ copies i*11 := by
      change reserve i+1≤((reserve i+11)/11)*11
      omega
    refine out.contacts i _ (RingHom.ker_isPrime _) ?_ (reserve i+1) 11 fit ?_ ?_
    · intro van
      apply regular
      simpa only [K1_14_2.eval_toJet] using RingHom.mem_ker.mp van
    · exact contact_at_mark F Crt noPole residues (inside i) (cutoff_fit lo hi i) γ mem
    · intro H hm
      have wh := Prefix6969Helper.helper_width lo hiAll
      have width : helperCutoff M.overhead.toNat+2*M.overhead.toNat*10 < helperBank.shape.m*179740 :=
        FreeSource.buffered_fit helperBank 179740 _ 10 wh
      exact contact_at_mark F Crt noPole residues hm width γ mem
  · intro i
    exact Classical.choice (K1_14_2_2_1.proof _ _ (out.free_ne i) (out.free_caps i))
  · intro i
    exact Classical.choice (K1_14_2_2_1.proof _ _ (pow_ne_zero _ out.helper_ne) (out.moving_caps i))

def Rows.marks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Finset K :=
  Γ.filter (fun γ=>jetAt R.out.exception (M.label γ) (F.scalar γ)≠0)

def Rows.family {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Family M R.marks :=
  ⟨F.scalar,fun γ hγ=>F.mark γ (mem_filter.mp hγ).1,F.distinct.mono (filter_subset _ _)⟩

theorem Rows.main_contact {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 21) (γ : K) (mem : γ∈R.marks) :
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.helper^copies i) :=
  R.contact i γ (mem_filter.mp mem).1 (mem_filter.mp mem).2

theorem Rows.intro_tests {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 21) (j : Fin 2) (a : ℕ) (ha : a≤reserve i) (γ : K) (mem : γ∈R.marks) :
    jetAt (seedHasse j a (R.out.free i)) (M.label γ) (R.family.scalar γ)=0 :=
  hasse_at_mark (R.main_contact i γ mem).1 j a ha (ha.trans_lt (reserve_small i))

def Rows.Passes {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 21) (J : Ideal Ambient) : Prop :=
  orderOn J (R.out.free i) (reserve i+1) ∧
  orderOn J (R.out.helper^copies i) (reserve i+1) ∧ chainCompatible (R.out.free i) (R.out.helper^copies i) J

theorem Rows.failed_cut {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 21) {J : Ideal Ambient} (active : Active J) (dualJ : dual J) (fail : ¬R.Passes i J) :
    ∃ C : Jet,(RowCaps C (freeShape i) ∨ RowCaps C (movingShape i)) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  rcases PrefixStage.order_or_cut active dualJ (reserve_small i) (R.out.free_caps i) (R.out.moving_caps i)
    (pow_ne_zero _ R.out.helper_ne) (moving_ode_guard i).jpos with passes | ⟨C,cap,proper,zero⟩
  · exact (fail passes).elim
  · refine ⟨C,cap,proper,?_⟩
    intro γ hγ on
    obtain ⟨free,moving⟩ := R.main_contact i γ hγ
    exact zero _ _ on free moving

end Lower6960.Prefix6969Wide

end
end Merged_R6960MainGeometry

section Merged_R6960MainGeometryIntro

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969Wide
open Finset Polynomial
open K1 (K)
open K1_14 (Shape Jet Seeds FX jetAt graphEval seedHasse atX)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (Ambient OnJet ODE fixedAt)
open K1_14_2_2 (RowCaps Active dual Fits FixedPart fixedOn mass sectionDegree sum_union_le ordinateIncl ODECaps)
open K1_14_2_2_2 (ordinaryBudget ordinate_eq length_le_mass)
open K1_14_3 (NoMovingCommon SeedCover joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open P1_7_4 (degreeVector introJump introWeight)
open P1_7_4_1 (SectionGeometry IntroFactors factorDegree factorMass factorMass_mono factorTariff
  weightedDegree tariff_step ordinary_charge residual_tariff collect proper_cover own_J_le_B own_caps retained_mass
  Stripped initial_factors strip)
open Far6969RescueGeometry (Model Family OnMark label_injective zero_of_contact)
open P1_7_4_1 (irreducible_cut terminal_piece)
open P0_10R_1 (seed_projection)
open scoped Classical BigOperators

private theorem intro_components
    {P Q : Jet} (hQ : Q ≠ 0) (hnc : NoMovingCommon P Q)
    (hQc : RowCaps Q (movingShape 0)) (later : Fin 21 → Jet)
    (rows : ∀ i, later i ≠ 0 ∧ RowCaps (later i) (freeShape i)) :
    ∀ (is : List (Fin 21)),
    ∀ (D : Finset Jet) (cap : Fin 3 → ℕ), IntroFactors P D → (∀ j, factorMass D j ≤ cap j) →
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧
      (∀ k old, mass S k ≤ introAccount k is cap old + weightedDegree old D) ∧
      ∀ z R, (∀ i ∈ is, ∀ j a, a ≤ reserve i →
        jetAt (seedHasse j a (later i)) z R = 0) →
        jetAt Q z R = 0 → (∃ f ∈ D, jetAt f z R = 0) → ∃ I ∈ S, OnJet I z R := by
  classical
  intro is
  induction is with
  | nil =>
    intro D cap hD hcap
    let t := movingShape 0
    have gt := moving_ode_guard 0
    obtain ⟨S, hG, hS, hC⟩ := collect D
      (fun f k => factorTariff t k f + ordinaryBudget (factorDegree f 2) (factorDegree f 0) k)
      (fun f z R => jetAt f z R = 0 ∧ jetAt Q z R = 0)
      (terminal_piece hD hnc hQc gt.jb gt.small hQ)
    refine ⟨S, hG, ?_, ?_⟩
    · intro k old
      have hstep := tariff_step (Finset.empty_subset D) cap old t k hcap
      simp only [Finset.sdiff_empty, weightedDegree, factorMass, Finset.sum_empty,
        mul_zero, Finset.sum_const_zero, Nat.add_zero] at hstep
      have hsum := Nat.add_le_add hstep (ordinary_charge D cap hcap k)
      calc
        _ ≤ ∑ f ∈ D, (factorTariff t k f +
            ordinaryBudget (factorDegree f 2) (factorDegree f 0) k) := hS k
        _ ≤ (weightedDegree old D + introJump cap old t k) +
            ordinaryBudget (cap 2) (cap 0) k := by
          rw [Finset.sum_add_distrib]
          exact hsum
        _ = _ := by
          simp only [introAccount]
          ac_rfl
    · intro z R _ hq ⟨f, hf, hz⟩
      exact hC f hf z R ⟨hz, hq⟩
  | cons i is ih =>
    intro D cap hD hcap
    let s := freeShape i
    let r := reserve i
    let T := D.filter fun f => ∀ j a, a ≤ r → f ∣ seedHasse j a (later i)
    have hT : T ⊆ D := Finset.filter_subset _ _
    have gt := free_ode_guard i
    obtain ⟨hrow, hc⟩ := rows i
    have hTcap (j : Fin 3) :
        factorMass T j ≤ min (cap j) (degreeVector s j / (r+1)) :=
      le_min ((factorMass_mono hT j).trans (hcap j))
        (retained_mass (hD.mono hT) hrow hc (free_seed_small i) r
          (fun f hf => (Finset.mem_filter.mp hf).2) j)
    obtain ⟨laterCover, hLaterGeom, hLaterCap, hLater⟩ :=
      ih T _ (hD.mono hT) hTcap
    obtain ⟨discard, hDiscardGeom, hDiscardCap, hDiscard⟩ :=
      collect (D \ T) (fun f k => factorTariff s k f)
        (fun f z R => jetAt f z R = 0 ∧
          ∀ j a, a ≤ r → jetAt (seedHasse j a (later i)) z R = 0) (by
        intro f hf
        obtain ⟨hfD, hfT⟩ := Finset.mem_sdiff.mp hf
        have hn : ¬ ∀ j a, a ≤ r → f ∣ seedHasse j a (later i) :=
          fun hall => hfT (Finset.mem_filter.mpr ⟨hfD, hall⟩)
        push Not at hn
        obtain ⟨j, a, ha, hd⟩ := hn
        have hirr := (hD.factors f hfD).1
        obtain ⟨S, hG, hF, hC⟩ := proper_cover (irreducible_cut hirr hd)
          (own_J_le_B hirr.ne_zero) gt.jb (own_caps f) (P1_7_4_1_2.proof s (later i) hc j a)
        exact ⟨S, hG, fun k => (hF k).trans_eq (residual_tariff f s gt.jb k),
          fun z R hr => hC z R hr.1 (hr.2 j a ha)⟩)
    refine ⟨discard ∪ laterCover, ?_, ?_, ?_⟩
    · intro I hI
      exact (Finset.mem_union.mp hI).elim (hDiscardGeom I) (hLaterGeom I)
    · intro k old
      let w := fun j => max (old j) (introWeight s k j)
      let newCap := fun j => min (cap j) (degreeVector s j / (r+1))
      have hstep := tariff_step hT cap old s k hcap
      calc
        _ ≤ mass discard k + mass laterCover k := sum_union_le (fun I => sectionDegree I k) _ _
        _ ≤ (∑ f ∈ D \ T, factorTariff s k f) +
            (introAccount k is newCap w + weightedDegree w T) :=
          Nat.add_le_add (hDiscardCap k) (hLaterCap k w)
        _ = introAccount k is newCap w +
            ((∑ f ∈ D \ T, factorTariff s k f) + weightedDegree w T) := by ac_rfl
        _ ≤ introAccount k is newCap w + (weightedDegree old D + introJump cap old s k) :=
          Nat.add_le_add_left hstep _
        _ = _ := by
          change _ = (introJump cap old s k + introAccount k is newCap w) + weightedDegree old D
          ac_rfl
    · intro z R hder hq ⟨f, hf, hz⟩
      by_cases h : f ∈ T
      · obtain ⟨I, hI, hMark⟩ := hLater z R
          (fun l hl => hder l (List.mem_cons_of_mem _ hl)) hq ⟨f, h, hz⟩
        exact ⟨I, Finset.mem_union_right _ hI, hMark⟩
      · obtain ⟨I, hI, hMark⟩ := hDiscard f (Finset.mem_sdiff.mpr ⟨hf, h⟩) z R
          ⟨hz, hder i (List.mem_cons_self ..)⟩
        exact ⟨I, Finset.mem_union_left _ hI, hMark⟩

def Rows.fixedMarksOf {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (G : ODE) : Finset K :=
  R.marks.filter (fun γ=>fixedAt G (R.family.scalar γ)=0)

def Rows.fixedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Finset K :=
  (univ : Finset (Fin 21)).biUnion (fun i=>
    R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation)

theorem Rows.mem_fixed_free {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 21)
    (root : fixedAt (R.fixedFree i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_left _ (mem_filter.mpr ⟨mark,root⟩)⟩

theorem Rows.mem_fixed_moving {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 21)
    (root : fixedAt (R.fixedMoving i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_right _ (mem_filter.mpr ⟨mark,root⟩)⟩

def Rows.Clean {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (J : Ideal Ambient) : Prop :=
  ∀ i, ¬ fixedOn (R.fixedFree i).equation J ∧ ¬ fixedOn (R.fixedMoving i).equation J

private theorem Rows.fixed_of_not_clean {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {J : Ideal Ambient} {γ : K} (mark : γ∈R.marks) (on : OnMark R.family J γ)
    (bad : ¬R.Clean J) : γ∈R.fixedMarks := by
  by_contra absent
  apply bad
  intro i
  constructor
  · intro h
    apply absent (R.mem_fixed_free mark i ?_)
    simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on h)
  · intro h
    apply absent (R.mem_fixed_moving mark i ?_)
    simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on h)

private theorem Rows.sections {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) :
    ∃ S : Finset (Ideal Ambient),SectionGeometry S ∧ Fits S initialCap ∧
      ∃ content : Seeds, content≠0 ∧ content.totalDegree≤(freeShape 0).U ∧
      ∀ γ∈R.marks,γ∈R.fixedMarks ∨ graphEval (M.label γ) content=0 ∨ ∃ J∈S,OnMark R.family J γ := by
  obtain ⟨a⟩ := strip (R.out.free_ne 0) (R.out.free_caps 0) (R.fixedFree 0)
  obtain ⟨A,hA,hcap,hroot⟩ := initial_factors a
  obtain ⟨S,geom,fit,cover⟩ := intro_components (pow_ne_zero _ R.out.helper_ne)
    (R.out.no_moving 0) (R.out.moving_caps 0) R.out.free
    (fun i=>⟨R.out.free_ne i,R.out.free_caps i⟩) introIndices A _ hA hcap
  refine ⟨S,geom,?_,a.content,a.content_ne,a.content_le,?_⟩
  · intro k
    simpa only [initialCap,weightedDegree,zero_mul,Finset.sum_const_zero,Nat.add_zero] using fit k (fun _=>0)
  · intro γ hγ
    obtain ⟨p,q⟩ := R.main_contact 0 γ hγ
    rcases a.covers _ _ (zero_of_contact p) with hs | hf | hp
    · exact Or.inr (Or.inl hs)
    · exact Or.inl (R.mem_fixed_free hγ 0 hf)
    · exact Or.inr (Or.inr (cover _ _ (fun i _ j r hr=>R.intro_tests i j r hr γ hγ)
        (zero_of_contact q) (hroot _ _ hp)))

structure Initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) where
  seed : SeedCover
  seed_cap : seed.curve.totalDegree ≤ initialCap 2
  seed_points : seed.points.card ≤ initialCap 3
  ordinates : Finset FX
  ordinate_cap : ordinates.card ≤ initialCap 0
  content : Seeds
  content_ne : content≠0
  content_cap : content.totalDegree≤(freeShape 0).U
  rankExit : Finset (Ideal Ambient)
  parents : Finset (Ideal Ambient)
  fits : Fits (rankExit∪parents) initialCap
  disjoint : Disjoint rankExit parents
  rank_geom : ∀ J∈rankExit,Active J ∧ ¬dual J
  parent_geom : ∀ J∈parents,Active J ∧ dual J ∧ J.height=2 ∧ R.Clean J
  covers : ∀ γ∈R.marks,γ∈R.fixedMarks ∨ graphEval (M.label γ) content=0 ∨
    seed.Covers (M.label γ) ∨ atX (R.family.scalar γ)∈ordinates ∨
      (∃ J∈rankExit,OnMark R.family J γ) ∨ ∃ J∈parents,OnMark R.family J γ

/-- Form the initial affine section cover, remove fixed-factor marks, and
split the remaining active parents at the actual rank-exit index zero. -/
theorem Rows.initial_cover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) :
    Nonempty (Initial R) := by
  obtain ⟨S,geom,fit,content,cn,cc,cover⟩ := R.sections
  let noSeeds := S.filter (fun J=>sectionDegree J 0=0)
  let constY := S.filter (fun J=>0<sectionDegree J 0 ∧
    ¬Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let active := S.filter (fun J=>0<sectionDegree J 0 ∧
    Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let rank := active.filter (fun J=>R.Clean J ∧ ¬dual J)
  let parents := active.filter (fun J=>R.Clean J ∧ dual J)
  have geomActive (J : Ideal Ambient) (mem : J∈active) : Active J ∧ J.height=2 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,height,finite⟩ := geom J hin
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (initial_small k))
    exact ⟨⟨prime,dim,finite.seeds,finite.ordinate,finite.mixed,finite.jets,
      ⟨seedPos,small 0⟩,small 2,small 3,ord⟩,height⟩
  have seed_exists (J : Ideal Ambient) (mem : J∈noSeeds) :
      ∃ C : SeedCover,C.curve.totalDegree≤sectionDegree J 2 ∧ C.points.card≤sectionDegree J 3 ∧
        ∀ z T,OnJet J z T → C.Covers z := by
    obtain ⟨hin,zero⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,_,finite⟩ := geom J hin
    exact seed_projection J prime dim finite zero
  let seedImage (J : Ideal Ambient) : SeedCover :=
    if mem : J∈noSeeds then Classical.choose (seed_exists J mem) else ⟨1,one_ne_zero,∅⟩
  have seed_spec (J : Ideal Ambient) (mem : J∈noSeeds) :
      (seedImage J).curve.totalDegree≤sectionDegree J 2 ∧
        (seedImage J).points.card≤sectionDegree J 3 ∧
        ∀ z T,OnJet J z T → (seedImage J).Covers z := by
    simpa only [seedImage,dite_eq_left mem] using Classical.choose_spec (seed_exists J mem)
  let onY (J : Ideal Ambient) :=
    (R.marks.filter (OnMark R.family J)).image fun γ=>atX (R.family.scalar γ)
  have ordinate_bound (J : Ideal Ambient) (mem : J∈constY) : (onY J).card≤sectionDegree J 0 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    apply le_trans (b:=1) _ seedPos
    apply card_le_one.mpr
    intro y hy z hz
    obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hy
    obtain ⟨δ,hδ,rfl⟩ := mem_image.mp hz
    exact ordinate_eq (geom J hin).1 ord (mem_filter.mp hγ).2 (mem_filter.mp hδ).2
  refine ⟨⟨joinCovers noSeeds seedImage,?_,?_,constY.biUnion onY,?_,content,cn,cc,
    rank,parents,?_,?_,?_,?_,?_⟩⟩
  · exact (joinCovers_degree _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 2).trans (fit 2)))
  · exact (joinCovers_points _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).2.1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 3).trans (fit 3)))
  · exact card_biUnion_le.trans ((sum_le_sum ordinate_bound).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 0).trans (fit 0)))
  · apply K1_14_2_2.fits_mono _ fit
    exact union_subset ((filter_subset _ _).trans (filter_subset _ _))
      ((filter_subset _ _).trans (filter_subset _ _))
  · exact disjoint_left.mpr fun _ a b=>(mem_filter.mp a).2.2 (mem_filter.mp b).2.2
  · intro J mem
    exact ⟨(geomActive J (mem_filter.mp mem).1).1,(mem_filter.mp mem).2.2⟩
  · intro J mem
    obtain ⟨hin,c,d⟩ := mem_filter.mp mem
    obtain ⟨act,ht⟩ := geomActive J hin
    exact ⟨act,d,ht,c⟩
  · intro γ hγ
    rcases cover γ hγ with fixed | seed | ⟨J,hin,on⟩
    · exact Or.inl fixed
    · exact Or.inr (Or.inl seed)
    · by_cases z : sectionDegree J 0=0
      · have mem : J∈noSeeds := mem_filter.mpr ⟨hin,z⟩
        exact Or.inr (Or.inr (Or.inl (joinCovers_covers mem ((seed_spec J mem).2.2 _ _ on))))
      · by_cases ord : Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl)
        · have mem : J∈active := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
          by_cases clean : R.Clean J
          · by_cases d : dual J
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨J,mem_filter.mpr ⟨mem,clean,d⟩,on⟩))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨J,mem_filter.mpr ⟨mem,clean,d⟩,on⟩))))
          · exact Or.inl (R.fixed_of_not_clean hγ on clean)
        · have mem : J∈constY := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
          exact Or.inr (Or.inr (Or.inr (Or.inl (mem_biUnion.mpr ⟨J,mem,
            mem_image.mpr ⟨γ,mem_filter.mpr ⟨hγ,on⟩,rfl⟩⟩))))

theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ E : ODE, ODECaps E (mass ini.rankExit 2) (mass ini.rankExit 1) ∧
      ∀ γ∈R.marks,(∃ J∈ini.rankExit,OnMark R.family J γ) → fixedAt E (R.family.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation ini.rankExit ini.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))

end Lower6960.Prefix6969Wide

end
end Merged_R6960MainGeometryIntro

section Merged_R6960MainGeometryProcess

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969Wide
open Finset Polynomial
open K1 (K I)
open K1_14 (L Shape Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated evaluated_shape nodeL)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (RowCaps Active dual mass mass_mono sectionDegree CutCover weight dot
  emptyCut joinCuts joinCuts_cost sum_dot)
open K1_14_3 (Surface Parent)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open P1_7_4 (Mass massQ massQ_mono pairedCap)
open Far6969RescueGeometry (Model Family OnMark OnSurface word contact_at_mark zero_of_contact)
open HighCore82258_3 (envelope_caps)
open Lower6960.Far6969RescueGeometry (proper_cut)
open scoped Classical BigOperators

def terminalCutoff : ℕ := terminalShape.m*179740-1
def TerminalFits (s : Shape) : Prop :=
  0<s.m ∧ s.B≤terminalShape.B ∧ s.J≤terminalShape.J ∧ s.U≤terminalShape.U
def TerminalPass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (J : Ideal Ambient) : Prop :=
  ∀ s, TerminalFits s → ∀ P∈evaluated Crt w s (s.m*179740-1),toJet P∈J

/-- A parent that fails any terminal bank provides a proper row inside
the single envelope used by the geometric cut bill. -/
theorem terminal_failure {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L)
    {J : Ideal Ambient} (failed : ¬ TerminalPass Crt w J) :
    ∃ (s : Shape) (P : Jet), 0<s.m ∧ P∈evaluated Crt w s (s.m*179740-1) ∧
      RowCaps P terminalShape ∧ toJet P∉J := by
  classical
  unfold TerminalPass at failed
  push Not at failed
  obtain ⟨s,⟨sm,sb,sj,su⟩,P,inside,proper⟩ := failed
  refine ⟨s,P,sm,inside,?_,proper⟩
  intro j i nz
  obtain ⟨b,v,u⟩ := evaluated_shape Crt w inside j i nz
  exact ⟨b.trans sb,v.trans sj,u.trans su⟩

def SurfacePass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (q : Surface) : Prop :=
  ∀ s, TerminalFits s → ∀ P∈evaluated Crt w s (s.m*179740-1),P∈q.asIdeal

theorem SurfacePass.original {h : ℕ} {D : PoleData h} {Crt : CRTLift D} {w : I→L}
    {q : Surface} (pass : SurfacePass Crt w q) :
    ∀ P∈evaluated Crt w terminalShape terminalCutoff,P∈q.asIdeal :=
  pass terminalShape ⟨by decide,le_rfl,le_rfl,le_rfl⟩
def Initial.kept {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) :=
  ini.parents.filter (fun J=>∀ i : Fin 21,0 < i.val → i.val≤n → R.Passes i J)

theorem Initial.kept_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.kept 0=ini.parents := by
  ext J
  constructor
  · exact fun h=>(mem_filter.mp h).1
  · intro h
    apply mem_filter.mpr
    refine ⟨h,fun i pos zero=>?_⟩
    omega

theorem Initial.kept_anti {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    Antitone ini.kept := by
  intro m n le J mem
  obtain ⟨p,pass⟩ := mem_filter.mp mem
  exact mem_filter.mpr ⟨p,fun i hi hm=>pass i hi (hm.trans le)⟩

theorem Initial.kept_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈ini.kept n) :
    Active J ∧ dual J ∧ J.height=2 ∧ R.Clean J :=
  ini.parent_geom J (mem_filter.mp mem).1

def Initial.final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    Finset (Ideal Ambient) :=
  (ini.kept 20).filter (TerminalPass Crt (word M))

def Initial.live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := if n<21 then ini.kept n else ini.final

def Initial.lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := ini.live n \ ini.live (n+1)

theorem Initial.live_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.live 0=ini.parents := by
  rw [Initial.live,ite_eq_left (by decide : 0<21),ini.kept_zero]

theorem Initial.next_sub {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<21) : ini.live (i+1)⊆ini.live i := by
  by_cases hn : i+1<21
  · simp only [Initial.live,ite_eq_left hi,ite_eq_left hn]
    exact ini.kept_anti (Nat.le_succ _)
  · have eq : i=20 := by omega
    subst i
    exact filter_subset _ _

theorem Initial.stage_mass {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (i : Fin 21) (hi : 0 < i.val) {n : ℕ} (step : i.val≤n) (k : Fin 4) :
    massQ (ini.kept n) k≤pairedCap (freeShape i) (movingShape i) (reserve i) true k := by
  have s := free_ode_guard i
  have t := moving_ode_guard i
  apply P1_7_4_2.proof (freeShape i) (movingShape i) (reserve i) true (R.out.free i)
    (R.out.helper^copies i) (reserve_pos hi) (reserve_small i) s.small t.small
    (free_seed_small i) (moving_seed_small i) s.jb t.jb (R.out.free_ne i)
    (pow_ne_zero _ R.out.helper_ne) (R.out.free_caps i) (R.out.moving_caps i)
    (R.out.no_moving i) (R.fixedFree i) (R.fixedMoving i)
  · intro _ J mem
    exact (ini.kept_geom mem).2.1
  · intro J mem
    have geom := ini.kept_geom mem
    have pass := (mem_filter.mp mem).2 i hi step
    have clean := geom.2.2.2 i
    exact ⟨geom.1,pass.2.2,clean.1,clean.2,pass.1,pass.2.1⟩

/-- Every failing parent has a marked cutter with the exact stage envelope.
The terminal failure uses a row of the common full bank. -/
theorem Initial.marked_cutter {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} {J : Ideal Ambient} (hi : i<21) (mem : J∈ini.lost i) :
    ∃ C : Jet,RowCaps C (cutShape i) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  obtain ⟨prev,lost⟩ := mem_sdiff.mp mem
  rw [Initial.live,ite_eq_left hi] at prev
  by_cases hn : i+1<21
  · let j : Fin 21 := ⟨i+1,hn⟩
    have hf : ¬R.Passes j J := by
      intro p
      apply lost
      rw [Initial.live,ite_eq_left hn]
      apply mem_filter.mpr
      refine ⟨(mem_filter.mp prev).1,?_⟩
      intro z hz ht
      by_cases same : z.val=i+1
      · exact (Fin.ext same : z=j) ▸ p
      · exact (mem_filter.mp prev).2 z hz (by omega)
    have geom := ini.kept_geom prev
    obtain ⟨C,cap,proper,zero⟩ := R.failed_cut j geom.1 geom.2.1 hf
    refine ⟨C,?_,proper,zero⟩
    rw [cutShape,dite_eq_left hn]
    exact envelope_caps (s:=stage j) (free_ode_guard j).jb (moving_ode_guard j).jb cap
  · have eq : i=20 := by omega
    subst i
    have hf : ¬ TerminalPass Crt (word M) J := fun p =>
      lost (mem_filter.mpr ⟨prev,p⟩)
    obtain ⟨s,C,sm,inside,cap,proper⟩ := terminal_failure Crt (word M) hf
    refine ⟨C,cap,proper,?_⟩
    intro γ hγ _
    apply zero_of_contact (r:=0)
    exact contact_at_mark R.family Crt noPole
      (fun δ hd=>residues δ (mem_filter.mp hd).1) inside
      (by simpa only [Nat.mul_zero,Nat.add_zero] using Nat.sub_lt (Nat.mul_pos sm (by decide : 0<179740)) (by decide : 0<1)) γ hγ

theorem Initial.cutCover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} (hi : i<21) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape i) fee) (mass (ini.lost i))) ∧
      ∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
  have oneCut (J : Ideal Ambient) (mem : J∈ini.lost i) :
      ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈R.marks,OnMark R.family J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
    obtain ⟨P,cap,proper,zero⟩ := ini.marked_cutter noPole residues hi mem
    have prev := (mem_sdiff.mp mem).1
    rw [Initial.live,ite_eq_left hi] at prev
    let sub := R.marks.filter (OnMark R.family J)
    let G : Family M sub :=
      ⟨R.family.scalar,fun γ hγ=>R.family.mark γ (mem_filter.mp hγ).1,
        R.family.distinct.mono (filter_subset _ _)⟩
    obtain ⟨C,cost,cover⟩ := proper_cut G (cutShape i) (cutShape_fit i)
      (ini.kept_geom prev).1 cap proper
      (fun γ hγ=>zero γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2)
    exact ⟨C,cost,fun γ hγ on=>cover γ (mem_filter.mpr ⟨hγ,on⟩) on⟩
  let C (J : Ideal Ambient) : CutCover :=
    if mem : J∈ini.lost i then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈ini.lost i) :
      (∀ fee,(C J).cost fee≤dot (weight (cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈R.marks,OnMark R.family J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves,OnMark R.family Q γ := by
    simpa only [C,dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts (ini.lost i) C,?_,?_⟩
  · intro fee
    exact (joinCuts_cost _ _ _).trans ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J,mem,on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q,hQ,hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J,mem,point⟩)
    · exact Or.inr ⟨Q,mem_biUnion.mpr ⟨J,mem,hQ⟩,hmark⟩

theorem Initial.retained_or_lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {J : Ideal Ambient} (mem : J∈ini.parents) :
    J∈ini.final ∨ ∃ i<21,J∈ini.lost i := by
  by_cases h : ∃ i<21,J∈ini.lost i
  · exact Or.inr h
  · have alive : ∀ n≤21,J∈ini.live n := by
      intro n hn
      induction n with
      | zero => exact ini.live_zero.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n,by omega,mem_sdiff.mpr ⟨ih (by omega),absent⟩⟩
    exact Or.inl (by simpa [Initial.live] using alive 21 le_rfl)

theorem Initial.terminal_surfaces_with_origins {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S,∃ J∈ini.final,q.asIdeal=J.comap K1_14_2.toJet) ∧
      ∀ γ∈R.marks,(∃ J∈ini.final,OnMark R.family J γ) → ∃ q∈S,OnSurface F q γ := by
  let geom (J : ini.final) := ini.kept_geom (mem_filter.mp J.property).1
  let surface (J : ini.final) := surfaceOf J.val (geom J).1.prime
  let S := ini.final.attach.image surface
  refine ⟨S,?_,?_,?_⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩ := mem_image.mp hq
    have hJ := geom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1,(mem_filter.mp J.property).2⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩:=mem_image.mp hq
    exact ⟨J.val,J.property,rfl⟩
  · rintro γ _ ⟨J,hJ,on⟩
    let q : ini.final := ⟨J,hJ⟩
    refine ⟨surface q,mem_image.mpr ⟨q,mem_attach _ _,rfl⟩,?_⟩
    intro P mem
    rw [←K1_14_2.eval_toJet]
    exact RingHom.mem_ker.mp (on mem)

theorem Initial.terminal_surfaces {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈R.marks,(∃ J∈ini.final,OnMark R.family J γ) → ∃ q∈S,OnSurface F q γ := by
  obtain ⟨S,geom,_,marks⟩:=ini.terminal_surfaces_with_origins
  exact ⟨S,geom,marks⟩

end Lower6960.Prefix6969Wide

end
end Merged_R6960MainGeometryProcess

section Merged_R6960MainGeometryBills

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969Wide
open Finset Polynomial
open K1 (K)
open K1_14 (Jet atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass mass_mono weight dot CutCover emptyCut)
open P1_7_4 (Mass massQ massQ_mono dotQ pairedCap weightedBill bill_bound)
open Far6969RescueGeometry (Model Family OnMark label_injective beforeCuts)
open Prefix6969Rates (fixedFee fixed_count)
open scoped Classical BigOperators

def initialMass : Mass := fun k=>initialCap k

private abbrev historyTable := suppliedHistory

def history (i : ℕ) : Mass := historyTable.getD i initialMass

theorem history_zero (k : Fin 4) : history 0 k=initialMass k := by
  fin_cases k <;> decide +kernel

theorem history_step (i : Fin 20) (k : Fin 4) :
    let j : Fin 21 := ⟨i.val+1,by have := i.isLt; omega⟩
    history (i.val+1) k =
      min (history i.val k) (pairedCap (freeShape j) (movingShape j) (reserve j) true k) := by
  fin_cases i <;> fin_cases k <;> decide +kernel

theorem Initial.cap_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) (k : Fin 4) : massQ (ini.kept n) k ≤ initialMass k := by
  exact (Nat.cast_le (α:=ℚ)).mpr ((mass_mono
    ((filter_subset _ _).trans subset_union_right) k).trans (ini.fits k))

theorem Initial.cap_kept {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<21) (k : Fin 4) : massQ (ini.kept i) k≤history i k := by
  induction i with
  | zero => rw [history_zero]; exact ini.cap_initial _ _
  | succ i ih =>
    have hl : i<20 := by omega
    have hstep := history_step ⟨i,hl⟩ k
    dsimp only at hstep
    rw [hstep]
    exact le_min ((massQ_mono (ini.kept_anti (Nat.le_succ i)) k).trans (ih (by omega)))
      (ini.stage_mass ⟨i+1,hi⟩ (Nat.succ_pos _) le_rfl k)

theorem Initial.cap_live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<21) (k : Fin 4) : massQ (ini.live i) k≤history i k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_kept hi k

theorem Initial.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<21) (k : Fin 4) : massQ (ini.live i) k ≤ initialMass k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_initial _ k

def cutWeight (fee : Fin 3) (i : ℕ) : Mass := fun k=>weight (cutShape i) fee k

def seedLimit : ℚ := weightedBill 21 (cutWeight 0) history

def pointLimit : ℚ := weightedBill 21 (cutWeight 2) (fun _=>initialMass)

def initialSeedLimit : ℕ := (K1.p+1)*initialCap 2+initialCap 3

def contentLimit : ℕ := (K1.p+1)*(freeShape 0).U

def fixedLimit : ℕ :=
  ∑ i : Fin 21, (fixedFee (freeShape i).B (freeShape i).J+fixedFee (movingShape i).B (movingShape i).J)

theorem seed_limit_small : seedLimit < (K1.p : ℚ) := by decide +kernel

theorem Initial.ordinary_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>atX (R.family.scalar γ)∈ini.ordinates)).card ≤ initialCap 0 := by
  apply (card_le_card_of_injOn (fun γ=>atX (R.family.scalar γ))
    (fun _ hγ=>(mem_filter.mp hγ).2) ?_).trans ini.ordinate_cap
  intro γ hγ δ hδ eq
  exact R.family.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1
    (K1_14_3.scalar_atX_injective eq)

theorem Initial.seed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))).card ≤ initialSeedLimit := by
  have bound := K1_14_3.seed_count
    (T:=R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))) (label_injective M).injOn ini.seed
    (ini.seed_cap.trans_lt (initial_small 2)) (fun _ hγ=>(mem_filter.mp hγ).2)
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ini.seed_cap) ini.seed_points)

theorem Initial.content_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)).card≤contentLimit := by
  let C : K1_14_3.SeedCover := ⟨ini.content,ini.content_ne,∅⟩
  have bound := K1_14_3.seed_count
    (T:=R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)) (label_injective M).injOn C
    (ini.content_cap.trans_lt (free_seed_small 0)) (fun _ hγ=>Or.inl (mem_filter.mp hγ).2)
  exact (by simpa only [C,card_empty,Nat.add_zero] using bound :
    (R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)).card≤(K1.p+1)*ini.content.totalDegree)
    |>.trans (Nat.mul_le_mul_left _ ini.content_cap)

theorem Rows.fixed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (hi : M.overhead.toNat≤2389) :
    R.fixedMarks.card≤fixedLimit := by
  calc
    _ ≤ ∑ i : Fin 21, (R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation).card :=
      card_biUnion_le
    _ ≤ _ := sum_le_sum fun i _=>(card_union_le _ _).trans (Nat.add_le_add
      (Prefix6969Rates.fixed_count R.family hi (free_ode_guard i) _ (R.fixedFree i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2))
      (Prefix6969Rates.fixed_count R.family hi (moving_ode_guard i) _ (R.fixedMoving i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2)))

structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) where
  cover : ℕ→CutCover
  cost : ∀ i<21,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))
  covers : ∀ i<21,∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) →
    γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark R.family Q γ

theorem Initial.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks ini) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<21 →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))) ∧
      ∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
    by_cases hi : i<21
    · obtain ⟨C,cap,cover⟩ := ini.cutCover noPole residues hi
      exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick
  exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩

theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) {i : ℕ} (hi : i<21) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight fee i) (massQ (ini.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound

theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (∑ i∈range 21,((C.cover i).cost 0 : ℚ))≤seedLimit :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound 21 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>ini.cap_live hi))

def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K := (range 21).biUnion fun i=>(C.cover i).direct

theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (C.pointMarks.card : ℚ) ≤ pointLimit := by
  calc
    _ ≤ ∑ i∈range 21,((C.cover i).cost 2 : ℚ) := by
      exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range 21,(C.cover i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range 21,dotQ (cutWeight 2 i) (massQ (ini.lost i)) :=
      sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
    _ ≤ _ := bill_bound 21 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>ini.live_initial hi)

private def Initial.jointLive {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ℕ→Finset (Ideal Ambient)
  | 0 => ini.rankExit∪ini.parents
  | i+1 => ini.live i

private def Initial.jointLost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ℕ→Finset (Ideal Ambient)
  | 0 => ini.rankExit
  | i+1 => ini.lost i

/-- The rank exit and the seventeen cut bins spend a single weighted
history, starting from the mass of the initial proper cover. -/
theorem Initial.joint_bill_with_final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ ini.rankExit) + (∑ i∈range 21,dotQ (cut i) (massQ (ini.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) 22) (massQ ini.final) ≤
      weightedBill 22 (beforeCuts rank cut) (beforeCuts (initialMass) (history)) := by
  have bill := P1_7_4.bill_bound_with_final 22 (beforeCuts rank cut) (beforeCuts (initialMass) (history))
    ini.jointLive ini.jointLost ?_ ?_ ?_
  · rw [show 22=21+1 by decide,sum_range_succ'] at bill
    have final : ini.jointLive 22 = ini.final := by simp [Initial.jointLive,Initial.live]
    simpa only [beforeCuts,Initial.jointLost,final,add_comm] using bill
  · intro i hi
    cases i with
    | zero => simpa only [Initial.jointLive,ini.live_zero] using
        (subset_union_right : ini.parents⊆ ini.rankExit∪ini.parents)
    | succ i => exact ini.next_sub (by omega)
  · intro i hi
    cases i with
    | zero =>
      intro J mem
      apply mem_sdiff.mpr
      refine ⟨mem_union_left _ mem,?_⟩
      rw [Initial.jointLive,ini.live_zero]
      exact fun h=>(disjoint_left.mp ini.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k
    cases i with
    | zero => exact (Nat.cast_le (α:=ℚ)).mpr (ini.fits k)
    | succ i => exact ini.cap_live (by omega) k


theorem Initial.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ ini.rankExit) + (∑ i∈range 21,dotQ (cut i) (massQ (ini.lost i))) ≤
      weightedBill 22 (beforeCuts rank cut) (beforeCuts initialMass history) :=
  (le_add_of_nonneg_right (P1_7_4.final_credit_nonneg 22 (beforeCuts rank cut) ini.final)).trans
    (ini.joint_bill_with_final rank cut)

end Lower6960.Prefix6969Wide

end
end Merged_R6960MainGeometryBills

section Merged_R6960MainGeometryInvoice

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969Wide
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open Far6969RescueGeometry (beforeCuts)
open Prefix6969Rates (RateOK curveUnit endpointDegree)
open scoped Classical BigOperators

abbrev degreeRates := suppliedDegreeRates
abbrev heightRates := suppliedHeightRates

def lambda : ℚ := ((262144 : ℚ) / 179740) * endpointDegree
def mu : ℚ := ((262144 - endpointDegree : ℕ) : ℚ) / (179740 - endpointDegree : ℕ)
def tau : ℚ := 1 / 2

def degreeRate (i : ℕ) : ℕ := degreeRates.getD i 0

def heightRate (i : ℕ) : ℕ := heightRates.getD i 0

private def heightTerms (a : ℕ) : List ℚ :=
  (List.range 80).map (fun i : ℕ =>
    let g := i+1
    max 0 (1-(a : ℚ)*(g : ℚ)/((p+1 : ℕ) : ℚ))*curveUnit g)

def heightBound (a : ℕ) : ℚ := (heightTerms a).foldr max 0

private theorem le_max_fold {q : ℚ} {terms : List ℚ} (mem : q∈terms) :
    q ≤ terms.foldr max 0 := by
  induction terms with
  | nil => simp at mem
  | cons a rest ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | h
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem height_spec (a g : ℕ) (pos : 0<g) (small : g≤80) :
    max 0 (1-(a : ℚ)*g/((p+1 : ℕ) : ℚ))*curveUnit g≤heightBound a := by
  apply le_max_fold
  unfold heightTerms
  apply List.mem_map.mpr
  refine ⟨g-1,List.mem_range.mpr (by omega),?_⟩
  dsimp only
  rw [Nat.sub_add_cancel (by omega : 1≤g)]

private theorem checked_rates (i : Fin 21) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate i.val : ℚ) ∧
      min seedLimit (dotQ (cutWeight 0 i.val) (history i.val)) ≤ (degreeRate i.val : ℚ) ∧
      heightBound (degreeRate i.val) ≤ (heightRate i.val : ℚ) := by
  fin_cases i <;> decide +kernel

theorem rate_spec {i : ℕ} (hi : i<21) :
    RateOK (degreeRate i) (heightRate i) ∧
      min seedLimit (dotQ (cutWeight 0 i) (history i)) ≤ degreeRate i := by
  obtain ⟨base,degree,height⟩ := checked_rates ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def rankB : ℕ := initialCap 2+2

def rankJ : ℕ := initialCap 1+1

def pivot : ℚ := min ((3/5 : ℚ) * rankJ) (tau*rankB)

def rankWeight : Mass :=
  ![0,4*lambda*rankB*tau+mu-4*lambda*pivot,4*lambda*rankJ*(1-tau)+rankB,0]

def rankRound : ℚ := rankWeight 1+2*rankWeight 2+2*lambda*pivot^2+1

def lossWeight (i : ℕ) : Mass :=
  fun k=>(degreeRate i : ℚ)*cutWeight 0 i k+(heightRate i : ℚ)*cutWeight 1 i k

def lossLimit : ℚ :=
  weightedBill 22 (beforeCuts rankWeight lossWeight) (beforeCuts initialMass history)+seedLimit+rankRound

def mainFee : ℕ := lossLimit.ceil.toNat+pointLimit.ceil.toNat+initialSeedLimit+initialCap 0+
  fixedLimit+contentLimit

theorem main_fee_exact : mainFee = prefixCap := by decide +kernel

theorem retained_credit_guard (k : Fin 4) :
    (retainedCredit k : ℚ) ≤ P1_7_4.running (beforeCuts rankWeight lossWeight) 22 k := by
  fin_cases k <;> decide +kernel

theorem rank_guard : rankB<p ∧ 0≤rankWeight 1 ∧ 0≤rankWeight 2 := by decide +kernel

end Lower6960.Prefix6969Wide

end
end Merged_R6960MainGeometryInvoice
end Z6969Source0602

-- Source: Research6969.PrefixWide
section Z6969Source0603
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960MainGeometryFee
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.Prefix6969Wide
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient ODE)
open K1_14_2_2 (mass mass_mono ODECaps)
open K1_14_3 (Surface Parent)
open P1_7_4 (ODEGuard Mass massQ dotQ dotQ_mono_mass massQ_mono dotQ_scale_add)
open HighCore82268JointRank (fixed_fee_linear)
open Far6969RescueGeometry (Model Family OnMark OnSurface word beforeCuts)
open Prefix6969Rates (curveMarks mem_curveMarks curve_tariff rated_curve_count fixedFee fixed_count
  persistentTotal persistentTop siteRatio density endpointDegree)
open P1_7_4_3 (mix)
open scoped Classical BigOperators
theorem fixedFee_eq (B J : ℕ) :
    fixedFee B J = (mix B J (mu+2*lambda*(B-1 : ℕ))
      (min (mu+2*lambda*(B-1 : ℕ)) (lambda*(2*J-1 : ℕ)))).ceil.toNat+B^2 := by
  have he : 2*density*(endpointDegree : ℚ)=2*lambda := by unfold lambda density; ring
  have hl : density*(endpointDegree : ℚ)=lambda := rfl
  have hm : siteRatio endpointDegree=mu := rfl
  unfold fixedFee persistentTop persistentTotal
  rw [he,hl,hm]
def Initial.rankMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>∃ J∈ini.rankExit,OnMark R.family J γ)
theorem Initial.rank_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) (hi : M.overhead.toNat≤2389) :
    (ini.rankMarks.card : ℚ)≤dotQ rankWeight (massQ ini.rankExit)+rankRound := by
  let S := ini.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨E,caps,roots⟩ := ini.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ initialCap k :=
    (mass_mono (subset_union_left : S⊆ini.rankExit∪ini.parents) k).trans (ini.fits k)
  have hBm : B≤mass S 2+2 := max_le (by omega) (by omega)
  have hJm : J≤mass S 1+1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B≤rankB := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J≤rankJ := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
  have hB2 : 2≤B := le_max_left _ _
  have hJ1 : 1≤J := le_max_left _ _
  have hJB : J≤B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree≤B := by
    have top : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree≠0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1,(le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  obtain ⟨small,cJ,cB⟩ := rank_guard
  have guard : ODEGuard B J := ⟨hB2,hJ1,hJB,hB.trans_lt small⟩
  have count : ini.rankMarks.card≤fixedFee B J :=
    Prefix6969Rates.fixed_count R.family hi guard E ocaps (filter_subset _ _)
      (fun γ mem => roots γ (mem_filter.mp mem).1 (mem_filter.mp mem).2)
  have lin := fixed_fee_linear lambda mu tau pivot (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤
      rankWeight 1 * J + rankWeight 2 * B + 2*lambda*pivot^2+1 := by
    rw [fixedFee_eq]
    exact lin
  have hJq : (J : ℚ)≤(mass S 1 : ℚ)+1 := by exact_mod_cast hJm
  have hBq : (B : ℚ)≤(mass S 2 : ℚ)+2 := by exact_mod_cast hBm
  have hjfee := mul_le_mul_of_nonneg_left hJq cJ
  have hbfee := mul_le_mul_of_nonneg_left hBq cB
  have hdot : dotQ rankWeight (massQ ini.rankExit) =
      rankWeight 1 * (mass S 1 : ℚ)+rankWeight 2 * (mass S 2 : ℚ) := by
    simp [dotQ,rankWeight,massQ,Fin.sum_univ_succ,S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [hdot,rankRound]
  linarith only [hjfee,hbfee]
private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ)≤q) : a≤q.ceil.toNat := by
  have ceil_cast : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans ceil_cast)
theorem CutBooks.curve_bin_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hiM : M.overhead.toNat≤2389) {i : ℕ} (hi : i<21) :
    ((curveMarks R.family (C.cover i)).card : ℚ)≤
      dotQ (lossWeight i) (massQ (ini.lost i))+((C.cover i).cost 0 : ℚ) := by
  have global : ((C.cover i).cost 0 : ℚ)≤seedLimit :=
    (single_le_sum (fun j _=>Nat.cast_nonneg (α:=ℚ) ((C.cover j).cost 0))
      (mem_range.mpr hi)).trans C.seed_bill
  have localCap : ((C.cover i).cost 0 : ℚ)≤ dotQ (cutWeight 0 i) (history i) :=
    (C.costQ hi 0).trans (dotQ_mono_mass (fun _=>Nat.cast_nonneg _)
      (fun k=>(massQ_mono sdiff_subset k).trans (ini.cap_live hi k)))
  have prime : (C.cover i).cost 0 < p := by exact_mod_cast global.trans_lt seed_limit_small
  obtain ⟨ok,degree⟩ := rate_spec hi
  have count := rated_curve_count R.family (curve_tariff R.family hiM) ok (C.cover i)
    global ((min_le_min le_rfl localCap).trans degree) prime
  calc
    _ ≤ (degreeRate i : ℚ)*((C.cover i).cost 0 : ℚ) +
          (heightRate i : ℚ)*((C.cover i).cost 1 : ℚ)+((C.cover i).cost 0 : ℚ) := count
    _ ≤ (degreeRate i : ℚ)*dotQ (cutWeight 0 i) (massQ (ini.lost i)) +
          (heightRate i : ℚ)*dotQ (cutWeight 1 i) (massQ (ini.lost i)) +
          ((C.cover i).cost 0 : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (C.costQ hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (C.costQ hi 1) (Nat.cast_nonneg _))) le_rfl
    _ = _ := by rw [dotQ_scale_add]; rfl
def CutBooks.lossMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R} (C : CutBooks ini) :
    Finset K := ini.rankMarks ∪ (range 21).biUnion (fun i=>curveMarks R.family (C.cover i))
/-- The retained weight is charged on every component of the terminal parent mass. -/
def retainedCharge (S : Finset (Ideal Ambient)) : ℕ :=
  ∑ k : Fin 4, retainedCredit k * mass S k

theorem retainedCharge_cast_le (S : Finset (Ideal Ambient)) :
    (retainedCharge S : ℚ) ≤
      dotQ (P1_7_4.running (beforeCuts rankWeight lossWeight) 22) (massQ S) := by
  unfold retainedCharge dotQ massQ
  push_cast
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
    (retained_credit_guard k) (Nat.cast_nonneg _))

theorem CutBooks.loss_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hi : M.overhead.toNat≤2389) : C.lossMarks.card + retainedCharge ini.final ≤ lossLimit.ceil.toNat := by
  apply card_round
  have cum : (C.lossMarks.card : ℚ) ≤ (ini.rankMarks.card : ℚ) +
      ∑ i∈range 21,((curveMarks R.family (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ ini.rankMarks.card +
      ∑ i∈range 21,(curveMarks R.family (C.cover i)).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have sum_cuts := sum_le_sum (fun _ mem=>C.curve_bin_count hi (mem_range.mp mem))
    (s:=range 21)
  rw [sum_add_distrib] at sum_cuts
  have both := add_le_add (ini.rank_count hi) sum_cuts
  have joint := ini.joint_bill_with_final rankWeight lossWeight
  have seed := C.seed_bill
  have total := cum.trans both
  have retained := retainedCharge_cast_le ini.final
  push_cast
  unfold lossLimit
  linarith only [total, joint, seed, retained]
def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))
def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>atX (R.family.scalar γ)∈ini.ordinates)
def Initial.contentMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)
def CutBooks.paid {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K :=
  (C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks) ∪ (R.fixedMarks ∪ ini.contentMarks)
theorem CutBooks.paid_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hi : M.overhead.toNat≤2389) : C.paid.card + retainedCharge ini.final ≤ mainFee := by
  have combined := card_union_le
    ((C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks)) (R.fixedMarks ∪ ini.contentMarks)
  have left := card_union_le (C.lossMarks ∪ C.pointMarks) (ini.seedMarks ∪ ini.ordinateMarks)
  have cuts := card_union_le C.lossMarks C.pointMarks
  have low := card_union_le ini.seedMarks ini.ordinateMarks
  have fixed := card_union_le R.fixedMarks ini.contentMarks
  have loss := C.loss_count hi
  have points := card_round C.point_bill
  have seeds : ini.seedMarks.card ≤ initialSeedLimit := ini.seed_count
  have ordinates : ini.ordinateMarks.card ≤ initialCap 0 := ini.ordinary_count
  have content : ini.contentMarks.card ≤ contentLimit := ini.content_count
  have fixedCard := R.fixed_count hi
  unfold mainFee CutBooks.paid
  omega
theorem Rows.main_prefix {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (hi : M.overhead.toNat≤2389) (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (ini : Initial R) (C : CutBooks ini) (S : Finset Surface),
      C.paid.card + retainedCharge ini.final ≤ prefixCap ∧
      (∀ k, massQ ini.final k ≤ history 20 k) ∧
      (∀ q∈S, Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S, ∃ J∈ini.final, q.asIdeal = J.comap K1_14_2.toJet) ∧
      ∀ γ∈R.marks, γ∈C.paid ∨ ∃ q∈S, OnSurface F q γ := by
  obtain ⟨ini⟩ := R.initial_cover
  obtain ⟨C⟩ := ini.cutBooks noPole residues
  obtain ⟨S, geom, origin, surface⟩ := ini.terminal_surfaces_with_origins
  refine ⟨ini, C, S, main_fee_exact ▸ C.paid_count hi, ?_, geom, origin, ?_⟩
  intro k
  exact (massQ_mono (filter_subset _ _) k).trans (ini.cap_kept (by decide) k)
  intro γ hγ
  rcases ini.covers γ hγ with fixed | content | seed | ord | rank | ⟨J,mem,on⟩
  · exact Or.inl (mem_union_right _ (mem_union_left _ fixed))
  · exact Or.inl (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hγ,content⟩)))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hγ,seed⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hγ,ord⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _
      (mem_union_left _ (mem_filter.mpr ⟨hγ,rank⟩)))))
  · rcases ini.retained_or_lost mem with final | ⟨i,hi,lost⟩
    · exact Or.inr (surface γ hγ ⟨J,final,on⟩)
    · rcases C.covers i hi γ hγ ⟨J,lost,on⟩ with point | ⟨Q,hQ,hmark⟩
      · have mark : γ∈C.pointMarks := mem_biUnion.mpr ⟨i,mem_range.mpr hi,point⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ mark)))
      · have mark : γ∈(range 21).biUnion (fun i=>curveMarks R.family (C.cover i)) :=
          mem_biUnion.mpr ⟨i,mem_range.mpr hi,mem_curveMarks (F:=R.family) hγ hQ hmark⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ mark))))
/-- Construct the actual wide prefix from the model's CRT data and the verified banks. -/
theorem main_prefix {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (R : Rows F Crt) (ini : Initial R) (C : CutBooks ini) (S : Finset Surface),
      C.paid.card + retainedCharge ini.final ≤ prefixCap ∧
      (∀ k, massQ ini.final k ≤ history 20 k) ∧
      (∀ q∈S, Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S, ∃ J∈ini.final, q.asIdeal = J.comap K1_14_2.toJet) ∧
      ∀ γ∈R.marks, γ∈C.paid ∨ ∃ q∈S, OnSurface F q γ := by
  obtain ⟨R⟩ := rows F Crt lo hi noPole residues
  obtain ⟨ini, C, S, paid, massCap, regular, origins, covered⟩ :=
    R.main_prefix hi noPole residues
  exact ⟨R, ini, C, S, paid, massCap, regular, origins, covered⟩

end Lower6960.Prefix6969Wide

end
end Merged_R6960MainGeometryFee
end Z6969Source0603

-- Source: Research6969.PrefixMiddleRates
section Z6969Source0604
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960RescueGeometryTariffs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969MiddleRates
open Far6969RescueGeometry (Model Family label_injective OnMark)
open Finset Polynomial ProximityPrize.Benchmark
open P1 (K I node p)
open K1_14 (Shape FX Seeds)
open K1_14_2 (ODE fixedAt RootSeedSection SeedField)
open K1_14_2_2 (ODECaps)
open K1_14_2_4 (taylorPower ordinateBound)
open P1_7_3 (persistentNodes hits_persistent section_bounds regular_chart persistent_taylor)
open P1_7_4 (ODEGuard)
open P1_7_4_3 (mix mix_eq cast_mixed short_cut)
open K1_13 (Geom Row extend embed)
open K1_13_5 (RegularAt)
open K1_13_5_3
open K1_14_2_5 (clear_equation factor_cover)
open K1_14_3_6 (power totalCap topCap)
open scoped Classical BigOperators

private abbrev agreement : ℕ := 179740
private abbrev blockLength : ℕ := 262144
abbrev endpointDegree : ℕ := 133605

structure FixedWord (w : I → K) (U : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop where
  distinct : Set.InjOn s (U : Set K)
  degree : ∀ γ ∈ U, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ U, ∃ B : Finset I, agreement ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
theorem persistent_card_le {w U s d} (hw : FixedWord w U s d) (hU : 1 < U.card) :
    (persistentNodes w U s).card ≤ d := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hU
  let P := s a - s b
  have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (hw.distinct ha hb eq)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective P hp _ ?_).trans
    ((natDegree_sub_le _ _).trans (max_le (hw.degree a ha) (hw.degree b hb)))
  intro i hi
  change ((s a) - (s b)).eval (node i) = 0
  rw [Polynomial.eval_sub, hits_persistent ha hi, hits_persistent hb hi, sub_self]
theorem section_incidence {w U s d} (hw : FixedWord w U s d) (D : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ U, (s γ).eval (node i) ≠ w i) →
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ D) :
    (agreement - (persistentNodes w U s).card) * U.card ≤
      (blockLength - (persistentNodes w U s).card) * D := by
  classical
  let sites := persistentNodes w U s
  let nodes : Finset I := univ \ sites
  let hits (γ : K) := nodes.filter fun i => (s γ).eval (node i) = w i
  let occ (i : I) := U.filter fun γ => (s γ).eval (node i) = w i
  have hhit (γ : K) (hγ : γ ∈ U) : agreement - sites.card ≤ (hits γ).card := by
    obtain ⟨B, hB, hvals⟩ := hw.hits γ hγ
    let good : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
    have hgood : agreement ≤ good.card :=
      hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hvals i hi⟩)
    have hZG : sites ⊆ good := fun i hi => mem_filter.mpr ⟨mem_univ _, hits_persistent hγ hi⟩
    have heq : hits γ = good \ sites := by
      ext i
      simp only [hits, nodes, good, mem_filter, mem_sdiff, mem_univ, true_and]
      exact and_comm
    rw [heq, card_sdiff_of_subset hZG]
    exact Nat.sub_le_sub_right hgood _
  have hnodes : nodes.card = blockLength - sites.card := by
    rw [card_sdiff_of_subset (subset_univ sites), card_univ, IRSProfile.card_index]
  calc
    _ = ∑ γ ∈ U, (agreement - sites.card) := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ γ ∈ U, (hits γ).card := sum_le_sum hhit
    _ = ∑ i ∈ nodes, (occ i).card := by simp only [hits, occ, card_filter]; rw [sum_comm]
    _ ≤ ∑ _i ∈ nodes, D := by
      apply sum_le_sum
      intro i hi
      apply hsection i
      by_contra! h
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
    _ = _ := by rw [sum_const, smul_eq_mul, hnodes]
private def rho (s : ℕ) : ℚ :=
  ((blockLength - s : ℕ) : ℚ) / ((agreement - s : ℕ) : ℚ)
abbrev density : ℚ := (blockLength : ℚ) / agreement
private theorem weights {s d : ℕ} (hs : s ≤ d) (hd : d < agreement)
    (haux : rho d ≤ density * d) :
    rho s ≤ rho d ∧ rho s * (max 1 (d-s) : ℕ) ≤ density * d := by
  have hAN : agreement ≤ blockLength := by decide
  have hsA := hs.trans_lt hd
  have hdN := hd.le.trans hAN
  have hsN := hs.trans hdN
  have hAs : (0 : ℚ) < (agreement : ℚ) - s := sub_pos.mpr (by exact_mod_cast hsA)
  have hAd : (0 : ℚ) < (agreement : ℚ) - d := sub_pos.mpr (by exact_mod_cast hd)
  have hmain : rho s ≤ rho d := by
    unfold rho
    rw [Nat.cast_sub hsN, Nat.cast_sub hsA.le, Nat.cast_sub hdN, Nat.cast_sub hd.le]
    apply (div_le_div_iff₀ hAs hAd).mpr
    have h := mul_nonneg (sub_nonneg.mpr (show (s : ℚ) ≤ d by exact_mod_cast hs))
      (sub_nonneg.mpr (show (agreement : ℚ) ≤ blockLength by exact_mod_cast hAN))
    nlinarith only [h]
  refine ⟨hmain, ?_⟩
  by_cases heq : s = d
  · subst s
    simpa using haux
  have hpos : 1 ≤ d - s := by omega
  rw [max_eq_right hpos]
  have hden : (0 : ℚ) < (agreement : ℚ) := by exact_mod_cast (by decide : 0 < agreement)
  have hfrac : ((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ) ≤ (d : ℚ) / agreement := by
    rw [Nat.cast_sub hs, Nat.cast_sub hsA.le]
    apply (div_le_div_iff₀ hAs hden).mpr
    have h := mul_nonneg (Nat.cast_nonneg s : (0 : ℚ) ≤ s) hAd.le
    nlinarith only [h]
  calc
    _ = ((blockLength-s : ℕ) : ℚ) * (((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ)) := by
      unfold rho
      ring
    _ ≤ (blockLength : ℚ) * ((d : ℚ) / agreement) :=
      mul_le_mul (by exact_mod_cast Nat.sub_le blockLength s) hfrac (by positivity) (by positivity)
    _ = density * d := by ring
private theorem rho_at_endpoint {d : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 133605) :
    rho d ≤ density * d := by
  have hdA : d < agreement := hh.trans_lt (by decide)
  have hdN : d ≤ blockLength := hh.trans (by decide)
  have hrho : rho d ≤ 17 := by
    unfold rho
    have hp : (0 : ℚ) < ((agreement - d : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hdA
    apply (div_le_iff₀ hp).mpr
    rw [Nat.cast_sub hdN, Nat.cast_sub hdA.le]
    change (262144 : ℚ) - d ≤ 17 * ((179740 : ℚ) - d)
    have hQ : (d : ℚ) ≤ 133605 := by exact_mod_cast hh
    linarith only [hQ]
  have hDensity : 1 ≤ density := by
    apply (le_div_iff₀ (show (0 : ℚ) < (agreement : ℚ) by positivity)).mpr
    rw [one_mul]
    exact_mod_cast (by decide : agreement ≤ blockLength)
  exact hrho.trans (calc
    (17 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (show 17 ≤ d by omega)
    _ = 1 * (d : ℚ) := (one_mul _).symm
    _ ≤ density * d := mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg _))
private theorem taylorPower_cast {g : ℕ} (hg : 0 < g) :
    (taylorPower g : ℚ) = 2 * (g : ℚ) - 1 := by
  unfold taylorPower
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl
private theorem regular_count {n g H d : ℕ} {U : Finset K} {s : K → Polynomial K} {w}
    (A : K1_14_2_4.RegularChart U s g H n) (hw : FixedWord w U s d)
    (hg : 0 < g) (hl : 131071 ≤ d) (hh : d ≤ 133605) :
    (U.card : ℚ) ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * H + 1 := by
  have hbound : 0 ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * (H : ℚ) := by
    unfold rho
    positivity
  by_cases hc : U.card ≤ 1
  · have h : (U.card : ℚ) ≤ 1 := by exact_mod_cast hc
    linarith only [h, hbound]
  let sites := persistentNodes w U s
  let t := max 1 (d-sites.card)
  have hd : d < agreement := hh.trans_lt (by decide)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left _ _)
  have htp : t < p := (max_le (by omega : 1 ≤ d) (Nat.sub_le _ _)).trans_lt
    (hh.trans_lt (by decide))
  have hdt : d ≤ sites.card + t := by
    have h := le_max_right 1 (d-sites.card)
    omega
  obtain ⟨C, hreconstruct⟩ := persistent_taylor sites w hdt htp hg A.equation A.equation_degree
  let D := taylorPower t * (g * H) + ordinateBound t g * H
  have hsection := section_bounds (w := w) A ht hw.distinct C fun γ hγ =>
    hreconstruct _ _ (hw.degree γ hγ) (fun _ hi => hits_persistent hγ hi) (A.root γ hγ) (A.simple γ hγ)
  have hinc : ((agreement - sites.card : ℕ) : ℚ) * U.card ≤ ((blockLength - sites.card : ℕ) : ℚ) * D := by
    exact_mod_cast section_incidence hw D hsection
  have hden : (0 : ℚ) < ((agreement - sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hcard : (U.card : ℚ) ≤ rho sites.card * (D : ℚ) := by
    rw [rho, div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    calc
      _ = ((agreement - sites.card : ℕ) : ℚ) * U.card := mul_comm _ _
      _ ≤ _ := hinc
  obtain ⟨hρ, hρt⟩ := weights hs hd (rho_at_endpoint hl hh)
  have hρb : rho sites.card * (taylorPower t : ℚ) ≤ 2 * density * d := by
    have hb : (taylorPower t : ℚ) ≤ 2 * (t : ℚ) := by
      exact_mod_cast (Nat.sub_le (2*t) 1 : taylorPower t ≤ 2*t)
    have hρ0 : 0 ≤ rho sites.card := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h := mul_le_mul_of_nonneg_left hb hρ0
    nlinarith only [h, hρt]
  have hsum : g + (g - 1) = taylorPower g := by unfold taylorPower; omega
  have hD : D = (taylorPower t * taylorPower g + 1) * H := by
    rw [← hsum]
    dsimp [D, ordinateBound]
    ring
  refine hcard.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
  calc
    _ = (rho sites.card * (taylorPower t : ℚ) * (taylorPower g : ℚ) + rho sites.card) * H := by
      rw [hD]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_right hρb (Nat.cast_nonneg _)) hρ) (Nat.cast_nonneg _)

/-- Degree and agreement at the new upper height, for an arbitrary set
of marks from the actual anchored family. -/
theorem fixed_word {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2534) {T : Finset K} (hT : T⊆Γ) :
    FixedWord M.word T F.scalar endpointDegree where
  distinct := F.distinct.mono hT
  degree := by
    intro γ hγ
    rcases (F.mark γ (hT hγ)).scalar_degree with zero | bound
    · simp [zero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at bound
      change (F.scalar γ).natDegree≤133605
      omega
  hits := by
    intro γ hγ
    let A := F.mark γ (hT hγ)
    exact ⟨A.bad.support,A.bad.agreement,A.scalar_hits⟩

def curveUnit (g : ℕ) : ℚ :=
  (2*(g : ℚ)-1)*(1+2*density*endpointDegree)+rho endpointDegree

def CurveTariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) : Prop :=
  ∀ T⊆Γ,∀ J g H,0<g → g≤80 →
    K1_14_2.SmallRootCurve J g H →
    Module.finrank SeedField (RootSeedSection J)<p →
    (∀ γ∈T,K1_14_2.OnRoot J (M.label γ) (F.scalar γ)) →
    (T.card : ℚ)≤curveUnit g*H+g

theorem curve_tariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2534) : CurveTariff F := by
  intro T hT J g H hg hgLimit hcurve _ hmarks
  obtain ⟨U,hU,hexc,n,⟨A⟩⟩ := regular_chart T M.label F.scalar J g H hg
    (hgLimit.trans_lt (by decide)) hcurve (label_injective M).injOn hmarks
  have hregular := regular_count A (fixed_word F hi (hU.trans hT)) hg (by decide) (by decide)
  have hgQ : (1 : ℚ)≤g := by exact_mod_cast hg
  have hexcQ : ((T \ U).card : ℚ)≤(taylorPower g : ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card : ℚ) = ((T \ U).card : ℚ)+(U.card : ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*endpointDegree*(taylorPower g : ℚ)+rho endpointDegree)*H+1) :=
      add_le_add hexcQ hregular
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*endpointDegree*(taylorPower g : ℚ)+rho endpointDegree)*H+g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _ = curveUnit g*H+g := by rw [taylorPower_cast hg]; unfold curveUnit; ring

theorem section_bound {w : I → K} {T : Finset K} {s : K → (Polynomial K)} {d a v : ℕ}
    (hw : FixedWord w T s d) (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) (ha : 0 < a) (hv : 0 < v)
    (i : I) (hmiss : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i)
    (cut : MvPolynomial (Fin 2) CenterField)
    (hcut : cut ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 a v)
    (heval : ∀ γ ∈ T, MvPolynomial.aeval (marked (extend (s γ))) cut = 0 ↔
      (s γ).eval (node i) = w i) :
    (T.filter fun γ => (s γ).eval (node i) = w i).card ≤
      MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) a v := by
  classical
  let x (γ : K) := marked (extend (s γ))
  have hx : Set.InjOn x (T : Set K) := fun _ ha _ hb heq =>
    hw.distinct ha hb (Polynomial.map_injective _ embed.injective (marked_injective heq))
  have hroot (γ : K) (hγ : γ ∈ T) : MvPolynomial.aeval (x γ) (plane f) = 0 := by
    dsimp only [x]
    rw [aeval_plane, (hreg γ hγ).1, map_zero]
  have hproper : cut ∉ Ideal.span {plane f} := by
    obtain ⟨η, hη, hbad⟩ := hmiss
    intro hmem
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
    exact hbad ((heval η hη).mp (by rw [hq, map_mul, hroot η hη, zero_mul]))
  let hits := T.filter fun γ => (s γ).eval (node i) = w i
  have hplane : plane f ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      f.totalDegree (f.degreeOf 1) := by
    intro m hm
    have hm' := MvPolynomial.support_map_subset toCenter f hm
    exact ⟨MvPolynomial.le_totalDegree hm', MvPolynomial.monomial_le_degreeOf 1 hm'⟩
  have hc := capped_cut_card ha hv (plane_ne_zero hf.ne_zero) (plane_prime hf hfpos)
    hplane hcut hproper (hits.image x) (by
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hγT, hγi⟩ := Finset.mem_filter.mp hγ
      exact ⟨hroot γ hγT, (heval γ hγT).mpr hγi⟩)
  rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hc

theorem fixed_bound {w T s d B J} (hw : FixedWord w T s d) (guard : ODEGuard B J)
    (G : ODE) (hG : ODECaps G B J) (hroot : ∀ γ ∈ T, fixedAt G (s γ) = 0)
    (a v : ℚ) (hv : 0 ≤ v) (hva : v ≤ a)
    (count : ∀ U ⊆ T, ∀ f : Row 2, Irreducible f → 0 < f.degreeOf 1 →
      f.totalDegree ≤ B → f.degreeOf 1 ≤ J →
      (∀ γ ∈ U, RegularAt 1 f (extend (s γ))) →
      (U.card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1) :
    (T.card : ℚ) ≤ mix B J a v + (B^2 : ℕ) := by
  classical
  obtain ⟨q, hq, hb, hj, hsolve⟩ := clear_equation G hG.1 hG.2.1 hG.2.2
  obtain ⟨A, R, hA, hAb, hAj, hR, hRd, hcover⟩ :=
    factor_cover q hq guard.bmin guard.small hb hj
  let ordinary := T.filter fun γ => R.eval (extend (s γ)) = 0
  let reg (g : Row 2) := T.filter fun γ => RegularAt 1 g (extend (s γ))
  have hord : ordinary.card ≤ B * (B - 1) := by
    let v (γ : K) := extend (s γ)
    have hinj : Set.InjOn v (ordinary : Set K) := fun _ ha _ hb he =>
      hw.distinct (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective he)
    have hcard : (ordinary.image v).card ≤ R.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      exact (Polynomial.mem_roots hR).mpr (Finset.mem_filter.mp hγ).2
    rw [Finset.card_image_of_injOn hinj] at hcard
    exact hcard.trans hRd
  have htotal : T.card ≤ ordinary.card + ∑ g ∈ A, (reg g).card := by
    have hsub : T ⊆ ordinary ∪ A.biUnion reg := by
      intro γ hγ
      rcases hcover _ (hsolve _ (hroot γ hγ)) with hr | ⟨g, ha, hr⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hr⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨g, ha, Finset.mem_filter.mpr ⟨hγ, hr⟩⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hnum : A.card ≤ B := by
    calc
      A.card = ∑ _ ∈ A, 1 := by simp
      _ ≤ ∑ g ∈ A, g.totalDegree := Finset.sum_le_sum fun g hg =>
        (hA g hg).2.trans_le (g.degreeOf_le_totalDegree 1)
      _ ≤ B := hAb
  have hlocal (f : Row 2) (hf : f ∈ A) :
      ((reg f).card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1 :=
    count (reg f) (Finset.filter_subset _ _) f (hA f hf).1 (hA f hf).2
      ((Finset.single_le_sum (fun g _ => Nat.zero_le g.totalDegree) hf).trans hAb)
      ((Finset.single_le_sum (fun g _ => Nat.zero_le (g.degreeOf 1)) hf).trans hAj)
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hreg : (∑ g ∈ A, ((reg g).card : ℚ)) ≤ mix B J a v + B := by
    refine (Finset.sum_le_sum hlocal).trans ?_
    simp only [mix_eq (MvPolynomial.degreeOf_le_totalDegree _ _), mix_eq guard.jb,
      Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hbt : (∑ g ∈ A, (g.totalDegree : ℚ)) ≤ B := by exact_mod_cast hAb
    have hjt : (∑ g ∈ A, (g.degreeOf 1 : ℚ)) ≤ J := by exact_mod_cast hAj
    have hnr : (A.card : ℚ) ≤ B := by exact_mod_cast hnum
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hbt hv)
      (mul_le_mul_of_nonneg_right hjt (sub_nonneg.mpr hva))) hnr
  have hbox : B * (B-1) + B = B^2 := by
    calc
      _ = B * ((B-1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans guard.bmin), pow_two]
  have hs : (T.card : ℚ) ≤ ordinary.card + ∑ g ∈ A, ((reg g).card : ℚ) := by exact_mod_cast htotal
  have ho : (ordinary.card : ℚ) ≤ (B * (B-1) : ℕ) := by exact_mod_cast hord
  have hboxQ : (↑(B * (B-1) : ℕ) : ℚ) + B = (B^2 : ℕ) := by exact_mod_cast hbox
  linarith only [hs,ho,hreg,hboxQ]



private theorem word_subset {w T s d} (hw : FixedWord w T s d) {U : Finset K}
    (hU : U ⊆ T) : FixedWord w U s d :=
  ⟨hw.distinct.mono hU, fun γ hγ => hw.degree γ (hU hγ), fun γ hγ => hw.hits γ (hU hγ)⟩
def siteRatio (m : ℕ) : ℚ :=
  ((blockLength - m : ℕ) : ℚ) / ((agreement - m : ℕ) : ℚ)
def persistentTotal (d B : ℕ) : ℚ := siteRatio d + 2 * density * d * (B-1 : ℕ)
def persistentTop (d B J : ℕ) : ℚ :=
  min (persistentTotal d B) (density * d * (2*J-1 : ℕ))
private theorem persistentTotal_nonneg (d B : ℕ) : 0 ≤ persistentTotal d B := by
  unfold persistentTotal siteRatio
  positivity
private theorem caps_weighted {d m B J : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 133605)
    (hm : m ≤ d) (hJ : 0 < J) :
    let t := max 1 (d-m)
    siteRatio m * totalCap t B ≤ persistentTotal d B ∧
      siteRatio m * topCap t B J ≤ persistentTop d B J := by
  let t := max 1 (d-m)
  have hd : d < agreement := hh.trans_lt (by decide)
  obtain ⟨hMu, hLambda⟩ := weights hm hd (rho_at_endpoint hl hh)
  change siteRatio m ≤ siteRatio d at hMu
  change siteRatio m * t ≤ density * d at hLambda
  have hRatio : 0 ≤ siteRatio m := by unfold siteRatio; positivity
  have hp : (power t : ℚ) ≤ 2 * (t : ℚ) := by
    exact_mod_cast (Nat.sub_le (2 * t) 3)
  have hpow : siteRatio m * power t ≤ 2 * (density * d) := by
    have h := mul_le_mul_of_nonneg_left hp hRatio
    linarith only [h,hLambda]
  have htot : siteRatio m * totalCap t B ≤ persistentTotal d B := by
    unfold totalCap persistentTotal
    push_cast
    rw [mul_add, mul_one, ← mul_assoc, show 2 * density * (d : ℚ) = 2 * (density * d) from
      mul_assoc _ _ _]
    exact add_le_add hMu (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  refine ⟨htot, ?_⟩
  unfold persistentTop
  apply le_min
  · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast
      (show topCap t B J ≤ totalCap t B from min_le_left _ _)) hRatio).trans htot
  · have hcap : topCap t B J ≤ t * (2*J-1) := by
      apply (min_le_right _ _).trans
      rw [show 2*J-1 = 2*(J-1)+1 by omega, Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right ((Nat.mul_le_mul_right _ (Nat.sub_le (2*t) 3)).trans_eq (by ring)) _
    calc
      _ ≤ siteRatio m * ((t * (2*J-1) : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) hRatio
      _ = (siteRatio m * t) * (2*J-1 : ℕ) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLambda (Nat.cast_nonneg _)
private theorem persistent_regular {w T s d B J} (hw : FixedWord w T s d)
    (hl : 131071 ≤ d) (hh : d ≤ 133605) (hJ : 0 < J)
    (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hb : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) :
    (T.card : ℚ) ≤
      mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) + 1 := by
  have hpos : 0 ≤ mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) := by
    have ha : 0 ≤ persistentTotal d B := persistentTotal_nonneg d B
    have hv : 0 ≤ persistentTop d B J := le_min ha (by positivity)
    unfold mix
    positivity
  by_cases hsmall : T.card ≤ 1
  · exact (show (T.card : ℚ) ≤ 1 from by exact_mod_cast hsmall).trans (by linarith only [hpos])
  let sites := persistentNodes w T s
  let t := max 1 (d-sites.card)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : t ≤ d := max_le (by omega) (Nat.sub_le _ _)
  have htpos : 0 < t := (Nat.le_max_left _ _)
  have hsum : d ≤ sites.card + t := by
    have h := Nat.le_max_right 1 (d-sites.card)
    omega
  have hd : d < agreement := hh.trans_lt (by decide)
  have hdp := hd.trans (by decide : agreement < p)
  have ha : 0 < totalCap t B := by simp [totalCap]
  have hv : 0 < topCap t B J := lt_min ha ((Nat.le_add_left _ _).trans' htpos)
  let D := MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (totalCap t B) (topCap t B J)
  have hcount := section_incidence hw D (fun i hi => by
    obtain ⟨cut, hc, he⟩ := short_cut f hdp ht hJ hb hj sites hsum w i
    exact section_bound hw f hf hfpos hreg ha hv i hi cut hc
      (fun γ hγ => he _ (hw.degree γ hγ) (hreg γ hγ) (fun _ hj => hits_persistent hγ hj)))
  have hgap : (0 : ℚ) < ((agreement-sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hratio : (T.card : ℚ) ≤ siteRatio sites.card * D := by
    unfold siteRatio
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hgap).mpr
    rw [mul_comm (T.card : ℚ)]
    exact_mod_cast hcount
  have hvle : topCap t B J ≤ totalCap t B := min_le_left _ _
  dsimp only [D] at hratio
  rw [cast_mixed (f.degreeOf_le_totalDegree 1) hvle] at hratio
  obtain ⟨hcapA, hcapV⟩ := caps_weighted (B := B) hl hh hs hJ
  refine hratio.trans ?_
  unfold mix
  calc
    _ = (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * (siteRatio sites.card * topCap t B J) +
        f.degreeOf 1 * (siteRatio sites.card * totalCap t B) := by ring
    _ ≤ (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * persistentTop d B J +
        f.degreeOf 1 * persistentTotal d B :=
      add_le_add (mul_le_mul_of_nonneg_left hcapV (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hcapA (Nat.cast_nonneg _))
    _ ≤ _ := le_add_of_nonneg_right (by decide)

/-- The explicit persistent ODE tariff on the actual family. -/
def fixedFee (B J : ℕ) : ℕ :=
  (mix B J (persistentTotal endpointDegree B) (persistentTop endpointDegree B J)).ceil.toNat+B^2

theorem fixed_count {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2534) {B J : ℕ} (guard : ODEGuard B J)
    (G : ODE) (caps : ODECaps G B J) {T : Finset K} (hT : T⊆Γ)
    (roots : ∀ γ∈T,fixedAt G (F.scalar γ)=0) :
    T.card≤fixedFee B J := by
  have hw := fixed_word F hi hT
  let a := persistentTotal endpointDegree B
  let v := persistentTop endpointDegree B J
  have ha : 0≤a := persistentTotal_nonneg _ _
  have hv : 0≤v := le_min ha (by positivity)
  have h := fixed_bound hw guard G caps roots a v hv (min_le_left _ _)
    (fun U hU=>persistent_regular (word_subset hw hU) (by decide) (by decide) guard.jpos)
  let r := mix B J a v
  have hceil : r≤(r.ceil.toNat : ℕ) := by
    have hs : (r.ceil : ℚ)≤(r.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat r.ceil
    exact Rat.le_ceil.trans hs
  change T.card≤r.ceil.toNat+B^2
  have bound : (T.card : ℚ)≤(r.ceil.toNat : ℚ)+(B^2 : ℕ) :=
    h.trans (add_le_add hceil le_rfl)
  exact_mod_cast bound


end Lower6960.Prefix6969MiddleRates

end
end Merged_R6960RescueGeometryTariffs

section Merged_R6960RescueGeometryRates

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969MiddleRates
open Far6969RescueGeometry (Model Family label_injective OnMark)
open Finset Polynomial
open K1 (K p)
open K1_14 (Seeds graphEval)
open K1_14_2 (Ambient OnJet SeedField RootSeedSection)
open K1_14_2_2 (CutCover CurveGeometry)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength yLength)
open K1_14_2_3 (on_root on_seed moving_graph_count seed_graph_count equal_image_degree union_card_le)
open scoped Classical BigOperators

structure RateOK (a h : ℚ) : Prop where
  degree : ((p+1 : ℕ) : ℚ)/81≤a
  height : 0≤h
  interpolation : ∀ g : ℕ,0<g → g≤80 →
    max 0 (1-a*g/((p+1 : ℕ) : ℚ))*curveUnit g≤h

def curveMarks {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) (C : CutCover) : Finset K :=
  C.curves.biUnion (fun J=>Γ.filter (OnMark F J))

theorem mem_curveMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {C : CutCover} {J : Ideal Ambient} {γ : K} (mark : γ∈Γ)
    (curve : J∈C.curves) (on : OnMark F J γ) : γ∈curveMarks F C :=
  mem_biUnion.mpr ⟨J,curve,mem_filter.mpr ⟨mark,on⟩⟩

private theorem projected_curve : K1_14_2_3.c2 :=
  K1_14_2_3_2.of_children K1_14_2_3_2_1.proof K1_14_2_3_2_2.proof
private theorem seed_slice {I : Ideal Ambient} (h : CurveGeometry I) : SeedSlice I :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
private theorem mark_graph {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : seedImage I = Ideal.span {C}) :
    ∀ z ∈ (Γ.filter (OnMark F I)).image M.label, graphEval z C = 0 := by
  intro z hz
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
  apply on_seed (Finset.mem_filter.mp hγ).2
  rw [hC]
  exact Ideal.mem_span_singleton_self C
private theorem translated_card {u del} (M : Model u del) (T : Finset K) :
    (T.image M.label).card = T.card :=
  Finset.card_image_of_injective _ (fun _ _ hab => sub_left_inj.mp hab)
private theorem direct_count {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : C ≠ 0) (hI : seedImage I = Ideal.span {C})
    (hp : C.totalDegree < p) :
    (Γ.filter (OnMark F I)).card ≤ (p+1)*C.totalDegree := by
  have h := seed_graph_count C hC hp ((Γ.filter (OnMark F I)).image M.label) (mark_graph F hI)
  rwa [translated_card] at h
private theorem interpolate (g : ℕ) (a h d H T : ℚ) (hg : 0 < g)
    (hH : 0 ≤ H) (hd : 0 ≤ d) (hu : RateOK a h)
    (direct : T ≤ ((p+1 : ℕ) : ℚ)*d)
    (tariff : g ≤ 80 → T ≤ curveUnit g * H + g) :
    T ≤ a*(d*g) + h*H + g := by
  let q : ℚ := (p+1 : ℕ)
  have hq : 0 < q := Nat.cast_pos.mpr (Nat.succ_pos p)
  have ha : 0 ≤ a := (show 0 ≤ q/81 by positivity).trans hu.degree
  by_cases large : q ≤ a*g
  · calc
      T ≤ q*d := direct
      _ ≤ (a*g)*d := mul_le_mul_of_nonneg_right large hd
      _ = a*(d*g) := by ring
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        have hgq : (0 : ℚ) ≤ g := Nat.cast_nonneg _
        linarith
  · have hgsmall : g ≤ 80 := by
      by_contra! h
      have hgQ : (81 : ℚ) ≤ g := by exact_mod_cast Nat.succ_le_of_lt h
      have he : q/81*81 = q := by ring
      apply large
      rw [← he]
      exact mul_le_mul hu.degree hgQ (by norm_num) ha
    let θ := a*g/q
    have hθ : 0 ≤ θ := div_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) hq.le
    have hc : 0 ≤ 1-θ := sub_nonneg.mpr ((div_le_iff₀ hq).mpr (by simpa using (le_of_lt (lt_of_not_ge large))))
    have hh : (1-θ)*curveUnit g ≤ h := by
      have hf := hu.interpolation g hg hgsmall
      rw [max_eq_right hc] at hf
      exact hf
    calc
      T = θ*T+(1-θ)*T := by ring
      _ ≤ θ*(q*d)+(1-θ)*(curveUnit g*H+g) :=
        add_le_add (mul_le_mul_of_nonneg_left direct hθ)
          (mul_le_mul_of_nonneg_left (tariff hgsmall) hc)
      _ = a*(d*g)+((1-θ)*curveUnit g)*H+(1-θ)*g := by
        dsimp only [θ]
        field_simp [hq.ne']; ring
      _ ≤ _ := by
        have hlast : (1-θ)*(g : ℚ) ≤ g := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (sub_le_self 1 hθ) (Nat.cast_nonneg (α := ℚ) g)
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hH)) hlast
private theorem rated_component {u del} {M : Model u del} {Γ} (F : Family M Γ)
    (tariff : CurveTariff F) {a h globalCap localCap : ℚ} (hu : RateOK a h)
    (hmin : min globalCap localCap ≤ a) {I : Ideal Ambient} (geom : CurveGeometry I)
    (hglobal : (seedLength I : ℚ) ≤ globalCap) (hlocal : (seedLength I : ℚ) ≤ localCap)
    (hp : seedLength I < p) :
    ((Γ.filter (OnMark F I)).card : ℚ) ≤
      a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
  let T := Γ.filter (OnMark F I)
  let D := seedLength I
  let H := yLength I
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg _
  have hH : (0 : ℚ) ≤ H := Nat.cast_nonneg _
  have ha : 0 ≤ a := (show (0 : ℚ) ≤ ((p+1 : ℕ) : ℚ)/81 by positivity).trans hu.degree
  obtain ⟨f, hf, he, hpos, hd⟩ := K1_14_2_3_1.proof I (seed_slice geom)
  have hdq : (f.totalDegree : ℚ) ≤ D := by exact_mod_cast hd
  by_cases hconst : DefinedOverConstants (seedImage I)
  · obtain ⟨Q, hQ, heQ⟩ := hconst
    have hdeg : f.totalDegree = Q.totalDegree := equal_image_degree f hf.ne_zero Q (he.symm.trans heQ)
    obtain ⟨g, hg, hroot, hgD⟩ := projected_curve I Q (seed_slice geom) geom.2.2.2.2 hQ heQ
    have hgcap : g ≤ D := (Nat.le_mul_of_pos_left g (hdeg ▸ hpos)).trans hgD
    have hp' : Module.finrank SeedField (RootSeedSection (rootImage I)) < p := by
      obtain ⟨_, Q', hQ', hQ'proj, _, hlen, _, _⟩ := hroot
      have heQ' : seedImage I = Ideal.span {MvPolynomial.map constantCoefficients Q'} := hQ'proj
      have hdeg' := equal_image_degree f hf.ne_zero Q' (he.symm.trans heQ')
      rw [hlen, ← hdeg', hdeg]
      exact hgD.trans_lt hp
    have hdir : (T.card : ℚ) ≤ ((p+1 : ℕ) : ℚ)*(Q.totalDegree : ℚ) := by
      have hcount := direct_count F hf.ne_zero he (hd.trans_lt hp)
      rw [hdeg] at hcount
      exact_mod_cast hcount
    have htar (hgi : g ≤ 80) : (T.card : ℚ) ≤ curveUnit g * H + g :=
      tariff T (Finset.filter_subset _ _) (rootImage I) g H hg hgi hroot hp'
        (fun _ hz => on_root (Finset.mem_filter.mp hz).2)
    have hfirst := interpolate g a h Q.totalDegree H T.card hg hH
      (Nat.cast_nonneg _) hu hdir htar
    have hgDq : (Q.totalDegree : ℚ)*g ≤ D := by exact_mod_cast hgD
    have hgcapq : (g : ℚ) ≤ D := by exact_mod_cast hgcap
    exact hfirst.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hgDq ha) le_rfl)
      hgcapq)
  · have hmov := moving_graph_count p f hf (he ▸ hconst)
      (T.image M.label) (mark_graph F he)
    rw [translated_card] at hmov
    have hcard : (T.card : ℚ) ≤ (f.totalDegree : ℚ)^2 := by exact_mod_cast hmov
    have hd0 : (0 : ℚ) ≤ f.totalDegree := Nat.cast_nonneg _
    have har : (f.totalDegree : ℚ) ≤ a :=
      (le_min (hdq.trans hglobal) (hdq.trans hlocal)).trans hmin
    calc
      _ ≤ (f.totalDegree : ℚ)^2 := hcard
      _ ≤ a*D := by rw [pow_two]; exact mul_le_mul har hdq hd0 ha
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        linarith
theorem rated_curve_count {u del} {M : Model u del} {Γ}
    (F : Family M Γ) (tariff : CurveTariff F)
    {a h globalCap : ℚ} (hu : RateOK a h) (C : CutCover)
    (hglobal : (C.cost 0 : ℚ) ≤ globalCap)
    (hdegree : min globalCap (C.cost 0 : ℚ) ≤ a) (hp : C.cost 0 < p) :
    ((curveMarks F C).card : ℚ) ≤ a*(C.cost 0 : ℚ)+h*(C.cost 1 : ℚ)+C.cost 0 := by
  have hsum : ∑ I ∈ C.curves, seedLength I = C.cost 0 := rfl
  have hsumH : ∑ I ∈ C.curves, yLength I = C.cost 1 := rfl
  have hcount (I : Ideal Ambient) (hI : I ∈ C.curves) :
      ((Γ.filter (OnMark F I)).card : ℚ) ≤
        a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
    have hn : seedLength I ≤ C.cost 0 := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hI
    have hq : (seedLength I : ℚ) ≤ (C.cost 0 : ℚ) := by exact_mod_cast hn
    exact rated_component F tariff hu hdegree (C.geometric I hI) (hq.trans hglobal) hq (hn.trans_lt hp)
  calc
    _ ≤ ∑ I ∈ C.curves, ((Γ.filter (OnMark F I)).card : ℚ) := union_card_le _ _
    _ ≤ ∑ I ∈ C.curves, (a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I) :=
      Finset.sum_le_sum hcount
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum, hsum, hsumH]

end Lower6960.Prefix6969MiddleRates

end
end Merged_R6960RescueGeometryRates
end Z6969Source0604

-- Source: Research6969.PrefixMiddleSchedule
section Z6969Source0605
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000

namespace Lower6960.Prefix6969Middle

open Research6969
open Research6969.TransitionBanks
open K1_14 (L)
open K1_14_1 (PoleData CRTLift evaluated)
open Lower6960.HelperSource
open P1_7_4 (Mass)

abbrev count : ℕ := 14
abbrev firstHeight : ℕ := 2390
abbrev lastHeight : ℕ := 2534
abbrev agreement : ℕ := 179740

def reserve (i : Fin count) : ℕ := ![0, 1, 2, 3, 5, 7, 10, 15, 21, 18, 40, 40, 75, 75] i
def bank (i : Fin count) : P1_7.Bank :=
  ![bank3 1490, bank10 1603, bank16 1778, bank24 1838, bank33 2191, bank42 2497, bank52 2900, bank65 3612, bank83 5597, bank107 3286, bank122 24063, bank147 6388, bank211 10626, bank171 201573] i

theorem free_checked (i : Fin count) : TransitionSources.Free firstHeight (reserve i) (bank i) := by
  fin_cases i
  · exact free3_2
  · exact free10_2
  · exact free16_2
  · exact free24_2
  · exact free33_4
  · exact free42_5
  · exact free52_2
  · exact free65_2
  · exact free83_4
  · exact free107_1
  · exact free122_2
  · exact free147_2
  · exact free211_2
  · exact free171_2

def cutoff (h : ℕ) (i : Fin count) : ℕ :=
  cutoffCount (bank i).shape agreement h (reserve i) - 1

theorem cutoff_fit {h : ℕ} (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) (i : Fin count) :
    cutoff h i + 2 * h * reserve i < (bank i).shape.m * agreement := by
  have cert := free_checked i
  have hw := width_at_height _ _ _ _ _ lo (hi.trans (by decide)) cert.reserve_fit cert.width
  exact Lower6960.FreeSource.buffered_fit (bank i) agreement h (reserve i) hw

theorem free_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) (i : Fin count) :
    ∃ P ∈ evaluated Crt word (bank i).shape (cutoff h i), P ≠ 0 :=
  (free_checked i).row Crt word ((by decide : 0 < firstHeight).trans_le lo) lo (hi.trans (by decide))

def suppliedHistory : List Mass :=
  [![14903, 177190, 830063, 4385603],
   ![24861/2, 316381/2, 2888671/4, 16041221/4],
   ![53228/9, 692533/9, 622300, 3161284],
   ![29433/8, 742761/16, 373366, 18392866/9],
   ![5468/3, 426403/18, 236628, 4800481/4],
   ![36739/32, 241217/16, 1203554/9, 24987479/36],
   ![86036/121, 102131/11, 205175/2, 525625],
   ![86036/121, 102131/11, 101136, 13046544/25],
   ![254619/484, 3963227/484, 16447228/225, 112018358/225],
   ![254619/484, 3963227/484, 16447228/225, 16441501/49],
   ![41249/100, 3963227/484, 16447228/225, 16441501/49],
   ![41249/100, 1373561/200, 1701616/29, 63924716/225],
   ![41249/100, 32538856/5329, 1170708/23, 67667334/275],
   ![1826342/5329, 32538856/5329, 1170708/23, 67667334/275]]

def suppliedDegreeRates : List ℕ := [396913411, 395939454, 396740372, 394810557, 394959385, 395653093, 175140468, 174974230, 178018559, 90482674, 90682971, 127660375, 169448931, 247783754]
def suppliedHeightRates : List ℕ := [859624, 862296, 860099, 865393, 864985, 863082, 2172638, 2174645, 2137894, 4395761, 4385650, 3052680, 2245952, 1468013]
def retainedCredit (i : Fin 4) : ℕ := ![131528572298280, 1592972508796, 223005378600, 3632689200] i
abbrev prefixCap : ℕ := 231373953658241386

end Lower6960.Prefix6969Middle
end Z6969Source0605
