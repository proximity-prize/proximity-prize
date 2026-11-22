import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m3_0 : availableMass (start .one5) ⟨1,3,0⟩ 6 < layerNeed := by
  rw [mass_eq (start .one5) ⟨1,3,0⟩ 6 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 212 [4585326679244, 3854160918486, 3178713321798, 2586292299190, 2071706477862, 1629707861910, 1254991832326, 942197146998, 685905940710, 480643725142, 320879388870, 201025197366, 115436792998, 58413195030, 24196799622, 6973379830, 872085606, 4530867] (by decide +kernel) (by decide)

private theorem m3_1 : availableMass (start .one5) ⟨2,6,0⟩ 23 < layerNeed := by
  rw [mass_eq (start .one5) ⟨2,6,0⟩ 23 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 173 [4628005587678, 4133686271820, 3372195789274, 2546422072910, 1866339141346, 1318457542870, 889057828970, 564190554334, 329676276850, 171105557606, 73838960890, 23007054190, 3510408194, 50879841, 0] (by decide +kernel) (by decide)

private theorem m3_2 : availableMass (start .one5) ⟨3,9,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .one5) ⟨3,9,0⟩ 44 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 161 [4628005587678, 4137434455250, 3682501885502, 3214333906986, 2340557229038, 1548175526654, 957005349582, 538636645214, 264014498990, 103439134398, 26565912974, 2405334302, 709821, 0] (by decide +kernel) (by decide)

private theorem m3_3 : availableMass (start .one5) ⟨4,12,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .one5) ⟨4,12,0⟩ 45 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 142 [4628005587678, 4137434455250, 3682501885502, 3223964527919, 2242089701325, 1336288695021, 713096655541, 321317579685, 108295242045, 19913195005, 610990270, 0] (by decide +kernel) (by decide)

private theorem m3_4 : availableMass (start .one5) ⟨5,15,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one5) ⟨5,15,0⟩ 49 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 131 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2415273024108, 1324174440828, 622213449868, 225980412828, 49190299308, 2682827323, 0] (by decide +kernel) (by decide)

private theorem m3_5 : availableMass (start .one5) ⟨6,17,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .one5) ⟨6,17,0⟩ 52 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 127 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2588214278919, 1385283317843, 605652683071, 192769482187, 30834368759, 543335418, 0] (by decide +kernel) (by decide)

private theorem m3_6 : availableMass (start .one5) ⟨9,27,0⟩ 63 < layerNeed := by
  rw [mass_eq (start .one5) ⟨9,27,0⟩ 63 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 114 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2028457032090, 697410547374, 127044352286, 3699060412, 0] (by decide +kernel) (by decide)

private theorem m3_7 : availableMass (start .one5) ⟨68,24,0⟩ 67 < layerNeed := by
  rw [mass_eq (start .one5) ⟨68,24,0⟩ 67 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 123 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2320893449164, 880938346288, 187926951132, 15573510912, 35420861, 0] (by decide +kernel) (by decide)

private theorem m3_8 : availableMass (start .one5) ⟨69,39,0⟩ 69 < layerNeed := by
  rw [mass_eq (start .one5) ⟨69,39,0⟩ 69 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 106 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2403447452566, 736530602442, 56806568650, 24747037] (by decide +kernel) (by decide)

private theorem m3_9 : availableMass (start .one5) ⟨99,41,0⟩ 71 < layerNeed := by
  rw [mass_eq (start .one5) ⟨99,41,0⟩ 71 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 106 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2496036186565, 878703109884, 62206350428, 41504086] (by decide +kernel) (by decide)

theorem checked3 (q : Threshold) (hq : q ∈ thresholds .one5) :
    0 < q.j ∧ availableMass (start .one5) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, m3_0⟩
  · exact ⟨by decide, m3_1⟩
  · exact ⟨by decide, m3_2⟩
  · exact ⟨by decide, m3_3⟩
  · exact ⟨by decide, m3_4⟩
  · exact ⟨by decide, m3_5⟩
  · exact ⟨by decide, m3_6⟩
  · exact ⟨by decide, m3_7⟩
  · exact ⟨by decide, m3_8⟩
  · exact ⟨by decide, m3_9⟩

end Low53At2389PriceMass
