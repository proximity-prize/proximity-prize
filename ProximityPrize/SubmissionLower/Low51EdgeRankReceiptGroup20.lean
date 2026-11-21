import ProximityPrize.SubmissionLower.Low51EdgeRankPrefixCode

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace Low51EdgeRankReceipt
open K1_13_1_1 (bandCount)

private def cert20_0 := witnessLow51 20 53 0 70839 70839 1 94
  0x0 (by decide +kernel)
private def cert20_1 := witnessLow51 20 52 0 80776 80838 2 188
  0x0 (by decide +kernel)
private def cert20_2 := witnessLow51 20 51 0 90713 90838 4 373
  0x11200 (by decide +kernel)
private def cert20_3 := witnessLow51 20 50 0 100650 100837 6 557
  0x44812200 (by decide +kernel)
private def cert20_4 := witnessLow51 20 49 0 110587 110837 9 829
  0x109112048812200 (by decide +kernel)
private def cert20_5 := witnessLow51 20 48 0 120524 120836 12 1100
  0x2122240908a122048812200 (by decide +kernel)
private def cert20_6 := witnessLow51 20 47 0 130461 130836 16 1455
  0x31242444812114244111122048812200 (by decide +kernel)
private def cert20_7 := witnessLow51 20 46 0 140398 140835 20 1809
  0x3124244481221424228488222244111122048812200 (by decide +kernel)
private def cert20_8 := witnessLow51 20 45 0 150335 150835 24 2150
  0x41262484889122142422848822114444488222244111122048812200 (by decide +kernel)
private def cert20_9 := witnessLow51 20 44 0 160272 160834 28 2492
  (packedSchedule 0xabf701ef0aaf35cd43c6ba7a67a9d3943c69439b9b3413) (by decide +kernel)
private def cert20_10 := witnessLow51 20 43 0 170209 170834 32 2821
  (packedSchedule 0x10fbd5fb80abcd7350f1ae9cd72303d53a72878dc69439b9b3416) (by decide +kernel)
private def cert20_11 := witnessLow51 20 42 0 180146 180833 36 3155
  (packedSchedule 0x21f7ababf3c3535cd43c6ba7a90f54e9ca19f69f1b8dc69439b9b3418) (by decide +kernel)
private def cert20_12 := witnessLow51 20 41 0 190083 190833 40 3475
  (packedSchedule 0xe7fb90d5f9e1a9ae6a1ea935ea43d53a70fb4a3fd3e36b98dc69439b9b3419) (by decide +kernel)
private def cert20_13 := witnessLow51 20 40 0 200020 200832 44 3803
  (packedSchedule 0x39f57e8135cf0d4d7a935ea43d53a7a928fc3c7da7c6d72b98dc69439b9b341a) (by decide +kernel)
private def cert20_14 := witnessLow51 20 39 0 210019 210832 47 4024
  (packedSchedule 0x8db57e8135cf2a73ca935ea43d53a73e0f1f69cf88fe59fa7ae572b98dc69439b83fc23c1e) (by decide +kernel)
private def cert20_15 := witnessLow51 20 38 0 220018 220769 50 4255
  (packedSchedule 0x1af3ec9ae81a9cf2a4d7a90f1f1ae7c1e3ed3ad8b2cfd3d70b3ae5731b8d02d84381c) (by decide +kernel)
private def cert20_16 := witnessLow51 20 37 0 230017 230768 52 4383
  (packedSchedule 0x1af3ecd4e81a9cf2a4d73e35cf83c7da73e96787ae74f1f691fd534b3ae5731b8d2873701e) (by decide +kernel)
private def cert20_17 := witnessLow51 20 36 0 240016 240768 55 4592
  (packedSchedule 0x358db66a740d4e787d9e1f1ae7c1e3ed3dc87ae74eebd25df4e5996659d72b98dc6816c1e) (by decide +kernel)
private def cert20_18 := witnessLow51 20 35 0 250015 250705 56 4631
  (packedSchedule 0x153cfb353a04fb3c3e35cf83d726bdc87ae74f1f6a5df4fea9608fe21c599675cae6371a50c1f) (by decide +kernel)
private def cert20_19 := witnessLow51 20 34 0 260014 260704 58 4751
  (packedSchedule 0x153cfb27da04fb3c3e35ee4d7b90f5ce9ee52ee1ef5d3faeb7b10eb90b32ceb95cc6e341e) (by decide +kernel)
private def cert20_20 := witnessLow51 20 33 0 270013 270704 59 4772
  (packedSchedule 0x1531b6c9f6813ecf2e73cb935ee43d73a7f50f7ae9fd52c5f67a7564bba5823f8875c8599675cae63422) (by decide +kernel)
private def cert20_21 := witnessLow51 20 32 0 280012 280641 60 4807
  (packedSchedule 0x7dcfb27da06e73cb935ee43dea6bfa87bd74fbde5f67a77ad37605b92e42ccb3ae5701d) (by decide +kernel)
private def cert20_22 := witnessLow51 20 31 0 290011 290640 60 4747
  (packedSchedule 0x3ee7d9b9d03739e5c9afea6bfa87bd74feb7d98795b4f4156488f61302dc97216659d701e) (by decide +kernel)
private def cert20_23 := witnessLow51 20 30 0 300010 300640 61 4764
  (packedSchedule 0x3e8db66e740dce79eb9e7a9afea1ef5d3ab0795b4ef58c66d34f11f37605816e4b90b32cc1f) (by decide +kernel)
private def cert20_24 := witnessLow51 20 29 0 310009 310577 60 4627
  (packedSchedule 0x173cfb373a07d73cf535fd43cac6bab0795b4f416d34eef282ac86530981605b92e42cc1e) (by decide +kernel)
private def cert20_25 := witnessLow51 20 28 0 320008 320576 60 4567
  (packedSchedule 0x5cf3ecfae81f5cf3d4d75635d583cada77ad681eb4d3b2632a6ed5d81605816e4b901d) (by decide +kernel)
private def cert20_26 := witnessLow51 20 27 0 330007 330576 59 4416
  (packedSchedule 0x1731b6cfae81f5cf15b3c5635d583cada7b40f5a69dde505ead3f5097590ca6135760581605b9021) (by decide +kernel)
private def cert20_27 := witnessLow51 20 26 0 340006 340513 58 4283
  (packedSchedule 0x7af3ecfae8156cf158d7560f5a1af681eb4d3c47f569eaeb267c0654ddabb02d5d816058141f) (by decide +kernel)
private def cert20_28 := witnessLow51 20 25 0 350005 350512 56 4063
  (packedSchedule 0x1ebcfb2ada055b3c5635ed0d7b40f5a69dde7507bab4fd425cde097591f0194c26aec0b5760581421) (by decide +kernel)
private def cert20_29 := witnessLow51 20 24 0 360004 360512 55 3916
  (packedSchedule 0x1eb1b6cab68156cf2d33cb435ed03d69a7ea0f7569ccaa4d39ff64cf80ca9ba7fe05abb02d5d81421) (by decide +kernel)
private def cert20_30 := witnessLow51 20 23 0 370003 370449 52 3631
  (packedSchedule 0x2b73ecab681b4cf2d0d7b40f751afd41eead3f56c66934e6f04b86537825d647c0653093ff02d5d81422) (by decide +kernel)
private def cert20_31 := witnessLow51 20 22 0 380002 380448 50 3419
  (packedSchedule 0x15b9f66d340da679686bf51afd41eead3d5da40f5269df0194194ffb262ca654dd3ff029ff81420) (by decide +kernel)
private def cert20_32 := witnessLow51 20 21 0 390001 390448 47 3124
  (packedSchedule 0x568db66d340da679d59e751afd41eead3d207a934f4941fced386537825c329bc12eb2165329849ff81423) (by decide +kernel)
private def cert20_33 := witnessLow51 20 20 0 400000 400385 44 2851
  (packedSchedule 0x169cfb369a07ab3cea35fa83d486bd207a934e7ff9da72ca651bd3fec98b2995374329ff8141f) (by decide +kernel)
private def cert20_34 := witnessLow51 20 19 0 410000 410384 40 2499
  (packedSchedule 0x5a73ecf5681eacf3a8d7a435e903d49a77c1ce0f73b4e1969283cde9bc12e6f4de097590b2994c2421) (by decide +kernel)
private def cert20_35 := witnessLow51 20 18 0 420000 420384 37 2216
  (packedSchedule 0xb48db67ab40f5679499e521af481ea4d3f383dced38653fe07e9feb165328de9ff64df58b299537421) (by decide +kernel)
private def cert20_36 := witnessLow51 20 17 0 430000 430321 33 1905
  (packedSchedule 0x1d5cfb3d5a06933ca435e903dce35f9c1ee769cb281fa737b4941f44cde9bc12e6f4de0975901f) (by decide +kernel)
private def cert20_37 := witnessLow51 20 16 0 440000 440320 30 1659
  (packedSchedule 0x3ab9f669340d2679486bf38d7e707b9da70ca078780fd39bd3ff44feb16532a899bd3fec981e) (by decide +kernel)
private def cert20_38 := witnessLow51 20 15 0 450000 450320 27 1428
  0x104e2a49454920aa24154462a88855108ab22156422ac8d119238422b08d91a2324608b91c2364688c91822e4588a91 (by decide +kernel)
private def cert20_39 := witnessLow51 20 14 0 460000 460257 24 1215
  0x9261524a2a89055118aa22156462ac8855908ab234470845611b2344648c11d23846c8d11923045c8b11 (by decide +kernel)
private def cert20_40 := witnessLow51 20 13 0 470000 470256 21 1017
  0x4930aa25154482a88c55918ab22156422ac8e110ac2115846c8d11923a4708d91a2324608b91 (by decide +kernel)
private def cert20_41 := witnessLow51 20 12 0 480000 480256 19 872
  0x124e2a89455120ab24156462ac8855908ac22158422b08d91a23a422b48e11b2344648c11 (by decide +kernel)
private def cert20_42 := witnessLow51 20 11 0 490000 490193 16 703
  0xa261544a2ac9055918ab22158462b08856108ac236474845691c2364688c91 (by decide +kernel)
private def cert20_43 := witnessLow51 20 10 0 500000 500192 14 583
  0x289855928ab24156462b08c56110ac211584748856908ad23846c8d11 (by decide +kernel)
private def cert20_44 := witnessLow51 20 9 0 510000 510192 12 473
  0xa271564a2ac9056120ac23158442b08456910ad2115a4708d91 (by decide +kernel)
private def cert20_45 := witnessLow51 20 8 0 520000 520129 10 374
  0x2c9855928ac24158462b08856918ad2215a422b48e11 (by decide +kernel)
private def cert20_46 := witnessLow51 20 7 0 530000 530128 8 284
  0xb261584a2b09056118ad2315a442b4845691 (by decide +kernel)
private def cert20_47 := witnessLow51 20 6 0 540000 540128 7 232
  0x164e2b09456120ad2415a462b48856908a (by decide +kernel)
private def cert20_48 := witnessLow51 20 5 0 550000 550065 5 158
  0x6130ac2515a482b48c56910a (by decide +kernel)
private def cert20_49 := witnessLow51 20 4 0 560000 560064 4 118
  0xc2615a4a2b49056918a (by decide +kernel)
private def cert20_50 := witnessLow51 20 3 0 570000 570064 3 82
  0x184e2b49456920a (by decide +kernel)
private def cert20_51 := witnessLow51 20 2 0 580000 580001 2 51
  0x349856928a (by decide +kernel)
private def cert20_52 := witnessLow51 20 1 0 590000 590000 1 24
  0x6930a (by decide +kernel)
private def cert20_53 := witnessLow51 20 0 0 600000 600000 1 21
  0x6938a (by decide +kernel)
private def chunks20 : List (Chunk 20) := [
  cert20_0, cert20_1, cert20_2, cert20_3, cert20_4, cert20_5, cert20_6, cert20_7, cert20_8, cert20_9,
  cert20_10, cert20_11, cert20_12, cert20_13, cert20_14, cert20_15, cert20_16, cert20_17, cert20_18, cert20_19,
  cert20_20, cert20_21, cert20_22, cert20_23, cert20_24, cert20_25, cert20_26, cert20_27, cert20_28, cert20_29,
  cert20_30, cert20_31, cert20_32, cert20_33, cert20_34, cert20_35, cert20_36, cert20_37, cert20_38, cert20_39,
  cert20_40, cert20_41, cert20_42, cert20_43, cert20_44, cert20_45, cert20_46, cert20_47, cert20_48, cert20_49,
  cert20_50, cert20_51, cert20_52, cert20_53]

def rows20 := rowsFrom chunks20

theorem good20 : ∀ r ∈ rows20, good 20 r = true := rowsFrom_good chunks20

theorem sorted20 : rows20.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks20 0 (by decide +kernel)).1

theorem mass20 (i : Fin 54) :
    bandCount 20 (i.val : ℤ) 53 13 ≤ (rows20.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks20).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 20 (j : ℤ) 53 13 ≤ mass j chunks20)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total20 : (rows20.map (price 20)).sum = 124838 :=
  (total_eq chunks20).trans (by decide +kernel)

private def cert21_0 := witnessLow51 21 53 0 100714 100839 4 375
  0x0 (by decide +kernel)
private def cert21_1 := witnessLow51 21 52 0 110651 110838 6 559
  0x4c810200 (by decide +kernel)
private def cert21_2 := witnessLow51 21 51 0 120588 120838 9 831
  0x101112050815200 (by decide +kernel)
private def cert21_3 := witnessLow51 21 50 0 130525 130837 12 1101
  0x131142240a882122048812200 (by decide +kernel)
private def cert21_4 := witnessLow51 21 49 0 140462 140837 16 1457
  0x1120442444814114244129122048812200 (by decide +kernel)
private def cert21_5 := witnessLow51 21 48 0 150399 150836 20 1810
  0x13214424448151110624228488141242440a892122048812200 (by decide +kernel)
private def cert21_6 := witnessLow51 21 47 0 160336 160836 25 2246
  0x10902312424448142142422848825114444488222244111122048812200 (by decide +kernel)
private def cert21_7 := witnessLow51 21 46 0 170273 170835 29 2584
  (packedSchedule 0x6135c07bc2f7c5ef7e1541a878d74f4ce93372874ee005b9b9b3418) (by decide +kernel)
private def cert21_8 := witnessLow51 21 45 0 180210 180835 34 3005
  (packedSchedule 0xefeafdc07bc2f7f06b9a878d74f4cf4c3d53a7287e119be8c9439b9b341b) (by decide +kernel)
private def cert21_9 := witnessLow51 21 44 0 190147 190834 38 3331
  (packedSchedule 0xc39e55fb80f7be02a0d4d7350f1ae9c7fcf5b553a72874e92df1b8dc69439b9b341e) (by decide +kernel)
private def cert21_10 := witnessLow51 21 43 0 200084 200834 43 3740
  (packedSchedule 0x2afbf21f7abf7f19e1a9ae6a1e35d3d335ea43d53a72869437c6d3abf1b8dc69439b9b3420) (by decide +kernel)
private def cert21_11 := witnessLow51 21 42 0 210021 210833 47 4057
  (packedSchedule 0x61d0243ef7eaea0d73c3535cd43d3c645487aa74e9d63fe99adb47da7c6a85c6df4cf1b8dc69439b9b3425) (by decide +kernel)
private def cert21_12 := witnessLow51 21 41 0 220020 220833 51 4363
  (packedSchedule 0x43dff3fdfc68135cf0d4d7a79e549af521ea9d3a75ff5b47da7c6d38637ae572b98dc69439b83fc23c24) (by decide +kernel)
private def cert21_13 := witnessLow51 21 40 0 230019 230832 54 4580
  (packedSchedule 0x1879f66f90d41ae8135cf27bc5d49af521ea9d3d335320f83c7da76ea3fce353d729a675cae5731b8d02d843827) (by decide +kernel)
private def cert21_14 := witnessLow51 21 39 0 240018 240832 57 4790
  (packedSchedule 0xe7f7fe39f64d740d3d03539e549af521efe320f83c7da76eb4ea6dab9d3d7326cd72fbed5cae5731b8d28737028) (by decide +kernel)
private def cert21_15 := witnessLow51 21 38 0 250017 250769 59 4914
  (packedSchedule 0x5fe7d41af3eccf51ea9cf2a4d7a66be2cf8d73e0f1f69ff66716d5ce9fb23751ff4ed76e5996659d72b98dc6816c28) (by decide +kernel)
private def cert21_16 := witnessLow51 21 37 0 260016 260768 61 5033
  (packedSchedule 0x3c46db34f9f66a740d4e79fde2cf8d73e0f1f69e9d4991721eb9d3f646eb93a9cb3a6fb166599675cae6371a50c28) (by decide +kernel)
private def cert21_17 := witnessLow51 21 36 0 270015 270768 63 5138
  (packedSchedule 0x6bcf7ecf73dbd4e81a66b478fb3c3e35cf83c70645c87ae74eb2533eb6bd74ec27c6e0b3bfb82ccb32ceb95cc6e342a) (by decide +kernel)
private def cert21_18 := witnessLow51 21 35 0 280014 280705 64 5172
  (packedSchedule 0x17cd79eaf53cfb3fd478fb3c3e35e9d4f8bb935ee43d73a7ec9936d7ae9e6ed3a85bdc9725c8599675cae63427) (by decide +kernel)
private def cert21_19 := witnessLow51 21 34 0 290013 290704 65 5189
  (packedSchedule 0x4f46d2266bcf6e7da04fb3c38f17726bdc87ae74f4cf8c8f50f7ae9fb1564f143b77acc269ee2e4b92e42ccb3ae57029) (by decide +kernel)
private def cert21_20 := witnessLow51 21 33 0 300012 300704 66 5208
  (packedSchedule 0x153cf7eff73db9f681a75347ae73cb935ee43d92647a87bd74e6334ee6da56d3bd69bbe30eb92fe1d725c97216659d702a) (by decide +kernel)
private def cert21_21 := witnessLow51 21 32 0 310011 310641 66 5144
  (packedSchedule 0xbf53cf573ee7d938a3d739e5c9af4cfbc5fa9afea1ef5d3f62f7b6d2b69e82ac94e876f11ec2605816e4b90b32cc28) (by decide +kernel)
private def cert21_22 := witnessLow51 21 31 0 320010 320640 66 5083
  (packedSchedule 0x3fa36913a9e7b7b9d03739e64f8bf535fd43deba7a772642b0795b4ef58c67c434de23e6ed3c3a0581605b92e42cc28) (by decide +kernel)
private def cert21_23 := witnessLow51 21 30 0 330009 330640 66 5004
  (packedSchedule 0x3ee7bf4e39edee740d33ea3deb9e7a9afea1eef4c8560f2b69e82d3f5b6ad34eef282ac9e32888f6137f2881605816e4b902b) (by decide +kernel)
private def cert21_24 := witnessLow51 21 29 0 340008 340577 65 4870
  (packedSchedule 0x5f3ee7abdcf3ece4d1ef5cf3d4d7a773e2d58d7560f2b69deb3396d5a69d9353869b995376aec0b5760581605b9028) (by decide +kernel)
private def cert21_25 := witnessLow51 21 28 0 350007 350576 64 4715
  (packedSchedule 0xe2369133ee7b7f5d03eb9e77be2d58d7560f2b69e9fa991681eb4d3bbca0a31f53f50975929e5065309abb02d5d816058142a) (by decide +kernel)
private def cert21_26 := witnessLow51 21 27 0 360006 360576 63 4570
  (packedSchedule 0x2e79efdc9e7b7f5d034ee68f2b678ac6bab0799c322d03d69a788fa6ad6d7569eaeb26f09d4ca9bb7d3ad5d816aec0b576058142c) (by decide +kernel)
private def cert21_27 := witnessLow51 21 26 0 370005 370513 61 4346
  (packedSchedule 0x2fdcf3d5fd79f67bda3cad9e2b1af4fd7c5da1af681eb4d3bbc18f6d7569fa84bd3b4d4e6f04bac8f80ca6127fe05abb02d5d8142c) (by decide +kernel)
private def cert21_28 := witnessLow51 21 25 0 380004 380512 59 4133
  (packedSchedule 0xc98da44ee79edd5b40ab678ce78bb435ed03d69a7a6ac647507bab4e6578ead4e7fd93534eaf80ca9ba7fe053ff02d5d8142a) (by decide +kernel)
private def cert21_29 := witnessLow51 21 24 0 390003 390512 57 3898
  (packedSchedule 0x3d79efdef79edd5b40d3f5a3d699e5a1af681e18e647507bab4fd5b19a7696d5269cde097f14964de097592fd2597c0653093ff029ff81430) (by decide +kernel)
private def cert21_30 := witnessLow51 21 23 0 400002 400449 54 3624
  (packedSchedule 0x5ff5e7abab73ecb3947ad33cb435e9ab78bea35fa83dd5a7abbe3aadaa4d3be032a9f56a70ca7fd9316532a6e8653ff029ff8142c) (by decide +kernel)
private def cert21_31 := witnessLow51 21 22 0 410001 410448 51 3325
  (packedSchedule 0xef636913f5e7b7b4d03699e0c7f17d46bf507bab4f4ed0c8a40f5269e9283fc526a70ca6f04bd3a4b2194de097590b2994c24329ff8142e) (by decide +kernel)
private def cert21_32 := witnessLow51 21 21 0 420000 420448 48 3044
  (packedSchedule 0xadcf7eb39cf6f69a069ab51eeacf3a8d7ea0f78ea322903d49a73ff4faadae769cb2995e39d64329ff64d7f9d64b2995374329ff8142f) (by decide +kernel)
private def cert21_33 := witnessLow51 21 20 0 430000 430385 44 2688
  (packedSchedule 0xbeadcf57b4e7d918f47bab3cea35e9da78ba435e903d49a77c1e292dae769c32d2507d3a4d4e6f4de09737a6f04bac9f58b2994c242d) (by decide +kernel)
private def cert21_34 := witnessLow51 21 19 0 440000 440384 40 2351
  (packedSchedule 0x3391b489ab73dbf5681eaabcababc5d21af481ea4d3d3ea3239c1ee769c329fff1ced4ff58b29954f9d64de9ff64df58b29953742c) (by decide +kernel)
private def cert21_35 := witnessLow51 21 18 0 450000 450384 37 2082
  (packedSchedule 0xb4e7bf463f3dbf5681a76947a933ca435e903de290c8e707b9da72cb4e92da03f4e6f69283fc01f64de9bc12f7c0fb26f4de0975902e) (by decide +kernel)
private def cert21_36 := witnessLow51 21 17 0 460000 460321 33 1786
  (packedSchedule 0x17ed39eafd5cfcabaa8f52679486bd3eaf17ce35f9c1ee769c32f8e75b407e9cde9ffa7ced4f44feb16532a899bd3fec9829) (by decide +kernel)
private def cert21_37 := witnessLow51 21 16 0 470000 470320 30 1551
  0x51c9c592b930b9251524828524905d118aa2215442289648c5d910ab211564688c9114b2117846c8d11923045c892d92c2364688c91822e4588a91 (by decide +kernel)
private def cert21_38 := witnessLow51 21 15 0 480000 480320 27 1334
  0x104c240c520985c928a25825174482a88c55110a14a23176442ac845591a224b4442f0845611b2344648c1114c25846c8d11923045c8b11 (by decide +kernel)
private def cert21_39 := witnessLow51 21 14 0 490000 490257 24 1132
  0x15826110924c28524945d120aa23144b2482ec8c55910ab211564452c885e108ac2364688c9125b2117a4708d91a2324608b91 (by decide +kernel)
private def cert21_40 := witnessLow51 21 13 0 500000 500256 21 945
  0xa4138b258261744a2a89050a5120bb23156442ac84512d118bc22158422b08d91a22298422f48e11b2344648c11 (by decide +kernel)
private def cert21_41 := witnessLow51 21 12 0 510000 510256 19 810
  0x124c240c524985d128a25925176482ac8c55910a14b23178442b0845611b224b6442f4845691c2364688c91 (by decide +kernel)
private def cert21_42 := witnessLow51 21 11 0 520000 520193 16 651
  0x15926110944c28528945d920ab23144b4482f08c56110ac2115844530885e908ad23846c8d11 (by decide +kernel)
private def cert21_43 := witnessLow51 21 10 0 530000 530192 14 538
  0x5249c592c930bb25156482852c905e118ac22158422896c8c5e910ad2115a4708d91 (by decide +kernel)
private def cert21_44 := witnessLow51 21 9 0 540000 540192 12 437
  0xa2612062944c2ec94512d128bc24158462b08850a6118bd2215a422b48e11 (by decide +kernel)
private def cert21_45 := witnessLow51 21 8 0 550000 550129 10 344
  0x568984425930a14b25178482b08c512d920bd2315a442b4845691 (by decide +kernel)
private def cert21_46 := witnessLow51 21 7 0 560000 560128 8 260
  0x14a27164b44c2f09456120a14c2417a462b48856908a (by decide +kernel)
private def cert21_47 := witnessLow51 21 6 0 570000 570128 7 213
  0x164c240c52c985e128a25b2517a482b48c56910a (by decide +kernel)
private def cert21_48 := witnessLow51 21 5 0 580000 580065 5 144
  0xad930884c26142984a2f49056918a (by decide +kernel)
private def cert21_49 := witnessLow51 21 4 0 590000 590064 4 106
  0x14b27164b64c2f49456920a (by decide +kernel)
private def cert21_50 := witnessLow51 21 3 0 600000 600064 3 75
  0x184c240c530985e928a (by decide +kernel)
private def cert21_51 := witnessLow51 21 2 0 610000 610001 2 46
  0x570984426930a (by decide +kernel)
private def cert21_52 := witnessLow51 21 1 0 620000 620000 1 21
  0xa6138b (by decide +kernel)
private def cert21_53 := witnessLow51 21 0 0 630000 630000 1 20
  0x6930903 (by decide +kernel)
private def chunks21 : List (Chunk 21) := [
  cert21_0, cert21_1, cert21_2, cert21_3, cert21_4, cert21_5, cert21_6, cert21_7, cert21_8, cert21_9,
  cert21_10, cert21_11, cert21_12, cert21_13, cert21_14, cert21_15, cert21_16, cert21_17, cert21_18, cert21_19,
  cert21_20, cert21_21, cert21_22, cert21_23, cert21_24, cert21_25, cert21_26, cert21_27, cert21_28, cert21_29,
  cert21_30, cert21_31, cert21_32, cert21_33, cert21_34, cert21_35, cert21_36, cert21_37, cert21_38, cert21_39,
  cert21_40, cert21_41, cert21_42, cert21_43, cert21_44, cert21_45, cert21_46, cert21_47, cert21_48, cert21_49,
  cert21_50, cert21_51, cert21_52, cert21_53]

def rows21 := rowsFrom chunks21

theorem good21 : ∀ r ∈ rows21, good 21 r = true := rowsFrom_good chunks21

theorem sorted21 : rows21.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks21 0 (by decide +kernel)).1

theorem mass21 (i : Fin 54) :
    bandCount 21 (i.val : ℤ) 53 13 ≤ (rows21.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks21).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 21 (j : ℤ) 53 13 ≤ mass j chunks21)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total21 : (rows21.map (price 21)).sum = 138773 :=
  (total_eq chunks21).trans (by decide +kernel)

private def cert22_0 := witnessLow51 22 53 0 130589 130839 9 841
  0x0 (by decide +kernel)
private def cert22_1 := witnessLow51 22 52 0 140526 140838 12 1109
  0x1322640b113204c810200 (by decide +kernel)
private def cert22_2 := witnessLow51 22 51 0 150463 150838 16 1464
  0x202464448131042840a9142050815200 (by decide +kernel)
private def cert22_3 := witnessLow51 22 50 0 160400 160837 20 1817
  0x13204262284481510428268488151342440a882122048812200 (by decide +kernel)
private def cert22_4 := witnessLow51 22 49 0 170337 170837 25 2251
  0x2012311442444815131062822848825248448815144244129122048812200 (by decide +kernel)
private def cert22_5 := witnessLow51 22 48 0 180274 180836 30 2684
  (packedSchedule 0x61c4fdc21e85ef8b33df82b209d4e6ba7a67a6f8d0e9f7e55e6f6877fcdf4cfb341d) (by decide +kernel)
private def cert22_6 := witnessLow51 22 47 0 190211 190836 35 3101
  (packedSchedule 0x18a309e1e01ef0bdf17bc36257f01e35d3d33d3efe9b4e50e9dec50f1e461079439b9b3420) (by decide +kernel)
private def cert22_7 := witnessLow51 22 46 0 200148 200835 40 3518
  (packedSchedule 0x6184fdc26b80f785ef7f145b04db46a1e35d3d33dff53a4cdca1e3efb34d70286bbacb4ee005b9b9b3425) (by decide +kernel)
private def cert22_8 := witnessLow51 22 45 0 210085 210835 45 3920
  (packedSchedule 0x85184f35eafdc07bc34257f06b9a878d74e3fe9e27ed307aa74e50fd7a9fc233a7dfc233e119be8c9439b9b3429) (by decide +kernel)
private def cert22_9 := witnessLow51 22 44 0 220022 220834 50 4325
  (packedSchedule 0x6100fdc39e55fbdf8516c12641a9ae6a1e35d3dfeda9eb6aa74e50f1e2a8a6a4b7c6fac8ae371dc31b8dc69439b9b342b) (by decide +kernel)
private def cert22_10 := witnessLow51 22 43 0 230021 230834 54 4621
  (packedSchedule 0x1184fcf087de1802bf8cf0d4d7350f5384fda635ea43d53a74eb1ffebb69286f8dd3a7a6abf1b7c24c6d3abf1b8dc69439b83fc23c30) (by decide +kernel)
private def cert22_11 := witnessLow51 22 42 0 240020 240833 58 4922
  (packedSchedule 0x61ab7ee1d037c045b04f8b35cf0d4d7bf9913c645487aa74e9d78e154556da3ed3e369cf2bf50b8dd37050b8d50b8dbe99e371b8d02d843831) (by decide +kernel)
private def cert22_12 := witnessLow51 22 41 0 250019 250833 61 5119
  (packedSchedule 0x2ae309fa061aad5fc68135cf29807ed3679526bd487aa74feb323fada3ed3b751ffa43d4d0c6f5ca6125731d5f5cae5731b8d28737030) (by decide +kernel)
private def cert22_13 := witnessLow51 22 40 0 260018 260832 64 5324
  (packedSchedule 0x3090bf6fd5c5b04d1e35d037ff173de2ea4d7a90f63015155320f83c7da76eb4e787038d4f5cd3496e28b35cbeeceb94d33ae572b98dc6816c33) (by decide +kernel)
private def cert22_14 := witnessLow51 22 39 0 270017 270832 66 5428
  (packedSchedule 0x218c4310abf8e7d9a756fda6d03539e549afebf17fc641f078fb4ffb3d26b872dab9d3f646ea3fe9ff2bfc9b35cd357e4d9ae64d9ae5f7dab95cae6371a50c39) (by decide +kernel)
private def cert22_15 := witnessLow51 22 38 0 280016 280769 68 5542
  (packedSchedule 0x5f218b609e7b7bfd1e9ea3d539e63aba8aaf8b3e35cf83c7da7a73c7b4e2dab9d3f646eba4d6daa6b5db9674dd99678d332ccb32ceb95cc6e3433) (by decide +kernel)
private def cert22_16 := witnessLow51 22 37 0 290015 290768 69 5560
  (packedSchedule 0xf1cf7ed3217ed373ecd4e81f5d1efef167c6b9f07b4e781c322e43d73a75929ff0e193a9d84e98637a67d8b3bf92dcb3a6fb166599675cae63434) (by decide +kernel)
private def cert22_17 := witnessLow51 22 36 0 300014 300768 71 5657
  (packedSchedule 0xd48452bbe7abcf73dbe321a8aad1e3ecf0f8d7a73d5778e0c8b90f5ce9fb26935320516d7ae9e6ed3e662c6e0b3d27d956e0b3f1b82cefee0b32ccb3ae57039) (by decide +kernel)
private def cert22_18 := witnessLow51 22 35 0 310013 310705 71 5591
  (packedSchedule 0xbe6a4237d346db3ebe7b7fea3c7d9e69d021cf17726bdc87ae74f4ff8f6e4db5eba7ec55934d4db54d50b77acc269e4b7b931bed725c97216659d7035) (by decide +kernel)
private def cert22_19 := witnessLow51 22 34 0 320012 320704 72 5606
  (packedSchedule 0x13dcfcc533521cc5579edcfb40d39e21bc71e2ee4d7b90f6935f1628323d43deba7319a6710858a1dbbd69bba6d76f4db8b9177eadee4a7b8b92e4b90b32cc39) (by decide +kernel)
private def cert22_20 := witnessLow51 22 33 0 330011 330704 72 5527
  (packedSchedule 0x54908a6fcf73de7fdcf6f8cd4855c3947ae73cb935e9ff55dec9323d43deba7ec5d35264535cdb4ada7a0ab253c9c42c61cf5984e9b9cab0eb93c61d725fc3ae4b92e42cc3e) (by decide +kernel)
private def cert22_21 := witnessLow51 22 32 0 340010 340641 72 5461
  (packedSchedule 0xbf524237d56369139ee7de38a3d739e6935a3c28f17ea6bfa87bd74f4ce0f6f7b6d2b69deb18ce93eb6a9a876f11f377d7eade05c7b881605816e4b9035) (by decide +kernel)
private def cert22_22 := witnessLow51 22 31 0 350009 350640 71 5308
  (packedSchedule 0x3fb9f98a75243980e73dbdce81a7fc437b27c5fa9afea1ed353e2e9ae4c8560f2b69e82d3c9842c434ddde5055934d42de9b0e88f612bb566f02d3c3a0581605b903b) (by decide +kernel)
private def cert22_23 := witnessLow51 22 30 0 360008 360640 71 5229
  (packedSchedule 0x3e2114dffee7bcce39edf1d490ab8a28f7ae79ea6bd338abbdde990ac1e56d3bd6d27c64537adb569a764deba1c58ca223e6ee9dc78ca205f19440b7f28816058143b) (by decide +kernel)
private def cert22_24 := witnessLow51 22 29 0 370007 370577 69 5003
  (packedSchedule 0x5f3e211bc391b489ff73ef64d1ef5cf34d4d1ea6b9f16ac6bab0795b4f4f24f6b396d5a69dde505d3736d53434dfa84bac9eb566e65309c78755d816aec0b576058143a) (by decide +kernel)
private def cert22_25 := witnessLow51 22 28 0 380006 380576 68 4854
  (packedSchedule 0x1c73f314cf8873028e7b7f5d034ce086f77be2d58d7560f693ef174dea645a07ad34f11febf51c063ea7abac9b4d0ede9b2832a6eaeed1bd5d8169e5157605abb02d5d8143c) (by decide +kernel)
private def cert22_26 := witnessLow51 22 27 0 390005 390576 66 4619
  (packedSchedule 0x1724229be71cf79e4f3dbe33e2157a6b9a3cad9e2b1af4f26aef338645a07ad34eef34dc9914cad6d7569fa84bfae1a1613af50975934ab6549d4ca613e13ad5d816fa75abb02d5d81441) (by decide +kernel)
private def cert22_27 := witnessLow51 22 26 0 400004 400513 64 4401
  (packedSchedule 0xbf7242378a23691338e7deef68f2b679a4fa8f537af8bb435ed03d69a7f5fa9ed18f6d7569ccad3eb6d535a6a73fec9bd768ddf01953771e507fe053ff029ff81438) (by decide +kernel)
private def cert22_28 := witnessLow51 22 25 0 410003 410512 61 4104
  (packedSchedule 0x3279f98a7724398a6b9e7b756d034f2486f339e2ed0d7b40f69b9f174cac647507bab4fd5b19f5ab42163ab539bc12fa61a6f4c9d4de09759177d4ddf0194c269a753ff029ff8143f) (by decide +kernel)
private def cert22_29 := witnessLow51 22 24 0 420002 420512 59 3877
  (packedSchedule 0xf52114dfc9e7bcfbde7b7c77242af4deb47ad33cb435fd7eb577863991d41eead3d5dd3ea64535a5b549a77c0657ad948b14964ffb26d3699552597c0654ddf14964ffc0b7e92c9ff81443) (by decide +kernel)
private def cert22_30 := witnessLow51 22 23 0 430001 430449 55 3519
  (packedSchedule 0xbfea4237d35cc6d22793cfbcce51eb4cf34dcd1ea656f17d46bf507bab4feb56002c755b549a7a4a0fd2ad6d53756a70ca6f04bfafa9b86537825d64c69d4b2994c24329ff8143d) (by decide +kernel)
private def cert22_31 := witnessLow51 22 22 0 440000 440448 52 3234
  (packedSchedule 0x1def3f314fd487314debcf6f69a07d7ea437863f8bea35fa83da7d7c5d35a191481ea4d39fff5da42162935396532b4da6a7a6a4b2194ffb265dd2372ca654dda74964329ff8143f) (by decide +kernel)
private def cert22_32 := witnessLow51 22 21 0 450000 450448 48 2871
  (packedSchedule 0x1588452bbf5e7bcd9ce7b7c7ea42af4cad47bab3cea35fd6ad562c75191481ea4d3be0d2ac6453755b5ced3865a4a0ff5f5621639d64329bc12fa7ab2ae7590ca6f04bac9e39d64b2994c2443) (by decide +kernel)
private def cert22_33 := witnessLow51 22 20 0 460000 460385 44 2529
  (packedSchedule 0x17d58846fa6f58dadfd7ebcfbc31e8f75679a7d68f535a78ba435e903d49a7f5da0016292dae769c329ffd3696d53526a7fac594caf5d23737a7fd9363a4b3f58b29953743c) (by decide +kernel)
private def cert22_34 := witnessLow51 22 19 0 470000 470384 40 2210
  (packedSchedule 0xce73f314d5887314cadcf6fd5a07d6ac422c7578ba435e903da55bc5d375191ce0f73b4e597d7d50858e76a737b4941fa7ab53d373ac9bd37825d77ce6e6f4de0975903b) (by decide +kernel)
private def cert22_35 := witnessLow51 22 18 0 480000 480384 37 1953
  (packedSchedule 0x16842295dab73de631f9edf1ab10abd35a51ea4cf290d7f5da558b148647383dced3865d3686453525b407e9cde9fff5d2621600fb3f58b2995a6932a03ec9bd3fec983b) (by decide +kernel)
private def cert22_36 := witnessLow51 22 17 0 490000 490321 33 1671
  (packedSchedule 0xbf684237d32b46d6feb56e78b1d547a933cd2ad47a9babc5f38d7e707b9da7f5f5001639d6d01fa7fac5974f55b54dced4f44cded2507faf9cde899bd37825c37) (by decide +kernel)
private def cert22_37 := witnessLow51 22 16 0 500000 500320 30 1450
  0x51c9848212b928904247261724a289451c9460a4920ba23154442915c905924918bb22156422ac8d11251492218296422f08d91a2324608a2c908b24b25846c8d11923045c8b11 (by decide +kernel)
private def cert22_38 := witnessLow51 22 15 0 510000 510320 27 1245
  0x104a280c5451c984428a4130b3572511084904a2e89055118a251482418294462ec8855908ab228b0462c928885e108ac2364688c912514a21182984b08d91a2324608b91 (by decide +kernel)
private def cert22_39 := witnessLow51 22 14 0 520000 520257 24 1053
  0x15825130848e4e2c9451c9860a4928ba24148ae4a2c924905d918ab221564228945248c60a5910bc2115846c8d114592216496422f48e11b2344648c11 (by decide +kernel)
private def cert22_40 := witnessLow51 22 13 0 530000 530256 21 879
  0xa41309042582512084904c2e8945128a4128c14a24176462ac88522c120b24a23178442b0845611b224a2944430530845e91c2364688c91 (by decide +kernel)
private def cert22_41 := witnessLow51 22 12 0 540000 540256 19 752
  0x124a280c54520984428a4930b3582511084924a2ec9055918a251492418296462f08856108ac228b2462c92c885e908ad23846c8d11 (by decide +kernel)
private def cert22_42 := witnessLow51 22 11 0 550000 550193 16 602
  0x1592513084904e2c945209860a5128bb24148b04a2c928905e118ac221584228945288c60a6110bd2115a4708d91 (by decide +kernel)
private def cert22_43 := witnessLow51 22 10 0 560000 560192 14 498
  0x5249848212c928904249261764a28945249460a5920bc231584429164905925918bd2215a422b48e11 (by decide +kernel)
private def cert22_44 := witnessLow51 22 9 0 570000 570192 12 404
  0xa2514062a2924c22145289859ac92888424a25178482b08c5128a5120c14c2317a442b4845691 (by decide +kernel)
private def cert22_45 := witnessLow51 22 8 0 580000 580129 10 316
  0x568944c2124938b2514926182964a2f090522c928b24b2417a462b48856908a (by decide +kernel)
private def cert22_46 := witnessLow51 22 7 0 590000 590128 8 240
  0x14a2612084b44a2410928985e128a2514a2518298482f48c56910a (by decide +kernel)
private def cert22_47 := witnessLow51 22 6 0 600000 600128 7 196
  0x164a280c54528984428a5930b35a2511084964a2f49056918a (by decide +kernel)
private def cert22_48 := witnessLow51 22 5 0 610000 610065 5 131
  0xad92898424a27164a2944c30530945e920a (by decide +kernel)
private def cert22_49 := witnessLow51 22 4 0 620000 620064 4 98
  0x14b2612084b64a241092c985e928a (by decide +kernel)
private def cert22_50 := witnessLow51 22 3 0 630000 630064 3 69
  0x184a280c5452c984428a6130b (by decide +kernel)
private def cert22_51 := witnessLow51 22 2 0 640000 640001 2 42
  0x570944c2125938b (by decide +kernel)
private def cert22_52 := witnessLow51 22 1 0 650000 650000 1 20
  0xa6130904 (by decide +kernel)
private def cert22_53 := witnessLow51 22 0 0 660000 660000 1 19
  0x6928a03 (by decide +kernel)
private def chunks22 : List (Chunk 22) := [
  cert22_0, cert22_1, cert22_2, cert22_3, cert22_4, cert22_5, cert22_6, cert22_7, cert22_8, cert22_9,
  cert22_10, cert22_11, cert22_12, cert22_13, cert22_14, cert22_15, cert22_16, cert22_17, cert22_18, cert22_19,
  cert22_20, cert22_21, cert22_22, cert22_23, cert22_24, cert22_25, cert22_26, cert22_27, cert22_28, cert22_29,
  cert22_30, cert22_31, cert22_32, cert22_33, cert22_34, cert22_35, cert22_36, cert22_37, cert22_38, cert22_39,
  cert22_40, cert22_41, cert22_42, cert22_43, cert22_44, cert22_45, cert22_46, cert22_47, cert22_48, cert22_49,
  cert22_50, cert22_51, cert22_52, cert22_53]

def rows22 := rowsFrom chunks22

theorem good22 : ∀ r ∈ rows22, good 22 r = true := rowsFrom_good chunks22

theorem sorted22 : rows22.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks22 0 (by decide +kernel)).1

theorem mass22 (i : Fin 54) :
    bandCount 22 (i.val : ℤ) 53 13 ≤ (rows22.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks22).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 22 (j : ℤ) 53 13 ≤ mass j chunks22)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total22 : (rows22.map (price 22)).sum = 152784 :=
  (total_eq chunks22).trans (by decide +kernel)

private def cert23_0 := witnessLow51 23 53 0 160464 160839 16 1490
  0x0 (by decide +kernel)
private def cert23_1 := witnessLow51 23 52 0 170401 170838 20 1835
  0x1322644c81622645c81322e40b113204c810200 (by decide +kernel)
private def cert23_2 := witnessLow51 23 51 0 180338 180838 25 2269
  0x101232464448161342e20850816104464508131042840a9142050815200 (by decide +kernel)
private def cert23_3 := witnessLow51 23 50 0 190275 190837 30 2699
  0x4c81199131142240b102231042e228488151342e2a84881615428268488151342440a882122048812200 (by decide +kernel)
private def cert23_4 := witnessLow51 23 49 0 200212 200837 36 3210
  (packedSchedule 0x10667dfa7e9e17be2ccf0d51e1dde34f4cf4ba88a88b7f951bcdf4fde9883ef887a641f4cfb3422) (by decide +kernel)
private def cert23_5 := witnessLow51 23 48 0 210149 210836 41 3622
  (packedSchedule 0x18631ef4f843d0bdf17bdf82b37edb183c6ba7a67a64dbfa9da1e3fb2bbc6343a6f8d0e9f7e55e6f6877fcdf4cfb342a) (by decide +kernel)
private def cert23_6 := witnessLow51 23 47 0 220086 220836 47 4115
  (packedSchedule 0x4eccf13f53c3c03de17bc345b213a9fc078d74f4cf4fbfa63ba4b72874f951afd65c7ef79b250e9dec50f1e461079439b9b342d) (by decide +kernel)
private def cert23_7 := witnessLow51 23 46 0 230023 230835 52 4512
  (packedSchedule 0x30e214fb0f6135c07bdf6cb3158b0635cd43c6ba71ff7f2b8d7eda499b943c7df67d78632338c9a8ce3efb34d70286bbacb4ee005b9b9b3434) (by decide +kernel)
private def cert23_8 := witnessLow51 23 45 0 240022 240835 57 4895
  (packedSchedule 0x6259d3e13f53cd7abf786c437909b6bc1ae6a1e35d3d38c43f14635b6aa74e50f1f2a35fa48b08ce9f7566548ce3bdbc233a7dfc233e119be8c9439b83fc23c3a) (by decide +kernel)
private def cert23_9 := witnessLow51 23 44 0 250021 250834 61 5186
  (packedSchedule 0x618429f66be1cf2fe26c6f150b06cf0d4d7350f5ff115d15f3227adaa9d3a758ffc70567d787151431be374936fd4b7c6e9efb37922b8df5915c6e3b86371b8d02d84383f) (by decide +kernel)
private def cert23_10 := witnessLow51 23 43 0 260020 260834 65 5467
  (packedSchedule 0x4259d3c03f53f3c868437909323c6786a6bd3c42987c28c6a645487aa74e9d7fdc5835f351c1286f8dd3dfab31464cf1a9e4fa678da9ef4d57e36f8498da757e371b8d28737040) (by decide +kernel)
private def cert23_11 := witnessLow51 23 42 0 270019 270833 68 5658
  (packedSchedule 0x308014fbcf2fc26c6f140306d026b9e5fe115d15ff173c645487aa74f8f145bf5e18545536d1f69dba8ff8d628d7e197942e36a77d95611550b8df2c8aa85c6e9b8285c6a85c6df4cf1b8dc6816c47) (by decide +kernel)
private def cert23_12 := witnessLow51 23 41 0 280018 280833 71 5844
  (packedSchedule 0xb3a7d5bf61800de427c5f8d034e10a61e0231af8ba935ea43dfd85835f353dbfd6d1f69dbae9c4fd56428d6bb7ae2798a35f3e6f5ca1ef7c38deb94c24ae63abeb95cae6371a50c44) (by decide +kernel)
private def cert23_13 := witnessLow51 23 40 0 290017 290832 73 5942
  (packedSchedule 0x61ab14df00d8de2aaf06e7d9bf802ba2bf47a7bc5d49af8e145bf5e1014552641f078fb4ffb38d428d7ea47038d4fd91ba8ffa98aa15949a27dab9a662bed5ca9701459ae5f7675ca699d72b95cc6e344a) (by decide +kernel)
private def cert23_14 := witnessLow51 23 39 0 300016 300832 75 6038
  (packedSchedule 0x2ad6786ab1bc8490913002987d5c635a3d539e7f4060d7cd6aef7f1907c1e3ed3e984fd56008c7d6d5ce9fb23754f2146bf6bdec9b35ca1a7a61c6f9366b98c24c9b35cd357e4d9ae64d9ae5f7dab95cae6344e) (by decide +kernel)
private def cert23_15 := witnessLow51 23 38 0 310015 310769 76 6049
  (packedSchedule 0x2fd5b6370490e62ff5657457f9ede7a8f630116fd786ae8aa7c59f1ae7c1e8d008d7ea4f69c5b573a7592a42a8a755854550b7613a526a2bf72dcb3a170be286e59d376659e34ccb32ccb3ae57049) (by decide +kernel)
private def cert23_16 := witnessLow51 23 37 0 320014 320768 77 6062
  (packedSchedule 0xf04229a75629d0a42f035e7b7fed5e0d7cd486f7f78b3e35f4807eab2ae31f191721eb9d3f644f0046be7c3864ea79bb403cac86516e0b3d3fd1b7059d4abe99f62cefe4b72ce9bec5996659d7048) (by decide +kernel)
private def cert23_17 := witnessLow51 23 36 0 330013 330768 78 6057
  (packedSchedule 0xd6ae58bb2182e31b6ce3ab8b7ebc2434553478fb3c8d55c6bf535778e0c8b90f5ce9ea00a8a7550145736d7ae9fb1564d33d0a8afd422c6e184d0a49131437f1b82cf1bb3f1b82cf49f655b82cfc6e0b3bfb82ccb32cc51) (by decide +kernel)
private def cert23_18 := witnessLow51 23 35 0 340012 340705 78 5991
  (packedSchedule 0xbe6b573f5373dfbeb212ba2be6bcfbdfd47b4d5bf5584318fbc5dc9af721e4f2ae35f3e3db936d7ae9cc6681af4c390a8a876ef5a6ee94a28affab7b92855f79b96f7253c96f72637dae4b92e42cc49) (by decide +kernel)
private def cert23_19 := witnessLow51 23 34 0 350011 350704 78 5907
  (packedSchedule 0x13c420bd335ab05ef3cfc1aa79edfcb21c1afd490de38f17726bd4aba8a755aba2b9323d43deba7ec5d33c028afdcc2162876f41564a06b6d2b2d7a2c39eb309d2711b0eb92a2674db8b9177eadee4a7b8b92e4b904e) (by decide +kernel)
private def cert23_20 := witnessLow51 23 33 0 360010 360704 78 5828
  (packedSchedule 0xa9ab965f9e2187e6b1b5be335ab1bd59cf8c7d47ae73c4f08635f3eabbd92647a87bd74f433ca61c0145eb6d2b69deb18ce9fe85457e871630e7ad3768431bab2e5bf8c3ae4c792dfc61d7269b9cab0eb93c61d725fc3ae4b9053) (by decide +kernel)
private def cert23_21 := witnessLow51 23 32 0 370009 370641 77 5669
  (packedSchedule 0x17ea6ae7eaaf3f314e78843b9fefd4f3ef1c51ed26b5798a75521a2b9f17ea6bfa87b4cf55d15fb93dbdedb4ada7a0b40d4c8a62885450d3777941564d3cce8afab3788f6134133bcfab7817d7eade05c7b8816058144f) (by decide +kernel)
private def cert23_22 := witnessLow51 23 31 0 380008 380640 76 5519
  (packedSchedule 0x1fc420bd3a9ab05efd579ef03ee7b7c73c42f0be7c437b27c5fa9af50d6ad5e9872ae8bd4c8560f2b69deb69fe01457fd610b10d3764d42a6da565434594447cddd3931b28816a3ed4d8740abb566f02d3c3a058144f) (by decide +kernel)
private def cert23_23 := witnessLow51 23 30 0 390007 390640 75 5346
  (packedSchedule 0x1f55cb2fff10c3fa98dadf1d4d58df4eabcfa2b9a3deb9e699e21a2bf73577bbd321583cada7a06b5644c5002895adab4d3bbca0ba4e21515f86858ca1de50559285aedd59eadfc65111ec271f7adfc65102e9dc78ca205f19440b7f2881457) (by decide +kernel)
private def cert23_24 := witnessLow51 23 29 0 400006 400577 73 5129
  (packedSchedule 0xbe7d573f0739f98a7fc421dcff7cfb9f7b268f69a9abcc530e10d17af8b5635d583da7faae8affa9ed672dab4d3c47d0a932159730a8ad353d5d64da7271515fb46e654dda0fb5e559bd5d817d6acdeaec0b8f0eabb02d5d81452) (by decide +kernel)
private def cert23_25 := witnessLow51 23 28 0 410005 410576 71 4889
  (packedSchedule 0x382105e99f5582f7c39cf785cf3dbe3fe21785fb921bddef8b5635ea54d5abd31455d12b191681eb4d3bbcd270028afab0e031f53f5097a07d6d2b287a24ebd425d64d3dec64ea65309a9b8a6ca2aec0abbb46f57605a79455d81453) (by decide +kernel)
private def cert23_26 := witnessLow51 23 27 0 420004 420576 69 4662
  (packedSchedule 0x2e6ae597ce0861f9f46d6f8cfaac6fa61ce7d17ad1e56cf34ff10d15ff5abbcce191681eb4d3d0a9f16acb90145696d7569ccad3930a8afb291613ad5d64d42a16eac566fe13a995377cb566fe13ad5d8174ab6549d6aec0be13ad5d81455) (by decide +kernel)
private def cert23_27 := witnessLow51 23 26 0 430003 430513 66 4359
  (packedSchedule 0x2fdcd5cfc28e7e6299c108773fdfb9e7deef68f693eabcc531410d12b78bb435ed03da4e2ae8afab1ed18f6d7569fab63340f8c8567ac2a2ead4e6f04ba7943d15fea6e6f04bac9437179b46ef80ca613ebb46e7fe05c7941ff81452) (by decide +kernel)
private def cert23_28 := witnessLow51 23 25 0 440002 440512 63 4073
  (packedSchedule 0x649082f4ee6ac17be28e7bc3d79edf19c10bc2ffa90de673c5da1af50faad5d5973574568647507bab4f5774e480a2bf690858ead4ef80caa1736d2b21aa2a4b27fd9369672352597c0654dda987532753ff02aefa9b9ff81452) (by decide +kernel)
private def cert23_29 := witnessLow51 23 24 0 450001 450512 60 3760
  (packedSchedule 0x3d6ae597f24861fdcc6d6f8ee6ac6fa628e7d12b51eb4cf349c10d15f56abbc31cc8ea0f7569e81f78b567a80a2eab6a934f4941fa7bd85457fab10b14964de097a143b7565a37f14964de097593cbb46fe292cbe032984e9b4caa92c9ff81459) (by decide +kernel)
private def cert23_30 := witnessLow51 23 23 0 460000 460449 56 3419
  (packedSchedule 0x17fd6ae7ea6b9e7e629e4908773fdff5e7de6728f69b9abcc2b2e4868ad3c5f51afd41ed39357457ed000b1d56d5269cffd0b932158ad0a8a93539653293c86a8afd2370ca7fd9350c3af3d4dcb2995377d7d4dc329ff81450) (by decide +kernel)
private def cert23_31 := witnessLow51 23 22 0 470000 470448 52 3051
  (packedSchedule 0x77a420bd3f5ab05ef373cf782b73dbe3c921785f5621bc31fc5f51af52e6ad5d59eb5745d4645207a934ef834f7a028aff5421629353865a4a0fa1eb6d2b194d173ac86537825f48c78dceb2194de097592a6514d4964b2994c2452) (by decide +kernel)
private def cert23_32 := witnessLow51 23 21 0 480000 480448 48 2704
  (packedSchedule 0x15aae58bbf52187feb1b5be3f5ab1bd5973cfa2b4a3dd59e69c921a2bf69562c75191481ea4d3d0b9f16ac560145496d73b4e194ffe96721515fa4c42c73ac96532a8434dd59d4dfc73ac8653fec9bcbea6fe39d64b299537452) (by decide +kernel)
private def cert23_33 := witnessLow51 23 20 0 490000 490385 44 2379
  (packedSchedule 0x5f56ab9fa9bd79f98f5fa908773fdf56e7de18f47b4fad5e6159ea4345d5e2e90d7a40f69ef6ae8aff50016292dae769cb2d0f532159690a8b9da9cded2507e918f8a8aff39b9bd37825e865179a46e6f4de0975904d) (by decide +kernel)
private def cert23_34 := witnessLow51 23 19 0 500000 500384 40 2075
  (packedSchedule 0x19c2105e9ab5582f79f5e7bc2d39edf1f7a42f0bf68422c7578ba435ea7ad5abab15aae8a90c8e707b9da70cba59c01457e9210b1ced4e6f4ffd056b6959d58a880fb3f58b29949e754603ec9bd3fec9849) (by decide +kernel)
private def cert23_35 := witnessLow51 23 18 0 510000 510384 37 1830
  (packedSchedule 0xb4ab962ed58861fab46d6f8d5aac6f567af3e8baa8f52679a7bd21a2bfd5562c52191ce0f73b4f43d7c5ab2d005173ada03f4ff58b2e918f0a8aff3b10b007d937b4941f42d353ab291bf803ec9bd37825c4a) (by decide +kernel)
private def cert23_36 := witnessLow51 23 17 0 520000 520321 33 1565
  (packedSchedule 0x17ed2ae7ea656e7e63d6ac421dcff7ed39e2c7551ed2ad5798562b10d15278be71afce0f69672ae8afd2001639d6d01fa737b4158c8567542a203f53d1337a7fd3ceac5457c0f6f44feb16532845) (by decide +kernel)
private def cert23_37 := witnessLow51 23 16 0 530000 530320 30 1355
  (packedSchedule 0x31c8417a769560bde55b9ef0eae7b7f2d5885e17fa88458a4f17ce35ea2b55abab2d2ae8b9c6401e1e03f4ff5b48c701457f9d085803f53d13fac59685a5b4aca4c544c959a266f69283c43) (by decide +kernel)
private def cert23_38 := witnessLow51 23 15 0 540000 540320 27 1161
  0x10482c0c5451c944c28c3938b3572413084a48c4c305e4945d120a4514625182e2b248305288c5d910ab2114cac482c949208c60bd910bc2115846c8d114514822182e2b642305309611b2344648c11 (by decide +kernel)
private def cert23_39 := witnessLow51 23 14 0 550000 550257 24 982
  0x15824150848e4c24109451c944828b8ac130c14925168ae4824109491c9460bd120bb2315644291451c9060b8ad118c14b22178422b08d9165723164a49244305f0845e91c2364688c91 (by decide +kernel)
private def cert23_40 := witnessLow51 23 13 0 560000 560256 21 818
  0xa4128a042582414082a48e4c22145e49859a8a3928885171592518294482ec8c52ab9208842524824182f6462f08856108ac228a29046305c56c8860a6108bd23846c8d11 (by decide +kernel)
private def cert23_41 := witnessLow51 23 12 0 570000 570256 19 698
  0x12482c0c54520944c28c4138b3582413084a48e4c305e8945d920a4514725182e2b4483052c8c5e110ac2114cae482c949248c60be110bd2115a4708d91 (by decide +kernel)
private def cert23_42 := witnessLow51 23 11 0 580000 580193 16 560
  0x1592415084904c241094520944828b8ac930c14a25168b0482410949209460bd920bc231584429145209060b8ad918c14c2217a422b48e11 (by decide +kernel)
private def cert23_43 := witnessLow51 23 10 0 590000 590192 14 462
  0x5249450212c920a041524826110a2f44c2cd4520944428b8ad128c14b2417846295609044212924920c17c2317a442b4845691 (by decide +kernel)
private def cert23_44 := witnessLow51 23 9 0 600000 600192 12 374
  0xa2416062a2924a26146249c59ac9209842524826182f64a2f0905228a4128c1715b2418298462f48856908a (by decide +kernel)
private def cert23_45 := witnessLow51 23 8 0 610000 610129 10 294
  0x568905421249309042514925120a2e2b44c3052c945a2c9209042524925182f8482f48c56910a (by decide +kernel)
private def cert23_46 := witnessLow51 23 7 0 620000 620128 8 222
  0x14a2514084b448281054924984428bd930b3514925110a2e2b64a30530905e918a (by decide +kernel)
private def cert23_47 := witnessLow51 23 6 0 630000 630128 7 181
  0x16482c0c54528944c28c5138b35a2413084a4924c305f0945e920a (by decide +kernel)
private def cert23_48 := witnessLow51 23 5 0 640000 640065 5 122
  0xad920a8424a2612084a2944a24145c56c9860a6128b (by decide +kernel)
private def cert23_49 := witnessLow51 23 4 0 650000 650064 4 91
  0x14b2514084b648281054928984428be130b (by decide +kernel)
private def cert23_50 := witnessLow51 23 3 0 660000 660064 3 64
  0x18482c0c5452c944c28c5938b (by decide +kernel)
private def cert23_51 := witnessLow51 23 2 0 670000 670001 2 40
  0x57090542125930904 (by decide +kernel)
private def cert23_52 := witnessLow51 23 1 0 680000 680000 1 19
  0xa6128a04 (by decide +kernel)
private def cert23_53 := witnessLow51 23 0 0 690000 690000 1 18
  0x6920b03 (by decide +kernel)
private def chunks23 : List (Chunk 23) := [
  cert23_0, cert23_1, cert23_2, cert23_3, cert23_4, cert23_5, cert23_6, cert23_7, cert23_8, cert23_9,
  cert23_10, cert23_11, cert23_12, cert23_13, cert23_14, cert23_15, cert23_16, cert23_17, cert23_18, cert23_19,
  cert23_20, cert23_21, cert23_22, cert23_23, cert23_24, cert23_25, cert23_26, cert23_27, cert23_28, cert23_29,
  cert23_30, cert23_31, cert23_32, cert23_33, cert23_34, cert23_35, cert23_36, cert23_37, cert23_38, cert23_39,
  cert23_40, cert23_41, cert23_42, cert23_43, cert23_44, cert23_45, cert23_46, cert23_47, cert23_48, cert23_49,
  cert23_50, cert23_51, cert23_52, cert23_53]

def rows23 := rowsFrom chunks23

theorem good23 : ∀ r ∈ rows23, good 23 r = true := rowsFrom_good chunks23

theorem sorted23 : rows23.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks23 0 (by decide +kernel)).1

theorem mass23 (i : Fin 54) :
    bandCount 23 (i.val : ℤ) 53 13 ≤ (rows23.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks23).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 23 (j : ℤ) 53 13 ≤ mass j chunks23)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total23 : (rows23.map (price 23)).sum = 166566 :=
  (total_eq chunks23).trans (by decide +kernel)

private def cert24_0 := witnessLow51 24 53 0 190339 190839 25 2320
  0x0 (by decide +kernel)
private def cert24_1 := witnessLow51 24 52 0 200276 200838 30 2735
  0x4c8991322640b11322e45c81322e45c81622645c81322e40b113204c810200 (by decide +kernel)
private def cert24_2 := witnessLow51 24 51 0 210213 210838 36 3242
  0x2024648c9191120584d0b882171342841312322e268508161342e20850816104464508131042840a9142050815200 (by decide +kernel)
private def cert24_3 := witnessLow51 24 50 0 220150 220837 42 3745
  (packedSchedule 0x30f7fefdfdecad3e2c1fdf8f27f951b4f4cf5aa8f6ed087a5d9b6cf887869fbf6699e97953e533df7ca67bfdf6421db342b) (by decide +kernel)
private def cert24_4 := witnessLow51 24 49 0 230087 230837 48 4234
  (packedSchedule 0x4199f7eb599e9e17be2b39fa199fc3a9fc69e99e9751153f0d1bcdfca1a35fe97cdf4ba88a88b7f951bcdf4fde9883ef887a641f4cfb3431) (by decide +kernel)
private def cert24_5 := witnessLow51 24 48 0 240024 240836 54 4719
  (packedSchedule 0x30c63df7fef4f843d0ab54622aa3c6761e35d3d33f286572ed9eeea76878fecdfb6c65db76874c9b4f2af37e3fb2bbc6343a6f8d0e9f7e55e6f6877fcdf4cfb3439) (by decide +kernel)
private def cert24_6 := witnessLow51 24 47 0 250023 250836 59 5095
  (packedSchedule 0x13b338c2dd3a787807bc345bbe198d86daf01e35d38ffa5c5ba63b86c545496e50f95fe353a8eed65c7f514dddddacb4f951afd65c7ef79b250e9dec50f1e461079439b83fc23c40) (by decide +kernel)
private def cert24_7 := witnessLow51 24 46 0 260022 260835 64 5472
  (packedSchedule 0x30acfef13f7d87b09af7db2cc545bf1ef14635cd43c6ba7bfbf70b67bb6d24cdca1e3f7ed3b6c65de2a246719371cfa330c59f5e18c8ce326a338fbecd35c0a1aeeb2d3b814302d843844) (by decide +kernel)
private def cert24_8 := witnessLow51 24 45 0 270021 270835 68 5742
  (packedSchedule 0x2f6678852b43c9e6bc336372ee2c1b0991e0d7350f538c43cae34342a235b6aa74e9d63fffb51eb4f8c930b08cc31518c777e78584671f2a35322be119d3eeacca919c77b784674fbf8467c2337d192873704c) (by decide +kernel)
private def cert24_9 := witnessLow51 24 44 0 280020 280834 72 6016
  (packedSchedule 0xc38a59ee13f7d9af7f62cc5621bfc7b851b3c3535efe29c2ea7ee9913d6d54e9d3af1c159c76d8cbb85450c6f8dd24dc78a30498de5a6ce304c60931ba49b7ea5be374f7d9bc915c6fac8ae371dc31b8dc6816c50) (by decide +kernel)
private def cert24_10 := witnessLow51 24 43 0 290019 290834 75 6188
  (packedSchedule 0x3102a9f0852b4d786c53f176160d87c5f8cf29acf0fc457450c0288d4c8a90f54e9ffb16fd69f8a8a78704a1bb751ffa7bfd23bbf3dafcfe99e374f2a363358c99e36a7b9db3e99e353c9f4cf1b53de9aafc6df0931b4eafc6e371a50c56) (by decide +kernel)
private def cert24_11 := witnessLow51 24 42 0 300018 300833 78 6367
  (packedSchedule 0x61852cf601fb7f16c378a8437f8f6023681bfe205f0b6d777c5cf191521ec6d965ab8b065d80a2a9b68fb4edd634571b1c28dfcafd42e36a77d9d2098d7ffaf285c6d426d3a96ea171b53becab08aa85c6f9645542e374dc142e3542e36fa678dc6e345d) (by decide +kernel)
private def cert24_12 := witnessLow51 24 41 0 310017 310833 80 6446
  (packedSchedule 0x840aa78014c3429f8ba0306c24244f14b21f08ae8a1aae88d7c5d49affdc437fad3e1514f1edfeb68fb4ffb3d3188e628d7e7b6a3fdaedfb23751ff53951b1d2689d9d7287bdb93eeceb953c4fdf3e6f5ca1ef7c38deb94c24ae63abeb95cae6345b) (by decide +kernel)
private def cert24_13 := witnessLow51 24 40 0 320016 320832 82 6535
  (packedSchedule 0x18404b2fc2d86f14006ff1efc5dfe102f85323bb47a7bc5e3c4d8ddab0b065dd5d1549907c1e3ed3c6b115d163011bf87038d4fd91bad482b3a4138a8afff6bf3fbed5ca04dc75319f6ae50efb38eab19f6ae6998afb572a5c05166b97dd9d729a675cae57060) (by decide +kernel)
private def cert24_14 := witnessLow51 24 39 0 330015 330832 83 6529
  (packedSchedule 0x56180360b09f5798a70a590f0057450c43446b47bfb086ff5a780a29eabbdfc641f07b4e214c72146bf3c4e1fcfadab9d3ac93be2c1b19ac2a23857f9367b23751ff43bfb73146be717b26cd728789fa67cdf26cd70e7de9871be4d9ae6309326cd734d5f9366b99366b97df6ae5706d) (by decide +kernel)
private def cert24_15 := witnessLow51 24 38 0 340014 340769 84 6534
  (packedSchedule 0x5f01b0dc13560bdfc002ebb4fab79f779edf1c26c6ed501832ec868aa7c59f1af1a8457458eae37f1ed38b6ae74fd92a628b7a4130a8afff6d47fa85bcdd207146c70ca2c96e599cf7d9d3558d92dcb3a9316fdcb72ce85c2f8a1b9674dd99678d332ccb32cc61) (by decide +kernel)
private def cert24_16 := witnessLow51 24 37 0 350013 350768 84 6447
  (packedSchedule 0x1e2ae594c04b342d5c3fc3cf6ffd0037fad3eae8a7886f7f78bd308531c011afcf7773f9f191721eb9d3cef0b06c66a0288e070c9d4fd8ab250c4fdb72146be71afcffb86134159c6c67d1b7059897be30e46dc167a7fa36e0b3a957d33ec59dfc96e59d37d8b32cc62) (by decide +kernel)
private def cert24_17 := witnessLow51 24 36 0 360012 360768 85 6440
  (packedSchedule 0x6a00cf5dd5b671e7bf71806c6febc3561dcfebbe7d154d1e8d002ba2c6431bfaaef1c191721ea90a2de90480a2bffc4e1fee6daf5d398c9030a363a98545938858dc4dd39c5516e5268afe48b1b82ce84c5a772dfc6e0b339b8531437f1b82cf1bb3f1b82cf49f655b82cfc6e0b3bfb82cc6c) (by decide +kernel)
private def cert24_18 := witnessLow51 24 35 0 370011 370705 84 6278
  (packedSchedule 0x5f350123e988453ebab21c6ff3f069ee7ded200538c1356f0bf3c42687f3ef17726bcee0306c66b5744707b726daf5d3f62d084fdb70046be71b51fe876f41564a1e2146c76bdeeefab77acc244b4fa438dfbbeadee4a9fd1affab7b92855f79b96f7253c96f72637dae4b9067) (by decide +kernel)
private def cert24_19 := witnessLow51 24 34 0 380010 380704 84 6192
  (packedSchedule 0x9eab5ba99a805baf24305c7c46d6fe5d5c171a7cf8dfc4378e3c5d40116f4826ae8afff7773fdc991ea1ef5d390202363a90145930858a1dbbd6319398551a6ab0a8afe4ebf3fe1cf5a6ed049a8b1dcc6c3ae412b8631446c3ae4d2711b0eb92a2674db8b9177eadee4a7b8b9067) (by decide +kernel)
private def cert24_20 := witnessLow51 24 33 0 390009 390704 83 6022
  (packedSchedule 0xa90067df9eab3966bcfcc6335013f2b084ae8afcf73cd0fe7d4793cab2ba2c66a434471577b24c8f50f5000fdb72ae35f38270ffeb6d2b69e82d0f0023633e1c3bb438b187505590483d6e4328977ea2c61cf5984d0fe8d4fd5bf8c3ae439abd5972dfc61d7263c96fe30eb934dce55875c9e30eb906e) (by decide +kernel)
private def cert24_21 := witnessLow51 24 32 0 400008 400641 82 5865
  (packedSchedule 0x17ea4048faa9082f4e7aac866535e7bc3fb9f7b49a8005ced21c1afff109a1fee7c5fa9af53c55e0d8ea6ae8b24f6f7b6d2b69deb1c80a8d35501457f276a3fc34dd93509e85458ee55ff7559bc47cdd12a4b7d2286fdd566f02d4388d7d59bc0b4133bcfab7817d7eade05c7b881469) (by decide +kernel)
private def cert24_22 := witnessLow51 24 31 0 410007 410640 80 5623
  (packedSchedule 0xfeab5ba9d4805bafd54861fcf46dbd8e7aae1fd335e7d11c10dec9f1750d400df6e10c6be71ddcffea642b0795b4f43c55c6c67c7b7bbeb0858869bbbca0a246be90e42a25dd0e687fca1de5055928251458fd6365111ec244aaf3b6e6365102e9c98d9440b51f6a6c3a055dab3781467) (by decide +kernel)
private def cert24_23 := witnessLow51 24 30 0 420006 420640 79 5458
  (packedSchedule 0xf8019f7ffaace5d4f3f318ea404fd4eaa421dcff7ffb9e687fb9a3da67aac3b9ff1d490d164d5deef4c8560f50350198d355aba2bf924e1fd5adab4d3c47d09e01458ee470eec342c650c9848d6dab72d7a25dab0b194447cdda0711a9ab37f19440a7299ab3d5bf8ca205c7deb7f19440ba771e3288146f) (by decide +kernel)
private def cert24_24 := witnessLow51 24 29 0 430005 430577 76 5153
  (packedSchedule 0x2f9f0091e1c2105e9ff5590ccb53cf781c73ef69a9000be3aa90bc2f9c109a1ffd7c5ab1af527aade18cfaaef777d4f6b396d5a69dde1c9a8057d21c0144bbf5da8ff69a9fa84bd0fe85458e87bdddb46fd425d64128637b72e5bf76d1b994c26a64c6bf68deaec0b41f6bcab37abb02fad59bd5d8146f) (by decide +kernel)
private def cert24_25 := witnessLow51 24 28 0 440004 440576 74 4919
  (packedSchedule 0x1c55add4cf802dd7c38430fffa36dec7fd570fe9d4f3e8b2486f77be2ea54801bf4d54868afe4f773fab191681eb4d3d09eaba2c7727b7baac380c7d4e65091a991a4510a8976adafcfe9d6aeb26a1cce8b1ab464ea654dd124ccedf58c9d6aec0ba7bd8c9d6aec0b53714d9455d81465) (by decide +kernel)
private def cert24_26 := witnessLow51 24 27 0 450003 450576 71 4610
  (packedSchedule 0xb90067df38ab3967dcfcc633e013f530e108773fdf38e79a1ffd68f69feab0ee7fc67c437bbbeb57799c322d03d42a406634872ae8977ea4e1fed2daead3f56c6687f00a2c7ea38775948b09d7a84b8954db56e54344bbb41613af5097592864c6a768dfc275329849cbecac566fe13ad5d817cb566fe13ad5d81471) (by decide +kernel)
private def cert24_27 := witnessLow51 24 26 0 460002 460513 68 4317
  (packedSchedule 0xbf7202478a08417a6715643329f73de193cfbda4f8002f8c3842f0bf9242687f56f17686bd4feab7863b9abbddd563da31edaead3d5d39a900afa450028976adb51ffab53be032a81c42a2c6acaffbbd4dcffb2612b5dbdb9eadfbbd4ddf0195376a77b1aff5373ff02d0dc5e6d1b9ff8146a) (by decide +kernel)
private def cert24_28 := witnessLow51 24 25 0 470001 470512 64 3947
  (packedSchedule 0xc9ab5ba9dc805baf8a0861f9c46dbd8ce2ae1fd33ee7deeefa90de673c5d43e0037e90e10d12efd7bb9fed0c8ea0f7569e87f55d163f53dbddb4842c756a7a4a0f12a9322dcb98544bbb4d7e7fa4b26f04bd0c9c5458ed23525937825d64127d8ed568d4965f0194c274b391a92c9ff81469) (by decide +kernel)
private def cert24_29 := witnessLow51 24 24 0 480000 480512 61 3650
  (packedSchedule 0x3d4019f7f26ace5dcf3f318ee404fd4c50421dcff7f279e687f56a3da4e2ac3b9ff1dc90deeeab55de18e647507a81f00cc691455d12ed589c3ff55b549a73ff40e005163561c3bbd58858a4b2f80ca123eb6adca1e8977d42c52593fec9a877b1a9f537f14965f0195374e770acb46fe292c9ff8146e) (by decide +kernel)
private def cert24_30 := witnessLow51 24 23 0 490000 490449 56 3229
  (packedSchedule 0x17fd4048fa6b92105e9e4d590ccb73cf79f77d79f7b4dc8005f18a085e0bbf521343fda78bea35ea1c55bc31fad5deeeda00163aadaa4d3be0393e00af6e5c80a25dda6d47fa4d4e1969283e864c2a2c768affbb48dc329bc12e2550b7b7159bf7691b86537825d64a8ce46bf48dcb2994c246a) (by decide +kernel)
private def cert24_31 := witnessLow51 24 22 0 500000 500448 52 2875
  (packedSchedule 0x3bdab5ba9fa805baf372430ff2636dec793570fe9dcf3ef7755886f0c7f1752e400dfa4504344bb56eee7fea322903d49a7a07157458d58f6f77aa10b149a9c329ff123e322dcf58544bbead7e7fe7592ca6550f143d163ea8dceb2194ffb2612dc1db691b9d64b299537462) (by decide +kernel)
private def cert24_32 := witnessLow51 24 21 0 510000 510448 48 2548
  (packedSchedule 0xac00cf5dfad59cbf5e7e631fa809f95972421dcfebbf5e79a1fed28f69c9ab0ee7fc7ea437bbb69562c75191481ea17203316e5cd5d12eed09c3fd25b5ced3965a192028b1da0e1dda4c42c73ac865a4a0f12b9b6adc86a8977482c73ac86537825e83391a9d237f1ceb2194de09759067) (by decide +kernel)
private def cert24_33 := witnessLow51 24 20 0 520000 520385 44 2237
  (packedSchedule 0x17d58048fa6f52105fd7eb564332faf3de7dd56e7ded3ea00173b6e485e0bb5621343ff578ba435ea64d5bc31ab55deeef50016292dae769c329cdc8057b73d40512efab6a3ff3b539bd3ff43bd85458fa95ff779cdfeb1653284a876f6e5a37eef39b9bd3fec985f) (by decide +kernel)
private def cert24_34 := witnessLow51 24 19 0 530000 530384 40 1947
  (packedSchedule 0xce55add4d5802dd79f52187fdec6dbd8fbdab87f4fd79f7bbb68422c7578ba9ea006fb72e486897769ddcff48647383dced3d0c9aba2c7687b7bb490858e76a7fac5944ae4c8b715a1512ee935f9fc0fb26f69283e87886a8b1d24603ec9bd37825c59) (by decide +kernel)
private def cert24_35 := witnessLow51 24 18 0 540000 540384 37 1718
  (packedSchedule 0x5a0033d76ad5672d5b9f98c6ac027e567a908773faed5b9e687feaa3da7bdab0ee7fc6ac437bbbd5562c52191ce0f50f50198b73d6ae8977d44e1ff9d6d01fa737b43bd01458fa870eef3b10b007d937a7fc4bd6dab7194d12ef9c2c01f67eb16532859) (by decide +kernel)
private def cert24_36 := witnessLow51 24 17 0 550000 550321 33 1466
  (packedSchedule 0x17ed0048fa6562105fd6ad564332ab73de7ddb4e7ded2ac00173b7d485e0bbb421343fd278be71af53bdab7863b4abbddda4002c73ada03f4ff58e7d402bdb8ac02897749b51fc0fd4f44feb165a0ce42a2c748affba07b7a266f69283c55) (by decide +kernel)
private def cert24_37 := witnessLow51 24 16 0 560000 560320 30 1266
  (packedSchedule 0x31ead6ea768016ebcab10c3f67236def2d5aae1fd356e7deeef5108b149e2ea2b001bedcf521a25df57773ff38c803c3c07e9e877b57458fa8f6f779d085803f53d1337a25ea645b9690a8977ced7e7f64acd1337a7fc4d) (by decide +kernel)
private def cert24_38 := witnessLow51 24 15 0 570000 570320 27 1087
  0x1046300c5451c905428c39309043572315084a48c4a24145c5451c9868bc928b4514624120a2e6ae4a305c5249060a5118bb2214cac462411149189060b8a8a4918d17b22178422b08d916514623182e6b244305c52c8460a612c2364688c91 (by decide +kernel)
private def cert24_39 := witnessLow51 24 14 0 580000 580257 24 917
  0x15823170848e4a28109451c905028c0ab9308851714826188ae462810d4918944428b8a8a4128d17a24176462954518904428b9ac120c1714a2318296442f08456117562311088a48e46305c545288868be108bd23846c8d11 (by decide +kernel)
private def cert24_40 := witnessLow51 24 13 0 590000 590256 21 762
  0xa4120b042582316082a48e4a26146051c9c61a8a39209851825726182e2924a30528905aab9189844524625182e2a29248345ec8c5e110ac2114ca28c48305cd648c60b8a5910c14c2117a4708d91 (by decide +kernel)
private def cert24_41 := witnessLow51 24 12 0 600000 600256 19 653
  0x1246300c54520905428c41309043582315084a48e4a24145c545209868bd128b4514724120a2e6b04a305c5289060a5918bc2214cae4624111491c9060b8a8a5118d17c2217a422b48e11 (by decide +kernel)
private def cert24_42 := witnessLow51 24 11 0 610000 610193 16 522
  0x1592317084904a281094520905028c0ac1308851714926188b0462810d491c944428b8a8a4928d17b2417846295451c904428b9ac920c1714b2318298442f4845691 (by decide +kernel)
private def cert24_43 := witnessLow51 24 10 0 620000 620192 14 430
  0x5249058212c918b041524825130a302904e30d4520904c28c12c130c1714a2518296482d5608c4c222923928c171514a241a2f8462f48856908a (by decide +kernel)
private def cert24_44 := witnessLow51 24 9 0 630000 630192 12 350
  0xa2318062a292482a14624984821ac918a842524825120a2e2a2924c345ec945a28a41209051735925182e29648305308c5e910a (by decide +kernel)
private def cert24_45 := witnessLow51 24 8 0 640000 640129 10 274
  0x5688c5c2124928a042514924140a302b24c22145c52898622c918a043524825110a2e2a2944a345f0905e918a (by decide +kernel)
private def cert24_46 := witnessLow51 24 7 0 650000 650128 8 206
  0x14a2416084b4462c1054924944c28c0a4938c3514924130a304b24c305c52c9460a6120b (by decide +kernel)
private def cert24_47 := witnessLow51 24 6 0 660000 660128 7 170
  0x1646300c54528905428c513090435a2315084a4924a24145c545289868be128b (by decide +kernel)
private def cert24_48 := witnessLow51 24 5 0 670000 670065 5 114
  0xad918b8424a2514084a29448281460568984428b8a5930c (by decide +kernel)
private def cert24_49 := witnessLow51 24 4 0 680000 680064 4 85
  0x14b2416084b6462c1054928944c28c0a5138c (by decide +kernel)
private def cert24_50 := witnessLow51 24 3 0 690000 690064 3 61
  0x1846300c5452c905428c5930904 (by decide +kernel)
private def cert24_51 := witnessLow51 24 2 0 700000 700001 2 38
  0x5708c5c2125928a04 (by decide +kernel)
private def cert24_52 := witnessLow51 24 1 0 710000 710000 1 18
  0xa6120b04 (by decide +kernel)
private def cert24_53 := witnessLow51 24 0 0 720000 720000 1 17
  0x6918c03 (by decide +kernel)
private def chunks24 : List (Chunk 24) := [
  cert24_0, cert24_1, cert24_2, cert24_3, cert24_4, cert24_5, cert24_6, cert24_7, cert24_8, cert24_9,
  cert24_10, cert24_11, cert24_12, cert24_13, cert24_14, cert24_15, cert24_16, cert24_17, cert24_18, cert24_19,
  cert24_20, cert24_21, cert24_22, cert24_23, cert24_24, cert24_25, cert24_26, cert24_27, cert24_28, cert24_29,
  cert24_30, cert24_31, cert24_32, cert24_33, cert24_34, cert24_35, cert24_36, cert24_37, cert24_38, cert24_39,
  cert24_40, cert24_41, cert24_42, cert24_43, cert24_44, cert24_45, cert24_46, cert24_47, cert24_48, cert24_49,
  cert24_50, cert24_51, cert24_52, cert24_53]

def rows24 := rowsFrom chunks24

theorem good24 : ∀ r ∈ rows24, good 24 r = true := rowsFrom_good chunks24

theorem sorted24 : rows24.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks24 0 (by decide +kernel)).1

theorem mass24 (i : Fin 54) :
    bandCount 24 (i.val : ℤ) 53 13 ≤ (rows24.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks24).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 24 (j : ℤ) 53 13 ≤ mass j chunks24)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total24 : (rows24.map (price 24)).sum = 179830 :=
  (total_eq chunks24).trans (by decide +kernel)

end Low51EdgeRankReceipt
