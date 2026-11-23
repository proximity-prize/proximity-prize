import ProximityPrize.SubmissionLower.ZAqJIcc
import ProximityPrize.SubmissionLower.ZyY02Da
import ProximityPrize.SubmissionLower.ZANbnda
import ProximityPrize.SubmissionLower.Zg1vQqc
import ProximityPrize.SubmissionLower.ZiAxakd
import ProximityPrize.SubmissionLower.ZWMflzd
import ProximityPrize.SubmissionLower.Zj6qwve
import ProximityPrize.SubmissionLower.ZK58iPc
import ProximityPrize.SubmissionLower.ZSrrUOd
import ProximityPrize.SubmissionLower.ZtVbzfa
import ProximityPrize.SubmissionLower.ZBs0nic
import ProximityPrize.SubmissionLower.ZFXgsrc
import ProximityPrize.SubmissionLower.ZDONgma
import ProximityPrize.SubmissionLower.ZdNjUtd
import ProximityPrize.SubmissionLower.ZV3T2ze
import ProximityPrize.SubmissionLower.ZeXFKme
import ProximityPrize.SubmissionLower.ZIcXkod
import ProximityPrize.SubmissionLower.Z2fqyGd
import ProximityPrize.SubmissionLower.ZCkMNPe
import ProximityPrize.SubmissionLower.ZwPPe7a
import ProximityPrize.SubmissionLower.ZspAKnb
import ProximityPrize.SubmissionLower.ZuQo7Ie
import ProximityPrize.SubmissionLower.ZXmQizb
import ProximityPrize.SubmissionLower.Z1urGMd
import ProximityPrize.SubmissionLower.ZNQXGme
import ProximityPrize.SubmissionLower.Z8bwyoc
import ProximityPrize.SubmissionLower.Zy89Gua
import ProximityPrize.SubmissionLower.Z7ssvqd
import ProximityPrize.SubmissionLower.ZDOZPPc
import ProximityPrize.SubmissionLower.ZjPnQId
import ProximityPrize.SubmissionLower.ZjvAb5c
import ProximityPrize.SubmissionLower.Z28bFab
import ProximityPrize.SubmissionLower.Z7sw41b
import ProximityPrize.SubmissionLower.ZaH3lsc
import ProximityPrize.SubmissionLower.ZRog5fb
import ProximityPrize.SubmissionLower.ZLcmX9d
import ProximityPrize.SubmissionLower.ZoYisee
import ProximityPrize.SubmissionLower.ZqzGq1b
import ProximityPrize.SubmissionLower.ZNetCjd
set_option Elab.async false
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
namespace qT7fytc
theorem k54_1h:headOk54 q54_1=true := by decide +kernel
theorem k54_1p0:planeOk54 q54_1 0=true := by decide +kernel
theorem k54_1p1 :planeOk54 q54_1 1=true := by decide +kernel
theorem k54_1p2 :planeOk54 q54_1 2=true := by decide +kernel
theorem k54_1p3:planeOk54 q54_1 3=true := by decide +kernel
theorem k54_1p4a :chunk54 q54_1 4 0 13=true := by decide +kernel
theorem k54_1p4b:chunk54 q54_1 4 13 4=true := by decide +kernel
theorem k54_1p4 :planeOk54 q54_1 4=true :=planeOk54_of_chunk (chunk54_join (k54_1p4a) k54_1p4b :)
theorem k54_1p5a :chunk54 q54_1 5 0 10=true := by decide +kernel
theorem k54_1p5b:chunk54 q54_1 5 10 7=true := by decide +kernel
theorem k54_1p5:planeOk54 q54_1 5=true :=planeOk54_of_chunk (chunk54_join (k54_1p5a) k54_1p5b :)
theorem k54_1p6a :chunk54 q54_1 6 0 9=true := by decide +kernel
theorem k54_1p6b:chunk54 q54_1 6 9 8=true := by decide +kernel
theorem k54_1p6:planeOk54 q54_1 6=true :=planeOk54_of_chunk (chunk54_join (k54_1p6a) k54_1p6b :)
theorem k54_1 :recOK54 q54_1=true :=
  recOK54_of_parts k54_1h (fun t ht=> by
    change t≤6 at ht
    interval_cases t
    · exact k54_1p0
    · exact k54_1p1
    · exact k54_1p2
    · exact k54_1p3
    · exact k54_1p4
    · exact k54_1p5
    · exact k54_1p6)
end qT7fytc
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
namespace qT7fytc
theorem k54_2h:headOk54 q54_2=true := by decide +kernel
theorem k54_2p0:planeOk54 q54_2 0=true := by decide +kernel
theorem k54_2p1 :planeOk54 q54_2 1=true := by decide +kernel
theorem k54_2p2 :planeOk54 q54_2 2=true := by decide +kernel
theorem k54_2p3:planeOk54 q54_2 3=true := by decide +kernel
theorem k54_2p4a :chunk54 q54_2 4 0 13=true := by decide +kernel
theorem k54_2p4b:chunk54 q54_2 4 13 4=true := by decide +kernel
theorem k54_2p4 :planeOk54 q54_2 4=true :=planeOk54_of_chunk (chunk54_join (k54_2p4a) k54_2p4b :)
theorem k54_2p5a :chunk54 q54_2 5 0 12=true := by decide +kernel
theorem k54_2p5b:chunk54 q54_2 5 12 5=true := by decide +kernel
theorem k54_2p5:planeOk54 q54_2 5=true :=planeOk54_of_chunk (chunk54_join (k54_2p5a) k54_2p5b :)
theorem k54_2 :recOK54 q54_2=true :=
  recOK54_of_parts k54_2h (fun t ht=> by
    change t≤5 at ht
    interval_cases t
    · exact k54_2p0
    · exact k54_2p1
    · exact k54_2p2
    · exact k54_2p3
    · exact k54_2p4
    · exact k54_2p5)
theorem k54_3h:headOk54 q54_3=true := by decide +kernel
theorem k54_3p0:planeOk54 q54_3 0=true := by decide +kernel
theorem k54_3p1 :planeOk54 q54_3 1=true := by decide +kernel
theorem k54_3p2 :planeOk54 q54_3 2=true := by decide +kernel
theorem k54_3p3:planeOk54 q54_3 3=true := by decide +kernel
theorem k54_3p4 :planeOk54 q54_3 4=true := by decide +kernel
theorem k54_3:recOK54 q54_3=true :=
  recOK54_of_parts k54_3h (fun t ht=> by
    change t≤4 at ht
    interval_cases t
    · exact k54_3p0
    · exact k54_3p1
    · exact k54_3p2
    · exact k54_3p3
    · exact k54_3p4)
theorem k54_4 :recOK54 q54_4=true := by decide +kernel
theorem k54_5:recOK54 q54_5=true := by decide +kernel
theorem k54_6:recOK54 q54_6=true := by decide +kernel
theorem k54_7:recOK54 q54_7=true := by decide +kernel
theorem k54_8:recOK54 q54_8=true := by decide +kernel
theorem k54_9:recOK54 q54_9=true := by decide +kernel
theorem k54_10 :recOK54 q54_10=true := by decide +kernel
theorem k54_11 :recOK54 q54_11=true := by decide +kernel
theorem k54_12 :recOK54 q54_12=true := by decide +kernel
theorem k54_13:recOK54 q54_13=true := by decide +kernel
theorem k54_14 :recOK54 q54_14=true := by decide +kernel
theorem k54_15:recOK54 q54_15=true := by decide +kernel
theorem k54_16:recOK54 q54_16=true := by decide +kernel
theorem k54_17:recOK54 q54_17=true := by decide +kernel
theorem k54_18:recOK54 q54_18=true := by decide +kernel
theorem k54_19:recOK54 q54_19=true := by decide +kernel
theorem k54_20:recOK54 q54_20=true := by decide +kernel
theorem k54_21 :recOK54 q54_21=true := by decide +kernel
theorem k54_22 :recOK54 q54_22=true := by decide +kernel
theorem k54_23:recOK54 q54_23=true := by decide +kernel
theorem k54_24 :recOK54 q54_24=true := by decide +kernel
theorem k54_25:recOK54 q54_25=true := by decide +kernel
theorem k54_26:recOK54 q54_26=true := by decide +kernel
theorem k54_27:recOK54 q54_27=true := by decide +kernel
theorem k54_28:recOK54 q54_28=true := by decide +kernel
theorem k54_29:recOK54 q54_29=true := by decide +kernel
theorem k54_30:recOK54 q54_30=true := by decide +kernel
end qT7fytc
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
namespace qT7fytc
theorem row54_83 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 83 f a=true := by decide +kernel
theorem row54_84 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 84 f a=true := by decide +kernel
theorem row54_85 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 85 f a=true := by decide +kernel
theorem row54_86 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 86 f a=true := by decide +kernel
theorem row54_87 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 87 f a=true := by decide +kernel
theorem row54_88 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 88 f a=true := by decide +kernel
theorem row54_89 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 89 f a=true := by decide +kernel
theorem row54_90 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 90 f a=true := by decide +kernel
theorem row54_91 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 91 f a=true := by decide +kernel
theorem row54_92 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 92 f a=true := by decide +kernel
theorem row54_93 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 93 f a=true := by decide +kernel
theorem row54_94 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 94 f a=true := by decide +kernel
theorem row54_95 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 95 f a=true := by decide +kernel
theorem row54_96 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 96 f a=true := by decide +kernel
theorem row54_97 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 97 f a=true := by decide +kernel
theorem row54_98 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 98 f a=true := by decide +kernel
theorem row54_99 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 99 f a=true := by decide +kernel
theorem row54_100 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 100 f a=true := by decide +kernel
theorem row54_101 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 101 f a=true := by decide +kernel
theorem row54_102 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 102 f a=true := by decide +kernel
theorem row54_103 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 103 f a=true := by decide +kernel
theorem row54_104 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 104 f a=true := by decide +kernel
theorem row54_105 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 105 f a=true := by decide +kernel
theorem row54_106 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 106 f a=true := by decide +kernel
theorem row54_107 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 107 f a=true := by decide +kernel
theorem row54_108 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 108 f a=true := by decide +kernel
theorem row54_109 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 109 f a=true := by decide +kernel
theorem row54_110 : ∀ a<17,∀ f<57,rowOK54 H54 recs54 110 f a=true := by decide +kernel
theorem src54_0:srcOK54 H54 recs54 83 110 0=true := by decide +kernel
theorem src54_1 :srcOK54 H54 recs54 83 110 1=true := by decide +kernel
theorem src54_2 :srcOK54 H54 recs54 83 110 2=true := by decide +kernel
theorem src54_3:srcOK54 H54 recs54 83 110 3=true := by decide +kernel
theorem src54_4 :srcOK54 H54 recs54 83 110 4=true := by decide +kernel
theorem src54_5:srcOK54 H54 recs54 83 110 5=true := by decide +kernel
theorem src54_6:srcOK54 H54 recs54 83 110 6=true := by decide +kernel
theorem src54_7:srcOK54 H54 recs54 83 110 7=true := by decide +kernel
theorem src54_8:srcOK54 H54 recs54 83 110 8=true := by decide +kernel
theorem src54_9:srcOK54 H54 recs54 83 110 9=true := by decide +kernel
theorem src54_10 :srcOK54 H54 recs54 83 110 10=true := by decide +kernel
theorem src54_11 :srcOK54 H54 recs54 83 110 11=true := by decide +kernel
theorem src54_12 :srcOK54 H54 recs54 83 110 12=true := by decide +kernel
theorem src54_13:srcOK54 H54 recs54 83 110 13=true := by decide +kernel
theorem src54_14 :srcOK54 H54 recs54 83 110 14=true := by decide +kernel
theorem src54_15:srcOK54 H54 recs54 83 110 15=true := by decide +kernel
theorem src54_16:srcOK54 H54 recs54 83 110 16=true := by decide +kernel
theorem src54_17:srcOK54 H54 recs54 83 110 17=true := by decide +kernel
theorem src54_18:srcOK54 H54 recs54 83 110 18=true := by decide +kernel
theorem src54_19:srcOK54 H54 recs54 83 110 19=true := by decide +kernel
theorem src54_20:srcOK54 H54 recs54 83 110 20=true := by decide +kernel
theorem src54_21 :srcOK54 H54 recs54 83 110 21=true := by decide +kernel
theorem src54_22 :srcOK54 H54 recs54 83 110 22=true := by decide +kernel
theorem src54_23:srcOK54 H54 recs54 83 110 23=true := by decide +kernel
theorem src54_24 :srcOK54 H54 recs54 83 110 24=true := by decide +kernel
theorem src54_25:srcOK54 H54 recs54 83 110 25=true := by decide +kernel
theorem src54_26:srcOK54 H54 recs54 83 110 26=true := by decide +kernel
theorem src54_27:srcOK54 H54 recs54 83 110 27=true := by decide +kernel
theorem src54_28:srcOK54 H54 recs54 83 110 28=true := by decide +kernel
theorem src54_29:srcOK54 H54 recs54 83 110 29=true := by decide +kernel
theorem src54_30:srcOK54 H54 recs54 83 110 30=true := by decide +kernel
theorem src54_31 :srcOK54 H54 recs54 83 110 31=true := by decide +kernel
theorem src54_32 :srcOK54 H54 recs54 83 110 32=true := by decide +kernel
theorem src54_33:srcOK54 H54 recs54 83 110 33=true := by decide +kernel
theorem src54_34 :srcOK54 H54 recs54 83 110 34=true := by decide +kernel
theorem src54_35:srcOK54 H54 recs54 83 110 35=true := by decide +kernel
theorem src54_36:srcOK54 H54 recs54 83 110 36=true := by decide +kernel
theorem src54_37:srcOK54 H54 recs54 83 110 37=true := by decide +kernel
theorem src54_38:srcOK54 H54 recs54 83 110 38=true := by decide +kernel
theorem src54_39:srcOK54 H54 recs54 83 110 39=true := by decide +kernel
theorem src54_40:srcOK54 H54 recs54 83 110 40=true := by decide +kernel
theorem src54_41 :srcOK54 H54 recs54 83 110 41=true := by decide +kernel
theorem src54_42 :srcOK54 H54 recs54 83 110 42=true := by decide +kernel
theorem src54_43:srcOK54 H54 recs54 83 110 43=true := by decide +kernel
theorem src54_44 :srcOK54 H54 recs54 83 110 44=true := by decide +kernel
theorem src54_45:srcOK54 H54 recs54 83 110 45=true := by decide +kernel
theorem src54_46:srcOK54 H54 recs54 83 110 46=true := by decide +kernel
theorem src54_47:srcOK54 H54 recs54 83 110 47=true := by decide +kernel
theorem src54_48:srcOK54 H54 recs54 83 110 48=true := by decide +kernel
theorem src54_49:srcOK54 H54 recs54 83 110 49=true := by decide +kernel
theorem src54_50:srcOK54 H54 recs54 83 110 50=true := by decide +kernel
theorem src54_51 :srcOK54 H54 recs54 83 110 51=true := by decide +kernel
theorem src54_52 :srcOK54 H54 recs54 83 110 52=true := by decide +kernel
theorem src54_53:srcOK54 H54 recs54 83 110 53=true := by decide +kernel
theorem src54_54 :srcOK54 H54 recs54 83 110 54=true := by decide +kernel
theorem src54_55:srcOK54 H54 recs54 83 110 55=true := by decide +kernel
theorem src54_56:srcOK54 H54 recs54 83 110 56=true := by decide +kernel
theorem src54_57:srcOK54 H54 recs54 83 110 57=true := by decide +kernel
theorem src54_58:srcOK54 H54 recs54 83 110 58=true := by decide +kernel
theorem src54_59:srcOK54 H54 recs54 83 110 59=true := by decide +kernel
theorem src54_60:srcOK54 H54 recs54 83 110 60=true := by decide +kernel
theorem src54_61 :srcOK54 H54 recs54 83 110 61=true := by decide +kernel
theorem src54_62 :srcOK54 H54 recs54 83 110 62=true := by decide +kernel
theorem src54_63:srcOK54 H54 recs54 83 110 63=true := by decide +kernel
theorem src54_64 :srcOK54 H54 recs54 83 110 64=true := by decide +kernel
theorem src54_65:srcOK54 H54 recs54 83 110 65=true := by decide +kernel
theorem src54_66:srcOK54 H54 recs54 83 110 66=true := by decide +kernel
theorem src54_67:srcOK54 H54 recs54 83 110 67=true := by decide +kernel
theorem src54_68:srcOK54 H54 recs54 83 110 68=true := by decide +kernel
theorem src54_69:srcOK54 H54 recs54 83 110 69=true := by decide +kernel
theorem src54_70:srcOK54 H54 recs54 83 110 70=true := by decide +kernel
theorem src54_71 :srcOK54 H54 recs54 83 110 71=true := by decide +kernel
theorem src54_72 :srcOK54 H54 recs54 83 110 72=true := by decide +kernel
theorem src54_73:srcOK54 H54 recs54 83 110 73=true := by decide +kernel
theorem src54_74 :srcOK54 H54 recs54 83 110 74=true := by decide +kernel
theorem src54_75:srcOK54 H54 recs54 83 110 75=true := by decide +kernel
theorem src54_76:srcOK54 H54 recs54 83 110 76=true := by decide +kernel
theorem src54_77:srcOK54 H54 recs54 83 110 77=true := by decide +kernel
theorem src54_78:srcOK54 H54 recs54 83 110 78=true := by decide +kernel
theorem src54_79:srcOK54 H54 recs54 83 110 79=true := by decide +kernel
theorem src54_80:srcOK54 H54 recs54 83 110 80=true := by decide +kernel
theorem src54_81 :srcOK54 H54 recs54 83 110 81=true := by decide +kernel
theorem src54_82 :srcOK54 H54 recs54 83 110 82=true := by decide +kernel
theorem src54_83:srcOK54 H54 recs54 83 110 83=true := by decide +kernel
theorem src54_84 :srcOK54 H54 recs54 83 110 84=true := by decide +kernel
theorem src54_85:srcOK54 H54 recs54 83 110 85=true := by decide +kernel
theorem src54_86:srcOK54 H54 recs54 83 110 86=true := by decide +kernel
theorem src54_87:srcOK54 H54 recs54 83 110 87=true := by decide +kernel
theorem src54_88:srcOK54 H54 recs54 83 110 88=true := by decide +kernel
theorem src54_89:srcOK54 H54 recs54 83 110 89=true := by decide +kernel
theorem src54_90:srcOK54 H54 recs54 83 110 90=true := by decide +kernel
theorem src54_91 :srcOK54 H54 recs54 83 110 91=true := by decide +kernel
theorem src54_92 :srcOK54 H54 recs54 83 110 92=true := by decide +kernel
theorem src54_93:srcOK54 H54 recs54 83 110 93=true := by decide +kernel
theorem src54_94 :srcOK54 H54 recs54 83 110 94=true := by decide +kernel
theorem src54_95:srcOK54 H54 recs54 83 110 95=true := by decide +kernel
theorem src54_96:srcOK54 H54 recs54 83 110 96=true := by decide +kernel
theorem src54_97:srcOK54 H54 recs54 83 110 97=true := by decide +kernel
theorem src54_98:srcOK54 H54 recs54 83 110 98=true := by decide +kernel
theorem rows54 : ∀ w,83≤w→w≤110 → ∀ a<17,∀ f<57,rowOK54 H54 recs54 w f a=true := by
  intro w h1 h2
  interval_cases w
  · exact row54_83
  · exact row54_84
  · exact row54_85
  · exact row54_86
  · exact row54_87
  · exact row54_88
  · exact row54_89
  · exact row54_90
  · exact row54_91
  · exact row54_92
  · exact row54_93
  · exact row54_94
  · exact row54_95
  · exact row54_96
  · exact row54_97
  · exact row54_98
  · exact row54_99
  · exact row54_100
  · exact row54_101
  · exact row54_102
  · exact row54_103
  · exact row54_104
  · exact row54_105
  · exact row54_106
  · exact row54_107
  · exact row54_108
  · exact row54_109
  · exact row54_110
theorem srcs54 : ∀ g<99,srcOK54 H54 recs54 83 110 g=true := by
  intro g hg
  interval_cases g
  · exact src54_0
  · exact src54_1
  · exact src54_2
  · exact src54_3
  · exact src54_4
  · exact src54_5
  · exact src54_6
  · exact src54_7
  · exact src54_8
  · exact src54_9
  · exact src54_10
  · exact src54_11
  · exact src54_12
  · exact src54_13
  · exact src54_14
  · exact src54_15
  · exact src54_16
  · exact src54_17
  · exact src54_18
  · exact src54_19
  · exact src54_20
  · exact src54_21
  · exact src54_22
  · exact src54_23
  · exact src54_24
  · exact src54_25
  · exact src54_26
  · exact src54_27
  · exact src54_28
  · exact src54_29
  · exact src54_30
  · exact src54_31
  · exact src54_32
  · exact src54_33
  · exact src54_34
  · exact src54_35
  · exact src54_36
  · exact src54_37
  · exact src54_38
  · exact src54_39
  · exact src54_40
  · exact src54_41
  · exact src54_42
  · exact src54_43
  · exact src54_44
  · exact src54_45
  · exact src54_46
  · exact src54_47
  · exact src54_48
  · exact src54_49
  · exact src54_50
  · exact src54_51
  · exact src54_52
  · exact src54_53
  · exact src54_54
  · exact src54_55
  · exact src54_56
  · exact src54_57
  · exact src54_58
  · exact src54_59
  · exact src54_60
  · exact src54_61
  · exact src54_62
  · exact src54_63
  · exact src54_64
  · exact src54_65
  · exact src54_66
  · exact src54_67
  · exact src54_68
  · exact src54_69
  · exact src54_70
  · exact src54_71
  · exact src54_72
  · exact src54_73
  · exact src54_74
  · exact src54_75
  · exact src54_76
  · exact src54_77
  · exact src54_78
  · exact src54_79
  · exact src54_80
  · exact src54_81
  · exact src54_82
  · exact src54_83
  · exact src54_84
  · exact src54_85
  · exact src54_86
  · exact src54_87
  · exact src54_88
  · exact src54_89
  · exact src54_90
  · exact src54_91
  · exact src54_92
  · exact src54_93
  · exact src54_94
  · exact src54_95
  · exact src54_96
  · exact src54_97
  · exact src54_98
end qT7fytc
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qT7fytc
theorem recsOk54 : ∀ q∈recs54,recOK54 q=true := by
  simp only [recs54,List.forall_mem_cons]
  exact ⟨k54_1,k54_2,k54_3,k54_4,k54_5,k54_6,k54_7,k54_8,k54_9,k54_10,k54_11,k54_12,k54_13,k54_14,k54_15,k54_16,k54_17,k54_18,k54_19,k54_20,k54_21,k54_22,k54_23,k54_24,k54_25,k54_26,k54_27,k54_28,k54_29,k54_30,fun _ h=>nomatch h⟩
theorem c2_of54 (h56:qHde8fc.aGq 85 91) :qwzqCne.c2 :=
  slab54_of 83 89 (by decide) (by decide) h56 H54 recs54 rows54 srcs54 recsOk54
theorem c3_of54 (h56:qHde8fc.aGq 92 97) :qwzqCne.c3 :=
  slab54_of 90 95 (by decide) (by decide) h56 H54 recs54 rows54 srcs54 recsOk54
theorem c4_of54 (h56:qHde8fc.aGq 98 101) :qwzqCne.c4 :=
  slab54_of 96 99 (by decide) (by decide) h56 H54 recs54 rows54 srcs54 recsOk54
theorem c5_of54 (h56:qHde8fc.aGq 102 105) :qwzqCne.c5 :=
  slab54_of 100 103 (by decide) (by decide) h56 H54 recs54 rows54 srcs54 recsOk54
theorem c6_of54 (h56:qHde8fc.aGq 106 108) :qwzqCne.c6 :=
  slab54_of 104 106 (by decide) (by decide) h56 H54 recs54 rows54 srcs54 recsOk54
theorem c7_of54 (h56:qHde8fc.aGq 109 110) :qwzqCne.c7 :=
  slab54_of 107 108 (by decide) (by decide) h56 H54 recs54 rows54 srcs54 recsOk54
theorem c8_of54 (h56:qHde8fc.aGq 111 112) :qwzqCne.c8 :=
  slab54_of 109 110 (by decide) (by decide) h56 H54 recs54 rows54 srcs54 recsOk54
end qT7fytc
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
set_option quotPrecheck false
namespace qYiv0Ea
theorem band5:qHde8fc.c5:=kc fun w f a h1 h2 h3=> by
  obtain ⟨h104_0_0,h104_0_1,h104_0_2,h104_0_3,h104_0_4,h104_0_5,h104_0_6,h104_0_7,h104_0_8,h104_0_9,h104_0_10,h104_0_11,h104_0_12,h104_0_13,h104_1_0,h104_1_1,h104_1_2,h104_1_3,h104_1_4,h104_1_5,h104_1_6,h104_1_7,h104_1_8,h104_1_9,h104_1_10,h104_1_11,h104_1_12,h104_2_0,h104_2_1,h104_2_2,h104_2_3,h104_2_4,h104_2_5,h104_2_6,h104_2_7,h104_2_8,h104_2_9,h104_2_10,h104_2_11,h104_2_12,h104_3_0,h104_3_1,h104_3_2,h104_3_3,h104_3_4,h104_3_5,h104_3_6,h104_3_7,h104_3_8,h104_3_9,h104_3_10,h104_3_11,h104_3_12,h104_3_14,h104_4_0,h104_4_1,h104_4_2,h104_4_3,h104_4_4,h104_4_5,h104_4_6,h104_4_7,h104_4_8,h104_4_9,h104_4_10,h104_4_11,h104_4_13,h104_5_0,h104_5_1,h104_5_2,h104_5_3,h104_5_4,h104_5_5,h104_5_6,h104_5_7⟩:=d5_1
  obtain ⟨h104_5_8,h104_5_9,h104_5_10,h104_5_11,h104_5_12,h104_6_0,h104_6_1,h104_6_2,h104_6_3,h104_6_4,h104_6_5,h104_6_6,h104_6_7,h104_6_8,h104_6_9,h104_6_10,h104_6_11,h104_6_12,h104_7_0,h104_7_1,h104_7_2,h104_7_3,h104_7_4,h104_7_5⟩:=d5_2
  obtain ⟨h104_7_6,h104_7_7,h104_7_8,h104_7_9,h104_7_10,h104_7_11,h104_8_9,h104_8_10,h104_9_9,h104_9_10,h104_10_9,h105_0_0,h105_0_1,h105_0_2,h105_0_3,h105_0_4,h105_0_5,h105_0_6,h105_0_7,h105_0_8,h105_0_9,h105_0_10,h105_0_11,h105_0_12,h105_0_13,h105_1_0,h105_1_1,h105_1_2,h105_1_3,h105_1_4,h105_1_5,h105_1_6,h105_1_7,h105_1_8,h105_1_9,h105_1_10,h105_1_11,h105_1_12,h105_1_13,h105_2_0,h105_2_1,h105_2_2,h105_2_3,h105_2_4,h105_2_5,h105_2_6,h105_2_7,h105_2_8,h105_2_9,h105_2_10,h105_2_11,h105_2_12,h105_2_13,h105_2_15,h105_3_0,h105_3_1,h105_3_2,h105_3_3,h105_3_4,h105_3_5,h105_3_6,h105_3_7,h105_3_8,h105_3_9,h105_3_10,h105_3_11,h105_3_12,h105_3_14,h105_4_0,h105_4_1,h105_4_2,h105_4_3,h105_4_4,h105_4_5,h105_4_6,h105_4_7,h105_4_8,h105_4_9,h105_4_10,h105_4_11⟩:=d5_3
  obtain ⟨h105_4_12,h105_4_13,h105_5_0,h105_5_1,h105_5_2,h105_5_3,h105_5_4,h105_5_5,h105_5_6,h105_5_7,h105_5_8,h105_5_9,h105_5_10,h105_5_11,h105_5_12,h105_5_13,h105_6_0,h105_6_1,h105_6_2,h105_6_3,h105_6_4,h105_6_5,h105_6_6,h105_6_7,h105_6_8,h105_6_9,h105_6_10,h105_6_11,h105_6_12,h105_7_10,h105_7_11,h105_8_10,h105_8_11,h105_9_10,h106_0_0,h106_0_1,h106_0_2,h106_0_3,h106_0_4,h106_0_5,h106_0_6,h106_0_7,h106_0_8,h106_0_9,h106_0_10,h106_0_11,h106_0_12,h106_0_13,h106_0_14,h106_1_0,h106_1_1,h106_1_2,h106_1_3,h106_1_4,h106_1_5,h106_1_6,h106_1_7,h106_1_8,h106_1_9,h106_1_10,h106_1_11,h106_1_12,h106_1_13,h106_1_14,h106_1_16,h106_2_0,h106_2_1,h106_2_2,h106_2_3,h106_2_4,h106_2_5,h106_2_6⟩:=d5_4
  obtain ⟨h106_2_7,h106_2_8,h106_2_9,h106_2_10,h106_2_11,h106_2_12,h106_2_13,h106_2_15,h106_3_0,h106_3_1,h106_3_2,h106_3_3,h106_3_4,h106_3_5,h106_3_6,h106_3_7,h106_3_8,h106_3_9,h106_3_10,h106_3_11,h106_3_12,h106_3_13,h106_3_14,h106_4_0,h106_4_1,h106_4_2,h106_4_3,h106_4_4,h106_4_5,h106_4_6,h106_4_7,h106_4_8,h106_4_9,h106_4_10,h106_4_11,h106_4_12,h106_4_13,h106_4_14,h106_5_0,h106_5_1,h106_5_2,h106_5_3,h106_5_4,h106_5_5,h106_5_6,h106_5_7,h106_5_8,h106_5_9,h106_5_10,h106_5_11,h106_5_12,h106_5_13,h106_6_11,h106_6_12,h106_7_11,h106_7_12,h106_8_11⟩:=d5_5
  have hf :f<(w - 56)/2+1 := by omega
  have ha :a<(w - 56 - 2*f)/3+1 := by omega
  interval_cases w <;> (conv at hf=>rhs; norm_num) <;> interval_cases f <;> (conv at ha=>rhs; norm_num) <;>
    interval_cases a <;> first | assumption | exact okE (by decide +kernel)
end qYiv0Ea
end
section
set_option autoImplicit true
set_option Elab.async false
namespace q4tnMXd
theorem a_P6_6_1_1_5_5:qHde8fc.c5:=qYiv0Ea.band5
theorem kc:qHde8fc.c5:=a_P6_6_1_1_5_5
end q4tnMXd
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
set_option quotPrecheck false
namespace qYiv0Ea
theorem band4 :qHde8fc.c4 :=kc fun w f a h1 h2 h3=> by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=g4_1_1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=g4_2_1
  obtain ⟨_,_,_,_,_⟩:=g4_3_1
  obtain ⟨_,_,_,_,_⟩:=g4_4_1
  have :=g4_4_2
  obtain ⟨_,_,_,_⟩:=g4_5_1
  have :=g4_5_2
  obtain ⟨_,_,_,_,_,_⟩:=g4_6_1
  have :=g4_6_2
  obtain ⟨_,_,_,_⟩:=g4_7_1
  have :=g4_7_2
  have :=g4_8_1
  obtain ⟨_,_,_⟩:=g4_8_2
  have :=g4_9_1
  obtain ⟨_,_⟩:=g4_9_2
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=g4_10_1
  have :=g4_10_2
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=g4_11_1
  obtain ⟨_,_,_,_,_,_,_⟩:=g4_12_1
  have :=g4_12_2
  obtain ⟨_,_,_,_,_,_,_,_⟩:=g4_13_1
  obtain ⟨_,_,_,_,_,_⟩:=g4_14_1
  have :=g4_14_2
  obtain ⟨_,_,_,_,_,_,_,_⟩:=g4_15_1
  obtain ⟨_,_,_⟩:=g4_16_1
  obtain ⟨_,_⟩:=g4_16_2
  obtain ⟨_,_,_,_,_⟩:=g4_17_1
  have :=g4_17_2
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=g4_18_1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=g4_19_1
  have :=g4_19_2
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_⟩:=g4_20_1
  have :=g4_20_2
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_⟩:=g4_21_1
  obtain ⟨_,_,_,_,_,_⟩:=g4_22_1
  have :=g4_22_2
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=g4_23_1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=g4_24_1
  have :=g4_24_2
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=g4_25_1
  have :=g4_25_2
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=g4_26_1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=g4_27_1
  have hf :f<(w - 56)/2+1 := by omega
  have ha :a<(w - 56 - 2*f)/3+1 := by omega
  interval_cases w <;> (conv at hf=>rhs; norm_num) <;> interval_cases f <;> (conv at ha=>rhs; norm_num) <;>
    interval_cases a <;> first | assumption | exact okE (by decide +kernel)
end qYiv0Ea
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qf6wZCd
theorem a_P6_6_1_1_5_4 :qHde8fc.c4 :=qYiv0Ea.band4
theorem kc:qHde8fc.c4 :=a_P6_6_1_1_5_4
end qf6wZCd
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qSWgXJc
theorem slab_mono {a b c d:ℕ} (h:qHde8fc.aGq a b) (hac:a≤ c) (hdb:d≤b) :
    qHde8fc.aGq c d :=
  fun e h1 h2=>h e (le_trans hac h1) (le_trans h2 hdb)
theorem slab_union {a b c:ℕ} (h1 :qHde8fc.aGq a b) (h2 :qHde8fc.aGq (b+1) c) :
    qHde8fc.aGq a c:= by
  intro e hl hh
  by_cases hb:qHde8fc.cP (qHde8fc.aD e.val)≤b
  · exact h1 e hl hb
  · exact h2 e (by omega) hh
end qSWgXJc
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qhMCwvd
theorem proof_P6_6_1_1_4_2_2 :qoWrama.c2 :=
  qT7fytc.c2_of52 (qSWgXJc.slab_mono qoYisee.kc (by decide) (by decide))
theorem proof_P6_6_1_1_4_2_3:qoWrama.c3 :=
  qT7fytc.c3_of52 (qSWgXJc.slab_mono qzH0Wge.kc (by decide) (by decide))
theorem proof_P6_6_1_1_4_2_4 :qoWrama.c4 :=
  qT7fytc.c4_of52 (qSWgXJc.slab_union (b:=99) (qSWgXJc.slab_mono qzH0Wge.kc (by decide) (by decide)) (qSWgXJc.slab_mono qf6wZCd.kc (by decide) (by decide)))
theorem proof_P6_6_1_1_4_2_5:qoWrama.c5 :=
  qT7fytc.c5_of52 (qSWgXJc.slab_union (b:=103) (qSWgXJc.slab_mono qf6wZCd.kc (by decide) (by decide)) (qSWgXJc.slab_mono q4tnMXd.kc (by decide) (by decide)))
theorem proof_P6_6_1_1_4_2_6:qoWrama.c6 :=
  qT7fytc.c6_of52 (qSWgXJc.slab_mono qqzGq1b.kc (by decide) (by decide))
theorem proof_P6_6_1_1_4_2_7:qoWrama.c7 :=
  qT7fytc.c7_of52 (qSWgXJc.slab_mono qLAc3id.kc (by decide) (by decide))
theorem proof_P6_6_1_1_4_4_2 :qwzqCne.c2 :=
  qT7fytc.c2_of54 (qSWgXJc.slab_mono qoYisee.kc (by decide) (by decide))
theorem proof_P6_6_1_1_4_4_3:qwzqCne.c3 :=
  qT7fytc.c3_of54 (qSWgXJc.slab_union (b:=92) (qSWgXJc.slab_mono qoYisee.kc (by decide) (by decide)) (qSWgXJc.slab_mono qzH0Wge.kc (by decide) (by decide)))
theorem proof_P6_6_1_1_4_4_4 :qwzqCne.c4 :=
  qT7fytc.c4_of54 (qSWgXJc.slab_union (b:=99) (qSWgXJc.slab_mono qzH0Wge.kc (by decide) (by decide)) (qSWgXJc.slab_mono qf6wZCd.kc (by decide) (by decide)))
theorem proof_P6_6_1_1_4_4_5:qwzqCne.c5 :=
  qT7fytc.c5_of54 (qSWgXJc.slab_union (b:=103) (qSWgXJc.slab_mono qf6wZCd.kc (by decide) (by decide)) (qSWgXJc.slab_mono q4tnMXd.kc (by decide) (by decide)))
theorem proof_P6_6_1_1_4_4_6:qwzqCne.c6 :=
  qT7fytc.c6_of54 (qSWgXJc.slab_union (b:=106) (qSWgXJc.slab_mono q4tnMXd.kc (by decide) (by decide)) (qSWgXJc.slab_mono qqzGq1b.kc (by decide) (by decide)))
theorem proof_P6_6_1_1_4_4_7:qwzqCne.c7 :=
  qT7fytc.c7_of54 (qSWgXJc.slab_union (b:=109) (qSWgXJc.slab_mono qqzGq1b.kc (by decide) (by decide)) (qSWgXJc.slab_mono qLAc3id.kc (by decide) (by decide)))
theorem proof_P6_6_1_1_4_4_8:qwzqCne.c8 :=
  qT7fytc.c8_of54 (qSWgXJc.slab_mono qLAc3id.kc (by decide) (by decide))
end qhMCwvd
end
