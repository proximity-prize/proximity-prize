import ProximityPrize.SubmissionLower.RecoveryRules02
set_option autoImplicit false
set_option linter.all false
set_option Elab.async true
section
namespace ProximityPrize.SubmissionLower
namespace EP
open DZ
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def d1_0:List Piece:=DZ.decode 58 42 0xa484aa4041e87f75507d7d3aabb85ea3aac58c7988b4c857936d779caf64deb6fa3ce991dad6d43a4980e0003
theorem shape1_0:validFrom 11192 0 d1_0=true:=by decide+kernel
def d1_1:List Piece:=DZ.decode 58 42 0xa484aa4041e89061539e293a6bb75ea3aac58c798f0e111773a5d792ef64deb6fa3cecce2789c4ea897fe0003
theorem shape1_1:validFrom 11191 0 d1_1=true:=by decide+kernel
def d1_2:List Piece:=DZ.decode 58 42 0xa484aa4041e8a14d56bed53a2bb65ea3aac58c79954fb0eca27b27892f64deb6fa3cf00a743cb59ac97ed0003
theorem shape1_2:validFrom 11190 0 d1_2=true:=by decide+kernel
def d1_3:List Piece:=DZ.decode 58 42 0xa484aa4041e8b23959df8139ebb55ea3aac58c799b9150c1d150777f6f64deb6fa3cf346c0efa64b097dc0003
theorem shape1_3:validFrom 11189 0 d1_3=true:=by decide+kernel
def d1_4:List Piece:=DZ.decode 58 42 0xa484aa4041e8c3255d002d39abb45ea3aac58c79a1d2f0970025c775af64deb6fa3cf6830da296fb497cb0003
theorem shape1_4:validFrom 11188 0 d1_4=true:=by decide+kernel
def d1_5:List Piece:=DZ.decode 58 42 0xa484aa4041e8d4116020d9396bb35ea3aac58c79a814906c2efb176bef64deb6fa3cf9bf5a5587ab897ba0003
theorem shape1_5:validFrom 11187 0 d1_5=true:=by decide+kernel
def d1_6:List Piece:=DZ.decode 58 42 0xa484aa4041e8e526846c15496bb25ea3aac58c79ae3e8756ac6d57626f64deb6fa3cfcfba708785bc97a80003
theorem shape1_6:validFrom 11186 0 d1_6=true:=by decide+kernel
def d1_7:List Piece:=DZ.decode 58 42 0xa484aa4041e8f612878cc1492bb15ea3aac58c79b480272bdb42a758af64deb6fa3d0037f3bb690c097970003
theorem shape1_7:validFrom 11185 0 d1_7=true:=by decide+kernel
def d1_8:List Piece:=DZ.decode 58 42 0xa484aa4041e906fe8aad6d48ebb05ea3aac58c79bac1c7010a17f74eef64deb6fa3d0374406e59bc497860003
theorem shape1_8:validFrom 11184 0 d1_8=true:=by decide+kernel
def d1_9:List Piece:=DZ.decode 58 42 0xa484aa4041e917ea8dce1948abaf5ea3aac58c79c0ebbdeb878a37452f64deb6fa3d06b08d214a6c897740003
theorem shape1_9:validFrom 11183 0 d1_9=true:=by decide+kernel
def _GAM:List Piece:=DZ.decode 58 42 0xa484aa4041e928d690eec5486bae5ea3aac58c79c715b4d604fc773b6f64deb6fa3d09ecd9d43b1cc97620003
theorem shape1_10:validFrom 11182 0 _GAM=true:=by decide+kernel
def _GAX:List Piece:=DZ.decode 58 42 0xa484aa4041e939c2940f71482bad5ea3aac58c79cd5754ab33d1c731af64deb6fa3d0d2926872bcd097510003
theorem shape1_11:validFrom 11181 0 _GAX=true:=by decide+kernel
def _GBF:List Piece:=DZ.decode 58 42 0xa484aa4041e94aae97301d47ebac5ea3aac58c79d3814b95b1440727ef64deb6fa3d1065733a1c7d4973f0003
theorem shape1_12:validFrom 11180 0 _GBF=true:=by decide+kernel
def _GBG:List Piece:=DZ.decode 58 42 0xa484aa4041e95bc3bb7b5957ebab5ea3aac58c79d9ab42802eb6471e6f64deb6fa3d13a1bfed0d2d8972d0003
theorem shape1_13:validFrom 11179 0 _GBG=true:=by decide+kernel
def _GBH:List Piece:=DZ.decode 58 42 0xa484aa4041e96cafbe9c0557abaa5ea3aac58c79dfd5396aac288714af64deb6fa3d16de0c9ffdddc971b0003
theorem shape1_14:validFrom 11178 0 _GBH=true:=by decide+kernel
def _GBI:List Piece:=DZ.decode 58 42 0xa484aa4041e97d9bc1bcb1576ba95ea3aac58c79e5ff3055299ac70aef64deb6fa3d1a1a5952ee8e097090003
theorem shape1_15:validFrom 11177 0 _GBI=true:=by decide+kernel
def _GBJ:List Piece:=DZ.decode 58 42 0xa484aa4041e98e87c4dd5d572ba85ea3aac58c79ec29273fa70d07012f64deb6fa3d1d56a605df3e496f70003
theorem shape1_16:validFrom 11176 0 _GBJ=true:=by decide+kernel
def _GBK:List Piece:=DZ.decode 58 42 0xa484aa4041e99f73c7fe0956eba75ea3aac58c79f23b753f731c36f76f64deb6fa3d2092f2b8cfee896e40003
theorem shape1_17:validFrom 11175 0 _GBK=true:=by decide+kernel
def _GBL:List Piece:=DZ.decode 58 42 0xa484aa4041e9b58f358716eb2ba65ea3aac58c79f8656c29f08e76f12f64deb6fa3d23cf3f6bc09ec96d20003
theorem shape1_18:validFrom 11174 0 _GBL=true:=by decide+kernel
def _GBM:List Piece:=DZ.decode 58 42 0xa484aa4041e9c67b38a7c2eaeba55ea3aac58c79fe77ba29bc9da6e76f64deb6fa3d270b8c1eb14f096bf0003
theorem shape1_19:validFrom 11173 0 _GBM=true:=by decide+kernel
def _GBO:List Piece:=DZ.decode 58 42 0xa484aa4041e9d7905cf2fefaeba45ea3aac58c7a048a082988acd6ddef64deb6fa3d2a47d8d1a1ff496ac0003
theorem shape1_20:validFrom 11172 0 _GBO=true:=by decide+kernel
def _GBP:List Piece:=DZ.decode 58 42 0xa484aa4041ea424e292e6063eba35ea3aac58c7a0ab3ff14061f1710ef64deb6fa3d2d84258492af8969a0003
theorem shape1_21:validFrom 11171 0 _GBP=true:=by decide+kernel
def _GBQ:List Piece:=DZ.decode 58 42 0xa484aa4041ea938d48db8852aba25ea3aac58c7a10c64d13d22e4732af64deb6fa3d30c07237835fc96870003
theorem shape1_22:validFrom 11170 0 _GBQ=true:=by decide+kernel
def _GBR:List Piece:=DZ.decode 58 42 0xa484aa4041eaa4794bfc34526ba15ea3aac58c7a16c0f228ecda6728ef64deb6fa3d33fcbeea7410096730003
theorem shape1_23:validFrom 11169 0 _GBR=true:=by decide+kernel
def _GBS:List Piece:=DZ.decode 58 42 0xa484aa4041eab5654f1ce0522ba05ea3aac58c7a1cd34028b8e9971f2f64deb6fa3d37390b9d64c0496600003
theorem shape1_24:validFrom 11168 0 _GBS=true:=by decide+kernel
def _GBT:List Piece:=DZ.decode 58 42 0xa484aa4041eac651523d8c51eb9f5ea3aac58c7a22e58e2884f8c7156f64deb6fa3d3a75585055708964d0003
theorem shape1_25:validFrom 11167 0 _GBT=true:=by decide+kernel
def _GBU:List Piece:=DZ.decode 58 42 0xa484aa4041ead73d555e3851ab9e5ea3aac58c7a28e0333d9fa4e70baf64deb6fa3d3db1a5034620c96390003
theorem shape1_26:validFrom 11166 0 _GBU=true:=by decide+kernel
def _GBV:List Piece:=DZ.decode 58 42 0xa484aa4041eae829587ee4516b9d5ea3aac58c7a2ef2813d6bb41701ef64deb6fa3d40edf1b636d1096260003
theorem shape1_27:validFrom 11165 0 _GBV=true:=by decide+kernel
def _GBW:List Piece:=DZ.decode 58 42 0xa484aa4041eaf93e7cca20616b9c5ea3aac58c7a34ed2652866036f86f64deb6fa3d442a3e692781496120003
theorem shape1_28:validFrom 11164 0 _GBW=true:=by decide+kernel
def _GBX:List Piece:=DZ.decode 58 42 0xa484aa4041eb0a2a7feacc612b9b5ea3aac58c7a3ae7cb67a10c56eeaf64deb6fa3d47668b1c1831895fe0003
theorem shape1_29:validFrom 11163 0 _GBX=true:=by decide+kernel
def _GBZ:List Piece:=DZ.decode 58 42 0xa484aa4041eb1b16830b7860eb9a5ea3aac58c7a40e2707cbbb876e4ef64deb6fa3d4aa2d7cf08e1c95ea0003
theorem shape1_30:validFrom 11162 0 _GBZ=true:=by decide+kernel
def _GCA:List Piece:=DZ.decode 58 42 0xa484aa4041eb2c02862c2460ab995ea3aac58c7a46dd1591d66496db2f64deb6fa3d4ddf2481f992095d60003
theorem shape1_31:validFrom 11161 0 _GCA=true:=by decide+kernel
def _GCB:List Piece:=DZ.decode 58 42 0xa484aa4041eb3cee894cd0606b985ea3aac58c7a4cc011bc3fada6d16f64deb6fa3d511b7134ea42495c10003
theorem shape1_32:validFrom 11160 0 _GCB=true:=by decide+kernel
def _GCC:List Piece:=DZ.decode 58 42 0xa484aa4041eb4dda8c6d7c602b975ea3aac58c7a52bab6d15a59c6c7af64deb6fa3d5457bde7daf2895ad0003
theorem shape1_33:validFrom 11159 0 _GCC=true:=by decide+kernel
def _GCD:List Piece:=DZ.decode 58 42 0xa484aa4041eb5ec68f8e285feb965ea3aac58c7a589db2fbc3a2d6bdef64deb6fa3d57940a9acba2c95980003
theorem shape1_34:validFrom 11158 0 _GCD=true:=by decide+kernel
def _GCE:List Piece:=DZ.decode 58 42 0xa484aa4041eb6fdbb3d9646feb955ea3aac58c7a5e80af262cebe6b46f64deb6fa3d5ad0574dbc53095830003
theorem shape1_35:validFrom 11157 0 _GCE=true:=by decide+kernel
def _GCF:List Piece:=DZ.decode 58 42 0xa484aa4041eb80c7b6fa106fab945ea3aac58c7a6463ab509634f6aaaf64deb6fa3d5e0ca400ad034956e0003
theorem shape1_36:validFrom 11156 0 _GCF=true:=by decide+kernel
def _GCG:List Piece:=DZ.decode 58 42 0xa484aa4041eb91b3ba1abc6f6b935ea3aac58c7a6a46a77aff7e06a0ef64deb6fa3d6148f0b39db3895590003
theorem shape1_37:validFrom 11155 0 _GCG=true:=by decide+kernel
def _GCH:List Piece:=DZ.decode 58 42 0xa484aa4041eba29fbd3b686f2b925ea3aac58c7a7029a3a568c716972f64deb6fa3d64853d668e63c95440003
theorem shape1_38:validFrom 11154 0 _GCH=true:=by decide+kernel
def _GCI:List Piece:=DZ.decode 58 42 0xa484aa4041ebb38bc05c146eeb915ea3aac58c7a75f4f6e520ad168d6f64deb6fa3d67c18a197f140952e0003
theorem shape1_39:validFrom 11153 0 _GCI=true:=by decide+kernel
def _GCK:List Piece:=DZ.decode 58 42 0xa484aa4041ebc477c37cc06eab905ea3aac58c7a7bd7f30f89f62683af64deb6fa3d6afdd6cc6fc4495190003
theorem shape1_40:validFrom 11152 0 _GCK=true:=by decide+kernel
def _GCL:List Piece:=DZ.decode 58 42 0xa484aa4041ebd563c69d6c6e6b8f5ea3aac58c7a81a3464f41dc2679ef64deb6fa3d6e3a237f6074895030003
theorem shape1_41:validFrom 11151 0 _GCL=true:=by decide+kernel
def _GCM:List Piece:=DZ.decode 58 42 0xa484aa4041ebe678eae8a87e6b8e5ea3aac58c7a8756f0a4485f16706f64deb6fa3d717670325124c94ec0003
theorem shape1_42:validFrom 11150 0 _GCM=true:=by decide+kernel
def _GCN:List Piece:=DZ.decode 58 42 0xa484aa4041ebf764ee09547e2b8d5ea3aac58c7a8d2243e400451666af64deb6fa3d74b2bce541d5094d60003
theorem shape1_43:validFrom 11149 0 _GCN=true:=by decide+kernel
def _GCO:List Piece:=DZ.decode 58 42 0xa484aa4041ec0850f12a007deb8c5ea3aac58c7a92ed9723b82b165cef64deb6fa3d77ef09983285494c00003
theorem shape1_44:validFrom 11148 0 _GCO=true:=by decide+kernel
def _GCP:List Piece:=DZ.decode 58 42 0xa484aa4041ec193cf44aac7dab8b5ea3aac58c7a98a14178beae06532f64deb6fa3d7b2b564b2335894a90003
theorem shape1_45:validFrom 11147 0 _GCP=true:=by decide+kernel
def _GCQ:List Piece:=DZ.decode 58 42 0xa484aa4041ec2a28f76b587d6b8a5ea3aac58c7a9e54ebcdc530f6496f64deb6fa3d7e67a2fe13e5c94920003
theorem shape1_46:validFrom 11146 0 _GCQ=true:=by decide+kernel
def _GCR:List Piece:=DZ.decode 58 42 0xa484aa4041ec3b14fa8c047d2b895ea3aac58c7aa4089622cbb3e63faf64deb6fa3d81a3efb104960947b0003
theorem shape1_47:validFrom 11145 0 _GCR=true:=by decide+kernel
def _GCS:List Piece:=DZ.decode 58 42 0xa484aa4041ec4c00fdacb07ceb885ea3aac58c7aa9a4978d20d3c635ef64deb6fa3d84e03c63f546494630003
theorem shape1_48:validFrom 11144 0 _GCS=true:=by decide+kernel
def _GCT:List Piece:=DZ.decode 58 42 0xa484aa4041ec5d1621f7ec8ceb875ea3aac58c7aaf4098f775f3a62c6f64deb6fa3d881c8916e5f68944b0003
theorem shape1_49:validFrom 11143 0 _GCT=true:=by decide+kernel
def _GCV:List Piece:=DZ.decode 58 42 0xa484aa4041ec6e022518988cab865ea3aac58c7ab4f4434c7c769622af64deb6fa3d8b58d5c9d6a6c94340003
theorem shape1_50:validFrom 11142 0 _GCV=true:=by decide+kernel
def _GCW:List Piece:=DZ.decode 58 42 0xa484aa4041ec7eee2839448c6b855ea3aac58c7aba789bcc20336618ef64deb6fa3d8e95227cc7570941b0003
theorem shape1_51:validFrom 11141 0 _GCW=true:=by decide+kernel
def _GCX:List Piece:=DZ.decode 58 42 0xa484aa4041ec8fda2b59f08c2b845ea3aac58c7ac0149d367553460f2f64deb6fa3da3ede9ac61601d4030003
theorem shape1_52:validFrom 11140 0 _GCX=true:=by decide+kernel
def _GCY:List Piece:=DZ.decode 58 42 0xa484aa4041eca0c62e7a9c8beb835ea3aac58c7ac598f5b6191016056f64deb6fa3da72a365f52105d3ea0003
theorem shape1_53:validFrom 11139 0 _GCY=true:=by decide+kernel
def _GCZ:List Piece:=DZ.decode 58 42 0x29212a90107b022131622d6d1ae0af64deb6fa3dab6c7b1eebc8b93d10002
theorem shape1_54:validFrom 11138 0 _GCZ=true:=by decide+kernel
def _GDA:List Piece:=DZ.decode 58 42 0x29212a90107b06ec263f50a5eae06f64deb6fa3daea8c7d1dc78f93b80002
theorem shape1_55:validFrom 11137 0 _GDA=true:=by decide+kernel
def _GDB:List Piece:=DZ.decode 58 42 0x29212a90107b0bacd2d1cfdaaae02f64deb6fa3db1e51484cd293939e0002
theorem shape1_56:validFrom 11136 0 _GDB=true:=by decide+kernel
def _GDC:List Piece:=DZ.decode 58 42 0x29212a90107b106d7f644f0f6adfef64deb6fa3db5216137bdd9793840002
theorem shape1_57:validFrom 11135 0 _GDC=true:=by decide+kernel
def _GDD:List Piece:=DZ.decode 58 42 0x29212a90107b152e2bf6ce442adfaf64deb6fa3db85dadeaae89b936a0002
theorem shape1_58:validFrom 11134 0 _GDD=true:=by decide+kernel
def _GDE:List Piece:=DZ.decode 58 42 0xa484aa4041ecc929bb51c9a72b7d5ea3aac58c7b226ccadffe82d4feef64deb6fa3dbebf193a2cd51d34f0003
theorem shape1_59:validFrom 11133 0 _GDE=true:=by decide+kernel
def _GDG:List Piece:=DZ.decode 58 42 0xa484aa4041ecdb35a69c6618ab7c5ea3aac58c7b276a1b30b77774f6ef64deb6fa3dc1fb65ed1d855d3340003
theorem shape1_60:validFrom 11132 0 _GDG=true:=by decide+kernel
def _GDH:List Piece:=DZ.decode 58 42 0xa484aa4041eced1870bc7279eb7b5ea3aac58c7b2c4fc296bf0904eeaf64deb6fa3dc537b2a00e359d3180003
theorem shape1_61:validFrom 11131 0 _GDH=true:=by decide+kernel
def _GDI:List Piece:=DZ.decode 58 42 0xa484aa4041ecff245c070eeb6b7a5ea3aac58c7b314d12e777fda4e6af64deb6fa3dcc3dd5d30eeb552fd0003
theorem shape1_62:validFrom 11130 0 _GDI=true:=by decide+kernel
def _GDJ:List Piece:=DZ.decode 62 42 0x3782dace9d900000ade4a484aa40410ed11304751ab5ceab05ea3aac58c43b361b1162ce2c24deaf64deb6fa30dcf7a2285ff9b952e00004
theorem shape1_63:validFrom 11129 0 _GDJ=true:=by decide+kernel
def _GDK:List Piece:=DZ.decode 62 42 0x3782dace9d900000ade0a484aa40410ed23131171b7be298e5ea3aac58c43b3b00b8c8d5bdb4d66f64deb6fa30dd2b66f38f04bd52c40004
theorem shape1_64:validFrom 11128 0 _GDK=true:=by decide+kernel
def _GDL:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7729212a901043b518bd62b184c4a17ef64deb6fa30dd897a7a81f83ad2a70003
theorem shape1_65:validFrom 11127 0 _GDL=true:=by decide+kernel
def _GDM:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7629212a901043b562361930770c9c86f64deb6fa30de043d0678bb4d12890003
theorem shape1_66:validFrom 11126 0 _GDM=true:=by decide+kernel
def _GDN:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7529212a901043b5abaecfaf6954975af64deb6fa30dec460acdf70bb126b0003
theorem shape1_67:validFrom 11125 0 _GDN=true:=by decide+kernel
def _GDO:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7429212a901043b5f48301841b5b91f2f64deb6fa30def825780e7bbf124c0003
theorem shape1_68:validFrom 11124 0 _GDO=true:=by decide+kernel
def _GDP:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7329212a901043b63d573358cd628c56f64deb6fa30df2bea433d86c3122d0003
theorem shape1_69:validFrom 11123 0 _GDP=true:=by decide+kernel
def _GDR:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7229212a901043b68586e0833f288682f64deb6fa30df5faf0e6c91c7120d0003
theorem shape1_70:validFrom 11122 0 _GDR=true:=by decide+kernel
def _GDS:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7129212a901043b6cdb68dadb0ee8072f64deb6fa30df9373d99b9ccb11ed0003
theorem shape1_71:validFrom 11121 0 _GDS=true:=by decide+kernel
def _GDT:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7029212a901043b71541b62de2737a2ef64deb6fa30dfc738a4caa7cf11cc0003
theorem shape1_72:validFrom 11120 0 _GDT=true:=by decide+kernel
def _GDU:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b6f29212a901043b75c285a03d3b773b2f64deb6fa30e032b6caccf5b851aa0003
theorem shape1_73:validFrom 11119 0 _GDU=true:=by decide+kernel
def _GDV:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b6e29212a901043b7a26a792f84ba6cfaf64deb6fa30e0667b95fc00bc51870003
theorem shape1_74:validFrom 11118 0 _GDV=true:=by decide+kernel
def _GDW:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b6d29212a901043b7e8ac985b35bd660ef64deb6fa30e0c3e1910b886251640003
theorem shape1_75:validFrom 11117 0 _GDW=true:=by decide+kernel
def _GDX:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b6c29212a901043b82e4a32dca67f5eeaf64deb6fa30e0f7a65c3a936651400003
theorem shape1_76:validFrom 11116 0 _GDX=true:=by decide+kernel
def _GDY:List Piece:=DZ.decode 62 41 0x3782dace9d900000adad49095480821dc1f9aa76ac137abc77a8eab16310e7daeba3b0745210ca0003
theorem shape1_77:validFrom 11115 0 _GDY=true:=by decide+kernel
def _GDZ:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b5000000000003c2e4e7a9dd9dc355bd49095480821db4962a4f7373527fd7a8eab16310e89bbb3e03b9f4cd9f0004
theorem shape1_78:validFrom 11114 0 _GDZ=true:=by decide+kernel
def _GEA:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b4800000000003c2f57d6861038b549149095480821db56aa15f08714a4157a8eab16310e8c86cbf22cfd04d380004
theorem shape1_79:validFrom 11113 0 _GEA=true:=by decide+kernel
def _GEC:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b4000000000003c30612c08017cc5354bd33aa8b0a1e0bfec8e90d482a1debd33aa8b090effc9d2115645790b8bd47558b188777b0963eaa2dfa82a5ea3aac58c43bb5aa90fa5ffa740dd49095480821db76948e331e5120137a8eab16310e8e91bd68fc9fb8d0b0008
theorem shape1_80:validFrom 11112 0 _GEC=true:=by decide+kernel
def _GED:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b3800000000003c316a7b23ada895208bd33aa8b0a1e0ce60f29afd42a174bd33aa8b090effc36bb5a25059082bd47558b188778b6e946dcb2927f1dea3aac58c43b9bb66003f16c23eb549095480821dc2ed0b599a2979bf57a8eab16310e9441dff42bb7a0d0e0008
theorem shape1_81:validFrom 11111 0 _GED=true:=by decide+kernel
def _GEE:List Piece:=DZ.decode 62 41 0x1bc16d674ec8000056cc00000000000f0c9cf0f6452e3d42c2f4ceaa2c287837411c36c2cd8841af4ceaa2c243c02538a79ed0ea412af51d562c621de2e9342282c7f9edb7a8eab16310e979c6878a5a4b8f1d0006
theorem shape1_82:validFrom 11110 0 _GEE=true:=by decide+kernel
def _GEF:List Piece:=DZ.decode 62 41 0x1bc16d674ec8000056ca00000000000f0cdf418a0dad093d32f4ceaa2c28783b01958ee831e824af4ceaa2c243c01f0d0c1f1341403ef51d562c621de6b190a29e3b69de97a8eab16310e9ce61669aa56fce8a0006
theorem shape1_83:validFrom 11109 0 _GEF=true:=by decide+kernel
def _GEG:List Piece:=DZ.decode 62 41 0x1bc16d674ec8000056c800000000000f0d21908444e5bd3762f4ceaa2c28783ec20239de284806af4ceaa2c243c01766a6c5809a3f46f51d562c621de3f56a4bdc1861ced7a8eab16310e9f0b16149df9d8df20006
theorem shape1_84:validFrom 11108 0 _GEG=true:=by decide+kernel
def _GEH:List Piece:=DZ.decode 62 41 0x1bc16d674ec8000056c600000000000f0d63dde4ead8593152f4ceaa2c2878428e35724d5b67e7af4ceaa2c243c045f4823b22723e46f51d562c621de3906f80bd3d41beb7a8eab16310ea2793eaac0fc7cd550006
theorem shape1_85:validFrom 11107 0 _GEH=true:=by decide+kernel
def _GEI:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6200000000000786d314d61964fe95897a675516143c233901396f3af3e357a675516121e01caebdbfefc71e9f7a8eab16310ea84756b80d4fe8d6f0005
theorem shape1_86:validFrom 11106 0 _GEI=true:=by decide+kernel
def _GEJ:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6100000000000786f439ecdb17d692497a675516143c2524f7c5cbb8d3d297a675516121e03299598053e39e137a8eab16310eabc6b307058fe0ce60005
theorem shape1_87:validFrom 11105 0 _GEJ=true:=by decide+kernel
def _GEK:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6000000000000787155e36d427a28ef17a675516143c27288e70e1db13c0d7a675516121e029bbbb5345ec1d857a8eab16310eae0761975107bcc580005
theorem shape1_88:validFrom 11104 0 _GEK=true:=by decide+kernel
def _GEL:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b5f000000000007873681b40494668b717a675516143c2922e9ad9a0b63aed7a675516121e0208c071c84c79cef7a8eab16310eb052ce53fcadccbc70005
theorem shape1_89:validFrom 11103 0 _GEL=true:=by decide+kernel
def _GEN:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b5e000000000007875738aa628b2487e17a675516143c2b188fd8b360f39bd7a675516121e016fd8b6ad1199c577a8eab16310eb2aff8537ff600b320005
theorem shape1_90:validFrom 11102 0 _GEN=true:=by decide+kernel
def _GEO:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b5d0000000000078775d3196f37fa84297a675516143c2d0e3042a9a0938857a675516121e00cb1ae752fb51bb77a8eab16310eb51bea2a3b0674a980005
theorem shape1_91:validFrom 11101 0 _GEO=true:=by decide+kernel
def _GEP:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b5c00000000000787946ccec9d41c80617a675516143c2a1e54a33556f37457a675516121e04f71aa3e7b3a19697a8eab16310eba76bff78c591c9fb0005
theorem shape1_92:validFrom 11100 0 _GEP=true:=by decide+kernel
def _GEQ:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b5b00000000000787b305caa5a1347c797a675516143c2d181096f650735f97a675516121e03b4607b9325899137a8eab16310ebcbb9f9a7b83fc9590005
theorem shape1_93:validFrom 11099 0 _GEQ=true:=by decide+kernel
def _GER:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b5a00000000000f0fa33c199ebd84f0e5e99d545850f0c07668173a2a4d28bd33aa8b090ee77e3b18b2c668c5c0004
theorem shape1_94:validFrom 11098 0 _GER=true:=by decide+kernel
def _GES:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad640000000000787f035957a4c20744de99d545850efacae5ad383400cd00003
theorem shape1_95:validFrom 11097 0 _GES=true:=by decide+kernel
def _GET:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad6000000000007880ecc64732ab8700de99d545850efbd92226099dd0c760003
theorem shape1_96:validFrom 11096 0 _GET=true:=by decide+kernel
def _GEU:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad5c00000000007882d6279ed385c6bade99d545850efcebcc64918b2cc180003
theorem shape1_97:validFrom 11095 0 _GEU=true:=by decide+kernel
def _GEV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ac0f1097efab6a6ff4ce60002
theorem shape1_98:validFrom 11094 0 _GEV=true:=by decide+kernel
def _GEW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056aa0f10d518effccbc0c530002
theorem shape1_99:validFrom 11093 0 _GEW=true:=by decide+kernel
def _GAN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a80f111240c12b0d10bbc0002
theorem shape1_100:validFrom 11092 0 _GAN=true:=by decide+kernel
def _GAO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a60f114f671f287164b220002
theorem shape1_101:validFrom 11091 0 _GAO=true:=by decide+kernel
def _GAP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a40f118c8c0a282e68a840002
theorem shape1_102:validFrom 11090 0 _GAP=true:=by decide+kernel
def _GAQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a20f11c9af81c3d3389e30002
theorem shape1_103:validFrom 11089 0 _GAQ=true:=by decide+kernel
def _GAR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a00f1206d18661d0c893e0002
theorem shape1_104:validFrom 11088 0 _GAR=true:=by decide+kernel
def _GAS:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569e0f1243f2179bb6e08960002
theorem shape1_105:validFrom 11087 0 _GAS=true:=by decide+kernel
def _GAT:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569c0f12811135d7f4f87ea0002
theorem shape1_106:validFrom 11086 0 _GAT=true:=by decide+kernel
def _GAU:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569a0f12be2ee0b01dec73a0002
theorem shape1_107:validFrom 11085 0 _GAU=true:=by decide+kernel
def _GAV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056980f12fb4b188a9c906860002
theorem shape1_108:validFrom 11084 0 _GAV=true:=by decide+kernel
def _GAW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056960f133865dd0107945cf0002
theorem shape1_109:validFrom 11083 0 _GAW=true:=by decide+kernel
def _GAY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056940f13757f2e79c6c05140002
theorem shape1_110:validFrom 11082 0 _GAY=true:=by decide+kernel
def _GAZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056920f13b2970c8e73d04550002
theorem shape1_111:validFrom 11081 0 _GAZ=true:=by decide+kernel
def _GBA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056900f13efad77a573843940002
theorem shape1_112:validFrom 11080 0 _GBA=true:=by decide+kernel
def _GBB:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000568e0f142cc26f5862ac2cf0002
theorem shape1_113:validFrom 11079 0 _GBB=true:=by decide+kernel
def _GBC:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000568c0f1469d5f40da2ec2070002
theorem shape1_114:validFrom 11078 0 _GBC=true:=by decide+kernel
def _GBD:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000568a0f14a6e8055ed42413c0002
theorem shape1_115:validFrom 11077 0 _GBD=true:=by decide+kernel
def _GBE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056880f14e3f8a3b254ec06d0002
theorem shape1_116:validFrom 11076 0 _GBE=true:=by decide+kernel
def row1 (v:ℕ):List Piece:=match v with
 | 0=>d1_0
 | 1=>d1_1
 | 2=>d1_2
 | 3=>d1_3
 | 4=>d1_4
 | 5=>d1_5
 | 6=>d1_6
 | 7=>d1_7
 | 8=>d1_8
 | 9=>d1_9
 | 10=>_GAM
 | 11=>_GAX
 | 12=>_GBF
 | 13=>_GBG
 | 14=>_GBH
 | 15=>_GBI
 | 16=>_GBJ
 | 17=>_GBK
 | 18=>_GBL
 | 19=>_GBM
 | 20=>_GBO
 | 21=>_GBP
 | 22=>_GBQ
 | 23=>_GBR
 | 24=>_GBS
 | 25=>_GBT
 | 26=>_GBU
 | 27=>_GBV
 | 28=>_GBW
 | 29=>_GBX
 | 30=>_GBZ
 | 31=>_GCA
 | 32=>_GCB
 | 33=>_GCC
 | 34=>_GCD
 | 35=>_GCE
 | 36=>_GCF
 | 37=>_GCG
 | 38=>_GCH
 | 39=>_GCI
 | 40=>_GCK
 | 41=>_GCL
 | 42=>_GCM
 | 43=>_GCN
 | 44=>_GCO
 | 45=>_GCP
 | 46=>_GCQ
 | 47=>_GCR
 | 48=>_GCS
 | 49=>_GCT
 | 50=>_GCV
 | 51=>_GCW
 | 52=>_GCX
 | 53=>_GCY
 | 54=>_GCZ
 | 55=>_GDA
 | 56=>_GDB
 | 57=>_GDC
 | 58=>_GDD
 | 59=>_GDE
 | 60=>_GDG
 | 61=>_GDH
 | 62=>_GDI
 | 63=>_GDJ
 | 64=>_GDK
 | 65=>_GDL
 | 66=>_GDM
 | 67=>_GDN
 | 68=>_GDO
 | 69=>_GDP
 | 70=>_GDR
 | 71=>_GDS
 | 72=>_GDT
 | 73=>_GDU
 | 74=>_GDV
 | 75=>_GDW
 | 76=>_GDX
 | 77=>_GDY
 | 78=>_GDZ
 | 79=>_GEA
 | 80=>_GEC
 | 81=>_GED
 | 82=>_GEE
 | 83=>_GEF
 | 84=>_GEG
 | 85=>_GEH
 | 86=>_GEI
 | 87=>_GEJ
 | 88=>_GEK
 | 89=>_GEL
 | 90=>_GEN
 | 91=>_GEO
 | 92=>_GEP
 | 93=>_GEQ
 | 94=>_GER
 | 95=>_GES
 | 96=>_GET
 | 97=>_GEU
 | 98=>_GEV
 | 99=>_GEW
 | 100=>_GAN
 | 101=>_GAO
 | 102=>_GAP
 | 103=>_GAQ
 | 104=>_GAR
 | 105=>_GAS
 | 106=>_GAT
 | 107=>_GAU
 | 108=>_GAV
 | 109=>_GAW
 | 110=>_GAY
 | 111=>_GAZ
 | 112=>_GBA
 | 113=>_GBB
 | 114=>_GBC
 | 115=>_GBD
 | 116=>_GBE
 | _=>[]
theorem checked1 (v:ℕ) (hy:1+v≤117):validFrom (11193-1-v) 0 (row1 v)=true:=by
 have hv:v≤116:=by omega
 interval_cases v
 · exact shape1_0
 · exact shape1_1
 · exact shape1_2
 · exact shape1_3
 · exact shape1_4
 · exact shape1_5
 · exact shape1_6
 · exact shape1_7
 · exact shape1_8
 · exact shape1_9
 · exact shape1_10
 · exact shape1_11
 · exact shape1_12
 · exact shape1_13
 · exact shape1_14
 · exact shape1_15
 · exact shape1_16
 · exact shape1_17
 · exact shape1_18
 · exact shape1_19
 · exact shape1_20
 · exact shape1_21
 · exact shape1_22
 · exact shape1_23
 · exact shape1_24
 · exact shape1_25
 · exact shape1_26
 · exact shape1_27
 · exact shape1_28
 · exact shape1_29
 · exact shape1_30
 · exact shape1_31
 · exact shape1_32
 · exact shape1_33
 · exact shape1_34
 · exact shape1_35
 · exact shape1_36
 · exact shape1_37
 · exact shape1_38
 · exact shape1_39
 · exact shape1_40
 · exact shape1_41
 · exact shape1_42
 · exact shape1_43
 · exact shape1_44
 · exact shape1_45
 · exact shape1_46
 · exact shape1_47
 · exact shape1_48
 · exact shape1_49
 · exact shape1_50
 · exact shape1_51
 · exact shape1_52
 · exact shape1_53
 · exact shape1_54
 · exact shape1_55
 · exact shape1_56
 · exact shape1_57
 · exact shape1_58
 · exact shape1_59
 · exact shape1_60
 · exact shape1_61
 · exact shape1_62
 · exact shape1_63
 · exact shape1_64
 · exact shape1_65
 · exact shape1_66
 · exact shape1_67
 · exact shape1_68
 · exact shape1_69
 · exact shape1_70
 · exact shape1_71
 · exact shape1_72
 · exact shape1_73
 · exact shape1_74
 · exact shape1_75
 · exact shape1_76
 · exact shape1_77
 · exact shape1_78
 · exact shape1_79
 · exact shape1_80
 · exact shape1_81
 · exact shape1_82
 · exact shape1_83
 · exact shape1_84
 · exact shape1_85
 · exact shape1_86
 · exact shape1_87
 · exact shape1_88
 · exact shape1_89
 · exact shape1_90
 · exact shape1_91
 · exact shape1_92
 · exact shape1_93
 · exact shape1_94
 · exact shape1_95
 · exact shape1_96
 · exact shape1_97
 · exact shape1_98
 · exact shape1_99
 · exact shape1_100
 · exact shape1_101
 · exact shape1_102
 · exact shape1_103
 · exact shape1_104
 · exact shape1_105
 · exact shape1_106
 · exact shape1_107
 · exact shape1_108
 · exact shape1_109
 · exact shape1_110
 · exact shape1_111
 · exact shape1_112
 · exact shape1_113
 · exact shape1_114
 · exact shape1_115
 · exact shape1_116
def d2_0:List Piece:=DZ.decode 58 42 0xa484aa4041e8d94c558aa0b0abb75ea3aac58c79ab8dc41e8dbde768af64deb6fa3cfad1c263afc9317c40003
theorem shape2_0:validFrom 11191 0 d2_0=true:=by decide+kernel
def d2_1:List Piece:=DZ.decode 58 42 0xa484aa4041e8ea3858ab4cb06bb65ea3aac58c79b1cf63f3bc93375eef64deb6fa3cfe0e0f16a079717b30003
theorem shape2_1:validFrom 11190 0 d2_1=true:=by decide+kernel
def d2_2:List Piece:=DZ.decode 58 42 0xa484aa4041e8fb245bcbf8b02bb55ea3aac58c79b81103c8eb6887552f64deb6fa3d014a5bc99129b17a20003
theorem shape2_2:validFrom 11189 0 d2_2=true:=by decide+kernel
def d2_3:List Piece:=DZ.decode 58 42 0xa484aa4041e90c105eeca4afebb45ea3aac58c79be52a39e1a3dd74b6f64deb6fa3d0486a87c81d9f17910003
theorem shape2_3:validFrom 11188 0 d2_3=true:=by decide+kernel
def d2_4:List Piece:=DZ.decode 58 42 0xa484aa4041e91cfc620d50afabb35ea3aac58c79c494437349132741af64deb6fa3d07c2f52f728a317800003
theorem shape2_4:validFrom 11187 0 d2_4=true:=by decide+kernel
def d2_5:List Piece:=DZ.decode 58 42 0xa484aa4041e92de8652dfcaf6bb25ea3aac58c79cad5e34877e87737ef64deb6fa3d0aff41e2633a7176f0003
theorem shape2_5:validFrom 11186 0 d2_5=true:=by decide+kernel
def d2_6:List Piece:=DZ.decode 58 42 0xa484aa4041e93ed4684ea8af2bb15ea3aac58c79d0ffda32f55ab72e2f64deb6fa3d0e3b8e9553eab175d0003
theorem shape2_6:validFrom 11185 0 d2_6=true:=by decide+kernel
def d2_7:List Piece:=DZ.decode 58 42 0xa484aa4041e94fe98c99e4bf2bb05ea3aac58c79d7417a0824300724af64deb6fa3d1177db48449af174c0003
theorem shape2_7:validFrom 11184 0 d2_7=true:=by decide+kernel
def d2_8:List Piece:=DZ.decode 58 42 0xa484aa4041e960d58fba90beebaf5ea3aac58c79dd6b70f2a1a2471aef64deb6fa3d14b427fb354b3173a0003
theorem shape2_8:validFrom 11183 0 d2_8=true:=by decide+kernel
def d2_9:List Piece:=DZ.decode 58 42 0xa484aa4041e971c192db3cbeabae5ea3aac58c79e39567dd1f1487112f64deb6fa3d17f074ae25fb717280003
theorem shape2_9:validFrom 11182 0 d2_9=true:=by decide+kernel
def _HLN:List Piece:=DZ.decode 58 42 0xa484aa4041e982ad95fbe8be6bad5ea3aac58c79e9d707b24de9d7076f64deb6fa3d1b2cc16116abb17170003
theorem shape2_10:validFrom 11181 0 _HLN=true:=by decide+kernel
def _HLY:List Piece:=DZ.decode 58 42 0xa484aa4041e99399991c94be2bac5ea3aac58c79f000fe9ccb5c16fdaf64deb6fa3d1e690e14075bf17050003
theorem shape2_11:validFrom 11180 0 _HLY=true:=by decide+kernel
def _HMF:List Piece:=DZ.decode 58 42 0xa484aa4041e9a4859c3d40bdebab5ea3aac58c79f62af58748ce56f3ef64deb6fa3d21a55ac6f80c316f30003
theorem shape2_12:validFrom 11179 0 _HMF=true:=by decide+kernel
def _HMG:List Piece:=DZ.decode 58 42 0xa484aa4041e9b5719f5decbdabaa5ea3aac58c79fc54ec71c64096ea2f64deb6fa3d24e1a779e8bc716e10003
theorem shape2_13:validFrom 11178 0 _HMG=true:=by decide+kernel
def _HMH:List Piece:=DZ.decode 58 42 0xa484aa4041e9c686c3a928cdaba95ea3aac58c7a027ee35c43b2d6e0af64deb6fa3d281df42cd96cb16cf0003
theorem shape2_14:validFrom 11177 0 _HMH=true:=by decide+kernel
def _HMI:List Piece:=DZ.decode 58 42 0xa484aa4041e9d772c6c9d4cd6ba85ea3aac58c7a0891315c0fc206d6ef64deb6fa3d2b5a40dfca1cf16bc0003
theorem shape2_15:validFrom 11176 0 _HMI=true:=by decide+kernel
def _HMJ:List Piece:=DZ.decode 58 42 0xa484aa4041e9e85ec9ea80cd2ba75ea3aac58c7a0ebb28468d3446cd2f64deb6fa3d2e968d92bacd316aa0003
theorem shape2_16:validFrom 11175 0 _HMJ=true:=by decide+kernel
def _HMK:List Piece:=DZ.decode 58 42 0xa484aa4041e9f94acd0b2ccceba65ea3aac58c7a14cd7646594376c36f64deb6fa3d31d2da45ab7d716970003
theorem shape2_17:validFrom 11174 0 _HMK=true:=by decide+kernel
def _HML:List Piece:=DZ.decode 58 42 0xa484aa4041ea0f663a943a612ba55ea3aac58c7a1af76d30d6b5b6bd2f64deb6fa3d350f26f89c2db16850003
theorem shape2_18:validFrom 11173 0 _HML=true:=by decide+kernel
def _HMM:List Piece:=DZ.decode 58 42 0xa484aa4041ea20523db4e660eba45ea3aac58c7a2109bb30a2c4e6b36f64deb6fa3d384b73ab8cddf16720003
theorem shape2_19:validFrom 11172 0 _HMM=true:=by decide+kernel
def _HMO:List Piece:=DZ.decode 58 42 0xa484aa4041ea316762002270eba35ea3aac58c7a271c09306ed416a9ef64deb6fa3d3b87c05e7d8e3165f0003
theorem shape2_20:validFrom 11171 0 _HMO=true:=by decide+kernel
def _HMP:List Piece:=DZ.decode 58 42 0xa484aa4041ea9c252e3b83d9eba25ea3aac58c7a2d2e57303ae346dcef64deb6fa3d3ec40d116e3e7164c0003
theorem shape2_21:validFrom 11170 0 _HMP=true:=by decide+kernel
def _HMQ:List Piece:=DZ.decode 58 42 0xa484aa4041eaed644de8abc8aba15ea3aac58c7a3340a53006f276feaf64deb6fa3d420059c45eeeb16390003
theorem shape2_22:validFrom 11169 0 _HMQ=true:=by decide+kernel
def _HMR:List Piece:=DZ.decode 58 42 0xa484aa4041eafe50510957c86ba05ea3aac58c7a393b4a45219e96f4ef64deb6fa3d453ca6774f9ef16250003
theorem shape2_23:validFrom 11168 0 _HMR=true:=by decide+kernel
def _HMS:List Piece:=DZ.decode 58 42 0xa484aa4041eb0f3c542a03c82b9f5ea3aac58c7a3f4d9844edadc6eb2f64deb6fa3d4878f32a404f316120003
theorem shape2_24:validFrom 11167 0 _HMS=true:=by decide+kernel
def _HMT:List Piece:=DZ.decode 58 42 0xa484aa4041eb2028574aafc7eb9e5ea3aac58c7a45483d5a0859e6e16f64deb6fa3d4bb53fdd30ff715fe0003
theorem shape2_25:validFrom 11166 0 _HMT=true:=by decide+kernel
def _HMU:List Piece:=DZ.decode 58 42 0xa484aa4041eb31145a6b5bc7ab9d5ea3aac58c7a4b5a8b59d46916d7af64deb6fa3d4ef18c9021afb15eb0003
theorem shape2_26:validFrom 11165 0 _HMU=true:=by decide+kernel
def _HMV:List Piece:=DZ.decode 58 42 0xa484aa4041eb42005d8c07c76b9c5ea3aac58c7a5155306eef1536cdef64deb6fa3d522dd943125ff15d70003
theorem shape2_27:validFrom 11164 0 _HMV=true:=by decide+kernel
def _HMW:List Piece:=DZ.decode 58 42 0xa484aa4041eb531581d743d76b9b5ea3aac58c7a574fd58409c156c46f64deb6fa3d556a25f60310315c30003
theorem shape2_28:validFrom 11163 0 _HMW=true:=by decide+kernel
def _HMX:List Piece:=DZ.decode 58 42 0xa484aa4041eb640184f7efd72b9a5ea3aac58c7a5d4a7a99246d76baaf64deb6fa3d58a672a8f3c0715af0003
theorem shape2_29:validFrom 11162 0 _HMX=true:=by decide+kernel
def _HMZ:List Piece:=DZ.decode 58 42 0xa484aa4041eb74ed88189bd6eb995ea3aac58c7a632d76c38db686b0ef64deb6fa3d5be2bf5be470b159a0003
theorem shape2_30:validFrom 11161 0 _HMZ=true:=by decide+kernel
def _HNA:List Piece:=DZ.decode 58 42 0xa484aa4041eb85d98b3947d6ab985ea3aac58c7a69281bd8a862a6a72f64deb6fa3d5f1f0c0ed520f15860003
theorem shape2_31:validFrom 11160 0 _HNA=true:=by decide+kernel
def _HNB:List Piece:=DZ.decode 58 42 0xa484aa4041eb96c58e59f3d66b975ea3aac58c7a6f0b180311abb69d6f64deb6fa3d625b58c1c5d1315710003
theorem shape2_32:validFrom 11159 0 _HNB=true:=by decide+kernel
def _HNC:List Piece:=DZ.decode 58 42 0xa484aa4041eba7b1917a9fd62b965ea3aac58c7a7505bd182c57d693af64deb6fa3d6597a574b6817155d0003
theorem shape2_33:validFrom 11158 0 _HNC=true:=by decide+kernel
def _HND:List Piece:=DZ.decode 58 42 0xa484aa4041ebb89d949b4bd5eb955ea3aac58c7a7ae8b94295a0e689ef64deb6fa3d68d3f227a731b15480003
theorem shape2_34:validFrom 11157 0 _HND=true:=by decide+kernel
def _HNE:List Piece:=DZ.decode 58 42 0xa484aa4041ebc9b2b8e687e5eb945ea3aac58c7a80cbb56cfee9f6806f64deb6fa3d6c103eda97e1f15330003
theorem shape2_35:validFrom 11156 0 _HNE=true:=by decide+kernel
def _HNF:List Piece:=DZ.decode 58 42 0xa484aa4041ebda9ebc0733e5ab935ea3aac58c7a869708acb6cff676af64deb6fa3d6f4c8b8d88923151d0003
theorem shape2_36:validFrom 11155 0 _HNF=true:=by decide+kernel
def _HNG:List Piece:=DZ.decode 58 42 0xa484aa4041ebeb8abf27dfe56b925ea3aac58c7a8c7a04d72019066cef64deb6fa3d7288d8407942715080003
theorem shape2_37:validFrom 11154 0 _HNG=true:=by decide+kernel
def _HNH:List Piece:=DZ.decode 58 42 0xa484aa4041ebfc76c2488be52b915ea3aac58c7a92455816d7ff06632f64deb6fa3d75c524f369f2b14f20003
theorem shape2_38:validFrom 11153 0 _HNH=true:=by decide+kernel
def _HNI:List Piece:=DZ.decode 58 42 0xa484aa4041ec0d62c56937e4eb905ea3aac58c7a9810ab568fe506596f64deb6fa3d790171a65aa2f14dc0003
theorem shape2_39:validFrom 11152 0 _HNI=true:=by decide+kernel
def _HNK:List Piece:=DZ.decode 58 42 0xa484aa4041ec1e4ec889e3e4ab8f5ea3aac58c7a9ddbfe9647cb064faf64deb6fa3d7c3dbe594b53314c60003
theorem shape2_40:validFrom 11151 0 _HNK=true:=by decide+kernel
def _HNL:List Piece:=DZ.decode 58 42 0xa484aa4041ec2f3acbaa8fe46b8e5ea3aac58c7aa3a751d5ffb10645ef64deb6fa3d7f7a0b0c3c03714b00003
theorem shape2_41:validFrom 11150 0 _HNL=true:=by decide+kernel
def _HNM:List Piece:=DZ.decode 58 42 0xa484aa4041ec404feff5cbf46b8d5ea3aac58c7aa972a515b797063c6f64deb6fa3d82b657bf2cb3b149a0003
theorem shape2_42:validFrom 11149 0 _HNM=true:=by decide+kernel
def _HNN:List Piece:=DZ.decode 58 42 0xa484aa4041ec513bf31677f42b8c5ea3aac58c7aaf264f6abe19f632af64deb6fa3d85f2a4721d63f14830003
theorem shape2_43:validFrom 11148 0 _HNN=true:=by decide+kernel
def _HNO:List Piece:=DZ.decode 58 42 0xa484aa4041ec6227f63723f3eb8b5ea3aac58c7ab4d9f9bfc49ce628ef64deb6fa3d892ef1250e143146c0003
theorem shape2_44:validFrom 11147 0 _HNO=true:=by decide+kernel
def _HNP:List Piece:=DZ.decode 58 42 0xa484aa4041ec7313f957cff3ab8a5ea3aac58c7aba8da414cb1fd61f2f64deb6fa3d8c6b3dd7fec4714550003
theorem shape2_45:validFrom 11146 0 _HNP=true:=by decide+kernel
def _HNQ:List Piece:=DZ.decode 58 42 0xa484aa4041ec83fffc787bf36b895ea3aac58c7ac029a57f203fb6156f64deb6fa3d8fa78a8aef74b143d0003
theorem shape2_46:validFrom 11145 0 _HNQ=true:=by decide+kernel
def _HNR:List Piece:=DZ.decode 58 42 0xa484aa4041ec94ebff9927f32b885ea3aac58c7ac5dd4fd426c2a60baf64deb6fa3d92e3d73de024f14260003
theorem shape2_47:validFrom 11144 0 _HNR=true:=by decide+kernel
def _HNS:List Piece:=DZ.decode 58 42 0xa484aa4041eca5d802b9d3f2eb875ea3aac58c7acb79513e7be28601ef64deb6fa3d962023f0d0d53140e0003
theorem shape2_48:validFrom 11143 0 _HNS=true:=by decide+kernel
def _HNT:List Piece:=DZ.decode 58 42 0xa484aa4041ecb6ed27051002eb865ea3aac58c7ad11552a8d10265f86f64deb6fa3d995c70a3c185713f60003
theorem shape2_49:validFrom 11142 0 _HNT=true:=by decide+kernel
def _HNV:List Piece:=DZ.decode 58 42 0xa484aa4041ecc7d92a25bc02ab855ea3aac58c7ad6b15413262245eeaf64deb6fa3d9c98bd56b235b13de0003
theorem shape2_50:validFrom 11141 0 _HNV=true:=by decide+kernel
def _HNW:List Piece:=DZ.decode 58 42 0xa484aa4041ecd8c52d4668026b845ea3aac58c7adc35ac92c9df15e4ef64deb6fa3d9fd50a09a2e5f13c50003
theorem shape2_51:validFrom 11140 0 _HNW=true:=by decide+kernel
def _HNX:List Piece:=DZ.decode 58 42 0xa484aa4041ece9b1306714022b835ea3aac58c7ae1ba05126d9be5db2f64deb6fa3db52dd1393cef053ac0003
theorem shape2_52:validFrom 11139 0 _HNX=true:=by decide+kernel
def _HNY:List Piece:=DZ.decode 58 42 0xa484aa4041ecfa9d3387c001eb825ea3aac58c7ae73e5d921158b5d16f64deb6fa3db86a1dec2d9f453930003
theorem shape2_53:validFrom 11138 0 _HNY=true:=by decide+kernel
def _HNZ:List Piece:=DZ.decode 58 42 0x29212a90107b1d68d5a258321ae06f64deb6fa3dbcac62abc757a13790002
theorem shape2_54:validFrom 11137 0 _HNZ=true:=by decide+kernel
def _HOA:List Piece:=DZ.decode 58 42 0x29212a90107b22298234d766dae02f64deb6fa3dbfe8af5eb807e135f0002
theorem shape2_55:validFrom 11136 0 _HOA=true:=by decide+kernel
def _HOB:List Piece:=DZ.decode 58 42 0x29212a90107b26ea2ec7569b9adfef64deb6fa3dc324fc11a8b8213450002
theorem shape2_56:validFrom 11135 0 _HOB=true:=by decide+kernel
def _HOC:List Piece:=DZ.decode 58 42 0x29212a90107b2baadb59d5d05adfaf64deb6fa3dc66148c499686132b0002
theorem shape2_57:validFrom 11134 0 _HOC=true:=by decide+kernel
def _HOD:List Piece:=DZ.decode 58 42 0x29212a90107b30613fa1b1010adf6f64deb6fa3dc99d95778a18a13100002
theorem shape2_58:validFrom 11133 0 _HOD=true:=by decide+kernel
def _HOE:List Piece:=DZ.decode 58 42 0xa484aa4041ed287728060f45ab7c5ea3aac58c7b41fe549459ce04d36f64deb6fa3dcfff00c70864052f50003
theorem shape2_59:validFrom 11132 0 _HOE=true:=by decide+kernel
def _HOG:List Piece:=DZ.decode 62 42 0x3782dace9d900000adeca484aa40410ed3a831350abb72b545ea3aac58c43b46e3fbfa615f94cb6f64deb6fa30dd33b4d79f914452d90004
theorem shape2_60:validFrom 11131 0 _HOG=true:=by decide+kernel
def _HOH:List Piece:=DZ.decode 62 42 0x3782dace9d900000ade8a484aa40410ed4c8efe9b4828aa455ea3aac58c43b4bc9a36068f124c36f64deb6fa30dd6779a2ce9c4852bd0004
theorem shape2_61:validFrom 11130 0 _HOH=true:=by decide+kernel
def _HOI:List Piece:=DZ.decode 62 42 0x3782dace9d900000ade4a484aa40410ed5e71c8bb5489e9295ea3aac58c43b5097a1dbbf1fa4bb2f64deb6fa30ddd7dbd5fea7a3d2a00004
theorem shape2_62:validFrom 11129 0 _HOI=true:=by decide+kernel
def _HOJ:List Piece:=DZ.decode 62 42 0x3782dace9d900000ade0a484aa40410ed707db405f0fb67fe5ea3aac58c43b557d4941c6b134b32f64deb6fa30de0ba0a12db2a7d2840004
theorem shape2_63:validFrom 11128 0 _HOJ=true:=by decide+kernel
def _HOK:List Piece:=DZ.decode 62 42 0x3782dace9d900000addca484aa40410ed82899f508d6ce6c65ea3aac58c43b5a339ed26b7ca4ab2f64deb6fa30de3f656c5cbdabd2660004
theorem shape2_64:validFrom 11127 0 _HOK=true:=by decide+kernel
def _HOL:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7629212a901043b6e3178b1c53939602f64deb6fa30de9d78f34fb12952480003
theorem shape2_65:validFrom 11126 0 _HOL=true:=by decide+kernel
def _HOM:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7529212a901043b7a51c39beae3d90b2f64deb6fa30df183b7f46743b922a0003
theorem shape2_66:validFrom 11125 0 _HOM=true:=by decide+kernel
def _HON:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7429212a901043b7edf06b9360448b2af64deb6fa30dfd85f25ad29a9920b0003
theorem shape2_67:validFrom 11124 0 _HON=true:=by decide+kernel
def _HOO:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7329212a901043b8362018bdd20a856af64deb6fa30e00c23f0dc34ad91eb0003
theorem shape2_68:validFrom 11123 0 _HOO=true:=by decide+kernel
def _HOP:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7229212a901043b87e4fc5e843d07f72f64deb6fa30e03fe8bc0b3fb191cb0003
theorem shape2_69:validFrom 11122 0 _HOP=true:=by decide+kernel
def _HOR:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7129212a901043b8c5daee6875557942f64deb6fa30e073ad873a4ab591aa0003
theorem shape2_70:validFrom 11121 0 _HOR=true:=by decide+kernel
def _HOS:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7029212a901043b90d6616e8a6da72daf64deb6fa30e0a772526955b991890003
theorem shape2_71:validFrom 11120 0 _HOS=true:=by decide+kernel
def _HOT:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b6f29212a901043b9544cbabe981e6c3af64deb6fa30e0db371d9860bd91670003
theorem shape2_72:validFrom 11119 0 _HOT=true:=by decide+kernel
def _HOU:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b6e29212a901043b99a8ed9ea49216562f64deb6fa30e146b5439aaea6d1440003
theorem shape2_73:validFrom 11118 0 _HOU=true:=by decide+kernel
def _HOV:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b6d29212a901043b9e02c746bb9e35e52f64deb6fa30e17a7a0ec9b9aad1200003
theorem shape2_74:validFrom 11117 0 _HOV=true:=by decide+kernel
def _HOW:List Piece:=DZ.decode 62 41 0x3782dace9d900000adb149095480821dcfcb92684ec902b877a8eab16310e8508f0a4c567510b70003
theorem shape2_75:validFrom 11116 0 _HOW=true:=by decide+kernel
def _HOX:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b5800000000003c306b42a3eb046551d49095480821dca0eddcc232ec27c77a8eab16310e8c1c05daee3b94f090004
theorem shape2_76:validFrom 11115 0 _HOX=true:=by decide+kernel
def _HOY:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b5000000000003c3170e19a5b4ec53f549095480821dcc2c5e3038aeba3eb7a8eab16310e8e11561c68b3f0ee20004
theorem shape2_77:validFrom 11114 0 _HOY=true:=by decide+kernel
def _HOZ:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b4800000000003c32767a3a33e2252c0bd33aa8b0a1e0d240e714c664a1a2bd33aa8b090f0179672beb8b5109abd47558b18877a319b90a7769481d5ea3aac58c43bca9f54b5381de407949095480821dd87c7ee7091391ff57a8eab16310e9427a7c7cbdc10ee50008
theorem shape2_78:validFrom 11113 0 _HOZ=true:=by decide+kernel
def _HPA:List Piece:=DZ.decode 62 41 0x1bc16d674ec8000056d000000000000f0cdf0320dd2e2945f2f4ceaa2c28783825d922d46a684e2f4ceaa2c243c0596d8e963ecb4196f51d562c621de72d4e5b9ddb61f957a8eab16310e96f2bfd9bd39c8f960006
theorem shape2_79:validFrom 11112 0 _HPA=true:=by decide+kernel
def _HPC:List Piece:=DZ.decode 62 41 0x1bc16d674ec8000056ce00000000000f0d20661d87760d40a2f4ceaa2c28783bbb6bf2a28f08332f4ceaa2c243c053c3bd08eb4040b6f51d562c621de4b358320aa759ead7a8eab16310e98fdb1508cdc7cf080006
theorem shape2_80:validFrom 11111 0 _HPC=true:=by decide+kernel
def _HPD:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6600000000000786b0e3c245e6b29d917a675516143c1fb44c5431edd40b57a675516121e0267ede39105c9fe77a8eab16310e9eadd3dbbbf464ede0005
theorem shape2_81:validFrom 11110 0 _HPD=true:=by decide+kernel
def _HPE:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6500000000000786d193aaf51c229ab97a675516143c2190c606415573fc97a675516121e03e7620548dab9f6f7a8eab16310ea2085c6035e17ce620005
theorem shape2_82:validFrom 11109 0 _HPE=true:=by decide+kernel
def _HPF:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6400000000000786f242c8d159f697b97a675516143c2373230ebab493ed57a675516121e038ca1dbfc8379ef17a8eab16310ea7520a513a93c0de20005
theorem shape2_83:validFrom 11108 0 _HPF=true:=by decide+kernel
def _HPG:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b630000000000078712f11bdaa0ea94a17a675516143c255b636d9e1313dd57a675516121e0331de9e8a34d9e6d7a8eab16310ea97709fc2e369cd5f0005
theorem shape2_84:validFrom 11107 0 _HPG=true:=by decide+kernel
def _HPH:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6200000000000787339ea410f0a091717a675516143c27498722eb7193cc97a675516121e047cea2ce8d9a1de57a8eab16310eace53292513940cd70005
theorem shape2_85:validFrom 11106 0 _HPH=true:=by decide+kernel
def _HPI:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b6100000000000f0ea896c2e891711c45e99d545850f0a4f638ba8b1dceedbd33aa8b090edda2f39d9db9dceab0004
theorem shape2_86:validFrom 11105 0 _HPI=true:=by decide+kernel
def _HPJ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad80000000000078774f75404a9ee8abde99d545850ef58b5bee697c44ea50003
theorem shape2_87:validFrom 11104 0 _HPJ=true:=by decide+kernel
def _HPK:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad7c000000000078795a27bc21388872de99d545850ef67ad7c0cd27e0e5b0003
theorem shape2_88:validFrom 11103 0 _HPK=true:=by decide+kernel
def _HPL:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad780000000000787b5e3695e49ee8385e99d545850ef76c3218e27c50e0e0003
theorem shape2_89:validFrom 11102 0 _HPL=true:=by decide+kernel
def _HPN:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad740000000000787d4134d718ee87fc5e99d545850ef861fa39c9aad4dbe0003
theorem shape2_90:validFrom 11101 0 _HPN=true:=by decide+kernel
def _HPO:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad700000000000787f242796071247be5e99d545850ef95daa8b3a1c38d6c0003
theorem shape2_91:validFrom 11100 0 _HPO=true:=by decide+kernel
def _HPP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f1020e1daba4d00efd0002
theorem shape2_92:validFrom 11099 0 _HPP=true:=by decide+kernel
def _HPQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f105d3d526af480e7a0002
theorem shape2_93:validFrom 11098 0 _HPQ=true:=by decide+kernel
def _HPR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f1099975a374000df30002
theorem shape2_94:validFrom 11097 0 _HPR=true:=by decide+kernel
def _HPS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b00f10d5eff1bac9c4d690002
theorem shape2_95:validFrom 11096 0 _HPS=true:=by decide+kernel
def _HPT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ae0f1112471959f47ccdb0002
theorem shape2_96:validFrom 11095 0 _HPT=true:=by decide+kernel
def _HPU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ac0f114e9cd0b06084c4a0002
theorem shape2_97:validFrom 11094 0 _HPU=true:=by decide+kernel
def _HPV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056aa0f118af118226d8cbb40002
theorem shape2_98:validFrom 11093 0 _HPV=true:=by decide+kernel
def _HPW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a80f11c743ef4bbbd4b1b0002
theorem shape2_99:validFrom 11092 0 _HPW=true:=by decide+kernel
def _HLO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a60f120395565e7ba0a7f0002
theorem shape2_100:validFrom 11091 0 _HLO=true:=by decide+kernel
def _HLP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a40f123fe54d8cda2c9df0002
theorem shape2_101:validFrom 11090 0 _HLP=true:=by decide+kernel
def _HLQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a20f127c33d4727c4093b0002
theorem shape2_102:validFrom 11089 0 _HLQ=true:=by decide+kernel
def _HLR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a00f12b880eb73b9f48950002
theorem shape2_103:validFrom 11088 0 _HLR=true:=by decide+kernel
def _HLS:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569e0f12f4cc922c3d887eb0002
theorem shape2_104:validFrom 11087 0 _HLS=true:=by decide+kernel
def _HLT:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569c0f133116c9005d9c73d0002
theorem shape2_105:validFrom 11086 0 _HLT=true:=by decide+kernel
def _HLU:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569a0f136d5f8f8bc43468c0002
theorem shape2_106:validFrom 11085 0 _HLU=true:=by decide+kernel
def _HLV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056980f13a9a6e632c5105d60002
theorem shape2_107:validFrom 11084 0 _HLV=true:=by decide+kernel
def _HLW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056960f13e5eccc910df051b0002
theorem shape2_108:validFrom 11083 0 _HLW=true:=by decide+kernel
def _HLX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056940f142231430aef9045e0002
theorem shape2_109:validFrom 11082 0 _HLX=true:=by decide+kernel
def _HLZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056920f145e74493c18f039d0002
theorem shape2_110:validFrom 11081 0 _HLZ=true:=by decide+kernel
def _HMA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056900f149ab5df88db542d90002
theorem shape2_111:validFrom 11080 0 _HMA=true:=by decide+kernel
def _HMB:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000568e0f14d6f6058ce8bc2120002
theorem shape2_112:validFrom 11079 0 _HMB=true:=by decide+kernel
def _HMC:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000568c0f151334bbac8be41490002
theorem shape2_113:validFrom 11078 0 _HMC=true:=by decide+kernel
def _HMD:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000568a0f154f7201837b9007b0002
theorem shape2_114:validFrom 11077 0 _HMD=true:=by decide+kernel
def _HME:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bd77e327b280210f158badd775ff7c0020002
theorem shape2_115:validFrom 11076 0 _HME=true:=by decide+kernel
def row2 (v:ℕ):List Piece:=match v with
 | 0=>d2_0
 | 1=>d2_1
 | 2=>d2_2
 | 3=>d2_3
 | 4=>d2_4
 | 5=>d2_5
 | 6=>d2_6
 | 7=>d2_7
 | 8=>d2_8
 | 9=>d2_9
 | 10=>_HLN
 | 11=>_HLY
 | 12=>_HMF
 | 13=>_HMG
 | 14=>_HMH
 | 15=>_HMI
 | 16=>_HMJ
 | 17=>_HMK
 | 18=>_HML
 | 19=>_HMM
 | 20=>_HMO
 | 21=>_HMP
 | 22=>_HMQ
 | 23=>_HMR
 | 24=>_HMS
 | 25=>_HMT
 | 26=>_HMU
 | 27=>_HMV
 | 28=>_HMW
 | 29=>_HMX
 | 30=>_HMZ
 | 31=>_HNA
 | 32=>_HNB
 | 33=>_HNC
 | 34=>_HND
 | 35=>_HNE
 | 36=>_HNF
 | 37=>_HNG
 | 38=>_HNH
 | 39=>_HNI
 | 40=>_HNK
 | 41=>_HNL
 | 42=>_HNM
 | 43=>_HNN
 | 44=>_HNO
 | 45=>_HNP
 | 46=>_HNQ
 | 47=>_HNR
 | 48=>_HNS
 | 49=>_HNT
 | 50=>_HNV
 | 51=>_HNW
 | 52=>_HNX
 | 53=>_HNY
 | 54=>_HNZ
 | 55=>_HOA
 | 56=>_HOB
 | 57=>_HOC
 | 58=>_HOD
 | 59=>_HOE
 | 60=>_HOG
 | 61=>_HOH
 | 62=>_HOI
 | 63=>_HOJ
 | 64=>_HOK
 | 65=>_HOL
 | 66=>_HOM
 | 67=>_HON
 | 68=>_HOO
 | 69=>_HOP
 | 70=>_HOR
 | 71=>_HOS
 | 72=>_HOT
 | 73=>_HOU
 | 74=>_HOV
 | 75=>_HOW
 | 76=>_HOX
 | 77=>_HOY
 | 78=>_HOZ
 | 79=>_HPA
 | 80=>_HPC
 | 81=>_HPD
 | 82=>_HPE
 | 83=>_HPF
 | 84=>_HPG
 | 85=>_HPH
 | 86=>_HPI
 | 87=>_HPJ
 | 88=>_HPK
 | 89=>_HPL
 | 90=>_HPN
 | 91=>_HPO
 | 92=>_HPP
 | 93=>_HPQ
 | 94=>_HPR
 | 95=>_HPS
 | 96=>_HPT
 | 97=>_HPU
 | 98=>_HPV
 | 99=>_HPW
 | 100=>_HLO
 | 101=>_HLP
 | 102=>_HLQ
 | 103=>_HLR
 | 104=>_HLS
 | 105=>_HLT
 | 106=>_HLU
 | 107=>_HLV
 | 108=>_HLW
 | 109=>_HLX
 | 110=>_HLZ
 | 111=>_HMA
 | 112=>_HMB
 | 113=>_HMC
 | 114=>_HMD
 | 115=>_HME
 | _=>[]
theorem checked2 (v:ℕ) (hy:2+v≤117):validFrom (11193-2-v) 0 (row2 v)=true:=by
 have hv:v≤115:=by omega
 interval_cases v
 · exact shape2_0
 · exact shape2_1
 · exact shape2_2
 · exact shape2_3
 · exact shape2_4
 · exact shape2_5
 · exact shape2_6
 · exact shape2_7
 · exact shape2_8
 · exact shape2_9
 · exact shape2_10
 · exact shape2_11
 · exact shape2_12
 · exact shape2_13
 · exact shape2_14
 · exact shape2_15
 · exact shape2_16
 · exact shape2_17
 · exact shape2_18
 · exact shape2_19
 · exact shape2_20
 · exact shape2_21
 · exact shape2_22
 · exact shape2_23
 · exact shape2_24
 · exact shape2_25
 · exact shape2_26
 · exact shape2_27
 · exact shape2_28
 · exact shape2_29
 · exact shape2_30
 · exact shape2_31
 · exact shape2_32
 · exact shape2_33
 · exact shape2_34
 · exact shape2_35
 · exact shape2_36
 · exact shape2_37
 · exact shape2_38
 · exact shape2_39
 · exact shape2_40
 · exact shape2_41
 · exact shape2_42
 · exact shape2_43
 · exact shape2_44
 · exact shape2_45
 · exact shape2_46
 · exact shape2_47
 · exact shape2_48
 · exact shape2_49
 · exact shape2_50
 · exact shape2_51
 · exact shape2_52
 · exact shape2_53
 · exact shape2_54
 · exact shape2_55
 · exact shape2_56
 · exact shape2_57
 · exact shape2_58
 · exact shape2_59
 · exact shape2_60
 · exact shape2_61
 · exact shape2_62
 · exact shape2_63
 · exact shape2_64
 · exact shape2_65
 · exact shape2_66
 · exact shape2_67
 · exact shape2_68
 · exact shape2_69
 · exact shape2_70
 · exact shape2_71
 · exact shape2_72
 · exact shape2_73
 · exact shape2_74
 · exact shape2_75
 · exact shape2_76
 · exact shape2_77
 · exact shape2_78
 · exact shape2_79
 · exact shape2_80
 · exact shape2_81
 · exact shape2_82
 · exact shape2_83
 · exact shape2_84
 · exact shape2_85
 · exact shape2_86
 · exact shape2_87
 · exact shape2_88
 · exact shape2_89
 · exact shape2_90
 · exact shape2_91
 · exact shape2_92
 · exact shape2_93
 · exact shape2_94
 · exact shape2_95
 · exact shape2_96
 · exact shape2_97
 · exact shape2_98
 · exact shape2_99
 · exact shape2_100
 · exact shape2_101
 · exact shape2_102
 · exact shape2_103
 · exact shape2_104
 · exact shape2_105
 · exact shape2_106
 · exact shape2_107
 · exact shape2_108
 · exact shape2_109
 · exact shape2_110
 · exact shape2_111
 · exact shape2_112
 · exact shape2_113
 · exact shape2_114
 · exact shape2_115
def d3_0:List Piece:=DZ.decode 58 42 0xa484aa4041e933235a97c426abb65ea3aac58c79ce376e1025483734af64deb6fa3d0c11a9f08b58197780003
theorem shape3_0:validFrom 11190 0 d3_0=true:=by decide+kernel
def d3_1:List Piece:=DZ.decode 58 42 0xa484aa4041e9440f5db870266bb55ea3aac58c79d4790de5541d872aef64deb6fa3d0f4df6a37c08597670003
theorem shape3_1:validFrom 11189 0 d3_1=true:=by decide+kernel
def d3_2:List Piece:=DZ.decode 58 42 0xa484aa4041e954fb60d91c262bb45ea3aac58c79dabaadba82f2d7212f64deb6fa3d128a43566cb8997560003
theorem shape3_2:validFrom 11188 0 d3_2=true:=by decide+kernel
def d3_3:List Piece:=DZ.decode 58 42 0xa484aa4041e965e763f9c825ebb35ea3aac58c79e0fc4d8fb1c827176f64deb6fa3d15c690095d68d97450003
theorem shape3_3:validFrom 11187 0 d3_3=true:=by decide+kernel
def d3_4:List Piece:=DZ.decode 58 42 0xa484aa4041e976d3671a7425abb25ea3aac58c79e726447a2f3a670daf64deb6fa3d1902dcbc4e19197330003
theorem shape3_4:validFrom 11186 0 d3_4=true:=by decide+kernel
def d3_5:List Piece:=DZ.decode 58 42 0xa484aa4041e987bf6a3b20256bb15ea3aac58c79ed67e44f5e0fb703ef64deb6fa3d1c3f296f3ec9597220003
theorem shape3_5:validFrom 11185 0 d3_5=true:=by decide+kernel
def d3_6:List Piece:=DZ.decode 58 42 0xa484aa4041e998ab6d5bcc252bb05ea3aac58c79f391db39db81f6fa2f64deb6fa3d1f7b76222f79997100003
theorem shape3_6:validFrom 11184 0 d3_6=true:=by decide+kernel
def d3_7:List Piece:=DZ.decode 58 42 0xa484aa4041e9a9c091a708352baf5ea3aac58c79f9d37b0f0a5746f0af64deb6fa3d22b7c2d52029d96ff0003
theorem shape3_7:validFrom 11183 0 d3_7=true:=by decide+kernel
def d3_8:List Piece:=DZ.decode 58 42 0xa484aa4041e9baac94c7b434ebae5ea3aac58c79fffd71f987c986e6ef64deb6fa3d25f40f8810da196ed0003
theorem shape3_8:validFrom 11182 0 d3_8=true:=by decide+kernel
def d3_9:List Piece:=DZ.decode 58 42 0xa484aa4041e9cb9897e86034abad5ea3aac58c7a062768e4053bc6dd2f64deb6fa3d29305c3b018a596db0003
theorem shape3_9:validFrom 11181 0 d3_9=true:=by decide+kernel
def _HPZ:List Piece:=DZ.decode 58 42 0xa484aa4041e9dc849b090c346bac5ea3aac58c7a0c515fce82ae06d36f64deb6fa3d2c6ca8edf23a996c90003
theorem shape3_10:validFrom 11180 0 _HPZ=true:=by decide+kernel
def _HQK:List Piece:=DZ.decode 58 42 0xa484aa4041e9ed709e29b8342bab5ea3aac58c7a127b56b9002046c9af64deb6fa3d2fa8f5a0e2ead96b70003
theorem shape3_11:validFrom 11179 0 _HQK=true:=by decide+kernel
def _HQQ:List Piece:=DZ.decode 58 42 0xa484aa4041e9fe5ca14a6433ebaa5ea3aac58c7a18a54da37d9286bfef64deb6fa3d32e54253d39b196a50003
theorem shape3_12:validFrom 11178 0 _HQQ=true:=by decide+kernel
def _HQR:List Piece:=DZ.decode 58 42 0xa484aa4041ea0f48a46b1033aba95ea3aac58c7a1ecf448dfb04c6b62f64deb6fa3d36218f06c44b596930003
theorem shape3_13:validFrom 11177 0 _HQR=true:=by decide+kernel
def _HQS:List Piece:=DZ.decode 58 42 0xa484aa4041ea205dc8b64c43aba85ea3aac58c7a24e1928dc713f6acaf64deb6fa3d395ddbb9b4fb996800003
theorem shape3_14:validFrom 11176 0 _HQS=true:=by decide+kernel
def _HQT:List Piece:=DZ.decode 58 42 0xa484aa4041ea3149cbd6f8436ba75ea3aac58c7a2b0b8978448636a2ef64deb6fa3d3c9a286ca5abd966e0003
theorem shape3_15:validFrom 11175 0 _HQT=true:=by decide+kernel
def _HQU:List Piece:=DZ.decode 58 42 0xa484aa4041ea4235cef7a4432ba65ea3aac58c7a311dd778109566992f64deb6fa3d3fd6751f965c1965b0003
theorem shape3_16:validFrom 11174 0 _HQU=true:=by decide+kernel
def _HQV:List Piece:=DZ.decode 58 42 0xa484aa4041ea5321d2185042eba55ea3aac58c7a3747ce628e07a68f6f64deb6fa3d4312c1d2870c596490003
theorem shape3_17:validFrom 11173 0 _HQV=true:=by decide+kernel
def _HQW:List Piece:=DZ.decode 58 42 0xa484aa4041ea693d3fa15dd72ba45ea3aac58c7a3d5a1c625a16d6892f64deb6fa3d464f0e8577bc996360003
theorem shape3_18:validFrom 11172 0 _HQW=true:=by decide+kernel
def _HQX:List Piece:=DZ.decode 58 42 0xa484aa4041ea7a2942c209d6eba35ea3aac58c7a436c6a622626067f6f64deb6fa3d498b5b38686cd96230003
theorem shape3_19:validFrom 11171 0 _HQX=true:=by decide+kernel
def _HQZ:List Piece:=DZ.decode 58 42 0xa484aa4041ea8b1545e2b5d6aba25ea3aac58c7a497eb861f2353675af64deb6fa3d4cc7a7eb591d196100003
theorem shape3_20:validFrom 11170 0 _HQZ=true:=by decide+kernel
def _HRA:List Piece:=DZ.decode 58 42 0xa484aa4041eaf5fc3348a74feba15ea3aac58c7a4f795d770ce156a8ef64deb6fa3d5003f49e49cd595fc0003
theorem shape3_21:validFrom 11169 0 _HRA=true:=by decide+kernel
def _HRB:List Piece:=DZ.decode 58 42 0xa484aa4041eb473b52f5cf3eaba05ea3aac58c7a558bab76d8f086caaf64deb6fa3d534041513a7d995e90003
theorem shape3_22:validFrom 11168 0 _HRB=true:=by decide+kernel
def _HRC:List Piece:=DZ.decode 58 42 0xa484aa4041eb582756167b3e6b9f5ea3aac58c7a5b86508bf39ca6c0ef64deb6fa3d567c8e042b2dd95d50003
theorem shape3_23:validFrom 11167 0 _HRC=true:=by decide+kernel
def _HRD:List Piece:=DZ.decode 58 42 0xa484aa4041eb69135937273e2b9e5ea3aac58c7a61989e8bbfabd6b72f64deb6fa3d59b8dab71bde195c20003
theorem shape3_24:validFrom 11166 0 _HRD=true:=by decide+kernel
def _HRE:List Piece:=DZ.decode 58 42 0xa484aa4041eb79ff5c57d33deb9d5ea3aac58c7a679343a0da57f6ad6f64deb6fa3d5cf5276a0c8e595ae0003
theorem shape3_25:validFrom 11165 0 _HRE=true:=by decide+kernel
def _HRF:List Piece:=DZ.decode 58 42 0xa484aa4041eb8aeb5f787f3dab9c5ea3aac58c7a6d8de8b5f50416a3af64deb6fa3d6031741cfd3e9959a0003
theorem shape3_26:validFrom 11164 0 _HRF=true:=by decide+kernel
def _HRG:List Piece:=DZ.decode 58 42 0xa484aa4041eb9bd762992b3d6b9b5ea3aac58c7a73888dcb0fb03699ef64deb6fa3d636dc0cfedeed95860003
theorem shape3_27:validFrom 11163 0 _HRG=true:=by decide+kernel
def _HRH:List Piece:=DZ.decode 58 42 0xa484aa4041ebacec86e4674d6b9a5ea3aac58c7a798332e02a5c56906f64deb6fa3d66aa0d82de9f195720003
theorem shape3_28:validFrom 11162 0 _HRH=true:=by decide+kernel
def _HRI:List Piece:=DZ.decode 58 42 0xa484aa4041ebbdd88a05134d2b995ea3aac58c7a7f662f0a93a56686af64deb6fa3d69e65a35cf4f5955d0003
theorem shape3_29:validFrom 11161 0 _HRI=true:=by decide+kernel
def _HRK:List Piece:=DZ.decode 58 42 0xa484aa4041ebcec48d25bf4ceb985ea3aac58c7a8560d41fae51867cef64deb6fa3d6d22a6e8bfff995490003
theorem shape3_30:validFrom 11160 0 _HRK=true:=by decide+kernel
def _HRL:List Piece:=DZ.decode 58 42 0xa484aa4041ebdfb090466b4cab975ea3aac58c7a8b43d04a179a96732f64deb6fa3d705ef39bb0afd95340003
theorem shape3_31:validFrom 11159 0 _HRL=true:=by decide+kernel
def _HRM:List Piece:=DZ.decode 58 42 0xa484aa4041ebf09c9367174c6b965ea3aac58c7a9126cc7480e3a6696f64deb6fa3d739b404ea1601951f0003
theorem shape3_32:validFrom 11158 0 _HRM=true:=by decide+kernel
def _HRN:List Piece:=DZ.decode 58 42 0xa484aa4041ec01889687c34c2b955ea3aac58c7a9709c89eea2cb65faf64deb6fa3d76d78d0192105950a0003
theorem shape3_33:validFrom 11157 0 _HRN=true:=by decide+kernel
def _HRO:List Piece:=DZ.decode 58 42 0xa484aa4041ec127499a86f4beb945ea3aac58c7a9cecc4c95375c655ef64deb6fa3d7a13d9b482c0994f50003
theorem shape3_34:validFrom 11156 0 _HRO=true:=by decide+kernel
def _HRP:List Piece:=DZ.decode 58 42 0xa484aa4041ec23609cc91b4bab935ea3aac58c7aa2cfc0f3bcbed64c2f64deb6fa3d7d5026677370d94e00003
theorem shape3_35:validFrom 11155 0 _HRP=true:=by decide+kernel
def _HRQ:List Piece:=DZ.decode 58 42 0xa484aa4041ec3475c114575bab925ea3aac58c7aa89b143374a4d642af64deb6fa3d808c731a6421194ca0003
theorem shape3_36:validFrom 11154 0 _HRQ=true:=by decide+kernel
def _HRR:List Piece:=DZ.decode 58 42 0xa484aa4041ec4561c435035b6b915ea3aac58c7aae6667732c8ad638ef64deb6fa3d83c8bfcd54d1594b40003
theorem shape3_37:validFrom 11153 0 _HRR=true:=by decide+kernel
def _HRS:List Piece:=DZ.decode 58 42 0xa484aa4041ec564dc755af5b2b905ea3aac58c7ab431bab2e470d62f2f64deb6fa3d87050c8045819949e0003
theorem shape3_38:validFrom 11152 0 _HRS=true:=by decide+kernel
def _HRT:List Piece:=DZ.decode 58 42 0xa484aa4041ec6739ca765b5aeb8f5ea3aac58c7ab9fd0df29c56d6256f64deb6fa3d8a4159333631d94880003
theorem shape3_39:validFrom 11151 0 _HRT=true:=by decide+kernel
def _HRV:List Piece:=DZ.decode 58 42 0xa484aa4041ec7825cd97075aab8e5ea3aac58c7abfc86132543cd61baf64deb6fa3d8d7da5e626e2194720003
theorem shape3_40:validFrom 11150 0 _HRV=true:=by decide+kernel
def _HRW:List Piece:=DZ.decode 58 42 0xa484aa4041ec8911d0b7b35a6b8d5ea3aac58c7ac57c0b875abfc611ef64deb6fa3d90b9f29917925945b0003
theorem shape3_41:validFrom 11149 0 _HRW=true:=by decide+kernel
def _HRX:List Piece:=DZ.decode 58 42 0xa484aa4041ec99fdd3d85f5a2b8c5ea3aac58c7acb2fb5dc6142b6082f64deb6fa3d93f63f4c0842994440003
theorem shape3_42:validFrom 11148 0 _HRX=true:=by decide+kernel
def _HRY:List Piece:=DZ.decode 58 42 0xa484aa4041ecab12f8239b6a2b8b5ea3aac58c7ad0e3603167c5a5feaf64deb6fa3d97328bfef8f2d942d0003
theorem shape3_43:validFrom 11147 0 _HRY=true:=by decide+kernel
def _HRZ:List Piece:=DZ.decode 58 42 0xa484aa4041ecbbfefb444769eb8a5ea3aac58c7ad6970a866e4895f4ef64deb6fa3d9a6ed8b1e9a3194160003
theorem shape3_44:validFrom 11146 0 _HRZ=true:=by decide+kernel
def _HSA:List Piece:=DZ.decode 58 42 0xa484aa4041eccceafe64f369ab895ea3aac58c7adc4ab4db74cb85eb2f64deb6fa3d9dab2564da53593ff0003
theorem shape3_45:validFrom 11145 0 _HSA=true:=by decide+kernel
def _HSB:List Piece:=DZ.decode 58 42 0xa484aa4041ecddd701859f696b885ea3aac58c7ae1e6b645c9eb65e16f64deb6fa3da0e77217cb03993e70003
theorem shape3_46:validFrom 11144 0 _HSB=true:=by decide+kernel
def _HSC:List Piece:=DZ.decode 58 42 0xa484aa4041eceec304a64b692b875ea3aac58c7ae782b7b01f0b45d7af64deb6fa3da423becabbb3d93cf0003
theorem shape3_47:validFrom 11143 0 _HSC=true:=by decide+kernel
def _HSD:List Piece:=DZ.decode 58 42 0xa484aa4041ecffaf07c6f768eb865ea3aac58c7aed1eb91a742b25cdef64deb6fa3da7600b7dac64193b70003
theorem shape3_48:validFrom 11142 0 _HSD=true:=by decide+kernel
def _HSE:List Piece:=DZ.decode 58 42 0xa484aa4041ed109b0ae7a368ab855ea3aac58c7af2a3119a17e7f5c42f64deb6fa3daa9c58309d145939e0003
theorem shape3_49:validFrom 11141 0 _HSE=true:=by decide+kernel
def _HSG:List Piece:=DZ.decode 58 42 0xa484aa4041ed21b02f32df78ab845ea3aac58c7af8276a19bba4c5baaf64deb6fa3dadd8a4e38dc4993850003
theorem shape3_50:validFrom 11140 0 _HSG=true:=by decide+kernel
def _HSH:List Piece:=DZ.decode 58 42 0xa484aa4041ed329c32538b786b835ea3aac58c7afdabc2995f6195b0ef64deb6fa3db114f1967e74d936c0003
theorem shape3_51:validFrom 11139 0 _HSH=true:=by decide+kernel
def _HSI:List Piece:=DZ.decode 58 42 0xa484aa4041ed4388357437782b825ea3aac58c7b03301b19031e65a72f64deb6fa3dc66db8c6187ded3530003
theorem shape3_52:validFrom 11138 0 _HSI=true:=by decide+kernel
def _HSJ:List Piece:=DZ.decode 58 42 0xa484aa4041ed54743894e377eb815ea3aac58c7b089ccaadf578259d6f64deb6fa3dc9aa0579092e2d3390003
theorem shape3_53:validFrom 11137 0 _HSJ=true:=by decide+kernel
def _HSK:List Piece:=DZ.decode 58 42 0x29212a90107b389be94d3aeefae02f64deb6fa3dcdec4a38a2e68931f0002
theorem shape3_54:validFrom 11136 0 _HSK=true:=by decide+kernel
def _HSL:List Piece:=DZ.decode 58 42 0x29212a90107b3d5c95dfba23badfef64deb6fa3dd12896eb9396c93050002
theorem shape3_55:validFrom 11135 0 _HSL=true:=by decide+kernel
def _HSM:List Piece:=DZ.decode 58 42 0x29212a90107b4212fa2795546adfaf64deb6fa3dd464e39e8447092ea0002
theorem shape3_56:validFrom 11134 0 _HSM=true:=by decide+kernel
def _HSN:List Piece:=DZ.decode 58 42 0x29212a90107b46c95e6f70851adf6f64deb6fa3dd7a1305174f7492cf0002
theorem shape3_57:validFrom 11133 0 _HSN=true:=by decide+kernel
def _HSO:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7c29212a901043b4b757a6ca7b1bab3af64deb6fa30ddadd7d0465a7892b30003
theorem shape3_58:validFrom 11132 0 _HSO=true:=by decide+kernel
def _HSP:List Piece:=DZ.decode 62 42 0x3782dace9d900000adeca484aa40410ed87edb5e4e4f469c45ea3aac58c43b61313a9def8cf4a82f64deb6fa30de13ee853e3f2ed2970004
theorem shape3_59:validFrom 11131 0 _HSP=true:=by decide+kernel
def _HSR:List Piece:=DZ.decode 62 42 0x3782dace9d900000ade8a484aa40410ed99d08004f155a8ad5ea3aac58c43b6616e203f71e849fef64deb6fa30de47b3506d4a32d27b0004
theorem shape3_60:validFrom 11130 0 _HSR=true:=by decide+kernel
def _HSS:List Piece:=DZ.decode 62 42 0x3782dace9d900000ade4a484aa40410edac058c7a1dd7678748e952589303b6ae4e07f4d4d04982f64deb6fa30de7b781b9c5536d25e0004
theorem shape3_61:validFrom 11129 0 _HSS=true:=by decide+kernel
def _HST:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7829212a901043b6f8ea63bd29649952f64deb6fa30deebda4ecc609252410003
theorem shape3_62:validFrom 11128 0 _HST=true:=by decide+kernel
def _HSU:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7729212a901043b743079ee65bed944ef64deb6fa30df1f9f19fb6b9652240003
theorem shape3_63:validFrom 11127 0 _HSU=true:=by decide+kernel
def _HSV:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7629212a901043b78bdbd0bb0df48f0ef64deb6fa30df5363e52a769a52050003
theorem shape3_64:validFrom 11126 0 _HSV=true:=by decide+kernel
def _HSW:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7529212a901043b891c92522bd9a899af64deb6fa30dfb1776c1d6a17d1e70003
theorem shape3_65:validFrom 11125 0 _HSW=true:=by decide+kernel
def _HSX:List Piece:=DZ.decode 62 42 0x3782dace9d900000add0a484aa40410ee7b94b4448bfce0fb5ea3aac58c43b9bdd98d2aa2a447a2f64deb6fa30e02c39f8142d2a11c70004
theorem shape3_66:validFrom 11124 0 _HSX=true:=by decide+kernel
def _HSY:List Piece:=DZ.decode 62 42 0x3782dace9d900000adcca484aa40410ee8c80b76537fc9f825ea3aac58c43ba0d3fbd22594b4706f64deb6fa30e0ec5d9e7ae29811a80004
theorem shape3_67:validFrom 11123 0 _HSY=true:=by decide+kernel
def _HSZ:List Piece:=DZ.decode 62 42 0x3782dace9d900000adc8a484aa40410ee9d6cba85e3fc5dfb5ea3aac58c43ba59b0cfc3e390466af64deb6fa30e1202269a9ed9c11870004
theorem shape3_68:validFrom 11122 0 _HSZ=true:=by decide+kernel
def _HTA:List Piece:=DZ.decode 62 42 0x3782dace9d900000adc4a484aa40410eeae81ded1200c5c665ea3aac58c43baa621e2656dd545d2f64deb6fa30e153e734d8f8a011660004
theorem shape3_69:validFrom 11121 0 _HTA=true:=by decide+kernel
def _HTC:List Piece:=DZ.decode 62 42 0x3782dace9d900000adc0a484aa40410eebf6de1f1cc0c1ac45ea3aac58c43baf118665be1e94536f64deb6fa30e187ac000803a411440004
theorem shape3_70:validFrom 11120 0 _HTC=true:=by decide+kernel
def _HTD:List Piece:=DZ.decode 62 42 0x3782dace9d900000adbca484aa40410eed059e512780bd9135ea3aac58c43bb3a945ba73fcc449af64deb6fa30e1bb70cb370ea811210004
theorem shape3_71:validFrom 11119 0 _HTD=true:=by decide+kernel
def _HTE:List Piece:=DZ.decode 62 42 0x3782dace9d900000adb8a484aa40410eee16f095db41bd7545ea3aac58c43bb833c48e091b44402f64deb6fa30e1ef35966619ac10fe0004
theorem shape3_72:validFrom 11118 0 _HTE=true:=by decide+kernel
def _HTF:List Piece:=DZ.decode 62 41 0x3782dace9d900000adb549095480821dde6f5e950a11aab117a8eab16310e8b69e86b518e2d0e00003
theorem shape3_73:validFrom 11117 0 _HTF=true:=by decide+kernel
def _HTG:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b6000000000003c328f8b1306a67546d49095480821dd90f3498a29bfa75b7a8eab16310e923c37fa2f0348f440004
theorem shape3_74:validFrom 11116 0 _HTG=true:=by decide+kernel
def _HTH:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b5800000000003c33916cf84dc41534949095480821ddb31d9220a1dfa38b7a8eab16310e94312dd4ec9da0f1e0004
theorem shape3_75:validFrom 11115 0 _HTH=true:=by decide+kernel
def _HTI:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b5000000000003c34934896aa8445218bd33aa8b0a1e0e52fda4271c6215ebd33aa8b090f023168447e6099079bd47558b18877ac984764a1df080cdea3aac58c43bd00f9449858843ff949095480821dddbf43e73decf9f9d7a8eab16310e9687f9c27e7858ef00008
theorem shape3_76:validFrom 11114 0 _HTI=true:=by decide+kernel
def _HTJ:List Piece:=DZ.decode 62 41 0x1bc16d674ec8000056d200000000000f0d65477b873b854362f4ceaa2c28783cce48cff9c2683daf4ceaa2c243c087909f68982f4112f51d562c621de8d3a87a57c9c1f577a8eab16310e987d4a03f8f0b4f770006
theorem shape3_77:validFrom 11113 0 _HTJ=true:=by decide+kernel
def _HTK:List Piece:=DZ.decode 62 41 0x1bc16d674ec8000056d000000000000f0da5bb3fa93e693e32f4ceaa2c2878405c61db85baa8232f4ceaa2c243c0bcb4350410924036f51d562c621dee93f019f5b529e717a8eab16310e9e939baf5c18d4eec0006
theorem shape3_78:validFrom 11112 0 _HTK=true:=by decide+kernel
def _HTL:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6700000000000786f316b90854f49c617a675516143c22010a76f492640397a675516121e059ac615015299fa97a8eab16310ea15eb3c14d768cec20005
theorem shape3_79:validFrom 11111 0 _HTL=true:=by decide+kernel
def _HTN:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6600000000000787134f095ebfea99917a675516143c23d9c7663d9de3f517a675516121e0549fdd89ca491f337a8eab16310ea369a5381d1940e480005
theorem shape3_80:validFrom 11110 0 _HTN=true:=by decide+kernel
def _HTO:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6500000000000787338690bf474c96a17a675516143c25b27e1d8928c3e5d7a675516121e04ea6a8697e661eb77a8eab16310ea8a68ee969fc18dc90005
theorem shape3_81:validFrom 11109 0 _HTO=true:=by decide+kernel
def _HTP:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b640000000000078753bd4f5b1bce93997a675516143c279701d900ee13d617a675516121e064664f855a9a1e357a8eab16310eac01176de3e930d470005
theorem shape3_82:validFrom 11108 0 _HTP=true:=by decide+kernel
def _HTQ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b6300000000000f0ee7e68a33486d20e5e99d545850f0a605a3ea40518f16bd33aa8b090edd2fd5c72aa934ed70004
theorem shape3_83:validFrom 11107 0 _HTQ=true:=by decide+kernel
def _HTR:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b6200000000000f0f2850e3f5c3011a55e99d545850f0adaf279388e18ed2bd33aa8b090ede85b9e9861850e910004
theorem shape3_84:validFrom 11106 0 _HTR=true:=by decide+kernel
def _HTS:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad840000000000787b45cd5fed3c089cde99d545850ef63aefd62fa274e8b0003
theorem shape3_85:validFrom 11105 0 _HTS=true:=by decide+kernel
def _HTT:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad800000000000787d490712579e2864de99d545850ef728d07112672ce420003
theorem shape3_86:validFrom 11104 0 _HTT=true:=by decide+kernel
def _HTU:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad7c0000000000787f4c3436ed54682b5e99d545850ef81a55009ed768df60003
theorem shape3_87:validFrom 11103 0 _HTU=true:=by decide+kernel
def _HTV:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad780000000000788148e285a096e7efde99d545850ef90dcf116b884cda80003
theorem shape3_88:validFrom 11102 0 _HTV=true:=by decide+kernel
def _HTW:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad74000000000078832538173e5d87b25e99d545850efa05b6ee256f28d570003
theorem shape3_89:validFrom 11101 0 _HTW=true:=by decide+kernel
def _HTY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f10a03047ee1c5cee60002
theorem shape3_90:validFrom 11100 0 _HTY=true:=by decide+kernel
def _HTZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f10dbb820295798e640002
theorem shape3_91:validFrom 11099 0 _HTZ=true:=by decide+kernel
def _HUA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f11173e8b3729fcddf0002
theorem shape3_92:validFrom 11098 0 _HUA=true:=by decide+kernel
def _HUB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f1152c38979e63cd560002
theorem shape3_93:validFrom 11097 0 _HUB=true:=by decide+kernel
def _HUC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b00f118e471a8f3c90cca0002
theorem shape3_94:validFrom 11096 0 _HUC=true:=by decide+kernel
def _HUD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ae0f11c9c93ed97848c3a0002
theorem shape3_95:validFrom 11095 0 _HUD=true:=by decide+kernel
def _HUE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ac0f120549f5f65114ba70002
theorem shape3_96:validFrom 11094 0 _HUE=true:=by decide+kernel
def _HUF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056aa0f1240c940480f54b0f0002
theorem shape3_97:validFrom 11093 0 _HUF=true:=by decide+kernel
def _HUG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a80f127c471d6c6a94a740002
theorem shape3_98:validFrom 11092 0 _HUG=true:=by decide+kernel
def _HUH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a60f12b7c38d9485dc9d50002
theorem shape3_99:validFrom 11091 0 _HUH=true:=by decide+kernel
def _HQA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a40f12f33e90f185f89330002
theorem shape3_100:validFrom 11090 0 _HQA=true:=by decide+kernel
def _HQB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a20f132eb82721254c88d0002
theorem shape3_101:validFrom 11089 0 _HQB=true:=by decide+kernel
def _HQC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a00f136a305085a4c07e40002
theorem shape3_102:validFrom 11088 0 _HQC=true:=by decide+kernel
def _HQD:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569e0f13a5a70cbcc5d07380002
theorem shape3_103:validFrom 11087 0 _HQD=true:=by decide+kernel
def _HQE:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569c0f13e11c5c28c7e86890002
theorem shape3_104:validFrom 11086 0 _HQE=true:=by decide+kernel
def _HQF:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569a0f141c903e676a7c5d50002
theorem shape3_105:validFrom 11085 0 _HQF=true:=by decide+kernel
def _HQG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056980f145802b3daed9051d0002
theorem shape3_106:validFrom 11084 0 _HQG=true:=by decide+kernel
def _HQH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056960f149373bc21144c4610002
theorem shape3_107:validFrom 11083 0 _HQH=true:=by decide+kernel
def _HQI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056940f14cee3579c16a83a10002
theorem shape3_108:validFrom 11082 0 _HQI=true:=by decide+kernel
def _HQJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056920f150a5185e9bfd42de0002
theorem shape3_109:validFrom 11081 0 _HQJ=true:=by decide+kernel
def _HQL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056900f1545be476c44e82170002
theorem shape3_110:validFrom 11080 0 _HQL=true:=by decide+kernel
def _HQM:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000568e0f1581299bc16ec814e0002
theorem shape3_111:validFrom 11079 0 _HQM=true:=by decide+kernel
def _HQN:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000568c0f15bc93834b74dc0820002
theorem shape3_112:validFrom 11078 0 _HQN=true:=by decide+kernel
def _HQO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bd5ccf9e25f7420f15f7fbfda822f80020002
theorem shape3_113:validFrom 11077 0 _HQO=true:=by decide+kernel
def _HQP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bd4df5dac1957d0f1633630b39aa0c0020002
theorem shape3_114:validFrom 11076 0 _HQP=true:=by decide+kernel
def row3 (v:ℕ):List Piece:=match v with
 | 0=>d3_0
 | 1=>d3_1
 | 2=>d3_2
 | 3=>d3_3
 | 4=>d3_4
 | 5=>d3_5
 | 6=>d3_6
 | 7=>d3_7
 | 8=>d3_8
 | 9=>d3_9
 | 10=>_HPZ
 | 11=>_HQK
 | 12=>_HQQ
 | 13=>_HQR
 | 14=>_HQS
 | 15=>_HQT
 | 16=>_HQU
 | 17=>_HQV
 | 18=>_HQW
 | 19=>_HQX
 | 20=>_HQZ
 | 21=>_HRA
 | 22=>_HRB
 | 23=>_HRC
 | 24=>_HRD
 | 25=>_HRE
 | 26=>_HRF
 | 27=>_HRG
 | 28=>_HRH
 | 29=>_HRI
 | 30=>_HRK
 | 31=>_HRL
 | 32=>_HRM
 | 33=>_HRN
 | 34=>_HRO
 | 35=>_HRP
 | 36=>_HRQ
 | 37=>_HRR
 | 38=>_HRS
 | 39=>_HRT
 | 40=>_HRV
 | 41=>_HRW
 | 42=>_HRX
 | 43=>_HRY
 | 44=>_HRZ
 | 45=>_HSA
 | 46=>_HSB
 | 47=>_HSC
 | 48=>_HSD
 | 49=>_HSE
 | 50=>_HSG
 | 51=>_HSH
 | 52=>_HSI
 | 53=>_HSJ
 | 54=>_HSK
 | 55=>_HSL
 | 56=>_HSM
 | 57=>_HSN
 | 58=>_HSO
 | 59=>_HSP
 | 60=>_HSR
 | 61=>_HSS
 | 62=>_HST
 | 63=>_HSU
 | 64=>_HSV
 | 65=>_HSW
 | 66=>_HSX
 | 67=>_HSY
 | 68=>_HSZ
 | 69=>_HTA
 | 70=>_HTC
 | 71=>_HTD
 | 72=>_HTE
 | 73=>_HTF
 | 74=>_HTG
 | 75=>_HTH
 | 76=>_HTI
 | 77=>_HTJ
 | 78=>_HTK
 | 79=>_HTL
 | 80=>_HTN
 | 81=>_HTO
 | 82=>_HTP
 | 83=>_HTQ
 | 84=>_HTR
 | 85=>_HTS
 | 86=>_HTT
 | 87=>_HTU
 | 88=>_HTV
 | 89=>_HTW
 | 90=>_HTY
 | 91=>_HTZ
 | 92=>_HUA
 | 93=>_HUB
 | 94=>_HUC
 | 95=>_HUD
 | 96=>_HUE
 | 97=>_HUF
 | 98=>_HUG
 | 99=>_HUH
 | 100=>_HQA
 | 101=>_HQB
 | 102=>_HQC
 | 103=>_HQD
 | 104=>_HQE
 | 105=>_HQF
 | 106=>_HQG
 | 107=>_HQH
 | 108=>_HQI
 | 109=>_HQJ
 | 110=>_HQL
 | 111=>_HQM
 | 112=>_HQN
 | 113=>_HQO
 | 114=>_HQP
 | _=>[]
theorem checked3 (v:ℕ) (hy:3+v≤117):validFrom (11193-3-v) 0 (row3 v)=true:=by
 have hv:v≤114:=by omega
 interval_cases v
 · exact shape3_0
 · exact shape3_1
 · exact shape3_2
 · exact shape3_3
 · exact shape3_4
 · exact shape3_5
 · exact shape3_6
 · exact shape3_7
 · exact shape3_8
 · exact shape3_9
 · exact shape3_10
 · exact shape3_11
 · exact shape3_12
 · exact shape3_13
 · exact shape3_14
 · exact shape3_15
 · exact shape3_16
 · exact shape3_17
 · exact shape3_18
 · exact shape3_19
 · exact shape3_20
 · exact shape3_21
 · exact shape3_22
 · exact shape3_23
 · exact shape3_24
 · exact shape3_25
 · exact shape3_26
 · exact shape3_27
 · exact shape3_28
 · exact shape3_29
 · exact shape3_30
 · exact shape3_31
 · exact shape3_32
 · exact shape3_33
 · exact shape3_34
 · exact shape3_35
 · exact shape3_36
 · exact shape3_37
 · exact shape3_38
 · exact shape3_39
 · exact shape3_40
 · exact shape3_41
 · exact shape3_42
 · exact shape3_43
 · exact shape3_44
 · exact shape3_45
 · exact shape3_46
 · exact shape3_47
 · exact shape3_48
 · exact shape3_49
 · exact shape3_50
 · exact shape3_51
 · exact shape3_52
 · exact shape3_53
 · exact shape3_54
 · exact shape3_55
 · exact shape3_56
 · exact shape3_57
 · exact shape3_58
 · exact shape3_59
 · exact shape3_60
 · exact shape3_61
 · exact shape3_62
 · exact shape3_63
 · exact shape3_64
 · exact shape3_65
 · exact shape3_66
 · exact shape3_67
 · exact shape3_68
 · exact shape3_69
 · exact shape3_70
 · exact shape3_71
 · exact shape3_72
 · exact shape3_73
 · exact shape3_74
 · exact shape3_75
 · exact shape3_76
 · exact shape3_77
 · exact shape3_78
 · exact shape3_79
 · exact shape3_80
 · exact shape3_81
 · exact shape3_82
 · exact shape3_83
 · exact shape3_84
 · exact shape3_85
 · exact shape3_86
 · exact shape3_87
 · exact shape3_88
 · exact shape3_89
 · exact shape3_90
 · exact shape3_91
 · exact shape3_92
 · exact shape3_93
 · exact shape3_94
 · exact shape3_95
 · exact shape3_96
 · exact shape3_97
 · exact shape3_98
 · exact shape3_99
 · exact shape3_100
 · exact shape3_101
 · exact shape3_102
 · exact shape3_103
 · exact shape3_104
 · exact shape3_105
 · exact shape3_106
 · exact shape3_107
 · exact shape3_108
 · exact shape3_109
 · exact shape3_110
 · exact shape3_111
 · exact shape3_112
 · exact shape3_113
 · exact shape3_114
def d4_0:List Piece:=DZ.decode 58 42 0xa484aa4041e98cfa5fa4e79cabb55ea3aac58c79f0c96f170b6f7700af64deb6fa3d1d51917d66e70172b0003
theorem shape4_0:validFrom 11189 0 d4_0=true:=by decide+kernel
def d4_1:List Piece:=DZ.decode 58 42 0xa484aa4041e99de662c5939c6bb45ea3aac58c79f6f3660188e1b6f6ef64deb6fa3d208dde305797417190003
theorem shape4_1:validFrom 11188 0 d4_1=true:=by decide+kernel
def d4_2:List Piece:=DZ.decode 58 42 0xa484aa4041e9aed265e63f9c2bb35ea3aac58c79fd3505d6b7b706ed2f64deb6fa3d23ca2ae34847817080003
theorem shape4_2:validFrom 11187 0 d4_2=true:=by decide+kernel
def d4_3:List Piece:=DZ.decode 58 42 0xa484aa4041e9bfbe6906eb9bebb25ea3aac58c7a0376a5abe68c56e36f64deb6fa3d2706779638f7c16f70003
theorem shape4_3:validFrom 11186 0 d4_3=true:=by decide+kernel
def d4_4:List Piece:=DZ.decode 58 42 0xa484aa4041e9d0aa6c27979babb15ea3aac58c7a09a09c9663fe96d9af64deb6fa3d2a42c44929a8016e50003
theorem shape4_4:validFrom 11185 0 d4_4=true:=by decide+kernel
def d4_5:List Piece:=DZ.decode 58 42 0xa484aa4041e9e1966f48439b6bb05ea3aac58c7a0fe23c6b92d3e6cfef64deb6fa3d2d7f10fc1a58416d40003
theorem shape4_5:validFrom 11184 0 d4_5=true:=by decide+kernel
def d4_6:List Piece:=DZ.decode 58 42 0xa484aa4041e9f2827268ef9b2baf5ea3aac58c7a160c3356104626c62f64deb6fa3d30bb5daf0b08816c20003
theorem shape4_6:validFrom 11183 0 d4_6=true:=by decide+kernel
def d4_7:List Piece:=DZ.decode 58 42 0xa484aa4041ea036e75899b9aebae5ea3aac58c7a1c362a408db866bc6f64deb6fa3d33f7aa61fbb8c16b00003
theorem shape4_7:validFrom 11182 0 d4_7=true:=by decide+kernel
def d4_8:List Piece:=DZ.decode 58 42 0xa484aa4041ea148399d4d7aaebad5ea3aac58c7a2260212b0b2aa6b2ef64deb6fa3d3733f714ec690169e0003
theorem shape4_8:validFrom 11181 0 d4_8=true:=by decide+kernel
def d4_9:List Piece:=DZ.decode 58 42 0xa484aa4041ea256f9cf583aaabac5ea3aac58c7a288a1815889ce6a92f64deb6fa3d3a7043c7dd194168c0003
theorem shape4_9:validFrom 11180 0 d4_9=true:=by decide+kernel
def _HUK:List Piece:=DZ.decode 58 42 0xa484aa4041ea365ba0162faa6bab5ea3aac58c7a2eb40f00060f269f6f64deb6fa3d3dac907acdc98167a0003
theorem shape4_10:validFrom 11179 0 _HUK=true:=by decide+kernel
def _HUV:List Piece:=DZ.decode 58 42 0xa484aa4041ea4799e58bfbcaabaa5ea3aac58c7a34c52ac7574c76962f64deb6fa3d40e8dd2dbe79c16680003
theorem shape4_11:validFrom 11178 0 _HUV=true:=by decide+kernel
def _HVA:List Piece:=DZ.decode 58 42 0xa484aa4041ea59a5d0d6983c2ba95ea3aac58c7a3a7fc26d9b59968e2f64deb6fa3d442529e0af2a016550003
theorem shape4_12:validFrom 11177 0 _HVA=true:=by decide+kernel
def _HVB:List Piece:=DZ.decode 58 42 0xa484aa4041ea6b889af6a49d6ba85ea3aac58c7a405202fe90c9c685ef64deb6fa3d476176939fda416430003
theorem shape4_13:validFrom 11176 0 _HVB=true:=by decide+kernel
def _HVC:List Piece:=DZ.decode 58 42 0xa484aa4041ea7d948641410eeba75ea3aac58c7a460c9aa4d4d6e67def64deb6fa3d4a9dc346908a816300003
theorem shape4_14:validFrom 11175 0 _HVC=true:=by decide+kernel
def _HVD:List Piece:=DZ.decode 58 42 0xa484aa4041ea8b20d0e41bb96ba65ea3aac58c7a4d568fbf1684466eef64deb6fa3d4dda0ff9813ac161e0003
theorem shape4_15:validFrom 11174 0 _HVD=true:=by decide+kernel
def _HVE:List Piece:=DZ.decode 58 42 0xa484aa4041ea9c0cd404c7b92ba55ea3aac58c7a5368ddbee29376652f64deb6fa3d51165cac71eb0160b0003
theorem shape4_16:validFrom 11173 0 _HVE=true:=by decide+kernel
def _HVF:List Piece:=DZ.decode 58 42 0xa484aa4041eaacf8d72573b8eba45ea3aac58c7a597b2bbeaea2a65b6f64deb6fa3d5452a95f629b415f80003
theorem shape4_17:validFrom 11172 0 _HVF=true:=by decide+kernel
def _HVG:List Piece:=DZ.decode 58 42 0xa484aa4041eac31444ae814d2ba35ea3aac58c7a5f8d79be7ab1d6552f64deb6fa3d578ef612534b815e50003
theorem shape4_18:validFrom 11171 0 _HVG=true:=by decide+kernel
def _HVH:List Piece:=DZ.decode 58 42 0xa484aa4041ead40047cf2d4ceba25ea3aac58c7a659fc7be46c1064b6f64deb6fa3d5acb42c543fbc15d20003
theorem shape4_19:validFrom 11170 0 _HVH=true:=by decide+kernel
def _HVJ:List Piece:=DZ.decode 58 42 0xa484aa4041eae4ec4aefd94caba15ea3aac58c7a6b9a6cd3616d2641af64deb6fa3d5e078f7834ac015be0003
theorem shape4_20:validFrom 11169 0 _HVJ=true:=by decide+kernel
def _HVK:List Piece:=DZ.decode 58 42 0xa484aa4041eb4faa172b3ab5aba05ea3aac58c7a71acbad32d7c5674af64deb6fa3d6143dc2b255c415ab0003
theorem shape4_21:validFrom 11168 0 _HVK=true:=by decide+kernel
def _HVL:List Piece:=DZ.decode 58 42 0xa484aa4041eba1125802f2b4ab9f5ea3aac58c7a77a75fe848287696af64deb6fa3d648028de160c815970003
theorem shape4_22:validFrom 11167 0 _HVL=true:=by decide+kernel
def _HVM:List Piece:=DZ.decode 58 42 0xa484aa4041ebb1fe5b239eb46b9e5ea3aac58c7a7db9ade81437a68cef64deb6fa3d67bc759106bcc15840003
theorem shape4_23:validFrom 11166 0 _HVM=true:=by decide+kernel
def _HVN:List Piece:=DZ.decode 58 42 0xa484aa4041ebc2ea5e444ab42b9d5ea3aac58c7a83b452fd2ee3c6832f64deb6fa3d6af8c243f76d015700003
theorem shape4_24:validFrom 11165 0 _HVN=true:=by decide+kernel
def _HVO:List Piece:=DZ.decode 58 42 0xa484aa4041ebd3d66164f6b3eb9c5ea3aac58c7a89aef812498fe6796f64deb6fa3d6e350ef6e81d4155c0003
theorem shape4_25:validFrom 11164 0 _HVO=true:=by decide+kernel
def _HVP:List Piece:=DZ.decode 58 42 0xa484aa4041ebe4c26485a2b3ab9b5ea3aac58c7a8f91f43cb2d8f66faf64deb6fa3d71715ba9d8cd815470003
theorem shape4_26:validFrom 11163 0 _HVP=true:=by decide+kernel
def _HVQ:List Piece:=DZ.decode 58 42 0xa484aa4041ebf5ae67a64eb36b9a5ea3aac58c7a958c9951cd851665ef64deb6fa3d74ada85cc97dc15330003
theorem shape4_27:validFrom 11162 0 _HVQ=true:=by decide+kernel
def _HVR:List Piece:=DZ.decode 58 42 0xa484aa4041ec069a6ac6fab32b995ea3aac58c7a9b873e66e831365c2f64deb6fa3d77e9f50fba2e0151f0003
theorem shape4_28:validFrom 11161 0 _HVR=true:=by decide+kernel
def _HVS:List Piece:=DZ.decode 58 42 0xa484aa4041ec17af8f1236c32b985ea3aac58c7aa16a3a91517a4652af64deb6fa3d7b2641c2aade4150a0003
theorem shape4_29:validFrom 11160 0 _HVS=true:=by decide+kernel
def _HVU:List Piece:=DZ.decode 58 42 0xa484aa4041ec289b9232e2c2eb975ea3aac58c7aa74d36bbbac35648ef64deb6fa3d7e628e759b8e814f50003
theorem shape4_30:validFrom 11159 0 _HVU=true:=by decide+kernel
def _HVV:List Piece:=DZ.decode 58 42 0xa484aa4041ec398795538ec2ab965ea3aac58c7aad3032e6240c663f2f64deb6fa3d819edb288c3ec14e00003
theorem shape4_31:validFrom 11158 0 _HVV=true:=by decide+kernel
def _HVW:List Piece:=DZ.decode 58 42 0xa484aa4041ec4a7398743ac26b955ea3aac58c7ab3132f108d5576356f64deb6fa3d84db27db7cef014cb0003
theorem shape4_32:validFrom 11157 0 _HVW=true:=by decide+kernel
def _HVX:List Piece:=DZ.decode 58 42 0xa484aa4041ec5b5f9b94e6c22b945ea3aac58c7ab8f62b3af69e862baf64deb6fa3d8817748e6d9f414b60003
theorem shape4_33:validFrom 11156 0 _HVX=true:=by decide+kernel
def _HVY:List Piece:=DZ.decode 58 42 0xa484aa4041ec6c4b9eb592c1eb935ea3aac58c7abec17e7aae848621ef64deb6fa3d8b53c1415e4f814a00003
theorem shape4_34:validFrom 11155 0 _HVY=true:=by decide+kernel
def _HVZ:List Piece:=DZ.decode 58 42 0xa484aa4041ec7d37a1d63ec1ab925ea3aac58c7ac48cd1ba666a86182f64deb6fa3d8e900df44effc148a0003
theorem shape4_35:validFrom 11154 0 _HVZ=true:=by decide+kernel
def _HWA:List Piece:=DZ.decode 58 42 0xa484aa4041ec8e4cc6217ad1ab915ea3aac58c7aca6fcde4cfb3960eaf64deb6fa3d91cc5aa73fb0014750003
theorem shape4_36:validFrom 11153 0 _HWA=true:=by decide+kernel
def _HWB:List Piece:=DZ.decode 58 42 0xa484aa4041ec9f38c94226d16b905ea3aac58c7ad0237839d6368604ef64deb6fa3d9508a75a30604145e0003
theorem shape4_37:validFrom 11152 0 _HWB=true:=by decide+kernel
def _HWC:List Piece:=DZ.decode 58 42 0xa484aa4041ecb024cc62d2d12b8f5ea3aac58c7ad5eecb798e1c85fb2f64deb6fa3d9844f40d2110814480003
theorem shape4_38:validFrom 11151 0 _HWC=true:=by decide+kernel
def _HWD:List Piece:=DZ.decode 58 42 0xa484aa4041ecc110cf837ed0eb8e5ea3aac58c7adbba1eb9460285f16f64deb6fa3d9b8140c011c0c14320003
theorem shape4_39:validFrom 11150 0 _HWD=true:=by decide+kernel
def _HWF:List Piece:=DZ.decode 58 42 0xa484aa4041ecd1fcd2a42ad0ab8d5ea3aac58c7ae16dc90e4c8575e7af64deb6fa3d9ebd8d7302710141b0003
theorem shape4_40:validFrom 11149 0 _HWF=true:=by decide+kernel
def _HWG:List Piece:=DZ.decode 58 42 0xa484aa4041ece2e8d5c4d6d06b8c5ea3aac58c7ae7217363530865ddef64deb6fa3da1f9da25f321414040003
theorem shape4_41:validFrom 11148 0 _HWG=true:=by decide+kernel
def _HWH:List Piece:=DZ.decode 58 42 0xa484aa4041ecf3d4d8e582d02b8b5ea3aac58c7aecd51db8598b55d42f64deb6fa3da53626d8e3d1813ed0003
theorem shape4_42:validFrom 11147 0 _HWH=true:=by decide+kernel
def _HWI:List Piece:=DZ.decode 58 42 0xa484aa4041ed04e9fd30bee02b8a5ea3aac58c7af2711f22aeab35caaf64deb6fa3da872738bd481c13d50003
theorem shape4_43:validFrom 11146 0 _HWI=true:=by decide+kernel
def _HWJ:List Piece:=DZ.decode 58 42 0xa484aa4041ed15d600516adfeb895ea3aac58c7af824c977b52e25c0ef64deb6fa3dabaec03ec532013be0003
theorem shape4_44:validFrom 11145 0 _HWJ=true:=by decide+kernel
def _HWK:List Piece:=DZ.decode 58 42 0xa484aa4041ed26c2037216dfab885ea3aac58c7afdc0cae20a4e05b72f64deb6fa3daeeb0cf1b5e2413a60003
theorem shape4_45:validFrom 11144 0 _HWK=true:=by decide+kernel
def _HWL:List Piece:=DZ.decode 58 42 0xa484aa4041ed37ae0692c2df6b875ea3aac58c7b035ccc4c5f6de5ad6f64deb6fa3db22759a4a6928138e0003
theorem shape4_46:validFrom 11143 0 _HWL=true:=by decide+kernel
def _HWM:List Piece:=DZ.decode 58 42 0xa484aa4041ed489a09b36edf2b865ea3aac58c7b08e124cc032ab5a3af64deb6fa3db563a6579742c13750003
theorem shape4_47:validFrom 11142 0 _HWM=true:=by decide+kernel
def _HWN:List Piece:=DZ.decode 58 42 0xa484aa4041ed59860cd41adeeb855ea3aac58c7b0e7d2636584a9599ef64deb6fa3db89ff30a87f30135d0003
theorem shape4_48:validFrom 11141 0 _HWN=true:=by decide+kernel
def _HWO:List Piece:=DZ.decode 58 42 0xa484aa4041ed6a720ff4c6deab845ea3aac58c7b14017eb5fc0765902f64deb6fa3dbbdc3fbd78a3413440003
theorem shape4_49:validFrom 11140 0 _HWO=true:=by decide+kernel
def _HWQ:List Piece:=DZ.decode 58 42 0xa484aa4041ed7b87344002eeab835ea3aac58c7b196e2e4aee612586af64deb6fa3dbf188c7069538132a0003
theorem shape4_50:validFrom 11139 0 _HWQ=true:=by decide+kernel
def _HWR:List Piece:=DZ.decode 58 42 0xa484aa4041ed8c733760aeee6b825ea3aac58c7b1ef286ca921df57cef64deb6fa3dc254d9235a03c13110003
theorem shape4_51:validFrom 11138 0 _HWR=true:=by decide+kernel
def _HWS:List Piece:=DZ.decode 58 42 0xa484aa4041ed9d5f3a815aee2b815ea3aac58c7b245f365f8477b5732f64deb6fa3dd7ada052f40cd52f70003
theorem shape4_52:validFrom 11137 0 _HWS=true:=by decide+kernel
def _HWT:List Piece:=DZ.decode 58 42 0xa484aa4041edae4b3da206edeb805ea3aac58c7b29cbe5f476d175696f64deb6fa3ddae9ed05e4bd152dd0003
theorem shape4_53:validFrom 11136 0 _HWT=true:=by decide+kernel
def _HWU:List Piece:=DZ.decode 58 42 0x29212a90107b53b02418319faadfef64deb6fa3ddf2c31c57e75712c20002
theorem shape4_54:validFrom 11135 0 _HWU=true:=by decide+kernel
def _HWV:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7e29212a901043b586688600cd05aca2f64deb6fa30de2687e786f25b12a70003
theorem shape4_55:validFrom 11134 0 _HWV=true:=by decide+kernel
def _HWW:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7d29212a901043b5d1ceca7e8010a8c6f64deb6fa30de5a4cb2b5fd5f128c0003
theorem shape4_56:validFrom 11133 0 _HWW=true:=by decide+kernel
def _HWX:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7c29212a901043b61c908a51f2daa4aef64deb6fa30de8e117de5086312700003
theorem shape4_57:validFrom 11132 0 _HWX=true:=by decide+kernel
def _HWY:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7b29212a901043b667524a2565a4a062f64deb6fa30dec1d64914136712540003
theorem shape4_58:validFrom 11131 0 _HWY=true:=by decide+kernel
def _HWZ:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7a29212a901043b7c9444c47fbd09bdef64deb6fa30df27ecfe0bf81d52370003
theorem shape4_59:validFrom 11130 0 _HWZ=true:=by decide+kernel
def _HXB:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7929212a901043b8136187712e599722f64deb6fa30df5bb1c93b0321521a0003
theorem shape4_60:validFrom 11129 0 _HXB=true:=by decide+kernel
def _HXC:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7829212a901043b85d7ec29a60e2922ef64deb6fa30df8f76946a0e2551fd0003
theorem shape4_61:validFrom 11128 0 _HXC=true:=by decide+kernel
def _HXD:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7729212a901043b8a6f77919532a8d06f64deb6fa30dfffd8c79a1980d1df0003
theorem shape4_62:validFrom 11127 0 _HXD=true:=by decide+kernel
def _HXE:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7629212a901043b8efcbaaee053187a2f64deb6fa30e0339d92c92484d1c00003
theorem shape4_63:validFrom 11126 0 _HXE=true:=by decide+kernel
def _HXF:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7529212a901043b9389fdcc2b738820af64deb6fa30e067625df82f88d1a10003
theorem shape4_64:validFrom 11125 0 _HXF=true:=by decide+kernel
def _HXG:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7429212a901043ba3de8ac80269d7c36f64deb6fa30e0c575e4eb230651820003
theorem shape4_65:validFrom 11124 0 _HXG=true:=by decide+kernel
def _HXH:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7329212a901043bbb252bdb72471762ef64deb6fa30e1403870e1e61891610003
theorem shape4_66:validFrom 11123 0 _HXH=true:=by decide+kernel
def _HXI:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7229212a901043bc1114fe32bb146feef64deb6fa30e20f4aa09a499d51400003
theorem shape4_67:validFrom 11122 0 _HXI=true:=by decide+kernel
def _HXJ:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7129212a901043bc58a026b2ec996976f64deb6fa30e2430f6bc954a1511f0003
theorem shape4_68:validFrom 11121 0 _HXJ=true:=by decide+kernel
def _HXK:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7029212a901043bc9ee245de9d9c62c6f64deb6fa30e28d7e2f0c858550fc0003
theorem shape4_69:validFrom 11120 0 _HXK=true:=by decide+kernel
def _HXM:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b6f29212a901043bce336d70b8ddc5bdef64deb6fa30e2c142fa3b908950d60003
theorem shape4_70:validFrom 11119 0 _HXM=true:=by decide+kernel
def _HXN:List Piece:=DZ.decode 62 41 0x3782dace9d900000adb949095480821de1beb0e146fb3aa617a8eab16310e96c94a51867104f3b0003
theorem shape4_71:validFrom 11118 0 _HXN=true:=by decide+kernel
def _HXO:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b6800000000003c34bb541adc5a653a949095480821de3e1556aae7d3a6b57a8eab16310e98be402c440b5cf150004
theorem shape4_72:validFrom 11117 0 _HXO=true:=by decide+kernel
def _HXP:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b6000000000003c35b978cf9f90b528949095480821de5fed5cec3fd322ef7a8eab16310e9ab3360701a5b4eee0004
theorem shape4_73:validFrom 11116 0 _HXP=true:=by decide+kernel
def _HXQ:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b5800000000003c36b7974d25c27515cbd33aa8b0a1e0f8e8b6829db12112bd33aa8b090f03e5ca9aada61d054bd47558b18877d6e47bba492bc7f95ea3aac58c43be1d131d9f36783f5949095480821de9b0923cee85b1f0b7a8eab16310e9ca82be1bf400cee90008
theorem shape4_74:validFrom 11115 0 _HXQ=true:=by decide+kernel
def _HXR:List Piece:=DZ.decode 62 41 0x1bc16d674ec8000056d400000000000f0ded6be4ab97d14092f4ceaa2c287841a93283a068e82baf4ceaa2c243c0f1b52750d9104082f51d562c621df345fa0adc9169f0b7a8eab16310e9e9d21bc7cda64f500006
theorem shape4_75:validFrom 11114 0 _HXR=true:=by decide+kernel
def _HXS:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b690000000000078716783437534c9db97a675516143c2297e8c5a956640897a675516121e0743e701492649fd57a8eab16310ea0f3edaa0eb51cf140005
theorem shape4_76:validFrom 11113 0 _HXS=true:=by decide+kernel
def _HXT:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b68000000000007873639af313c109b097a675516143c24611bbf4738b3fad7a675516121e06f4382642bc99f657a8eab16310ea2e93deb892d78e9f0005
theorem shape4_77:validFrom 11112 0 _HXT=true:=by decide+kernel
def _HXU:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b670000000000078755fa6343844098417a675516143c2630322f663cb3ec97a675516121e0879db23246e01eef7a8eab16310ea8ff8f96ec5598e260005
theorem shape4_78:validFrom 11111 0 _HXU=true:=by decide+kernel
def _HXV:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b660000000000078775ba506e2d7a95597a675516143c280b15b1e1ecb3dd97a675516121e08059c42b6d211e757a8eab16310eab576ecefb7e40da90005
theorem shape4_79:validFrom 11110 0 _HXV=true:=by decide+kernel
def _HXX:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6500000000000787957976b1367892597a675516143c29e5f30d8a5e33ce17a675516121e078b70b903ba11df57a8eab16310ead626045cb20f4d280005
theorem shape4_80:validFrom 11109 0 _HXX=true:=by decide+kernel
def _HXY:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b6400000000000f0f6a6fabe91ec51e85e99d545850f0af3275ee3e2e8ef7bd33aa8b090ede28a24b16aa2ceb80004
theorem shape4_81:validFrom 11108 0 _HXY=true:=by decide+kernel
def _HXZ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad8c0000000000787d4f56e6859868c05e99d545850ef6112d5e134344eb40003
theorem shape4_82:validFrom 11107 0 _HXZ=true:=by decide+kernel
def _HYA:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad880000000000787f4b23ff484c088ade99d545850ef6f6bc5d3f2144e6e0003
theorem shape4_83:validFrom 11106 0 _HYA=true:=by decide+kernel
def _HYB:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad840000000000788146e4a990fb0853de99d545850ef7e0b9085745d0e250003
theorem shape4_84:validFrom 11105 0 _HYB=true:=by decide+kernel
def _HYC:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad80000000000078834298e55fc1481ade99d545850ef8d09dc70eee28dda0003
theorem shape4_85:validFrom 11104 0 _HYC=true:=by decide+kernel
def _HYD:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad7c000000000078853e40b2b47d47dfde99d545850ef9c5a57b193790d8d0003
theorem shape4_86:validFrom 11103 0 _HYD=true:=by decide+kernel
def _HYE:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad7800000000007887338e755c8387a35e99d545850efabb3f449d4658d3d0003
theorem shape4_87:validFrom 11102 0 _HYE=true:=by decide+kernel
def _HYF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ba0f1121276aec7990ec90002
theorem shape4_88:validFrom 11101 0 _HYF=true:=by decide+kernel
def _HYG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f115bdb9d1b566ce490002
theorem shape4_89:validFrom 11100 0 _HYG=true:=by decide+kernel
def _HYI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f11968e659860b8dc50002
theorem shape4_90:validFrom 11099 0 _HYI=true:=by decide+kernel
def _HYJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f11d13fc40360f8d3d0002
theorem shape4_91:validFrom 11098 0 _HYJ=true:=by decide+kernel
def _HYK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f120befb8bc8c7ccb20002
theorem shape4_92:validFrom 11097 0 _HYK=true:=by decide+kernel
def _HYL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b00f12469e4363af60c230002
theorem shape4_93:validFrom 11096 0 _HYL=true:=by decide+kernel
def _HYM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ae0f12814b6458fd9cb910002
theorem shape4_94:validFrom 11095 0 _HYM=true:=by decide+kernel
def _HYN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ac0f12bbf71b3c41a8afc0002
theorem shape4_95:validFrom 11094 0 _HYN=true:=by decide+kernel
def _HYO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056aa0f12f6a1686db118a630002
theorem shape4_96:validFrom 11093 0 _HYO=true:=by decide+kernel
def _HYP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a80f13314a4b8d17c49c50002
theorem shape4_97:validFrom 11092 0 _HYP=true:=by decide+kernel
def _HYQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a60f136bf1c4ca91b49240002
theorem shape4_98:validFrom 11091 0 _HYQ=true:=by decide+kernel
def _HYR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a40f13a697d45631bc87f0002
theorem shape4_99:validFrom 11090 0 _HYR=true:=by decide+kernel
def _HUL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a20f13e13c79cfce547d70002
theorem shape4_100:validFrom 11089 0 _HUL=true:=by decide+kernel
def _HUM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a00f141bdfb5978f9472c0002
theorem shape4_101:validFrom 11088 0 _HUM=true:=by decide+kernel
def _HUN:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569e0f145681874d4e1867e0002
theorem shape4_102:validFrom 11087 0 _HUN=true:=by decide+kernel
def _HUO:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569c0f149121ef5130885cc0002
theorem shape4_103:validFrom 11086 0 _HUO=true:=by decide+kernel
def _HUP:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569a0f14cbc0ed4312745170002
theorem shape4_104:validFrom 11085 0 _HUP=true:=by decide+kernel
def _HUQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056980f15065e8183161045d0002
theorem shape4_105:validFrom 11084 0 _HUQ=true:=by decide+kernel
def _HUR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056960f1540faabb11aa839f0002
theorem shape4_106:validFrom 11083 0 _HUR=true:=by decide+kernel
def _HUS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056940f157b956c2d3f782dd0002
theorem shape4_107:validFrom 11082 0 _HUS=true:=by decide+kernel
def _HUT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056920f15b62ec29766b42170002
theorem shape4_108:validFrom 11081 0 _HUT=true:=by decide+kernel
def _HUU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056900f15f0c6af4facb814e0002
theorem shape4_109:validFrom 11080 0 _HUU=true:=by decide+kernel
def _HUW:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000568e0f162b5d31f5f6a00820002
theorem shape4_110:validFrom 11079 0 _HUW=true:=by decide+kernel
def _HUX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3bd41520ad5688b0f1665f24aea5dd40020002
theorem shape4_111:validFrom 11078 0 _HUX=true:=by decide+kernel
def _HUY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bd32ad1f1ccd670f16a085f9ccca640020002
theorem shape4_112:validFrom 11077 0 _HUY=true:=by decide+kernel
def _HUZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bd24088dd0ab4d0f16db183efd52cc0020002
theorem shape4_113:validFrom 11076 0 _HUZ=true:=by decide+kernel
def row4 (v:ℕ):List Piece:=match v with
 | 0=>d4_0
 | 1=>d4_1
 | 2=>d4_2
 | 3=>d4_3
 | 4=>d4_4
 | 5=>d4_5
 | 6=>d4_6
 | 7=>d4_7
 | 8=>d4_8
 | 9=>d4_9
 | 10=>_HUK
 | 11=>_HUV
 | 12=>_HVA
 | 13=>_HVB
 | 14=>_HVC
 | 15=>_HVD
 | 16=>_HVE
 | 17=>_HVF
 | 18=>_HVG
 | 19=>_HVH
 | 20=>_HVJ
 | 21=>_HVK
 | 22=>_HVL
 | 23=>_HVM
 | 24=>_HVN
 | 25=>_HVO
 | 26=>_HVP
 | 27=>_HVQ
 | 28=>_HVR
 | 29=>_HVS
 | 30=>_HVU
 | 31=>_HVV
 | 32=>_HVW
 | 33=>_HVX
 | 34=>_HVY
 | 35=>_HVZ
 | 36=>_HWA
 | 37=>_HWB
 | 38=>_HWC
 | 39=>_HWD
 | 40=>_HWF
 | 41=>_HWG
 | 42=>_HWH
 | 43=>_HWI
 | 44=>_HWJ
 | 45=>_HWK
 | 46=>_HWL
 | 47=>_HWM
 | 48=>_HWN
 | 49=>_HWO
 | 50=>_HWQ
 | 51=>_HWR
 | 52=>_HWS
 | 53=>_HWT
 | 54=>_HWU
 | 55=>_HWV
 | 56=>_HWW
 | 57=>_HWX
 | 58=>_HWY
 | 59=>_HWZ
 | 60=>_HXB
 | 61=>_HXC
 | 62=>_HXD
 | 63=>_HXE
 | 64=>_HXF
 | 65=>_HXG
 | 66=>_HXH
 | 67=>_HXI
 | 68=>_HXJ
 | 69=>_HXK
 | 70=>_HXM
 | 71=>_HXN
 | 72=>_HXO
 | 73=>_HXP
 | 74=>_HXQ
 | 75=>_HXR
 | 76=>_HXS
 | 77=>_HXT
 | 78=>_HXU
 | 79=>_HXV
 | 80=>_HXX
 | 81=>_HXY
 | 82=>_HXZ
 | 83=>_HYA
 | 84=>_HYB
 | 85=>_HYC
 | 86=>_HYD
 | 87=>_HYE
 | 88=>_HYF
 | 89=>_HYG
 | 90=>_HYI
 | 91=>_HYJ
 | 92=>_HYK
 | 93=>_HYL
 | 94=>_HYM
 | 95=>_HYN
 | 96=>_HYO
 | 97=>_HYP
 | 98=>_HYQ
 | 99=>_HYR
 | 100=>_HUL
 | 101=>_HUM
 | 102=>_HUN
 | 103=>_HUO
 | 104=>_HUP
 | 105=>_HUQ
 | 106=>_HUR
 | 107=>_HUS
 | 108=>_HUT
 | 109=>_HUU
 | 110=>_HUW
 | 111=>_HUX
 | 112=>_HUY
 | 113=>_HUZ
 | _=>[]
theorem checked4 (v:ℕ) (hy:4+v≤117):validFrom (11193-4-v) 0 (row4 v)=true:=by
 have hv:v≤113:=by omega
 interval_cases v
 · exact shape4_0
 · exact shape4_1
 · exact shape4_2
 · exact shape4_3
 · exact shape4_4
 · exact shape4_5
 · exact shape4_6
 · exact shape4_7
 · exact shape4_8
 · exact shape4_9
 · exact shape4_10
 · exact shape4_11
 · exact shape4_12
 · exact shape4_13
 · exact shape4_14
 · exact shape4_15
 · exact shape4_16
 · exact shape4_17
 · exact shape4_18
 · exact shape4_19
 · exact shape4_20
 · exact shape4_21
 · exact shape4_22
 · exact shape4_23
 · exact shape4_24
 · exact shape4_25
 · exact shape4_26
 · exact shape4_27
 · exact shape4_28
 · exact shape4_29
 · exact shape4_30
 · exact shape4_31
 · exact shape4_32
 · exact shape4_33
 · exact shape4_34
 · exact shape4_35
 · exact shape4_36
 · exact shape4_37
 · exact shape4_38
 · exact shape4_39
 · exact shape4_40
 · exact shape4_41
 · exact shape4_42
 · exact shape4_43
 · exact shape4_44
 · exact shape4_45
 · exact shape4_46
 · exact shape4_47
 · exact shape4_48
 · exact shape4_49
 · exact shape4_50
 · exact shape4_51
 · exact shape4_52
 · exact shape4_53
 · exact shape4_54
 · exact shape4_55
 · exact shape4_56
 · exact shape4_57
 · exact shape4_58
 · exact shape4_59
 · exact shape4_60
 · exact shape4_61
 · exact shape4_62
 · exact shape4_63
 · exact shape4_64
 · exact shape4_65
 · exact shape4_66
 · exact shape4_67
 · exact shape4_68
 · exact shape4_69
 · exact shape4_70
 · exact shape4_71
 · exact shape4_72
 · exact shape4_73
 · exact shape4_74
 · exact shape4_75
 · exact shape4_76
 · exact shape4_77
 · exact shape4_78
 · exact shape4_79
 · exact shape4_80
 · exact shape4_81
 · exact shape4_82
 · exact shape4_83
 · exact shape4_84
 · exact shape4_85
 · exact shape4_86
 · exact shape4_87
 · exact shape4_88
 · exact shape4_89
 · exact shape4_90
 · exact shape4_91
 · exact shape4_92
 · exact shape4_93
 · exact shape4_94
 · exact shape4_95
 · exact shape4_96
 · exact shape4_97
 · exact shape4_98
 · exact shape4_99
 · exact shape4_100
 · exact shape4_101
 · exact shape4_102
 · exact shape4_103
 · exact shape4_104
 · exact shape4_105
 · exact shape4_106
 · exact shape4_107
 · exact shape4_108
 · exact shape4_109
 · exact shape4_110
 · exact shape4_111
 · exact shape4_112
 · exact shape4_113
def d5_0:List Piece:=DZ.decode 58 42 0xa484aa4041e9e6a843877b026bb45ea3aac58c7a1314755ddd6d86cc6f64deb6fa3d2e91790a4275e96db0003
theorem shape5_0:validFrom 11188 0 d5_0=true:=by decide+kernel
def d5_1:List Piece:=DZ.decode 58 42 0xa484aa4041e9f7bd67d2b7126bb35ea3aac58c7a195615330c42d6c2ef64deb6fa3d31cdc5bd3326296ca0003
theorem shape5_1:validFrom 11187 0 d5_1=true:=by decide+kernel
def d5_2:List Piece:=DZ.decode 58 42 0xa484aa4041ea08a96af363122bb25ea3aac58c7a1f800c1d89b516b92f64deb6fa3d350a127023d6696b80003
theorem shape5_2:validFrom 11186 0 d5_2=true:=by decide+kernel
def d5_3:List Piece:=DZ.decode 58 42 0xa484aa4041ea19956e140f11ebb15ea3aac58c7a25c1abf2b88a66af6f64deb6fa3d38465f231486a96a70003
theorem shape5_3:validFrom 11185 0 d5_3=true:=by decide+kernel
def d5_4:List Piece:=DZ.decode 58 42 0xa484aa4041ea2a817134bb11abb05ea3aac58c7a2beba2dd35fca6a5af64deb6fa3d3b82abd60536e96950003
theorem shape5_4:validFrom 11184 0 d5_4=true:=by decide+kernel
def d5_5:List Piece:=DZ.decode 58 42 0xa484aa4041ea3b6d745567116baf5ea3aac58c7a321599c7b36ee69bef64deb6fa3d3ebef888f5e7296830003
theorem shape5_5:validFrom 11183 0 d5_5=true:=by decide+kernel
def d5_6:List Piece:=DZ.decode 58 42 0xa484aa4041ea4cfdfc2053522bae5ea3aac58c7a381061e723e246932f64deb6fa3d41fb453be697696710003
theorem shape5_6:validFrom 11182 0 d5_6=true:=by decide+kernel
def d5_7:List Piece:=DZ.decode 58 42 0xa484aa4041ea5f09e76aefc3abad5ea3aac58c7a3de2a2781952768b2f64deb6fa3d453791eed747a965f0003
theorem shape5_7:validFrom 11181 0 d5_7=true:=by decide+kernel
def d5_8:List Piece:=DZ.decode 58 42 0xa484aa4041ea70ecb18afc24ebac5ea3aac58c7a43b4e3090ec2a682ef64deb6fa3d4873dea1c7f7e964d0003
theorem shape5_8:validFrom 11180 0 d5_8=true:=by decide+kernel
def d5_9:List Piece:=DZ.decode 58 42 0xa484aa4041ea82f89cd598966bab5ea3aac58c7a4987239a0432d67aef64deb6fa3d4bb02b54b8a82963b0003
theorem shape5_9:validFrom 11179 0 d5_9=true:=by decide+kernel
def _HYU:List Piece:=DZ.decode 58 42 0xa484aa4041ea950488203507ebaa5ea3aac58c7a4f59642af9a30672ef64deb6fa3d4eec7807a958696290003
theorem shape5_10:validFrom 11178 0 _HYU=true:=by decide+kernel
def _HZF:List Piece:=DZ.decode 58 42 0xa484aa4041eaa6e7524041692ba95ea3aac58c7a5513fbd13db0266aaf64deb6fa3d5228c4ba9a08a96160003
theorem shape5_11:validFrom 11177 0 _HZF=true:=by decide+kernel
def _HZJ:List Piece:=DZ.decode 58 42 0xa484aa4041eab8f33d8adddaaba85ea3aac58c7a5ae63c6233205662af64deb6fa3d5565116d8ab8e96040003
theorem shape5_12:validFrom 11176 0 _HZJ=true:=by decide+kernel
def _HZK:List Piece:=DZ.decode 58 42 0xa484aa4041eacaff28d57a4c2ba75ea3aac58c7a60a0d408772d765aaf64deb6fa3d58a15e207b69295f10003
theorem shape5_13:validFrom 11175 0 _HZK=true:=by decide+kernel
def _HZL:List Piece:=DZ.decode 58 42 0xa484aa4041eadce1f2f586ad6ba65ea3aac58c7a665b6baebb3a96526f64deb6fa3d5bddaad36c19695de0003
theorem shape5_14:validFrom 11174 0 _HZL=true:=by decide+kernel
def _HZM:List Piece:=DZ.decode 58 42 0xa484aa4041eae4f7d5f13f2f6ba55ea3aac58c7a6f5a9b45d459263aef64deb6fa3d5f19f7865cc9a95cb0003
theorem shape5_15:validFrom 11173 0 _HZM=true:=by decide+kernel
def _HZN:List Piece:=DZ.decode 58 42 0xa484aa4041eaf5e3d911eb2f2ba45ea3aac58c7a756ce945a06856312f64deb6fa3d625644394d79e95b80003
theorem shape5_16:validFrom 11172 0 _HZN=true:=by decide+kernel
def _HZO:List Piece:=DZ.decode 58 42 0xa484aa4041eb06cfdc32972eeba35ea3aac58c7a7b7f37456c7786276f64deb6fa3d659290ec3e2a295a50003
theorem shape5_17:validFrom 11171 0 _HZO=true:=by decide+kernel
def _HZP:List Piece:=DZ.decode 58 42 0xa484aa4041eb1ceb49bba4c32ba25ea3aac58c7a819185453886b6212f64deb6fa3d68cedd9f2eda695920003
theorem shape5_18:validFrom 11170 0 _HZP=true:=by decide+kernel
def _HZQ:List Piece:=DZ.decode 58 42 0xa484aa4041eb2dd74cdc50c2eba15ea3aac58c7a87a3d3450495e6176f64deb6fa3d6c0b2a521f8aa957f0003
theorem shape5_19:validFrom 11169 0 _HZQ=true:=by decide+kernel
def _HZS:List Piece:=DZ.decode 58 42 0xa484aa4041eb3ec34ffcfcc2aba05ea3aac58c7a8d9e785a1f42060daf64deb6fa3d6f477705103ae956b0003
theorem shape5_20:validFrom 11168 0 _HZS=true:=by decide+kernel
def _HZT:List Piece:=DZ.decode 58 42 0xa484aa4041eba9811c385e2bab9f5ea3aac58c7a93991d6f39ee2640af64deb6fa3d7283c3b800eb295570003
theorem shape5_21:validFrom 11167 0 _HZT=true:=by decide+kernel
def _HZU:List Piece:=DZ.decode 58 42 0xa484aa4041ebfae95d10162aab9e5ea3aac58c7a9993c284549a4662af64deb6fa3d75c0106af19b695430003
theorem shape5_22:validFrom 11166 0 _HZU=true:=by decide+kernel
def _HZV:List Piece:=DZ.decode 58 42 0xa484aa4041ec0bd56030c22a6b9d5ea3aac58c7a9f8e67996f466658ef64deb6fa3d78fc5d1de24ba952f0003
theorem shape5_23:validFrom 11165 0 _HZV=true:=by decide+kernel
def _HZW:List Piece:=DZ.decode 58 42 0xa484aa4041ec1cc163516e2a2b9c5ea3aac58c7aa5890cae89f2864f2f64deb6fa3d7c38a9d0d2fbe951b0003
theorem shape5_24:validFrom 11164 0 _HZW=true:=by decide+kernel
def _HZX:List Piece:=DZ.decode 58 42 0xa484aa4041ec2dad66721a29eb9b5ea3aac58c7aab83b1c3a49ea6456f64deb6fa3d7f74f683c3ac295070003
theorem shape5_25:validFrom 11163 0 _HZX=true:=by decide+kernel
def _HZY:List Piece:=DZ.decode 58 42 0xa484aa4041ec3e996992c629ab9a5ea3aac58c7ab17e56d8bf4ac63baf64deb6fa3d82b14336b45c694f30003
theorem shape5_26:validFrom 11162 0 _HZY=true:=by decide+kernel
def _HZZ:List Piece:=DZ.decode 58 42 0xa484aa4041ec4f856cb372296b995ea3aac58c7ab76153032893d631ef64deb6fa3d85ed8fe9a50ca94de0003
theorem shape5_27:validFrom 11161 0 _HZZ=true:=by decide+kernel
def _IAA:List Piece:=DZ.decode 58 42 0xa484aa4041ec60716fd41e292b985ea3aac58c7abd444f2d91dce6282f64deb6fa3d8929dc9c95bce94c90003
theorem shape5_28:validFrom 11160 0 _IAA=true:=by decide+kernel
def _IAB:List Piece:=DZ.decode 58 42 0xa484aa4041ec7186941f5a392b975ea3aac58c7ac3274b57fb25f61eaf64deb6fa3d8c66294f866d294b40003
theorem shape5_29:validFrom 11159 0 _IAB=true:=by decide+kernel
def _IAD:List Piece:=DZ.decode 58 42 0xa484aa4041ec827297400638eb965ea3aac58c7ac90a4782646f0614ef64deb6fa3d8fa27602771d6949f0003
theorem shape5_30:validFrom 11158 0 _IAD=true:=by decide+kernel
def _IAE:List Piece:=DZ.decode 58 42 0xa484aa4041ec935e9a60b238ab955ea3aac58c7aceed43accdb8160b2f64deb6fa3d92dec2b567cda948a0003
theorem shape5_31:validFrom 11157 0 _IAE=true:=by decide+kernel
def _IAF:List Piece:=DZ.decode 58 42 0xa484aa4041eca44a9d815e386b945ea3aac58c7ad4b896ec859e16016f64deb6fa3d961b0f68587de94740003
theorem shape5_32:validFrom 11156 0 _IAF=true:=by decide+kernel
def _IAG:List Piece:=DZ.decode 58 42 0xa484aa4041ecb536a0a20a382b935ea3aac58c7ada9b9316eee725f7af64deb6fa3d99575c1b492e2945f0003
theorem shape5_33:validFrom 11155 0 _IAG=true:=by decide+kernel
def _IAH:List Piece:=DZ.decode 58 42 0xa484aa4041ecc622a3c2b637eb925ea3aac58c7ae066e656a6cd25edef64deb6fa3d9c93a8ce39de694490003
theorem shape5_34:validFrom 11154 0 _IAH=true:=by decide+kernel
def _IAI:List Piece:=DZ.decode 58 42 0xa484aa4041ecd70ea6e36237ab915ea3aac58c7ae63239965eb325e42f64deb6fa3d9fcff5812a8ea94330003
theorem shape5_35:validFrom 11153 0 _IAI=true:=by decide+kernel
def _IAJ:List Piece:=DZ.decode 58 42 0xa484aa4041ece823cb2e9e47ab905ea3aac58c7aebfd8cd6169925daaf64deb6fa3da30c42341b3ee941d0003
theorem shape5_36:validFrom 11152 0 _IAJ=true:=by decide+kernel
def _IAK:List Piece:=DZ.decode 58 42 0xa484aa4041ecf90fce4f4a476b8f5ea3aac58c7af1b1372b1d1c15d0ef64deb6fa3da6488ee70bef294060003
theorem shape5_37:validFrom 11151 0 _IAK=true:=by decide+kernel
def _IAL:List Piece:=DZ.decode 58 42 0xa484aa4041ed09fbd16ff6472b8e5ea3aac58c7af77c8a6ad50215c72f64deb6fa3da984db99fc9f693f00003
theorem shape5_38:validFrom 11150 0 _IAL=true:=by decide+kernel
def _IAM:List Piece:=DZ.decode 58 42 0xa484aa4041ed1ae7d490a246eb8d5ea3aac58c7afd3034bfdb8505bd6f64deb6fa3dacc1284ced4fa93d90003
theorem shape5_39:validFrom 11149 0 _IAM=true:=by decide+kernel
def _IAO:List Piece:=DZ.decode 58 42 0xa484aa4041ed2bd3d7b14e46ab8c5ea3aac58c7b02e3df14e207f5b3af64deb6fa3daffd74ffddffe93c20003
theorem shape5_40:validFrom 11148 0 _IAO=true:=by decide+kernel
def _IAP:List Piece:=DZ.decode 58 42 0xa484aa4041ed3cbfdad1fa466b8b5ea3aac58c7b087fe07f3727d5a9ef64deb6fa3db339c1b2ceb0293aa0003
theorem shape5_41:validFrom 11147 0 _IAP=true:=by decide+kernel
def _IAQ:List Piece:=DZ.decode 58 42 0xa484aa4041ed4dabddf2a6462b8a5ea3aac58c7b0e338ad43daac5a02f64deb6fa3db6760e65bf60693930003
theorem shape5_42:validFrom 11146 0 _IAQ=true:=by decide+kernel
def _IAR:List Piece:=DZ.decode 58 42 0xa484aa4041ed5ec1023de2562b895ea3aac58c7b13cf8c3e92caa596af64deb6fa3db9b25b18b010a937b0003
theorem shape5_43:validFrom 11145 0 _IAR=true:=by decide+kernel
def _IAS:List Piece:=DZ.decode 58 42 0xa484aa4041ed6fad055e8e55eb885ea3aac58c7b196b8da8e7ea858cef64deb6fa3dbceea7cba0c0e93630003
theorem shape5_44:validFrom 11144 0 _IAS=true:=by decide+kernel
def _IAT:List Piece:=DZ.decode 58 42 0xa484aa4041ed8099087f3a55ab875ea3aac58c7b1eefe6288ba755832f64deb6fa3dc02af47e91712934a0003
theorem shape5_45:validFrom 11143 0 _IAT=true:=by decide+kernel
def _IAU:List Piece:=DZ.decode 58 42 0xa484aa4041ed91850b9fe6556b865ea3aac58c7b248be792e0c735796f64deb6fa3dc36741318221693320003
theorem shape5_46:validFrom 11142 0 _IAU=true:=by decide+kernel
def _IAV:List Piece:=DZ.decode 58 42 0xa484aa4041eda2710ec092552b855ea3aac58c7b2a1040128484056faf64deb6fa3dc6a38de472d1a93190003
theorem shape5_47:validFrom 11141 0 _IAV=true:=by decide+kernel
def _IAW:List Piece:=DZ.decode 58 42 0xa484aa4041edb35d11e13e54eb845ea3aac58c7b2f9498922840d565ef64deb6fa3dc9dfda976381e93000003
theorem shape5_48:validFrom 11140 0 _IAW=true:=by decide+kernel
def _IAX:List Piece:=DZ.decode 58 42 0xa484aa4041edc4491501ea54ab835ea3aac58c7b350148271a9a955c2f64deb6fa3dcd1c274a5432292e60003
theorem shape5_49:validFrom 11139 0 _IAX=true:=by decide+kernel
def _IAZ:List Piece:=DZ.decode 58 42 0xa484aa4041edd535182296546b825ea3aac58c7b3a6df7bc0cf455526f64deb6fa3dd05873fd44e2692cc0003
theorem shape5_50:validFrom 11138 0 _IAZ=true:=by decide+kernel
def _IBA:List Piece:=DZ.decode 58 42 0xa484aa4041ede64a3c6dd2646b815ea3aac58c7b3fdaa750ff4e1548ef64deb6fa3dd394c0b03592a92b20003
theorem shape5_51:validFrom 11137 0 _IBA=true:=by decide+kernel
def _IBB:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae00a484aa40410edf7363f8e7e642b545ea3aac58c43b454756e5f1a7d53f2f64deb6fa30de8ed87dfcf9bbd2980004
theorem shape5_52:validFrom 11136 0 _IBB=true:=by decide+kernel
def _IBC:List Piece:=DZ.decode 62 42 0x3782dace9d900000adfca484aa40410ee082242af2a63ea6d5ea3aac58c43b4a9c5d90329e85356f64deb6fa30dec29d492c04bfd27d0004
theorem shape5_53:validFrom 11135 0 _IBC=true:=by decide+kernel
def _IBD:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7e29212a901043b6ea586033c442a5e6f64deb6fa30df06c19525a04592620003
theorem shape5_54:validFrom 11134 0 _IBD=true:=by decide+kernel
def _IBE:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7d29212a901043b7351a2007370ca1e2f64deb6fa30df3a866054ab4992460003
theorem shape5_55:validFrom 11133 0 _IBE=true:=by decide+kernel
def _IBF:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7c29212a901043b77fdbdfdaa9d69da2f64deb6fa30df6e4b2b83b64d922a0003
theorem shape5_56:validFrom 11132 0 _IBF=true:=by decide+kernel
def _IBG:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7b29212a901043b7ca9d9fae1ca0992ef64deb6fa30dfa20ff6b2c151920e0003
theorem shape5_57:validFrom 11131 0 _IBG=true:=by decide+kernel
def _IBH:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7a29212a901043b814badad74f299482f64deb6fa30dfd5d4c1e1cc5591f10003
theorem shape5_58:validFrom 11130 0 _IBH=true:=by decide+kernel
def _IBI:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7929212a901043b97608584fa5148f9ef64deb6fa30e03beb76d9b10bd1d30003
theorem shape5_59:validFrom 11129 0 _IBI=true:=by decide+kernel
def _IBK:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7829212a901043b9c0259378d79d8a86f64deb6fa30e06fb04208bc0fd1b60003
theorem shape5_60:validFrom 11128 0 _IBK=true:=by decide+kernel
def _IBL:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7729212a901043ba08f9c54d89a48532f64deb6fa30e0a3750d37c713d1970003
theorem shape5_61:validFrom 11127 0 _IBL=true:=by decide+kernel
def _IBM:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7629212a901043ba51cdf7223bab7faaf64deb6fa30e113d74067d26f51780003
theorem shape5_62:validFrom 11126 0 _IBM=true:=by decide+kernel
def _IBN:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7529212a901043ba9aa228f6edb279eaf64deb6fa30e1479c0b96dd7351590003
theorem shape5_63:validFrom 11125 0 _IBN=true:=by decide+kernel
def _IBO:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7429212a901043bae2d1d6215f7873f2f64deb6fa30e17b60d6c5e87751390003
theorem shape5_64:validFrom 11124 0 _IBO=true:=by decide+kernel
def _IBP:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7329212a901043bbe6d19c8a4e5b6dc2f64deb6fa30e1d9745db8dbf4d1180003
theorem shape5_65:validFrom 11123 0 _IBP=true:=by decide+kernel
def _IBQ:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7229212a901043bd5b3badc14c2f675ef64deb6fa30e25436e9af9f0710f70003
theorem shape5_66:validFrom 11122 0 _IBQ=true:=by decide+kernel
def _IBR:List Piece:=DZ.decode 62 42 0x3782dace9d900000adc4a484aa40410efdc1deda41aa718305ea3aac58c43bf6818460898e7436ef64deb6fa30e323491968028bd0d50004
theorem shape5_67:validFrom 11121 0 _IBR=true:=by decide+kernel
def _IBS:List Piece:=DZ.decode 62 42 0x3782dace9d900000adc0a484aa40410efee29d8eeb718967a5ea3aac58c43bfac18d5bb76a942eef64deb6fa30e3570de4970d8fd0b20004
theorem shape5_68:validFrom 11120 0 _IBS=true:=by decide+kernel
def _IBT:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b7800000000003c35f4305d371a553dd49095480821e00019461d86f3a96f7a8eab16310e9dcee409e77c3109a0004
theorem shape5_69:validFrom 11119 0 _IBT=true:=by decide+kernel
def _IBV:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b7000000000003c36ee9de9f6a3652cd49095480821e024311cb2bfd6a5cd7a8eab16310e9fadec4e43160507a0004
theorem shape5_70:validFrom 11118 0 _IBV=true:=by decide+kernel
def _IBW:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b6800000000003c37e9054e6a19351b149095480821e0392ec5a712c222117a8eab16310ea18cf4929eafd902b0004
theorem shape5_71:validFrom 11117 0 _IBW=true:=by decide+kernel
def _IBX:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6c000000000007871c6cd169bec8a1117a675516143c21a19c6efc20d41817a675516121e0b4ee914f1a0e20577a8eab16310ea36bfcd6fa49acfc30005
theorem shape5_72:validFrom 11116 0 _IBX=true:=by decide+kernel
def _IBY:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6b000000000007873bb8342bd4729ea97a675516143c235b4b4cfdad940b97a675516121e0af667deb073a9ff17a8eab16310ea54b051b55e380f580005
theorem shape5_73:validFrom 11115 0 _IBY=true:=by decide+kernel
def _IBZ:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6a000000000007875b02d1e4686c9c217a675516143c2514f41264bb53fe97a675516121e0a8f1b9b01f7e9f877a8eab16310ea72a0d5fb17d54ee80005
theorem shape5_74:validFrom 11114 0 _IBZ=true:=by decide+kernel
def _ICA:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b69000000000007877a4caac296f699817a675516143c26da69fb4a7a23f117a675516121e0a27cc52df0a39f177a8eab16310ea90915a40d1728e740005
theorem shape5_75:validFrom 11113 0 _ICA=true:=by decide+kernel
def _ICB:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b68000000000007879995be9743e096c17a675516143c28abad06f6a743e317a675516121e09ba9069a75651ea57a8eab16310eaaeca8b7bcbcd0dfd0005
theorem shape5_76:validFrom 11112 0 _ICB=true:=by decide+kernel
def _ICC:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6700000000000787b8de0d79fdcc93e97a675516143c2a77005cb40a43d457a675516121e09417e415282a9e2b7a8eab16310eace1f8f937352cd810005
theorem shape5_77:validFrom 11111 0 _ICC=true:=by decide+kernel
def _ICD:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b6600000000000787d825978250e490f17a675516143c229adab78f3003c517a675516121e10329d88e87551a657a8eab16310eb2f84aa49a5d4cd020005
theorem shape5_78:validFrom 11110 0 _ICD=true:=by decide+kernel
def _ICE:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b6500000000000f0feed8b90246d11bb5e99d545850f0951b3ce315b30ed4bd33aa8b090ee2ab88a9caf558d130004
theorem shape5_79:validFrom 11109 0 _ICE=true:=by decide+kernel
def _ICG:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad90000000000078816b25ca58e1c8aade99d545850ef6db9c24639fa8e910003
theorem shape5_80:validFrom 11108 0 _ICG=true:=by decide+kernel
def _ICH:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad8c000000000078835f797c07a3a875de99d545850ef7bd4727de341ce4c0003
theorem shape5_81:validFrom 11107 0 _ICH=true:=by decide+kernel
def _ICI:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad880000000000788553c0de9725683f5e99d545850ef8a4da42e29c34e040003
theorem shape5_82:validFrom 11106 0 _ICI=true:=by decide+kernel
def _ICJ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad840000000000788747fbf3801ec806de99d545850ef993cfdc97e214dba0003
theorem shape5_83:validFrom 11105 0 _ICJ=true:=by decide+kernel
def _ICK:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad80000000000078893c2ab7d13aa7ccde99d545850efa85b8befec43cd6e0003
theorem shape5_84:validFrom 11104 0 _ICK=true:=by decide+kernel
def _ICL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056be0f116609a5cf764cf210002
theorem shape5_85:validFrom 11103 0 _ICL=true:=by decide+kernel
def _ICM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056bc0f11a3c74ca30e04ea50002
theorem shape5_86:validFrom 11102 0 _ICM=true:=by decide+kernel
def _ICN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ba0f11dda7d2f128e0e260002
theorem shape5_87:validFrom 11101 0 _ICN=true:=by decide+kernel
def _ICO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f121786f2489080da40002
theorem shape5_88:validFrom 11100 0 _ICO=true:=by decide+kernel
def _ICP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f125164ab076b54d1e0002
theorem shape5_89:validFrom 11099 0 _ICP=true:=by decide+kernel
def _ICR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f128b40fccf97f4c930002
theorem shape5_90:validFrom 11098 0 _ICR=true:=by decide+kernel
def _ICS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f12c51be7ff3434c060002
theorem shape5_91:validFrom 11097 0 _ICS=true:=by decide+kernel
def _ICT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b00f12fef56c382230b740002
theorem shape5_92:validFrom 11096 0 _ICT=true:=by decide+kernel
def _ICU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ae0f1338cd89d88168ae00002
theorem shape5_93:validFrom 11095 0 _ICU=true:=by decide+kernel
def _ICV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ac0f1372a440823234a490002
theorem shape5_94:validFrom 11094 0 _ICV=true:=by decide+kernel
def _ICW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056aa0f13ac79909351509ae0002
theorem shape5_95:validFrom 11093 0 _ICW=true:=by decide+kernel
def _ICX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a80f13e64d79adc68890e0002
theorem shape5_96:validFrom 11092 0 _ICX=true:=by decide+kernel
def _ICY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a60f14201ffc009bec86b0002
theorem shape5_97:validFrom 11091 0 _ICY=true:=by decide+kernel
def _ICZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a40f1459f117badd847c30002
theorem shape5_98:validFrom 11090 0 _ICZ=true:=by decide+kernel
def _IDA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a20f1493c0cc7e775c7190002
theorem shape5_99:validFrom 11089 0 _IDA=true:=by decide+kernel
def _HYV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a00f14cd8f1aa97a6066b0002
theorem shape5_100:validFrom 11088 0 _HYV=true:=by decide+kernel
def _HYW:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569e0f15075c01ddd4bc5bb0002
theorem shape5_101:validFrom 11087 0 _HYW=true:=by decide+kernel
def _HYX:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569c0f15412782799ad45070002
theorem shape5_102:validFrom 11086 0 _HYX=true:=by decide+kernel
def _HYY:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569a0f157af19c1eb8bc44f0002
theorem shape5_103:validFrom 11085 0 _HYY=true:=by decide+kernel
def _HYZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056980f15b4ba4f2b3e983930002
theorem shape5_104:validFrom 11084 0 _HYZ=true:=by decide+kernel
def _HZA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056960f15ee819b4121042d40002
theorem shape5_105:validFrom 11083 0 _HZA=true:=by decide+kernel
def _HZB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056940f16284780be684c2100002
theorem shape5_106:validFrom 11082 0 _HZB=true:=by decide+kernel
def _HZC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056920f16620bff450bd41480002
theorem shape5_107:validFrom 11081 0 _HZC=true:=by decide+kernel
def _HZD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056900f169bcf1733164c07c0002
theorem shape5_108:validFrom 11080 0 _HZD=true:=by decide+kernel
def _HZE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3bd256a6b8560d40f16d590c82a7cb00020002
theorem shape5_109:validFrom 11079 0 _HZE=true:=by decide+kernel
def _HZG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3bd16fa58edae4d0f170f51128946cc0020002
theorem shape5_110:validFrom 11078 0 _HZG=true:=by decide+kernel
def _HZH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bd088aa013a38c0f17490ff5f171d00020002
theorem shape5_111:validFrom 11077 0 _HZH=true:=by decide+kernel
def _HZI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bcfa1b40dfc0a90f1782cd72c0fd5c0020002
theorem shape5_112:validFrom 11076 0 _HZI=true:=by decide+kernel
def row5 (v:ℕ):List Piece:=match v with
 | 0=>d5_0
 | 1=>d5_1
 | 2=>d5_2
 | 3=>d5_3
 | 4=>d5_4
 | 5=>d5_5
 | 6=>d5_6
 | 7=>d5_7
 | 8=>d5_8
 | 9=>d5_9
 | 10=>_HYU
 | 11=>_HZF
 | 12=>_HZJ
 | 13=>_HZK
 | 14=>_HZL
 | 15=>_HZM
 | 16=>_HZN
 | 17=>_HZO
 | 18=>_HZP
 | 19=>_HZQ
 | 20=>_HZS
 | 21=>_HZT
 | 22=>_HZU
 | 23=>_HZV
 | 24=>_HZW
 | 25=>_HZX
 | 26=>_HZY
 | 27=>_HZZ
 | 28=>_IAA
 | 29=>_IAB
 | 30=>_IAD
 | 31=>_IAE
 | 32=>_IAF
 | 33=>_IAG
 | 34=>_IAH
 | 35=>_IAI
 | 36=>_IAJ
 | 37=>_IAK
 | 38=>_IAL
 | 39=>_IAM
 | 40=>_IAO
 | 41=>_IAP
 | 42=>_IAQ
 | 43=>_IAR
 | 44=>_IAS
 | 45=>_IAT
 | 46=>_IAU
 | 47=>_IAV
 | 48=>_IAW
 | 49=>_IAX
 | 50=>_IAZ
 | 51=>_IBA
 | 52=>_IBB
 | 53=>_IBC
 | 54=>_IBD
 | 55=>_IBE
 | 56=>_IBF
 | 57=>_IBG
 | 58=>_IBH
 | 59=>_IBI
 | 60=>_IBK
 | 61=>_IBL
 | 62=>_IBM
 | 63=>_IBN
 | 64=>_IBO
 | 65=>_IBP
 | 66=>_IBQ
 | 67=>_IBR
 | 68=>_IBS
 | 69=>_IBT
 | 70=>_IBV
 | 71=>_IBW
 | 72=>_IBX
 | 73=>_IBY
 | 74=>_IBZ
 | 75=>_ICA
 | 76=>_ICB
 | 77=>_ICC
 | 78=>_ICD
 | 79=>_ICE
 | 80=>_ICG
 | 81=>_ICH
 | 82=>_ICI
 | 83=>_ICJ
 | 84=>_ICK
 | 85=>_ICL
 | 86=>_ICM
 | 87=>_ICN
 | 88=>_ICO
 | 89=>_ICP
 | 90=>_ICR
 | 91=>_ICS
 | 92=>_ICT
 | 93=>_ICU
 | 94=>_ICV
 | 95=>_ICW
 | 96=>_ICX
 | 97=>_ICY
 | 98=>_ICZ
 | 99=>_IDA
 | 100=>_HYV
 | 101=>_HYW
 | 102=>_HYX
 | 103=>_HYY
 | 104=>_HYZ
 | 105=>_HZA
 | 106=>_HZB
 | 107=>_HZC
 | 108=>_HZD
 | 109=>_HZE
 | 110=>_HZG
 | 111=>_HZH
 | 112=>_HZI
 | _=>[]
theorem checked5 (v:ℕ) (hy:5+v≤117):validFrom (11193-5-v) 0 (row5 v)=true:=by
 have hv:v≤112:=by omega
 interval_cases v
 · exact shape5_0
 · exact shape5_1
 · exact shape5_2
 · exact shape5_3
 · exact shape5_4
 · exact shape5_5
 · exact shape5_6
 · exact shape5_7
 · exact shape5_8
 · exact shape5_9
 · exact shape5_10
 · exact shape5_11
 · exact shape5_12
 · exact shape5_13
 · exact shape5_14
 · exact shape5_15
 · exact shape5_16
 · exact shape5_17
 · exact shape5_18
 · exact shape5_19
 · exact shape5_20
 · exact shape5_21
 · exact shape5_22
 · exact shape5_23
 · exact shape5_24
 · exact shape5_25
 · exact shape5_26
 · exact shape5_27
 · exact shape5_28
 · exact shape5_29
 · exact shape5_30
 · exact shape5_31
 · exact shape5_32
 · exact shape5_33
 · exact shape5_34
 · exact shape5_35
 · exact shape5_36
 · exact shape5_37
 · exact shape5_38
 · exact shape5_39
 · exact shape5_40
 · exact shape5_41
 · exact shape5_42
 · exact shape5_43
 · exact shape5_44
 · exact shape5_45
 · exact shape5_46
 · exact shape5_47
 · exact shape5_48
 · exact shape5_49
 · exact shape5_50
 · exact shape5_51
 · exact shape5_52
 · exact shape5_53
 · exact shape5_54
 · exact shape5_55
 · exact shape5_56
 · exact shape5_57
 · exact shape5_58
 · exact shape5_59
 · exact shape5_60
 · exact shape5_61
 · exact shape5_62
 · exact shape5_63
 · exact shape5_64
 · exact shape5_65
 · exact shape5_66
 · exact shape5_67
 · exact shape5_68
 · exact shape5_69
 · exact shape5_70
 · exact shape5_71
 · exact shape5_72
 · exact shape5_73
 · exact shape5_74
 · exact shape5_75
 · exact shape5_76
 · exact shape5_77
 · exact shape5_78
 · exact shape5_79
 · exact shape5_80
 · exact shape5_81
 · exact shape5_82
 · exact shape5_83
 · exact shape5_84
 · exact shape5_85
 · exact shape5_86
 · exact shape5_87
 · exact shape5_88
 · exact shape5_89
 · exact shape5_90
 · exact shape5_91
 · exact shape5_92
 · exact shape5_93
 · exact shape5_94
 · exact shape5_95
 · exact shape5_96
 · exact shape5_97
 · exact shape5_98
 · exact shape5_99
 · exact shape5_100
 · exact shape5_101
 · exact shape5_102
 · exact shape5_103
 · exact shape5_104
 · exact shape5_105
 · exact shape5_106
 · exact shape5_107
 · exact shape5_108
 · exact shape5_109
 · exact shape5_110
 · exact shape5_111
 · exact shape5_112
def d6_0:List Piece:=DZ.decode 58 42 0xa484aa4041ea407f48949e786bb35ea3aac58c7a3547d2b9fe0886986f64deb6fa3d3fd160971e04d168a0003
theorem shape6_0:validFrom 11187 0 d6_0=true:=by decide+kernel
def d6_1:List Piece:=DZ.decode 58 42 0xa484aa4041ea526212b4aad9abb25ea3aac58c7a3b2c47318db1f6902f64deb6fa3d430dad4a0eb5116780003
theorem shape6_1:validFrom 11186 0 d6_1=true:=by decide+kernel
def d6_2:List Piece:=DZ.decode 58 42 0xa484aa4041ea6444dcd4b73aebb15ea3aac58c7a40fe87c283222687ef64deb6fa3d4649f9fcff65516660003
theorem shape6_2:validFrom 11185 0 d6_2=true:=by decide+kernel
def d6_3:List Piece:=DZ.decode 58 42 0xa484aa4041ea7650c81f53ac6bb05ea3aac58c7a46e8713e29f5667fef64deb6fa3d498646aff015916550003
theorem shape6_3:validFrom 11184 0 d6_3=true:=by decide+kernel
def d6_4:List Piece:=DZ.decode 58 42 0xa484aa4041ea885cb369f01debaf5ea3aac58c7a4cbab1cf1f659677ef64deb6fa3d4cc29362e0c5d16430003
theorem shape6_4:validFrom 11183 0 d6_4=true:=by decide+kernel
def d6_5:List Piece:=DZ.decode 58 42 0xa484aa4041ea9a689eb48c8f6bae5ea3aac58c7a528cf26014d5c66fef64deb6fa3d4ffee015d176116310003
theorem shape6_5:validFrom 11182 0 d6_5=true:=by decide+kernel
def d6_6:List Piece:=DZ.decode 58 42 0xa484aa4041eaac4b68d498f0abad5ea3aac58c7a585f32f10a45f667af64deb6fa3d533b2cc8c2265161f0003
theorem shape6_6:validFrom 11181 0 d6_6=true:=by decide+kernel
def d6_7:List Piece:=DZ.decode 58 42 0xa484aa4041eabe57541f35622bac5ea3aac58c7a5e317381ffb6265faf64deb6fa3d5677797bb2d69160d0003
theorem shape6_7:validFrom 11180 0 d6_7=true:=by decide+kernel
def d6_8:List Piece:=DZ.decode 58 42 0xa484aa4041ead0633f69d1d3abab5ea3aac58c7a63ec0b2843c34657af64deb6fa3d59b3c62ea386d15fa0003
theorem shape6_8:validFrom 11179 0 d6_8=true:=by decide+kernel
def d6_9:List Piece:=DZ.decode 58 42 0xa484aa4041eae2460989de34ebaa5ea3aac58c7a69be4bb93933764f6f64deb6fa3d5cf012e19437115e80003
theorem shape6_9:validFrom 11178 0 d6_9=true:=by decide+kernel
def _IDD:List Piece:=DZ.decode 58 42 0xa484aa4041eaf451f4d47aa66ba95ea3aac58c7a6f78e35f7d4096476f64deb6fa3d602c5f9484e7515d50003
theorem shape6_10:validFrom 11177 0 _IDD=true:=by decide+kernel
def _IDO:List Piece:=DZ.decode 58 42 0xa484aa4041eb065de01f1717eba85ea3aac58c7a754b23f072b0c63f6f64deb6fa3d6368ac477597915c30003
theorem shape6_11:validFrom 11176 0 _IDO=true:=by decide+kernel
def _IDR:List Piece:=DZ.decode 58 42 0xa484aa4041eb1840aa3f23792ba75ea3aac58c7a7b05bb96b6bde6372f64deb6fa3d66a4f8fa6647d15b00003
theorem shape6_12:validFrom 11175 0 _IDR=true:=by decide+kernel
def _IDS:List Piece:=DZ.decode 58 42 0xa484aa4041eb2a4c9589bfeaaba65ea3aac58c7a80c0533cfacb062f2f64deb6fa3d69e145ad56f81159d0003
theorem shape6_13:validFrom 11174 0 _IDS=true:=by decide+kernel
def _IDT:List Piece:=DZ.decode 58 42 0xa484aa4041eb3c5880d45c5c2ba55ea3aac58c7a867aeae33ed826272f64deb6fa3d6d1d926047a85158a0003
theorem shape6_14:validFrom 11173 0 _IDT=true:=by decide+kernel
def _IDU:List Piece:=DZ.decode 58 42 0xa484aa4041eb3ecedafe62a56ba45ea3aac58c7a9146fde1e0caf606ef64deb6fa3d7059df133858915770003
theorem shape6_15:validFrom 11172 0 _IDU=true:=by decide+kernel
def _IDV:List Piece:=DZ.decode 58 42 0xa484aa4041eb4fbade1f0ea52ba35ea3aac58c7a97594be1acda25fd2f64deb6fa3d73962bc62908d15640003
theorem shape6_16:validFrom 11171 0 _IDV=true:=by decide+kernel
def _IDW:List Piece:=DZ.decode 58 42 0xa484aa4041eb60a6e13fbaa4eba25ea3aac58c7a9d53f0f6c78645f36f64deb6fa3d76d2787919b9115500003
theorem shape6_17:validFrom 11170 0 _IDW=true:=by decide+kernel
def _IDX:List Piece:=DZ.decode 58 42 0xa484aa4041eb76c24ec8c8392ba15ea3aac58c7aa3663ef6939575ed2f64deb6fa3d7a0ec52c0a695153d0003
theorem shape6_18:validFrom 11169 0 _IDX=true:=by decide+kernel
def _IDY:List Piece:=DZ.decode 58 42 0xa484aa4041eb87ae51e97438eba05ea3aac58c7aa960e40bae4195e36f64deb6fa3d7d4b11defb19915290003
theorem shape6_19:validFrom 11168 0 _IDY=true:=by decide+kernel
def _IEA:List Piece:=DZ.decode 58 42 0xa484aa4041eb989a550a2038ab9f5ea3aac58c7aaf5b8920c8edb5d9af64deb6fa3d80875e91ebc9d15150003
theorem shape6_20:validFrom 11167 0 _IEA=true:=by decide+kernel
def _IEB:List Piece:=DZ.decode 58 42 0xa484aa4041ec0358214581a1ab9e5ea3aac58c7ab5562e35e399d60caf64deb6fa3d83c3ab44dc7a115010003
theorem shape6_21:validFrom 11166 0 _IEB=true:=by decide+kernel
def _IEC:List Piece:=DZ.decode 58 42 0xa484aa4041ec549740f2a9906b9d5ea3aac58c7abb50d34afe45f62e6f64deb6fa3d86fff7f7cd2a514ed0003
theorem shape6_22:validFrom 11165 0 _IEC=true:=by decide+kernel
def _IED:List Piece:=DZ.decode 58 42 0xa484aa4041ec65ac653de5a06b9c5ea3aac58c7ac14b786018f21624ef64deb6fa3d8a3c44aabdda914d90003
theorem shape6_23:validFrom 11164 0 _IED=true:=by decide+kernel
def _IEE:List Piece:=DZ.decode 58 42 0xa484aa4041ec7698685e91a02b9b5ea3aac58c7ac7461d75339e361b2f64deb6fa3d8d78915dae8ad14c50003
theorem shape6_24:validFrom 11163 0 _IEE=true:=by decide+kernel
def _IEF:List Piece:=DZ.decode 58 42 0xa484aa4041ec87846b7f3d9feb9a5ea3aac58c7acd29199f9ce746116f64deb6fa3d90b4de109f3b114b00003
theorem shape6_25:validFrom 11162 0 _IEF=true:=by decide+kernel
def _IEG:List Piece:=DZ.decode 58 42 0xa484aa4041ec98706e9fe99fab995ea3aac58c7ad30c15ca06305607af64deb6fa3d93f12ac38feb5149b0003
theorem shape6_26:validFrom 11161 0 _IEG=true:=by decide+kernel
def _IEH:List Piece:=DZ.decode 58 42 0xa484aa4041eca95c71c0959f6b985ea3aac58c7ad8ef11f46f7965fdef64deb6fa3d972d7776809b914860003
theorem shape6_27:validFrom 11160 0 _IEH=true:=by decide+kernel
def _IEI:List Piece:=DZ.decode 58 42 0xa484aa4041ecba4874e1419f2b975ea3aac58c7aded20e1ed8c275f42f64deb6fa3d9a69c429714bd14710003
theorem shape6_28:validFrom 11159 0 _IEI=true:=by decide+kernel
def _IEJ:List Piece:=DZ.decode 58 42 0xa484aa4041eccb347801ed9eeb965ea3aac58c7ae4b50a49420b85ea6f64deb6fa3d9da610dc61fc1145c0003
theorem shape6_29:validFrom 11158 0 _IEJ=true:=by decide+kernel
def _IEL:List Piece:=DZ.decode 58 42 0xa484aa4041ecdc499c4d29aeeb955ea3aac58c7aea980673ab5495e0ef64deb6fa3da0e25d8f52ac514470003
theorem shape6_30:validFrom 11157 0 _IEL=true:=by decide+kernel
def _IEM:List Piece:=DZ.decode 58 42 0xa484aa4041eced359f6dd5aeab945ea3aac58c7af06359b3633a95d72f64deb6fa3da41eaa42435c914310003
theorem shape6_31:validFrom 11156 0 _IEM=true:=by decide+kernel
def _IEN:List Piece:=DZ.decode 58 42 0xa484aa4041ecfe21a28e81ae6b935ea3aac58c7af62eacf31b2095cd6f64deb6fa3da75af6f5340cd141b0003
theorem shape6_32:validFrom 11155 0 _IEN=true:=by decide+kernel
def _IEO:List Piece:=DZ.decode 58 42 0xa484aa4041ed0f0da5af2dae2b925ea3aac58c7afbfa0032d30695c3af64deb6fa3daa9743a824bd114050003
theorem shape6_33:validFrom 11154 0 _IEO=true:=by decide+kernel
def _IEP:List Piece:=DZ.decode 58 42 0xa484aa4041ed1ff9a8cfd9adeb915ea3aac58c7b01c553728aec95b9ef64deb6fa3dadd3905b156d513ef0003
theorem shape6_34:validFrom 11153 0 _IEP=true:=by decide+kernel
def _IEQ:List Piece:=DZ.decode 58 42 0xa484aa4041ed30e5abf085adab905ea3aac58c7b0790a6b242d295b02f64deb6fa3db10fdd0e061d913d90003
theorem shape6_35:validFrom 11152 0 _IEQ=true:=by decide+kernel
def _IER:List Piece:=DZ.decode 58 42 0xa484aa4041ed41d1af1131ad6b8f5ea3aac58c7b0d445107495585a66f64deb6fa3db44c29c0f6cdd13c20003
theorem shape6_36:validFrom 11151 0 _IER=true:=by decide+kernel
def _IES:List Piece:=DZ.decode 58 42 0xa484aa4041ed52e6d35c6dbd6b8e5ea3aac58c7b12f7fb5c4fd8759cef64deb6fa3db7887673e77e113ab0003
theorem shape6_37:validFrom 11150 0 _IES=true:=by decide+kernel
def _IET:List Piece:=DZ.decode 58 42 0xa484aa4041ed63d2d67d19bd2b8d5ea3aac58c7b18aba5b1565b65932f64deb6fa3dbac4c326d82e513940003
theorem shape6_38:validFrom 11149 0 _IET=true:=by decide+kernel
def _IEU:List Piece:=DZ.decode 58 42 0xa484aa4041ed74bed99dc5bceb8c5ea3aac58c7b1e5f50065cde55896f64deb6fa3dbe010fd9c8de9137d0003
theorem shape6_39:validFrom 11148 0 _IEU=true:=by decide+kernel
def _IEW:List Piece:=DZ.decode 58 42 0xa484aa4041ed85aadcbe71bcab8b5ea3aac58c7b23fb5170b1fe357faf64deb6fa3dc13d5c8cb98ed13650003
theorem shape6_40:validFrom 11147 0 _IEW=true:=by decide+kernel
def _IEX:List Piece:=DZ.decode 58 42 0xa484aa4041ed9696dfdf1dbc6b8a5ea3aac58c7b29aefbc5b8812575ef64deb6fa3dc479a93faa3f1134e0003
theorem shape6_41:validFrom 11146 0 _IEX=true:=by decide+kernel
def _IEY:List Piece:=DZ.decode 58 42 0xa484aa4041eda782e2ffc9bc2b895ea3aac58c7b2f4afd300da1056c2f64deb6fa3dc7b5f5f29aef513360003
theorem shape6_42:validFrom 11145 0 _IEY=true:=by decide+kernel
def _IEZ:List Piece:=DZ.decode 58 42 0xa484aa4041edb86ee62075bbeb885ea3aac58c7b34cf55afb15dd5626f64deb6fa3dcaf242a58b9f9131d0003
theorem shape6_43:validFrom 11144 0 _IEZ=true:=by decide+kernel
def _IFA:List Piece:=DZ.decode 58 42 0xa484aa4041edc9840a6bb1cbeb875ea3aac58c7b3a6b571a067db558ef64deb6fa3dce2e8f587c4fd13050003
theorem shape6_44:validFrom 11143 0 _IFA=true:=by decide+kernel
def _IFB:List Piece:=DZ.decode 58 42 0xa484aa4041edda700d8c5dcbab865ea3aac58c7b3fefaf99aa3a854f2f64deb6fa3dd16adc0b6d00112ec0003
theorem shape6_45:validFrom 11142 0 _IFB=true:=by decide+kernel
def _IFC:List Piece:=DZ.decode 58 42 0xa484aa4041edeb5c10ad09cb6b855ea3aac58c7b457408194df755456f64deb6fa3dd4a728be5db0512d30003
theorem shape6_46:validFrom 11141 0 _IFC=true:=by decide+kernel
def _IFD:List Piece:=DZ.decode 58 42 0xa484aa4041edfc4813cdb5cb2b845ea3aac58c7b4ae0b7ae4051153baf64deb6fa3dd7e375714e60912b90003
theorem shape6_47:validFrom 11140 0 _IFD=true:=by decide+kernel
def _IFE:List Piece:=DZ.decode 58 42 0xa484aa4041ee0d3416ee61caeb835ea3aac58c7b5065102de40de531ef64deb6fa3ddb1fc2243f10d12a00003
theorem shape6_48:validFrom 11139 0 _IFE=true:=by decide+kernel
def _IFF:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae08a484aa40410ee1e201a0f0dcaab4f5ea3aac58c43b55d1bfc2d667a5282f64deb6fa30dde5c0ed72fc1112860004
theorem shape6_49:validFrom 11138 0 _IFF=true:=by decide+kernel
def _IFH:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae04a484aa40410ee2f0c1d2fb9ca6a795ea3aac58c43b5b26c66d175e551e6f64deb6fa30de1985b8a20715126b0004
theorem shape6_50:validFrom 11137 0 _IFH=true:=by decide+kernel
def _IFI:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae00a484aa40410ee4021417af5da69955ea3aac58c43b6093760209b81514ef64deb6fa30de4d4a83d1121912510004
theorem shape6_51:validFrom 11136 0 _IFI=true:=by decide+kernel
def _IFJ:List Piece:=DZ.decode 62 42 0x3782dace9d900000adfca484aa40410ee510d449ba1da28a45ea3aac58c43b65d0d3c1994bb50b2f64deb6fa30dfa2d6f6cab2aa52350004
theorem shape6_52:validFrom 11135 0 _IFJ=true:=by decide+kernel
def _IFK:List Piece:=DZ.decode 62 42 0x3782dace9d900000adf8a484aa40410ee61f947bc4dd9e7a55ea3aac58c43b6b25da6bda4265016f64deb6fa30dfd69bc1f9bdae521a0004
theorem shape6_53:validFrom 11134 0 _IFK=true:=by decide+kernel
def _IFL:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7d29212a901043b8971c6c3b6d869a66f64deb6fa30e01ac00df3593411fe0003
theorem shape6_54:validFrom 11133 0 _IFL=true:=by decide+kernel
def _IFM:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7c29212a901043b8e1de2c0ee05095fef64deb6fa30e04e84d922643811e20003
theorem shape6_55:validFrom 11132 0 _IFM=true:=by decide+kernel
def _IFN:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7b29212a901043b92bfb673812d99162f64deb6fa30e08249a4516f3c11c50003
theorem shape6_56:validFrom 11131 0 _IFN=true:=by decide+kernel
def _IFO:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7a29212a901043b97618a26145628c8af64deb6fa30e0b60e6f807a4011a80003
theorem shape6_57:validFrom 11130 0 _IFO=true:=by decide+kernel
def _IFP:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7929212a901043b9bf9158e037aa877ef64deb6fa30e0e9d33aaf8544118a0003
theorem shape6_58:validFrom 11129 0 _IFP=true:=by decide+kernel
def _IFQ:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7829212a901043bb20ded6588d95823ef64deb6fa30e14fe9efa769fa516c0003
theorem shape6_59:validFrom 11128 0 _IFQ=true:=by decide+kernel
def _IFS:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7729212a901043bb69b3082d3f9c7cc2f64deb6fa30e183aebad674fe514d0003
theorem shape6_60:validFrom 11127 0 _IFS=true:=by decide+kernel
def _IFT:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7629212a901043bbb2873a01f1a37712f64deb6fa30e1b77386058002512e0003
theorem shape6_61:validFrom 11126 0 _IFT=true:=by decide+kernel
def _IFU:List Piece:=DZ.decode 62 41 0x3782dace9d900000add549095480821ddb7f37bc31648b8977a8eab16310e8dde4fe3b2a4390360003
theorem shape6_62:validFrom 11125 0 _IFU=true:=by decide+kernel
def _IFV:List Piece:=DZ.decode 62 41 0x3782dace9d900000add149095480821dddc0b52584f2bb5877a8eab16310e8fbd58280e3e0d0160003
theorem shape6_63:validFrom 11124 0 _IFV=true:=by decide+kernel
def _IFW:List Piece:=DZ.decode 62 41 0x3782dace9d900000adcd49095480821ddffd0e69867ee325d7a8eab16310e919c606c69d7e0ff50003
theorem shape6_64:validFrom 11123 0 _IFW=true:=by decide+kernel
def _IFX:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b72a484aa40410ecb5e76f362e7ad78b0002
theorem shape6_65:validFrom 11122 0 _IFX=true:=by decide+kernel
def _IFY:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b71a484aa40410ed184f3a00800815da0002
theorem shape6_66:validFrom 11121 0 _IFY=true:=by decide+kernel
def _IFZ:List Piece:=DZ.decode 62 39 0x3782dace9d900000adc0000000000078706571434ca8ea5d5e99d545850eef681fe69b01d50bd0003
theorem shape6_67:validFrom 11120 0 _IFZ=true:=by decide+kernel
def _IGA:List Piece:=DZ.decode 62 39 0x3782dace9d900000adbc0000000000787252d15e676a4a3bde99d545850ef00f468e43d7bd0910003
theorem shape6_68:validFrom 11119 0 _IGA=true:=by decide+kernel
def _IGB:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb800000000007874402549bdb1ca18de99d545850ef0bc555133cdad0630003
theorem shape6_69:validFrom 11118 0 _IGB=true:=by decide+kernel
def _IGD:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb4000000000078762d6d03dee9c9f45e99d545850ef16dd1c7e8c8350330003
theorem shape6_70:validFrom 11117 0 _IGD=true:=by decide+kernel
def _IGE:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb0000000000078781aa88fac3329cdde99d545850ef223bbf2bcd2a90020003
theorem shape6_71:validFrom 11116 0 _IGE=true:=by decide+kernel
def _IGF:List Piece:=DZ.decode 62 39 0x3782dace9d900000adac0000000000787a07d7ebb502c9a65e99d545850ef2df8e38aaf924fcf0003
theorem shape6_72:validFrom 11115 0 _IGF=true:=by decide+kernel
def _IGG:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada80000000000787bf4fb17f957a97c5e99d545850ef39fce32b82e34f990003
theorem shape6_73:validFrom 11114 0 _IGG=true:=by decide+kernel
def _IGH:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada40000000000787de2121308ae89515e99d545850ef465f6480c82a4f620003
theorem shape6_74:validFrom 11113 0 _IGH=true:=by decide+kernel
def _IGI:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada00000000000787fcf1cdfc4064923de99d545850ef53206787af66cf270003
theorem shape6_75:validFrom 11112 0 _IGI=true:=by decide+kernel
def _IGJ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad9c00000000007881bc1b7cbad968f4de99d545850ef602845d087574eeb0003
theorem shape6_76:validFrom 11111 0 _IGJ=true:=by decide+kernel
def _IGK:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad9800000000007883a90de87cc8e8c45e99d545850ef6d76ff55aff20eac0003
theorem shape6_77:validFrom 11110 0 _IGK=true:=by decide+kernel
def _IGL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ca0f10b2be84bd54651230002
theorem shape6_78:validFrom 11109 0 _IGL=true:=by decide+kernel
def _IGM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c80f10f059c67281cd0ba0002
theorem shape6_79:validFrom 11108 0 _IGM=true:=by decide+kernel
def _IGO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c60f112df3822f1d5104e0002
theorem shape6_80:validFrom 11107 0 _IGO=true:=by decide+kernel
def _IGP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c40f116b8bb7c51f18fdf0002
theorem shape6_81:validFrom 11106 0 _IGP=true:=by decide+kernel
def _IGQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c20f11a92267909c34f6c0002
theorem shape6_82:validFrom 11105 0 _IGQ=true:=by decide+kernel
def _IGR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c00f11e6b7916388b4ef40002
theorem shape6_83:validFrom 11104 0 _IGR=true:=by decide+kernel
def _IGS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056be0f12244b353de554e7a0002
theorem shape6_84:validFrom 11103 0 _IGS=true:=by decide+kernel
def _IGT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056bc0f12611cca9a8b98dfc0002
theorem shape6_85:validFrom 11102 0 _IGT=true:=by decide+kernel
def _IGU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ba0f129a283af5d6bcd7b0002
theorem shape6_86:validFrom 11101 0 _IGU=true:=by decide+kernel
def _IGV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f12d3324775ca90cf60002
theorem shape6_87:validFrom 11100 0 _IGV=true:=by decide+kernel
def _IGW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f130c3af07675ecc6e0002
theorem shape6_88:validFrom 11099 0 _IGW=true:=by decide+kernel
def _IGX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f134542359bcd74be10002
theorem shape6_89:validFrom 11098 0 _IGX=true:=by decide+kernel
def _IGZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f137e481741da74b510002
theorem shape6_90:validFrom 11097 0 _IGZ=true:=by decide+kernel
def _IHA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b00f13b74c950c9500abd0002
theorem shape6_91:validFrom 11096 0 _IHA=true:=by decide+kernel
def _IHB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ae0f13f04faf580530a270002
theorem shape6_92:validFrom 11095 0 _IHB=true:=by decide+kernel
def _IHC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ac0f14295165c822c898d0002
theorem shape6_93:validFrom 11094 0 _IHC=true:=by decide+kernel
def _IHD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056aa0f146251b8b8f3188f00002
theorem shape6_94:validFrom 11093 0 _IHD=true:=by decide+kernel
def _IHE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a80f149b50a7ce73b484e0002
theorem shape6_95:validFrom 11092 0 _IHE=true:=by decide+kernel
def _IHF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a60f14d44e3336a62c7a90002
theorem shape6_96:validFrom 11091 0 _IHF=true:=by decide+kernel
def _IHG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a40f150d4a5b1f89486ff0002
theorem shape6_97:validFrom 11090 0 _IHG=true:=by decide+kernel
def _IHH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a20f1546451f2d20686520002
theorem shape6_98:validFrom 11089 0 _IHH=true:=by decide+kernel
def _IHI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a00f157f3e7fbb65305a20002
theorem shape6_99:validFrom 11088 0 _IHI=true:=by decide+kernel
def _IDE:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569e0f15b8367c6e5d084ef0002
theorem shape6_100:validFrom 11087 0 _IDE=true:=by decide+kernel
def _IDF:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569c0f15f12d15a203784390002
theorem shape6_101:validFrom 11086 0 _IDF=true:=by decide+kernel
def _IDG:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569a0f162a224afa5f0037f0002
theorem shape6_102:validFrom 11085 0 _IDG=true:=by decide+kernel
def _IDH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056980f1663161cd367182c10002
theorem shape6_103:validFrom 11084 0 _IDH=true:=by decide+kernel
def _IDI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056960f169c088ad127601ff0002
theorem shape6_104:validFrom 11083 0 _IDI=true:=by decide+kernel
def _IDJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056940f16d4f9954f91201390002
theorem shape6_105:validFrom 11082 0 _IDJ=true:=by decide+kernel
def _IDK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056920f170de93bf2b2b806f0002
theorem shape6_106:validFrom 11081 0 _IDK=true:=by decide+kernel
def _IDL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233bd0918bdca60790f1746d77f167e1c0020002
theorem shape6_107:validFrom 11080 0 _IDL=true:=by decide+kernel
def _IDM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3bcfadd85f83f510f177fc45e5f02bc0020002
theorem shape6_108:validFrom 11079 0 _IDM=true:=by decide+kernel
def _IDN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3bceca2a705f40f0f17b8afda282fc40020002
theorem shape6_109:validFrom 11078 0 _IDN=true:=by decide+kernel
def _IDP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bcde68210a7a250f17f199f216176c0020002
theorem shape6_110:validFrom 11077 0 _IDP=true:=by decide+kernel
def _IDQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bcd02df3eed6050f182a82a684a7ec0020002
theorem shape6_111:validFrom 11076 0 _IDQ=true:=by decide+kernel
def row6 (v:ℕ):List Piece:=match v with
 | 0=>d6_0
 | 1=>d6_1
 | 2=>d6_2
 | 3=>d6_3
 | 4=>d6_4
 | 5=>d6_5
 | 6=>d6_6
 | 7=>d6_7
 | 8=>d6_8
 | 9=>d6_9
 | 10=>_IDD
 | 11=>_IDO
 | 12=>_IDR
 | 13=>_IDS
 | 14=>_IDT
 | 15=>_IDU
 | 16=>_IDV
 | 17=>_IDW
 | 18=>_IDX
 | 19=>_IDY
 | 20=>_IEA
 | 21=>_IEB
 | 22=>_IEC
 | 23=>_IED
 | 24=>_IEE
 | 25=>_IEF
 | 26=>_IEG
 | 27=>_IEH
 | 28=>_IEI
 | 29=>_IEJ
 | 30=>_IEL
 | 31=>_IEM
 | 32=>_IEN
 | 33=>_IEO
 | 34=>_IEP
 | 35=>_IEQ
 | 36=>_IER
 | 37=>_IES
 | 38=>_IET
 | 39=>_IEU
 | 40=>_IEW
 | 41=>_IEX
 | 42=>_IEY
 | 43=>_IEZ
 | 44=>_IFA
 | 45=>_IFB
 | 46=>_IFC
 | 47=>_IFD
 | 48=>_IFE
 | 49=>_IFF
 | 50=>_IFH
 | 51=>_IFI
 | 52=>_IFJ
 | 53=>_IFK
 | 54=>_IFL
 | 55=>_IFM
 | 56=>_IFN
 | 57=>_IFO
 | 58=>_IFP
 | 59=>_IFQ
 | 60=>_IFS
 | 61=>_IFT
 | 62=>_IFU
 | 63=>_IFV
 | 64=>_IFW
 | 65=>_IFX
 | 66=>_IFY
 | 67=>_IFZ
 | 68=>_IGA
 | 69=>_IGB
 | 70=>_IGD
 | 71=>_IGE
 | 72=>_IGF
 | 73=>_IGG
 | 74=>_IGH
 | 75=>_IGI
 | 76=>_IGJ
 | 77=>_IGK
 | 78=>_IGL
 | 79=>_IGM
 | 80=>_IGO
 | 81=>_IGP
 | 82=>_IGQ
 | 83=>_IGR
 | 84=>_IGS
 | 85=>_IGT
 | 86=>_IGU
 | 87=>_IGV
 | 88=>_IGW
 | 89=>_IGX
 | 90=>_IGZ
 | 91=>_IHA
 | 92=>_IHB
 | 93=>_IHC
 | 94=>_IHD
 | 95=>_IHE
 | 96=>_IHF
 | 97=>_IHG
 | 98=>_IHH
 | 99=>_IHI
 | 100=>_IDE
 | 101=>_IDF
 | 102=>_IDG
 | 103=>_IDH
 | 104=>_IDI
 | 105=>_IDJ
 | 106=>_IDK
 | 107=>_IDL
 | 108=>_IDM
 | 109=>_IDN
 | 110=>_IDP
 | 111=>_IDQ
 | _=>[]
theorem checked6 (v:ℕ) (hy:6+v≤117):validFrom (11193-6-v) 0 (row6 v)=true:=by
 have hv:v≤111:=by omega
 interval_cases v
 · exact shape6_0
 · exact shape6_1
 · exact shape6_2
 · exact shape6_3
 · exact shape6_4
 · exact shape6_5
 · exact shape6_6
 · exact shape6_7
 · exact shape6_8
 · exact shape6_9
 · exact shape6_10
 · exact shape6_11
 · exact shape6_12
 · exact shape6_13
 · exact shape6_14
 · exact shape6_15
 · exact shape6_16
 · exact shape6_17
 · exact shape6_18
 · exact shape6_19
 · exact shape6_20
 · exact shape6_21
 · exact shape6_22
 · exact shape6_23
 · exact shape6_24
 · exact shape6_25
 · exact shape6_26
 · exact shape6_27
 · exact shape6_28
 · exact shape6_29
 · exact shape6_30
 · exact shape6_31
 · exact shape6_32
 · exact shape6_33
 · exact shape6_34
 · exact shape6_35
 · exact shape6_36
 · exact shape6_37
 · exact shape6_38
 · exact shape6_39
 · exact shape6_40
 · exact shape6_41
 · exact shape6_42
 · exact shape6_43
 · exact shape6_44
 · exact shape6_45
 · exact shape6_46
 · exact shape6_47
 · exact shape6_48
 · exact shape6_49
 · exact shape6_50
 · exact shape6_51
 · exact shape6_52
 · exact shape6_53
 · exact shape6_54
 · exact shape6_55
 · exact shape6_56
 · exact shape6_57
 · exact shape6_58
 · exact shape6_59
 · exact shape6_60
 · exact shape6_61
 · exact shape6_62
 · exact shape6_63
 · exact shape6_64
 · exact shape6_65
 · exact shape6_66
 · exact shape6_67
 · exact shape6_68
 · exact shape6_69
 · exact shape6_70
 · exact shape6_71
 · exact shape6_72
 · exact shape6_73
 · exact shape6_74
 · exact shape6_75
 · exact shape6_76
 · exact shape6_77
 · exact shape6_78
 · exact shape6_79
 · exact shape6_80
 · exact shape6_81
 · exact shape6_82
 · exact shape6_83
 · exact shape6_84
 · exact shape6_85
 · exact shape6_86
 · exact shape6_87
 · exact shape6_88
 · exact shape6_89
 · exact shape6_90
 · exact shape6_91
 · exact shape6_92
 · exact shape6_93
 · exact shape6_94
 · exact shape6_95
 · exact shape6_96
 · exact shape6_97
 · exact shape6_98
 · exact shape6_99
 · exact shape6_100
 · exact shape6_101
 · exact shape6_102
 · exact shape6_103
 · exact shape6_104
 · exact shape6_105
 · exact shape6_106
 · exact shape6_107
 · exact shape6_108
 · exact shape6_109
 · exact shape6_110
 · exact shape6_111
def d7_0:List Piece:=DZ.decode 58 42 0xa484aa4041ea9fa3941e5406abb25ea3aac58c7a557985d51bdf566caf64deb6fa3d51114823f993b96360003
theorem shape7_0:validFrom 11186 0 d7_0=true:=by decide+kernel
def d7_1:List Piece:=DZ.decode 58 42 0xa484aa4041eab1af7f68f0782bb15ea3aac58c7a5b4bc666114f8664af64deb6fa3d544d94d6ea43f96240003
theorem shape7_1:validFrom 11185 0 d7_1=true:=by decide+kernel
def d7_2:List Piece:=DZ.decode 58 42 0xa484aa4041eac3bb6ab38ce9abb05ea3aac58c7a611e06f706bfb65caf64deb6fa3d5789e189daf4396120003
theorem shape7_2:validFrom 11184 0 d7_2=true:=by decide+kernel
def d7_3:List Piece:=DZ.decode 58 42 0xa484aa4041ead5c755fe295b2baf5ea3aac58c7a66f04787fc2fe654af64deb6fa3d5ac62e3ccba4796000003
theorem shape7_3:validFrom 11183 0 d7_3=true:=by decide+kernel
def d7_4:List Piece:=DZ.decode 58 42 0xa484aa4041eae7aa201e35bc6bae5ea3aac58c7a6cc28818f1a0164c6f64deb6fa3d5e027aefbc54b95ee0003
theorem shape7_4:validFrom 11182 0 d7_4=true:=by decide+kernel
def d7_5:List Piece:=DZ.decode 58 42 0xa484aa4041eaf9b60b68d22debad5ea3aac58c7a7294c8a9e71046446f64deb6fa3d613ec7a2ad04f95dc0003
theorem shape7_5:validFrom 11181 0 d7_5=true:=by decide+kernel
def d7_6:List Piece:=DZ.decode 58 42 0xa484aa4041eb0bc1f6b36e9f6bac5ea3aac58c7a7867093adc80763c6f64deb6fa3d647b14559db5395ca0003
theorem shape7_6:validFrom 11180 0 d7_6=true:=by decide+kernel
def d7_7:List Piece:=DZ.decode 58 42 0xa484aa4041eb1da4c0d37b00abab5ea3aac58c7a7e3949cbd1f0a6342f64deb6fa3d67b761088e65795b80003
theorem shape7_7:validFrom 11179 0 d7_7=true:=by decide+kernel
def d7_8:List Piece:=DZ.decode 58 42 0xa484aa4041eb2fb0ac1e17722baa5ea3aac58c7a83f3e17215fdc62c2f64deb6fa3d6af3adbb7f15b95a50003
theorem shape7_8:validFrom 11178 0 d7_8=true:=by decide+kernel
def d7_9:List Piece:=DZ.decode 58 42 0xa484aa4041eb41bc9768b3e3aba95ea3aac58c7a89ae79185a0ae6242f64deb6fa3d6e2ffa6e6fc5f95920003
theorem shape7_9:validFrom 11177 0 d7_9=true:=by decide+kernel
def _IHL:List Piece:=DZ.decode 58 42 0xa484aa4041eb539f6188c044eba85ea3aac58c7a8f80b9a94f7b161bef64deb6fa3d716c47216076395800003
theorem shape7_10:validFrom 11176 0 _IHL=true:=by decide+kernel
def _IHW:List Piece:=DZ.decode 58 42 0xa484aa4041eb65ab4cd35cb66ba75ea3aac58c7a953b514f93883613ef64deb6fa3d74a893d451267956d0003
theorem shape7_11:validFrom 11175 0 _IHW=true:=by decide+kernel
def _IHY:List Piece:=DZ.decode 58 42 0xa484aa4041eb77b7381df927eba65ea3aac58c7a9af5e8f5d795560bef64deb6fa3d77e4e08741d6b955a0003
theorem shape7_12:validFrom 11174 0 _IHY=true:=by decide+kernel
def _IHZ:List Piece:=DZ.decode 58 42 0xa484aa4041eb899a023e05892ba55ea3aac58c7aa0b0809c1ba27603af64deb6fa3d7b212d3a3286f95470003
theorem shape7_13:validFrom 11173 0 _IHZ=true:=by decide+kernel
def _IIA:List Piece:=DZ.decode 58 42 0xa484aa4041eb9ba5ed88a1faaba45ea3aac58c7aa6536f57ae4c85fbaf64deb6fa3d7e5d79ed2337395330003
theorem shape7_14:validFrom 11172 0 _IIA=true:=by decide+kernel
def _IIB:List Piece:=DZ.decode 58 42 0xa484aa4041eb987cbee0f60b2ba35ea3aac58c7ab2ec65bdd91395d2af64deb6fa3d8199c6a013e7795200003
theorem shape7_15:validFrom 11171 0 _IIB=true:=by decide+kernel
def _IIC:List Piece:=DZ.decode 58 42 0xa484aa4041eba991e32c321b2ba25ea3aac58c7ab8feb3bda522c5c92f64deb6fa3d84d613530497b950d0003
theorem shape7_16:validFrom 11170 0 _IIC=true:=by decide+kernel
def _IID:List Piece:=DZ.decode 58 42 0xa484aa4041ebba7de64cde1aeba15ea3aac58c7abef958d2bfcee5bf6f64deb6fa3d88126005f547f94f90003
theorem shape7_17:validFrom 11169 0 _IID=true:=by decide+kernel
def _IIE:List Piece:=DZ.decode 58 42 0xa484aa4041ebd09953d5ebaf2ba05ea3aac58c7ac4f3fde7da7b05b92f64deb6fa3d8b4eacb8e5f8394e50003
theorem shape7_18:validFrom 11168 0 _IIE=true:=by decide+kernel
def _IIF:List Piece:=DZ.decode 58 42 0xa484aa4041ebe18556f697aeeb9f5ea3aac58c7acaeea2fcf52725af6f64deb6fa3d8e8af96bd6a8794d10003
theorem shape7_19:validFrom 11167 0 _IIF=true:=by decide+kernel
def _IIH:List Piece:=DZ.decode 58 42 0xa484aa4041ebf2715a1743aeab9e5ea3aac58c7ad0e948120fd345a5af64deb6fa3d91c7461ec758b94bd0003
theorem shape7_20:validFrom 11166 0 _IIH=true:=by decide+kernel
def _III:List Piece:=DZ.decode 58 42 0xa484aa4041ec5d2f2652a517ab9d5ea3aac58c7ad6e3ed272a7f65d8af64deb6fa3d950392d1b808f94a90003
theorem shape7_21:validFrom 11165 0 _III=true:=by decide+kernel
def _IIJ:List Piece:=DZ.decode 58 42 0xa484aa4041ecae6e45ffcd066b9c5ea3aac58c7adcc6e95193c875fa6f64deb6fa3d983fdf84a8b9394940003
theorem shape7_22:validFrom 11164 0 _IIJ=true:=by decide+kernel
def _IIK:List Piece:=DZ.decode 58 42 0xa484aa4041ecbf836a4b09166b9b5ea3aac58c7ae2c18e66ae7495f0ef64deb6fa3d9b7c2c379969794800003
theorem shape7_23:validFrom 11163 0 _IIK=true:=by decide+kernel
def _IIL:List Piece:=DZ.decode 58 42 0xa484aa4041ecd06f6d6bb5162b9a5ea3aac58c7ae8a48a9117bda5e72f64deb6fa3d9eb878ea8a19b946b0003
theorem shape7_24:validFrom 11162 0 _IIL=true:=by decide+kernel
def _IIM:List Piece:=DZ.decode 58 42 0xa484aa4041ece15b708c6115eb995ea3aac58c7aee8786bb8106b5dd6f64deb6fa3da1f4c59d7ac9f94560003
theorem shape7_25:validFrom 11161 0 _IIM=true:=by decide+kernel
def _IIN:List Piece:=DZ.decode 58 42 0xa484aa4041ecf24773ad0d15ab985ea3aac58c7af46a82e5ea4fc5d3af64deb6fa3da53112506b7a394410003
theorem shape7_26:validFrom 11160 0 _IIN=true:=by decide+kernel
def _IIO:List Piece:=DZ.decode 58 42 0xa484aa4041ed033376cdb9156b975ea3aac58c7afa4d7f105398d5c9ef64deb6fa3da86d5f035c2a7942c0003
theorem shape7_27:validFrom 11159 0 _IIO=true:=by decide+kernel
def _IIP:List Piece:=DZ.decode 58 42 0xa484aa4041ed141f79ee65152b965ea3aac58c7b00307b3abce1e5c02f64deb6fa3daba9abb64cdab94170003
theorem shape7_28:validFrom 11158 0 _IIP=true:=by decide+kernel
def _IIQ:List Piece:=DZ.decode 58 42 0xa484aa4041ed250b7d0f1114eb955ea3aac58c7b05fbce7a74c7e5b66f64deb6fa3daee5f8693d8af94010003
theorem shape7_29:validFrom 11157 0 _IIQ=true:=by decide+kernel
def _IIS:List Piece:=DZ.decode 58 42 0xa484aa4041ed3620a15a4d24eb945ea3aac58c7b0bc721ba2cade5acef64deb6fa3db222451c2e3b393eb0003
theorem shape7_30:validFrom 11156 0 _IIS=true:=by decide+kernel
def _IIT:List Piece:=DZ.decode 58 42 0xa484aa4041ed470ca47af924ab935ea3aac58c7b119274f9e493e5a32f64deb6fa3db55e91cf1eeb793d50003
theorem shape7_31:validFrom 11155 0 _IIT=true:=by decide+kernel
def _IIU:List Piece:=DZ.decode 58 42 0xa484aa4041ed57f8a79ba5246b925ea3aac58c7b175dc8399c79e5996f64deb6fa3db89ade820f9bb93bf0003
theorem shape7_32:validFrom 11154 0 _IIU=true:=by decide+kernel
def _IIV:List Piece:=DZ.decode 58 42 0xa484aa4041ed68e4aabc51242b915ea3aac58c7b1d291b79545fe58faf64deb6fa3dbbd72b35004bf93a90003
theorem shape7_33:validFrom 11153 0 _IIV=true:=by decide+kernel
def _IIW:List Piece:=DZ.decode 58 42 0xa484aa4041ed79d0addcfd23eb905ea3aac58c7b22dcc5ce5ae2d585ef64deb6fa3dbf1377e7f0fc393920003
theorem shape7_34:validFrom 11152 0 _IIW=true:=by decide+kernel
def _IIX:List Piece:=DZ.decode 58 42 0xa484aa4041ed8abcb0fda923ab8f5ea3aac58c7b28a8190e12c8d57c2f64deb6fa3dc24fc49ae1ac7937c0003
theorem shape7_35:validFrom 11151 0 _IIX=true:=by decide+kernel
def _IIY:List Piece:=DZ.decode 58 42 0xa484aa4041ed9ba8b41e55236b8e5ea3aac58c7b2e5bc363194bc5726f64deb6fa3dc58c114dd25cb93650003
theorem shape7_36:validFrom 11150 0 _IIY=true:=by decide+kernel
def _IIZ:List Piece:=DZ.decode 58 42 0xa484aa4041edacbdd86991336b8d5ea3aac58c7b33f7c4cd6e6ba568ef64deb6fa3dc8c85e00c30cf934d0003
theorem shape7_37:validFrom 11149 0 _IIZ=true:=by decide+kernel
def _IJA:List Piece:=DZ.decode 58 42 0xa484aa4041edbda9db8a3d332b8c5ea3aac58c7b39ab6f2274ee955f2f64deb6fa3dcc04aab3b3bd393360003
theorem shape7_38:validFrom 11148 0 _IJA=true:=by decide+kernel
def _IJB:List Piece:=DZ.decode 58 42 0xa484aa4041edce95deaae932eb8b5ea3aac58c7b3f47708cca0e75556f64deb6fa3dcf40f766a46d7931e0003
theorem shape7_39:validFrom 11147 0 _IJB=true:=by decide+kernel
def _IJD:List Piece:=DZ.decode 58 42 0xa484aa4041eddf81e1cb9532ab8a5ea3aac58c7b44e371f71f2e554baf64deb6fa3dd27d4419951db93060003
theorem shape7_40:validFrom 11146 0 _IJD=true:=by decide+kernel
def _IJE:List Piece:=DZ.decode 58 42 0xa484aa4041edf06de4ec41326b895ea3aac58c7b4a7f7361744e3541ef64deb6fa3dd5b990cc85cdf92ee0003
theorem shape7_41:validFrom 11145 0 _IJE=true:=by decide+kernel
def _IJF:List Piece:=DZ.decode 58 42 0xa484aa4041ee0159e80ced322b885ea3aac58c7b5003cbe1180b05382f64deb6fa3dd8f5dd7f767e392d50003
theorem shape7_42:validFrom 11144 0 _IJF=true:=by decide+kernel
def _IJG:List Piece:=DZ.decode 58 42 0xa484aa4041ee1245eb2d9931eb875ea3aac58c7b559fcd4b6d2ae52e6f64deb6fa3ddc322a32672e792bd0003
theorem shape7_43:validFrom 11143 0 _IJG=true:=by decide+kernel
def _IJH:List Piece:=DZ.decode 58 42 0xa484aa4041ee235b0f78d541eb865ea3aac58c7b5b2425cb10e7b524ef64deb6fa3ddf6e76e557deb92a40003
theorem shape7_44:validFrom 11142 0 _IJH=true:=by decide+kernel
def _IJI:List Piece:=DZ.decode 58 42 0xa484aa4041ee344712998141ab855ea3aac58c7b6090d5600341751b2f64deb6fa3de2aac398488ef928a0003
theorem shape7_45:validFrom 11141 0 _IJI=true:=by decide+kernel
def _IJJ:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae10a484aa40410ee453315ba2d416b1b5ea3aac58c43b66152ddfa6fe45116f64deb6fa30de5e7104b393f392710004
theorem shape7_46:validFrom 11140 0 _IJJ=true:=by decide+kernel
def _IJK:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae0ca484aa40410ee561f18dad9412a525ea3aac58c43b6b81dd7499580507af64deb6fa30de9235cfe29ef792570004
theorem shape7_47:validFrom 11139 0 _IJK=true:=by decide+kernel
def _IJL:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae08a484aa40410ee670b1bfb8540e97d5ea3aac58c43b70d6e41eda4eb4fdef64deb6fa30dec5fa9b11a9fb923c0004
theorem shape7_48:validFrom 11138 0 _IJL=true:=by decide+kernel
def _IJM:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae04a484aa40410ee77f71f1c3140a89b5ea3aac58c43b764393b3cca874f42f64deb6fa30def9bf6640b4ff92220004
theorem shape7_49:validFrom 11137 0 _IJM=true:=by decide+kernel
def _IJO:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae00a484aa40410ee88e3223cdd4067ac5ea3aac58c43b7b989a5e0d9f24ea6f64deb6fa30df2d84316fc00392070004
theorem shape7_50:validFrom 11136 0 _IJO=true:=by decide+kernel
def _IJP:List Piece:=DZ.decode 62 42 0x3782dace9d900000adfca484aa40410ee99f84688195066b05ea3aac58c43b80d5f81d9d32c4e0ef64deb6fa30df6148fc9ecb0791eb0004
theorem shape7_51:validFrom 11135 0 _IJP=true:=by decide+kernel
def _IJQ:List Piece:=DZ.decode 62 41 0x3782dace9d900000adf949095480821dd55c893518aa04b4d7a8eab16310e782e8a940a671d35c0003
theorem shape7_52:validFrom 11134 0 _IJQ=true:=by decide+kernel
def _IJR:List Piece:=DZ.decode 62 41 0x3782dace9d900000adf549095480821dd77a09992e29fc91f7a8eab16310e7a23806ec801753350003
theorem shape7_53:validFrom 11133 0 _IJR=true:=by decide+kernel
def _IJS:List Piece:=DZ.decode 62 41 0x3782dace9d900000adf149095480821dc5f37369f7e7646d57a8eab16310e88dec8ce83dd4cf3c0003
theorem shape7_54:validFrom 11132 0 _IJS=true:=by decide+kernel
def _IJT:List Piece:=DZ.decode 62 41 0x3782dace9d900000aded49095480821dc834f0d34b75944717a8eab16310e8abdd112df7720f1c0003
theorem shape7_55:validFrom 11131 0 _IJT=true:=by decide+kernel
def _IJU:List Piece:=DZ.decode 62 41 0x3782dace9d900000ade949095480821dca714a174d01bc1f17a8eab16310e8c9cd9573b10f4efb0003
theorem shape7_56:validFrom 11130 0 _IJU=true:=by decide+kernel
def _IJV:List Piece:=DZ.decode 62 41 0x3782dace9d900000ade549095480821dccb2c780a08febf577a8eab16310e8e7be19b96aac8edb0003
theorem shape7_57:validFrom 11129 0 _IJV=true:=by decide+kernel
def _IJW:List Piece:=DZ.decode 62 41 0x3782dace9d900000ade149095480821dcef444e9f41e1bca17a8eab16310e905ae9dff2449cebb0003
theorem shape7_58:validFrom 11128 0 _IJW=true:=by decide+kernel
def _IJX:List Piece:=DZ.decode 62 41 0x3782dace9d900000addd49095480821de0a9913c116fd39d17a8eab16310e9239f2244dde70fe90003
theorem shape7_59:validFrom 11127 0 _IJX=true:=by decide+kernel
def _IJZ:List Piece:=DZ.decode 62 41 0x3782dace9d900000add949095480821de2eb0ea564fe036e37a8eab16310e9418fa68a97844fc90003
theorem shape7_60:validFrom 11126 0 _IJZ=true:=by decide+kernel
def _IKA:List Piece:=DZ.decode 62 41 0x3782dace9d900000add549095480821de52c8c0eb88c333dd7a8eab16310e95f802ad051218fa90003
theorem shape7_61:validFrom 11125 0 _IKA=true:=by decide+kernel
def _IKB:List Piece:=DZ.decode 62 41 0x3782dace9d900000add149095480821de768e552ba185b0b97a8eab16310e97d70af160abecf880003
theorem shape7_62:validFrom 11124 0 _IKB=true:=by decide+kernel
def _IKC:List Piece:=DZ.decode 62 41 0x3782dace9d900000adcd49095480821de9aa62bc0da68ad7b7a8eab16310e99b61335bc45c0f680003
theorem shape7_63:validFrom 11123 0 _IKC=true:=by decide+kernel
def _IKD:List Piece:=DZ.decode 62 41 0x3782dace9d900000adc949095480821debebe0256134baa217a8eab16310e9b951b7a17df94f480003
theorem shape7_64:validFrom 11122 0 _IKD=true:=by decide+kernel
def _IKE:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7100000000000f0e9e308abbbd49476a484aa40410ed312966d85f24d3560003
theorem shape7_65:validFrom 11121 0 _IKE=true:=by decide+kernel
def _IKF:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7000000000000f0edaed2690cd81434a484aa40410eeb1106a14b17e518dbd33aa8b090ed68bcb8ab42cc06f10004
theorem shape7_66:validFrom 11120 0 _IKF=true:=by decide+kernel
def _IKG:List Piece:=DZ.decode 62 39 0x3782dace9d900000adbc00000000007878bd42015cf089f7de99d545850ef1b4ed12f1a7210310003
theorem shape7_67:validFrom 11119 0 _IKG=true:=by decide+kernel
def _IKH:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb80000000000787aa30ebf31f2c9d3de99d545850ef2657a29f874a50020003
theorem shape7_68:validFrom 11118 0 _IKH=true:=by decide+kernel
def _IKI:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb40000000000787c88cf6c9d32c9adde99d545850ef318fa91878eacfd20003
theorem shape7_69:validFrom 11117 0 _IKI=true:=by decide+kernel
def _IKK:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb00000000000787e6e84083685a9865e99d545850ef3d263184920bcf9f0003
theorem shape7_70:validFrom 11116 0 _IKK=true:=by decide+kernel
def _IKL:List Piece:=DZ.decode 62 39 0x3782dace9d900000adac00000000007880542c94ce46095d5e99d545850ef491b3be692238f6a0003
theorem shape7_71:validFrom 11115 0 _IKL=true:=by decide+kernel
def _IKM:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada80000000000788239c90f942429325e99d545850ef555721c3a8f84f330003
theorem shape7_72:validFrom 11114 0 _IKM=true:=by decide+kernel
def _IKN:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada4000000000078841f597b58650905de99d545850ef61d9e31e95ebcef90003
theorem shape7_73:validFrom 11113 0 _IKN=true:=by decide+kernel
def _IKO:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada00000000000788604ddd6b2de68d75e99d545850ef6ebb266f69cacebd0003
theorem shape7_74:validFrom 11112 0 _IKO=true:=by decide+kernel
def _IKP:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad9c00000000007887ea56203b9008a6de99d545850ef7bfaebb0a5d38e7f0003
theorem shape7_75:validFrom 11111 0 _IKP=true:=by decide+kernel
def _IKQ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad9800000000007889cfc25ac289c874de99d545850ef90f494cb4e1d4e3e0003
theorem shape7_76:validFrom 11110 0 _IKQ=true:=by decide+kernel
def _IKR:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad940000000000788bb5228377c6c8415e99d545850ef9f587ab4014ecdfa0003
theorem shape7_77:validFrom 11109 0 _IKR=true:=by decide+kernel
def _IKS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c80f11b34ed3a568250170002
theorem shape7_78:validFrom 11108 0 _IKS=true:=by decide+kernel
def _IKT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c60f11eff7d4ce9fc8fa80002
theorem shape7_79:validFrom 11107 0 _IKT=true:=by decide+kernel
def _IKV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c40f122c9f53bda088f360002
theorem shape7_80:validFrom 11106 0 _IKV=true:=by decide+kernel
def _IKW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c20f12694550cc6840ec10002
theorem shape7_81:validFrom 11105 0 _IKW=true:=by decide+kernel
def _IKX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c00f12a5e9cba0fb14e470002
theorem shape7_82:validFrom 11104 0 _IKX=true:=by decide+kernel
def _IKY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056be0f12e28cc4955230dca0002
theorem shape7_83:validFrom 11103 0 _IKY=true:=by decide+kernel
def _IKZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056bc0f131e7248920a9cd4a0002
theorem shape7_84:validFrom 11102 0 _IKZ=true:=by decide+kernel
def _ILA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ba0f1356a8a2fa849ccc60002
theorem shape7_85:validFrom 11101 0 _ILA=true:=by decide+kernel
def _ILB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f138edd9ca304a4c3f0002
theorem shape7_86:validFrom 11100 0 _ILB=true:=by decide+kernel
def _ILC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f13c71135e58084bb40002
theorem shape7_87:validFrom 11099 0 _ILC=true:=by decide+kernel
def _ILD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f13ff436e680470b260002
theorem shape7_88:validFrom 11098 0 _ILD=true:=by decide+kernel
def _ILE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f14377446848230a930002
theorem shape7_89:validFrom 11097 0 _ILE=true:=by decide+kernel
def _ILG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b00f146fa3bde109589fd0002
theorem shape7_90:validFrom 11096 0 _ILG=true:=by decide+kernel
def _ILH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ae0f14a7d1d4d788f89640002
theorem shape7_91:validFrom 11095 0 _ILH=true:=by decide+kernel
def _ILI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ac0f14dffe8b0e13588c80002
theorem shape7_92:validFrom 11094 0 _ILI=true:=by decide+kernel
def _ILJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056aa0f151829e0de94dc8280002
theorem shape7_93:validFrom 11093 0 _ILJ=true:=by decide+kernel
def _ILK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a80f155053d5ef22747840002
theorem shape7_94:validFrom 11092 0 _ILK=true:=by decide+kernel
def _ILL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a60f15887c6a6cb1fc6dd0002
theorem shape7_95:validFrom 11091 0 _ILL=true:=by decide+kernel
def _ILM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a40f15c0a39e8436b06310002
theorem shape7_96:validFrom 11090 0 _ILM=true:=by decide+kernel
def _ILN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a20f15f8c971dbc9705820002
theorem shape7_97:validFrom 11089 0 _ILN=true:=by decide+kernel
def _ILO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a00f1630ede4cd50004cf0002
theorem shape7_98:validFrom 11088 0 _ILO=true:=by decide+kernel
def _ILP:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569e0f166910f6fee5504190002
theorem shape7_99:validFrom 11087 0 _ILP=true:=by decide+kernel
def _IHM:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569c0f16a132a8ca6dc43610002
theorem shape7_100:validFrom 11086 0 _IHM=true:=by decide+kernel
def _IHN:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569a0f16d952f9d606f82a40002
theorem shape7_101:validFrom 11085 0 _IHN=true:=by decide+kernel
def _IHO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056980f171171ea7b8f981e40002
theorem shape7_102:validFrom 11084 0 _IHO=true:=by decide+kernel
def _IHP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056960f17498f7a612c041200002
theorem shape7_103:validFrom 11083 0 _IHP=true:=by decide+kernel
def _IHQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056940f1781aba9e0b8340580002
theorem shape7_104:validFrom 11082 0 _IHQ=true:=by decide+kernel
def _IHR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273bcec5cff67ea0a0f17b9c678a057d80020002
theorem shape7_105:validFrom 11081 0 _IHR=true:=by decide+kernel
def _IHS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233bcde56a3d186850f17f1dfe6f9e5ec0020002
theorem shape7_106:validFrom 11080 0 _IHS=true:=by decide+kernel
def _IHT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3bcd050a06b1dce0f1829f7f49388c80020002
theorem shape7_107:validFrom 11079 0 _IHT=true:=by decide+kernel
def _IHU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3bcc24af51e39d00f18620ea1c718c00020002
theorem shape7_108:validFrom 11078 0 _IHU=true:=by decide+kernel
def _IHV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bcb445a201504b0f189a23ee3abed40020002
theorem shape7_109:validFrom 11077 0 _IHV=true:=by decide+kernel
def _IHX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bca640a6fdebd50f18d237da4850ac0020002
theorem shape7_110:validFrom 11076 0 _IHX=true:=by decide+kernel
def row7 (v:ℕ):List Piece:=match v with
 | 0=>d7_0
 | 1=>d7_1
 | 2=>d7_2
 | 3=>d7_3
 | 4=>d7_4
 | 5=>d7_5
 | 6=>d7_6
 | 7=>d7_7
 | 8=>d7_8
 | 9=>d7_9
 | 10=>_IHL
 | 11=>_IHW
 | 12=>_IHY
 | 13=>_IHZ
 | 14=>_IIA
 | 15=>_IIB
 | 16=>_IIC
 | 17=>_IID
 | 18=>_IIE
 | 19=>_IIF
 | 20=>_IIH
 | 21=>_III
 | 22=>_IIJ
 | 23=>_IIK
 | 24=>_IIL
 | 25=>_IIM
 | 26=>_IIN
 | 27=>_IIO
 | 28=>_IIP
 | 29=>_IIQ
 | 30=>_IIS
 | 31=>_IIT
 | 32=>_IIU
 | 33=>_IIV
 | 34=>_IIW
 | 35=>_IIX
 | 36=>_IIY
 | 37=>_IIZ
 | 38=>_IJA
 | 39=>_IJB
 | 40=>_IJD
 | 41=>_IJE
 | 42=>_IJF
 | 43=>_IJG
 | 44=>_IJH
 | 45=>_IJI
 | 46=>_IJJ
 | 47=>_IJK
 | 48=>_IJL
 | 49=>_IJM
 | 50=>_IJO
 | 51=>_IJP
 | 52=>_IJQ
 | 53=>_IJR
 | 54=>_IJS
 | 55=>_IJT
 | 56=>_IJU
 | 57=>_IJV
 | 58=>_IJW
 | 59=>_IJX
 | 60=>_IJZ
 | 61=>_IKA
 | 62=>_IKB
 | 63=>_IKC
 | 64=>_IKD
 | 65=>_IKE
 | 66=>_IKF
 | 67=>_IKG
 | 68=>_IKH
 | 69=>_IKI
 | 70=>_IKK
 | 71=>_IKL
 | 72=>_IKM
 | 73=>_IKN
 | 74=>_IKO
 | 75=>_IKP
 | 76=>_IKQ
 | 77=>_IKR
 | 78=>_IKS
 | 79=>_IKT
 | 80=>_IKV
 | 81=>_IKW
 | 82=>_IKX
 | 83=>_IKY
 | 84=>_IKZ
 | 85=>_ILA
 | 86=>_ILB
 | 87=>_ILC
 | 88=>_ILD
 | 89=>_ILE
 | 90=>_ILG
 | 91=>_ILH
 | 92=>_ILI
 | 93=>_ILJ
 | 94=>_ILK
 | 95=>_ILL
 | 96=>_ILM
 | 97=>_ILN
 | 98=>_ILO
 | 99=>_ILP
 | 100=>_IHM
 | 101=>_IHN
 | 102=>_IHO
 | 103=>_IHP
 | 104=>_IHQ
 | 105=>_IHR
 | 106=>_IHS
 | 107=>_IHT
 | 108=>_IHU
 | 109=>_IHV
 | 110=>_IHX
 | _=>[]
theorem checked7 (v:ℕ) (hy:7+v≤117):validFrom (11193-7-v) 0 (row7 v)=true:=by
 have hv:v≤110:=by omega
 interval_cases v
 · exact shape7_0
 · exact shape7_1
 · exact shape7_2
 · exact shape7_3
 · exact shape7_4
 · exact shape7_5
 · exact shape7_6
 · exact shape7_7
 · exact shape7_8
 · exact shape7_9
 · exact shape7_10
 · exact shape7_11
 · exact shape7_12
 · exact shape7_13
 · exact shape7_14
 · exact shape7_15
 · exact shape7_16
 · exact shape7_17
 · exact shape7_18
 · exact shape7_19
 · exact shape7_20
 · exact shape7_21
 · exact shape7_22
 · exact shape7_23
 · exact shape7_24
 · exact shape7_25
 · exact shape7_26
 · exact shape7_27
 · exact shape7_28
 · exact shape7_29
 · exact shape7_30
 · exact shape7_31
 · exact shape7_32
 · exact shape7_33
 · exact shape7_34
 · exact shape7_35
 · exact shape7_36
 · exact shape7_37
 · exact shape7_38
 · exact shape7_39
 · exact shape7_40
 · exact shape7_41
 · exact shape7_42
 · exact shape7_43
 · exact shape7_44
 · exact shape7_45
 · exact shape7_46
 · exact shape7_47
 · exact shape7_48
 · exact shape7_49
 · exact shape7_50
 · exact shape7_51
 · exact shape7_52
 · exact shape7_53
 · exact shape7_54
 · exact shape7_55
 · exact shape7_56
 · exact shape7_57
 · exact shape7_58
 · exact shape7_59
 · exact shape7_60
 · exact shape7_61
 · exact shape7_62
 · exact shape7_63
 · exact shape7_64
 · exact shape7_65
 · exact shape7_66
 · exact shape7_67
 · exact shape7_68
 · exact shape7_69
 · exact shape7_70
 · exact shape7_71
 · exact shape7_72
 · exact shape7_73
 · exact shape7_74
 · exact shape7_75
 · exact shape7_76
 · exact shape7_77
 · exact shape7_78
 · exact shape7_79
 · exact shape7_80
 · exact shape7_81
 · exact shape7_82
 · exact shape7_83
 · exact shape7_84
 · exact shape7_85
 · exact shape7_86
 · exact shape7_87
 · exact shape7_88
 · exact shape7_89
 · exact shape7_90
 · exact shape7_91
 · exact shape7_92
 · exact shape7_93
 · exact shape7_94
 · exact shape7_95
 · exact shape7_96
 · exact shape7_97
 · exact shape7_98
 · exact shape7_99
 · exact shape7_100
 · exact shape7_101
 · exact shape7_102
 · exact shape7_103
 · exact shape7_104
 · exact shape7_105
 · exact shape7_106
 · exact shape7_107
 · exact shape7_108
 · exact shape7_109
 · exact shape7_110
end EP

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace EP
open DZ
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def d8_0:List Piece:=DZ.decode 58 42 0xa484aa4041eaff1a21fd29b56bb15ea3aac58c7a7569b3343cb6c6416f64deb6fa3d62512fb0d522a15e00003
theorem shape8_0:validFrom 11185 0 d8_0=true:=by decide+kernel
def d8_1:List Piece:=DZ.decode 58 42 0xa484aa4041eb11260d47c626ebb05ea3aac58c7a7b3bf3c53226f6396f64deb6fa3d658d7c63c5d2e15ce0003
theorem shape8_1:validFrom 11184 0 d8_1=true:=by decide+kernel
def d8_2:List Piece:=DZ.decode 58 42 0xa484aa4041eb2308d767d2882baf5ea3aac58c7a810e3456279726312f64deb6fa3d68c9c916b683215bc0003
theorem shape8_2:validFrom 11183 0 d8_2=true:=by decide+kernel
def d8_3:List Piece:=DZ.decode 58 42 0xa484aa4041eb3514c2b26ef9abae5ea3aac58c7a86e074e71d0756292f64deb6fa3d6c0615c9a733615aa0003
theorem shape8_3:validFrom 11182 0 d8_3=true:=by decide+kernel
def d8_4:List Piece:=DZ.decode 58 42 0xa484aa4041eb4720adfd0b6b2bad5ea3aac58c7a8cb2b578127786212f64deb6fa3d6f42627c97e3a15980003
theorem shape8_4:validFrom 11181 0 d8_4=true:=by decide+kernel
def d8_5:List Piece:=DZ.decode 58 42 0xa484aa4041eb5903781d17cc6bac5ea3aac58c7a926d4d1e5684a618ef64deb6fa3d727eaf2f8893e15850003
theorem shape8_5:validFrom 11180 0 d8_5=true:=by decide+kernel
def d8_6:List Piece:=DZ.decode 58 42 0xa484aa4041eb6b0f6367b43debab5ea3aac58c7a983f8daf4bf4d610ef64deb6fa3d75bafbe27944215730003
theorem shape8_6:validFrom 11179 0 d8_6=true:=by decide+kernel
def d8_7:List Piece:=DZ.decode 58 42 0xa484aa4041eb7d1b4eb250af6baa5ea3aac58c7a9dfa25559001f608ef64deb6fa3d78f7489569f4615600003
theorem shape8_7:validFrom 11178 0 d8_7=true:=by decide+kernel
def d8_8:List Piece:=DZ.decode 58 42 0xa484aa4041eb8efe18d25d10aba95ea3aac58c7aa3b4bcfbd40f1600af64deb6fa3d7c3395485aa4a154d0003
theorem shape8_8:validFrom 11177 0 d8_8=true:=by decide+kernel
def d8_9:List Piece:=DZ.decode 58 42 0xa484aa4041eba10a041cf9822ba85ea3aac58c7aa96f54a2181c35f8af64deb6fa3d7f6fe1fb4b54e153a0003
theorem shape8_9:validFrom 11176 0 d8_9=true:=by decide+kernel
def _ILS:List Piece:=DZ.decode 58 42 0xa484aa4041ebb315ef6795f3aba75ea3aac58c7aaf29ec485c2955f0af64deb6fa3d82ac2eae3c05215270003
theorem shape8_10:validFrom 11175 0 _ILS=true:=by decide+kernel
def _IMD:List Piece:=DZ.decode 58 42 0xa484aa4041ebc4f8b987a254eba65ea3aac58c7ab4e483eea03675e86f64deb6fa3d85e87b612cb5615140003
theorem shape8_11:validFrom 11174 0 _IMD=true:=by decide+kernel
def _IME:List Piece:=DZ.decode 58 42 0xa484aa4041ebd704a4d23ec66ba55ea3aac58c7aba9f1b94e44395e06f64deb6fa3d8924c8141d65a15010003
theorem shape8_12:validFrom 11173 0 _IME=true:=by decide+kernel
def _IMF:List Piece:=DZ.decode 58 42 0xa484aa4041ebe910901cdb37eba45ea3aac58c7ac059b33b2850b5d86f64deb6fa3d8c6114c70e15e14ee0003
theorem shape8_13:validFrom 11172 0 _IMF=true:=by decide+kernel
def _IMG:List Piece:=DZ.decode 58 42 0xa484aa4041ebfb1c7b6777a96ba35ea3aac58c7ac5fca1f6bafac5d06f64deb6fa3d8f9d6179fec6214da0003
theorem shape8_14:validFrom 11171 0 _IMG=true:=by decide+kernel
def _IMH:List Piece:=DZ.decode 58 42 0xa484aa4041ebf253c3ee19812ba25ea3aac58c7ad4627bc46e96159eaf64deb6fa3d92d9ae2cef76614c70003
theorem shape8_15:validFrom 11170 0 _IMH=true:=by decide+kernel
def _IMI:List Piece:=DZ.decode 58 42 0xa484aa4041ec0368e83955912ba15ea3aac58c7ada5d20d9894235952f64deb6fa3d9615fadfe026a14b30003
theorem shape8_16:validFrom 11169 0 _IMI=true:=by decide+kernel
def _IMJ:List Piece:=DZ.decode 58 42 0xa484aa4041ec1454eb5a0190eba05ea3aac58c7ae057c5eea3ee558b6f64deb6fa3d99524792d0d6e149f0003
theorem shape8_17:validFrom 11168 0 _IMJ=true:=by decide+kernel
def _IMK:List Piece:=DZ.decode 58 42 0xa484aa4041ec2a7058e30f252b9f5ea3aac58c7ae6526b03be9a75852f64deb6fa3d9c8e9445c1872148b0003
theorem shape8_18:validFrom 11167 0 _IMK=true:=by decide+kernel
def _IML:List Piece:=DZ.decode 58 42 0xa484aa4041ec3b5c5c03bb24eb9e5ea3aac58c7aec4d1018d946957b6f64deb6fa3d9fcae0f8b237614770003
theorem shape8_19:validFrom 11166 0 _IML=true:=by decide+kernel
def _IMN:List Piece:=DZ.decode 58 42 0xa484aa4041ec4c485f246724ab9d5ea3aac58c7af2300c43428fa571af64deb6fa3da3072daba2e7a14620003
theorem shape8_20:validFrom 11165 0 _IMN=true:=by decide+kernel
def _IMO:List Piece:=DZ.decode 58 42 0xa484aa4041ecb7062b5fc88dab9c5ea3aac58c7af82ab1585d3bc5a4af64deb6fa3da6437a5e9397e144e0003
theorem shape8_21:validFrom 11164 0 _IMO=true:=by decide+kernel
def _IMP:List Piece:=DZ.decode 58 42 0xa484aa4041ed08454b0cf07c6b9b5ea3aac58c7afe0dad82c684d5c66f64deb6fa3da97fc7118448214390003
theorem shape8_22:validFrom 11163 0 _IMP=true:=by decide+kernel
def _IMQ:List Piece:=DZ.decode 58 42 0xa484aa4041ed19314e2d9c7c2b9a5ea3aac58c7b03f0a9ad2fcde5bcaf64deb6fa3dacbc13c474f8614240003
theorem shape8_23:validFrom 11162 0 _IMQ=true:=by decide+kernel
def _IMR:List Piece:=DZ.decode 58 42 0xa484aa4041ed2a467278d88c2b995ea3aac58c7b09d3a5d79916f5b32f64deb6fa3daff8607765a8a140f0003
theorem shape8_24:validFrom 11161 0 _IMR=true:=by decide+kernel
def _IMS:List Piece:=DZ.decode 58 42 0xa484aa4041ed3b327599848beb985ea3aac58c7b0fb6a202026005a96f64deb6fa3db334ad2a5658e13fa0003
theorem shape8_25:validFrom 11160 0 _IMS=true:=by decide+kernel
def _IMT:List Piece:=DZ.decode 58 42 0xa484aa4041ed4c1e78ba308bab975ea3aac58c7b1581f541ba46059faf64deb6fa3db670f9dd4709213e40003
theorem shape8_26:validFrom 11159 0 _IMT=true:=by decide+kernel
def _IMU:List Piece:=DZ.decode 58 42 0xa484aa4041ed5d0a7bdadc8b6b965ea3aac58c7b1b64f16c238f1595ef64deb6fa3db9ad469037b9613cf0003
theorem shape8_27:validFrom 11158 0 _IMU=true:=by decide+kernel
def _IMV:List Piece:=DZ.decode 58 42 0xa484aa4041ed6df67efb888b2b955ea3aac58c7b213044abdb75158c2f64deb6fa3dbce993432869a13b90003
theorem shape8_28:validFrom 11157 0 _IMV=true:=by decide+kernel
def _IMW:List Piece:=DZ.decode 58 42 0xa484aa4041ed7ee2821c348aeb945ea3aac58c7b26fb97eb935b15826f64deb6fa3dc025dff61919e13a30003
theorem shape8_29:validFrom 11156 0 _IMW=true:=by decide+kernel
def _IMY:List Piece:=DZ.decode 58 42 0xa484aa4041ed8fce853ce08aab935ea3aac58c7b2cc6eb2b4b411578af64deb6fa3dc3622ca909ca2138d0003
theorem shape8_30:validFrom 11155 0 _IMY=true:=by decide+kernel
def _IMZ:List Piece:=DZ.decode 58 42 0xa484aa4041eda0e3a9881c9aab925ea3aac58c7b32923e6b0327156f2f64deb6fa3dc69e795bfa7a613770003
theorem shape8_31:validFrom 11154 0 _IMZ=true:=by decide+kernel
def _INA:List Piece:=DZ.decode 58 42 0xa484aa4041edb1cfaca8c89a6b915ea3aac58c7b3845e8c009aa05656f64deb6fa3dc9dac60eeb2aa13600003
theorem shape8_32:validFrom 11153 0 _INA=true:=by decide+kernel
def _INB:List Piece:=DZ.decode 58 42 0xa484aa4041edc2bbafc9749a2b905ea3aac58c7b3df99315102cf55baf64deb6fa3dcd1712c1dbdae13490003
theorem shape8_33:validFrom 11152 0 _INB=true:=by decide+kernel
def _INC:List Piece:=DZ.decode 58 42 0xa484aa4041edd3a7b2ea2099eb8f5ea3aac58c7b43ad3d6a16afe551ef64deb6fa3dd0535f74cc8b213320003
theorem shape8_34:validFrom 11151 0 _INC=true:=by decide+kernel
def _IND:List Piece:=DZ.decode 58 42 0xa484aa4041ede493b60acc99ab8e5ea3aac58c7b4960e7bf1d32d5482f64deb6fa3dd38fac27bd3b6131b0003
theorem shape8_35:validFrom 11150 0 _IND=true:=by decide+kernel
def _INE:List Piece:=DZ.decode 58 42 0xa484aa4041edf57fb92b78996b8d5ea3aac58c7b4f14921423b5c53e6f64deb6fa3dd6cbf8daadeba13040003
theorem shape8_36:validFrom 11149 0 _INE=true:=by decide+kernel
def _INF:List Piece:=DZ.decode 58 42 0xa484aa4041ee066bbc4c24992b8c5ea3aac58c7b54b0937e78d5a534af64deb6fa3dda08458d9e9be12ec0003
theorem shape8_37:validFrom 11148 0 _INF=true:=by decide+kernel
def _ING:List Piece:=DZ.decode 58 42 0xa484aa4041ee1780e09760a92b8b5ea3aac58c7b5a4c94e8cdf5852b2f64deb6fa3ddd4492408f4c212d40003
theorem shape8_38:validFrom 11147 0 _ING=true:=by decide+kernel
def _INH:List Piece:=DZ.decode 58 42 0xa484aa4041ee286ce3b80ca8eb8a5ea3aac58c7b5fe89653231565216f64deb6fa3de080def37ffc612bc0003
theorem shape8_39:validFrom 11146 0 _INH=true:=by decide+kernel
def _INJ:List Piece:=DZ.decode 58 42 0xa484aa4041ee3958e6d8b8a8ab895ea3aac58c7b656ceed2c6d23517af64deb6fa3de3bd2ba670aca12a30003
theorem shape8_40:validFrom 11145 0 _INJ=true:=by decide+kernel
def _INK:List Piece:=DZ.decode 58 42 0xa484aa4041ee4a44e9f964a86b885ea3aac58c7b6b08f03d1bf2150def64deb6fa3de6f97859615ce128b0003
theorem shape8_41:validFrom 11144 0 _INK=true:=by decide+kernel
def _INL:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae1ca484aa40410ee5b30ed1a10a82b6b5ea3aac58c43b708d48bcbfaee5042f64deb6fa30dea35c50c520d212720004
theorem shape8_42:validFrom 11143 0 _INL=true:=by decide+kernel
def _INM:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae18a484aa40410ee6c1cf03abca7eab65ea3aac58c43b75f9f851b208a4fa6f64deb6fa30ded7211bf42bd612580004
theorem shape8_43:validFrom 11142 0 _INM=true:=by decide+kernel
def _INN:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae14a484aa40410ee7d08f35b68a7a9f85ea3aac58c43b7b7e50d155c574f0af64deb6fa30df0ae5e72336da123f0004
theorem shape8_44:validFrom 11141 0 _INN=true:=by decide+kernel
def _INO:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae10a484aa40410ee8e1e17a6a4b7a92f5ea3aac58c43b80eb0066481f34e72f64deb6fa30df3eaab25241de12250004
theorem shape8_45:validFrom 11140 0 _INO=true:=by decide+kernel
def _INP:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae0ca484aa40410ee9f0a1ac750b7685b5ea3aac58c43b864007108915e4dd6f64deb6fa30df726f7d814ce2120a0004
theorem shape8_46:validFrom 11139 0 _INP=true:=by decide+kernel
def _INQ:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae08a484aa40410eeaff61de7fcb7277a5ea3aac58c43b8bacb6a57b6fa4d3af64deb6fa30dfa63448b057e611f00004
theorem shape8_47:validFrom 11138 0 _INQ=true:=by decide+kernel
def _INR:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae04a484aa40410eec0e22108a8b6e68c5ea3aac58c43b9101bd4fbc6654c9ef64deb6fa30dfd9f913df62ea11d50004
theorem shape8_48:validFrom 11137 0 _INR=true:=by decide+kernel
def _INS:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae00a484aa40410eed1ce242954b6a5915ea3aac58c43b9656c3f9fd5d04c02f64deb6fa30e00dbddf0e6dee11ba0004
theorem shape8_49:validFrom 11136 0 _INS=true:=by decide+kernel
def _INU:List Piece:=DZ.decode 62 42 0x3782dace9d900000adfca484aa40410eee2ba274a00b664895ea3aac58c43b9b9421b98cf0a4b66f64deb6fa30e04182aa3d78f2119e0004
theorem shape8_50:validFrom 11135 0 _INU=true:=by decide+kernel
def _INV:List Piece:=DZ.decode 62 42 0x3782dace9d900000adf8a484aa40410eef3a62a6aacb623745ea3aac58c43ba0d17f791c8444acaf64deb6fa30e07547756c83f611820004
theorem shape8_51:validFrom 11134 0 _INV=true:=by decide+kernel
def _INW:List Piece:=DZ.decode 62 41 0x3782dace9d900000adf549095480821de09769d6bd18c44a37a8eab16310e829a7e7b9aa3e128c0003
theorem shape8_52:validFrom 11133 0 _INW=true:=by decide+kernel
def _INX:List Piece:=DZ.decode 62 41 0x3782dace9d900000adf149095480821de2b4ea3ad298bc2457a8eab16310e848f7456583e392650003
theorem shape8_53:validFrom 11132 0 _INX=true:=by decide+kernel
def _INY:List Piece:=DZ.decode 62 41 0x3782dace9d900000aded49095480821dd1dd2100809b33fcb7a8eab16310e92d783dc31e500e8e0003
theorem shape8_54:validFrom 11131 0 _INY=true:=by decide+kernel
def _INZ:List Piece:=DZ.decode 62 41 0x3782dace9d900000ade949095480821dd41e9e69d42963d357a8eab16310e94b68c208d7ed4e6e0003
theorem shape8_55:validFrom 11130 0 _INZ=true:=by decide+kernel
def _IOA:List Piece:=DZ.decode 62 41 0x3782dace9d900000ade549095480821dd6601bd327b793a857a8eab16310e96959464e918a8e4e0003
theorem shape8_56:validFrom 11129 0 _IOA=true:=by decide+kernel
def _IOB:List Piece:=DZ.decode 62 41 0x3782dace9d900000ade149095480821dd8a1993c7b45c37bb7a8eab16310e98749ca944b27ce2e0003
theorem shape8_57:validFrom 11128 0 _IOB=true:=by decide+kernel
def _IOC:List Piece:=DZ.decode 62 41 0x3782dace9d900000addd49095480821ddaddf2807cd1eb4d57a8eab16310e9a53a4eda04c50e0d0003
theorem shape8_58:validFrom 11127 0 _IOC=true:=by decide+kernel
def _IOD:List Piece:=DZ.decode 62 41 0x3782dace9d900000add949095480821dec9862f7ec25ab1d57a8eab16310e9c32ad31fbe624f3c0003
theorem shape8_59:validFrom 11126 0 _IOD=true:=by decide+kernel
def _IOF:List Piece:=DZ.decode 62 41 0x3782dace9d900000add549095480821deed4bc3bedb1d2eb97a8eab16310e9e11b576577ff8f1b0003
theorem shape8_60:validFrom 11125 0 _IOF=true:=by decide+kernel
def _IOG:List Piece:=DZ.decode 62 41 0x3782dace9d900000add149095480821df11639a5414002b837a8eab16310e9ff0bdbab319ccefb0003
theorem shape8_61:validFrom 11124 0 _IOG=true:=by decide+kernel
def _IOH:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b9800000000003c3bd7127e2d68051ad49095480821df357b70e94ce328317a8eab16310ea1cfc5ff0eb3a0edb0004
theorem shape8_62:validFrom 11123 0 _IOH=true:=by decide+kernel
def _IOI:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b9000000000003c3cc64d27e6dbb50b149095480821df5941052965a5a4c37a8eab16310ea3aece436a4d74eba0004
theorem shape8_63:validFrom 11122 0 _IOI=true:=by decide+kernel
def _IOJ:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015b8800000000003c3db581d9c8c084fa949095480821df7d58dbbe9e88a13b7a8eab16310ea58dd687c5e748e9a0004
theorem shape8_64:validFrom 11121 0 _IOJ=true:=by decide+kernel
def _IOK:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7000000000000f0fa92c249ccbf93a65e99d545850f0a0ee70f5ef730ffbbd33aa8b090f041cfadc679778fc7a484aa40410eeabdf5cd554bc4ecbbd33aa8b090ed8618dad0c9eec6360006
theorem shape8_65:validFrom 11120 0 _IOK=true:=by decide+kernel
def _IOL:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b6f00000000000f0fe4f654a5889d35e5e99d545850f0a7616f7ac9e80fcdbd33aa8b090edaffed7a596000f970004
theorem shape8_66:validFrom 11119 0 _IOL=true:=by decide+kernel
def _IOM:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb80000000000788105f835c302098a5e99d545850ef41d670c110440f9c0003
theorem shape8_67:validFrom 11118 0 _IOM=true:=by decide+kernel
def _ION:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb400000000007882e431d3eaecc962de99d545850ef4d465cbb955ccf6a0003
theorem shape8_68:validFrom 11117 0 _ION=true:=by decide+kernel
def _IOO:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb000000000007884c25f8103da693a5e99d545850ef5914caeaa652cf360003
theorem shape8_69:validFrom 11116 0 _IOO=true:=by decide+kernel
def _IOQ:List Piece:=DZ.decode 62 39 0x3782dace9d900000adac00000000007886a0813d0dc5c90fde99d545850ef652a14d394278eff0003
theorem shape8_70:validFrom 11115 0 _IOQ=true:=by decide+kernel
def _IOR:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada8000000000078887e9709686a08e35e99d545850ef719de0f10d93cec60003
theorem shape8_71:validFrom 11114 0 _IOR=true:=by decide+kernel
def _IOS:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada40000000000788a5ca0e3545ae8b55e99d545850ef7e5888c86410ce8b0003
theorem shape8_72:validFrom 11113 0 _IOS=true:=by decide+kernel
def _IOT:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada00000000000788c3a9ecc31494885de99d545850ef8b71b2d4462f4e4d0003
theorem shape8_73:validFrom 11112 0 _IOT=true:=by decide+kernel
def _IOU:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad9c0000000000788e1890c55eeae8545e99d545850ef98d1b89a0540ce0c0003
theorem shape8_74:validFrom 11111 0 _IOU=true:=by decide+kernel
def _IOV:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad980000000000788ff676cc1ddee820de99d545850efa69040944fe8cdc90003
theorem shape8_75:validFrom 11110 0 _IOV=true:=by decide+kernel
def _IOW:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad9400000000007891d450e1cdcb67ebde99d545850efb495a44877b78d840003
theorem shape8_76:validFrom 11109 0 _IOW=true:=by decide+kernel
def _IOX:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad9000000000007893b21f066ebfc7b4de99d545850efc2f98a312ae90d3c0003
theorem shape8_77:validFrom 11108 0 _IOX=true:=by decide+kernel
def _IOY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c60f12b1fc276c0a44ef80002
theorem shape8_78:validFrom 11107 0 _IOY=true:=by decide+kernel
def _IOZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c40f12edb2efbc6988e840002
theorem shape8_79:validFrom 11106 0 _IOZ=true:=by decide+kernel
def _IPB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c20f13296839eae924e0c0002
theorem shape8_80:validFrom 11105 0 _IPB=true:=by decide+kernel
def _IPC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c00f13651c062377d8d900002
theorem shape8_81:validFrom 11104 0 _IPC=true:=by decide+kernel
def _IPD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056be0f13a0ce540e377cd110002
theorem shape8_82:validFrom 11103 0 _IPD=true:=by decide+kernel
def _IPE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056bc0f13dbc7c6898830c8e0002
theorem shape8_83:validFrom 11102 0 _IPE=true:=by decide+kernel
def _IPF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ba0f1413290aff327cc070002
theorem shape8_84:validFrom 11101 0 _IPF=true:=by decide+kernel
def _IPG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f144a88f1d03eb4b7e0002
theorem shape8_85:validFrom 11100 0 _IPG=true:=by decide+kernel
def _IPH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f1481e77b5489a4af10002
theorem shape8_86:validFrom 11099 0 _IPH=true:=by decide+kernel
def _IPI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f14b944a73439eca600002
theorem shape8_87:validFrom 11098 0 _IPI=true:=by decide+kernel
def _IPJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f14f0a075c728709cb0002
theorem shape8_88:validFrom 11097 0 _IPJ=true:=by decide+kernel
def _IPK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b00f1527fae6b57c249320002
theorem shape8_89:validFrom 11096 0 _IPK=true:=by decide+kernel
def _IPM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ae0f155f53fa570cc48970002
theorem shape8_90:validFrom 11095 0 _IPM=true:=by decide+kernel
def _IPN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ac0f1596abb05403e87f80002
theorem shape8_91:validFrom 11094 0 _IPN=true:=by decide+kernel
def _IPO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056aa0f15ce02090435187560002
theorem shape8_92:validFrom 11093 0 _IPO=true:=by decide+kernel
def _IPP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a80f160557040fcfa06b00002
theorem shape8_93:validFrom 11092 0 _IPP=true:=by decide+kernel
def _IPQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a60f163caaa1a2bc3c6060002
theorem shape8_94:validFrom 11091 0 _IPQ=true:=by decide+kernel
def _IPR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a40f1673fce1e8e2745580002
theorem shape8_95:validFrom 11090 0 _IPR=true:=by decide+kernel
def _IPS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a20f16ab4dc48a727c4a70002
theorem shape8_96:validFrom 11089 0 _IPS=true:=by decide+kernel
def _IPT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a00f16e29d49df392c3f20002
theorem shape8_97:validFrom 11088 0 _IPT=true:=by decide+kernel
def _IPU:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569e0f1719eb718f6bf433a0002
theorem shape8_98:validFrom 11087 0 _IPU=true:=by decide+kernel
def _IPV:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569c0f1751383bf2d66427f0002
theorem shape8_99:validFrom 11086 0 _IPV=true:=by decide+kernel
def _ILT:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569a0f178883a8b1ad3c1c00002
theorem shape8_100:validFrom 11085 0 _ILT=true:=by decide+kernel
def _ILU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056980f17bfcdb823b9d00fd0002
theorem shape8_101:validFrom 11084 0 _ILU=true:=by decide+kernel
def _ILV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056960f17f71669f132600360002
theorem shape8_102:validFrom 11083 0 _ILV=true:=by decide+kernel
def _ILW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3bccf372df387be0f182e5dbe71e1080020002
theorem shape8_103:validFrom 11082 0 _ILW=true:=by decide+kernel
def _ILX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273bcc165b03c80520f1865a3b54dfeb80020002
theorem shape8_104:validFrom 11081 0 _ILX=true:=by decide+kernel
def _ILY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233bcb39489d8ac200f189ce84edd4f800020002
theorem shape8_105:validFrom 11080 0 _ILY=true:=by decide+kernel
def _ILZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3bca5c3baddfbd80f18d42b8ac810a00020002
theorem shape8_106:validFrom 11079 0 _ILZ=true:=by decide+kernel
def _IMA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3bc97f343367f920f190b6d696601b80020002
theorem shape8_107:validFrom 11078 0 _IMA=true:=by decide+kernel
def _IMB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bc8a2322f826700f1942adea5f66400020002
theorem shape8_108:validFrom 11077 0 _IMB=true:=by decide+kernel
def _IMC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bc7c535a0d01300f1979ed0e0bfb400020002
theorem shape8_109:validFrom 11076 0 _IMC=true:=by decide+kernel
def row8 (v:ℕ):List Piece:=match v with
 | 0=>d8_0
 | 1=>d8_1
 | 2=>d8_2
 | 3=>d8_3
 | 4=>d8_4
 | 5=>d8_5
 | 6=>d8_6
 | 7=>d8_7
 | 8=>d8_8
 | 9=>d8_9
 | 10=>_ILS
 | 11=>_IMD
 | 12=>_IME
 | 13=>_IMF
 | 14=>_IMG
 | 15=>_IMH
 | 16=>_IMI
 | 17=>_IMJ
 | 18=>_IMK
 | 19=>_IML
 | 20=>_IMN
 | 21=>_IMO
 | 22=>_IMP
 | 23=>_IMQ
 | 24=>_IMR
 | 25=>_IMS
 | 26=>_IMT
 | 27=>_IMU
 | 28=>_IMV
 | 29=>_IMW
 | 30=>_IMY
 | 31=>_IMZ
 | 32=>_INA
 | 33=>_INB
 | 34=>_INC
 | 35=>_IND
 | 36=>_INE
 | 37=>_INF
 | 38=>_ING
 | 39=>_INH
 | 40=>_INJ
 | 41=>_INK
 | 42=>_INL
 | 43=>_INM
 | 44=>_INN
 | 45=>_INO
 | 46=>_INP
 | 47=>_INQ
 | 48=>_INR
 | 49=>_INS
 | 50=>_INU
 | 51=>_INV
 | 52=>_INW
 | 53=>_INX
 | 54=>_INY
 | 55=>_INZ
 | 56=>_IOA
 | 57=>_IOB
 | 58=>_IOC
 | 59=>_IOD
 | 60=>_IOF
 | 61=>_IOG
 | 62=>_IOH
 | 63=>_IOI
 | 64=>_IOJ
 | 65=>_IOK
 | 66=>_IOL
 | 67=>_IOM
 | 68=>_ION
 | 69=>_IOO
 | 70=>_IOQ
 | 71=>_IOR
 | 72=>_IOS
 | 73=>_IOT
 | 74=>_IOU
 | 75=>_IOV
 | 76=>_IOW
 | 77=>_IOX
 | 78=>_IOY
 | 79=>_IOZ
 | 80=>_IPB
 | 81=>_IPC
 | 82=>_IPD
 | 83=>_IPE
 | 84=>_IPF
 | 85=>_IPG
 | 86=>_IPH
 | 87=>_IPI
 | 88=>_IPJ
 | 89=>_IPK
 | 90=>_IPM
 | 91=>_IPN
 | 92=>_IPO
 | 93=>_IPP
 | 94=>_IPQ
 | 95=>_IPR
 | 96=>_IPS
 | 97=>_IPT
 | 98=>_IPU
 | 99=>_IPV
 | 100=>_ILT
 | 101=>_ILU
 | 102=>_ILV
 | 103=>_ILW
 | 104=>_ILX
 | 105=>_ILY
 | 106=>_ILZ
 | 107=>_IMA
 | 108=>_IMB
 | 109=>_IMC
 | _=>[]
theorem checked8 (v:ℕ) (hy:8+v≤117):validFrom (11193-8-v) 0 (row8 v)=true:=by
 have hv:v≤109:=by omega
 interval_cases v
 · exact shape8_0
 · exact shape8_1
 · exact shape8_2
 · exact shape8_3
 · exact shape8_4
 · exact shape8_5
 · exact shape8_6
 · exact shape8_7
 · exact shape8_8
 · exact shape8_9
 · exact shape8_10
 · exact shape8_11
 · exact shape8_12
 · exact shape8_13
 · exact shape8_14
 · exact shape8_15
 · exact shape8_16
 · exact shape8_17
 · exact shape8_18
 · exact shape8_19
 · exact shape8_20
 · exact shape8_21
 · exact shape8_22
 · exact shape8_23
 · exact shape8_24
 · exact shape8_25
 · exact shape8_26
 · exact shape8_27
 · exact shape8_28
 · exact shape8_29
 · exact shape8_30
 · exact shape8_31
 · exact shape8_32
 · exact shape8_33
 · exact shape8_34
 · exact shape8_35
 · exact shape8_36
 · exact shape8_37
 · exact shape8_38
 · exact shape8_39
 · exact shape8_40
 · exact shape8_41
 · exact shape8_42
 · exact shape8_43
 · exact shape8_44
 · exact shape8_45
 · exact shape8_46
 · exact shape8_47
 · exact shape8_48
 · exact shape8_49
 · exact shape8_50
 · exact shape8_51
 · exact shape8_52
 · exact shape8_53
 · exact shape8_54
 · exact shape8_55
 · exact shape8_56
 · exact shape8_57
 · exact shape8_58
 · exact shape8_59
 · exact shape8_60
 · exact shape8_61
 · exact shape8_62
 · exact shape8_63
 · exact shape8_64
 · exact shape8_65
 · exact shape8_66
 · exact shape8_67
 · exact shape8_68
 · exact shape8_69
 · exact shape8_70
 · exact shape8_71
 · exact shape8_72
 · exact shape8_73
 · exact shape8_74
 · exact shape8_75
 · exact shape8_76
 · exact shape8_77
 · exact shape8_78
 · exact shape8_79
 · exact shape8_80
 · exact shape8_81
 · exact shape8_82
 · exact shape8_83
 · exact shape8_84
 · exact shape8_85
 · exact shape8_86
 · exact shape8_87
 · exact shape8_88
 · exact shape8_89
 · exact shape8_90
 · exact shape8_91
 · exact shape8_92
 · exact shape8_93
 · exact shape8_94
 · exact shape8_95
 · exact shape8_96
 · exact shape8_97
 · exact shape8_98
 · exact shape8_99
 · exact shape8_100
 · exact shape8_101
 · exact shape8_102
 · exact shape8_103
 · exact shape8_104
 · exact shape8_105
 · exact shape8_106
 · exact shape8_107
 · exact shape8_108
 · exact shape8_109
def d9_0:List Piece:=DZ.decode 58 42 0xa484aa4041eb5e678eb16f53ebb05ea3aac58c7a9512e5d349650615ef64deb6fa3d7391173db0b1895870003
theorem shape9_0:validFrom 11184 0 d9_0=true:=by decide+kernel
def d9_1:List Piece:=DZ.decode 58 42 0xa484aa4041eb707379fc0bc56baf5ea3aac58c7a9ae526643ed5360def64deb6fa3d76cd63f0a161c95750003
theorem shape9_1:validFrom 11183 0 d9_1=true:=by decide+kernel
def d9_2:List Piece:=DZ.decode 58 42 0xa484aa4041eb827f6546a836ebae5ea3aac58c7aa0b766f534456605ef64deb6fa3d7a09b0a39212095630003
theorem shape9_2:validFrom 11182 0 d9_2=true:=by decide+kernel
def d9_3:List Piece:=DZ.decode 58 42 0xa484aa4041eb94622f66b4982bad5ea3aac58c7aa689a78629b595fdaf64deb6fa3d7d45fd5682c2495510003
theorem shape9_3:validFrom 11181 0 d9_3=true:=by decide+kernel
def d9_4:List Piece:=DZ.decode 58 42 0xa484aa4041eba66e1ab15109abac5ea3aac58c7aac443f2c6dc2b5f5af64deb6fa3d80824a0973728953e0003
theorem shape9_4:validFrom 11180 0 d9_4=true:=by decide+kernel
def d9_5:List Piece:=DZ.decode 58 42 0xa484aa4041ebb87a05fbed7b2bab5ea3aac58c7ab1fed6d2b1cfd5edaf64deb6fa3d83be96bc6422c952b0003
theorem shape9_5:validFrom 11179 0 d9_5=true:=by decide+kernel
def d9_6:List Piece:=DZ.decode 58 42 0xa484aa4041ebca5cd01bf9dc6baa5ea3aac58c7ab7d11763a74005e56f64deb6fa3d86fae36f54d3095190003
theorem shape9_6:validFrom 11178 0 d9_6=true:=by decide+kernel
def d9_7:List Piece:=DZ.decode 58 42 0xa484aa4041ebdc68bb66964deba95ea3aac58c7abd8baf09eb4d25dd6f64deb6fa3d8a3730224583495060003
theorem shape9_7:validFrom 11177 0 d9_7=true:=by decide+kernel
def d9_8:List Piece:=DZ.decode 58 42 0xa484aa4041ebee74a6b132bf6ba85ea3aac58c7ac34646b02f5a45d56f64deb6fa3d8d737cd53633894f30003
theorem shape9_8:validFrom 11176 0 d9_8=true:=by decide+kernel
def d9_9:List Piece:=DZ.decode 58 42 0xa484aa4041ec005770d13f20aba75ea3aac58c7ac900de56736765cd2f64deb6fa3d90afc98826e3c94e00003
theorem shape9_9:validFrom 11175 0 d9_9=true:=by decide+kernel
def _IPY:List Piece:=DZ.decode 58 42 0xa484aa4041ec12635c1bdb922ba65ea3aac58c7acea3cd12061175c52f64deb6fa3d93ec163b1794094cc0003
theorem shape9_10:validFrom 11174 0 _IPY=true:=by decide+kernel
def _IQI:List Piece:=DZ.decode 58 42 0xa484aa4041ec246f47667803aba55ea3aac58c7ad45e64b84a1e95bd2f64deb6fa3d972862ee0844494b90003
theorem shape9_11:validFrom 11173 0 _IQI=true:=by decide+kernel
def _IQJ:List Piece:=DZ.decode 58 42 0xa484aa4041ec367b32b114752ba45ea3aac58c7ada18fc5e8e2bb5b52f64deb6fa3d9a64afa0f8f4894a60003
theorem shape9_12:validFrom 11172 0 _IQJ=true:=by decide+kernel
def _IQK:List Piece:=DZ.decode 58 42 0xa484aa4041ec485dfcd120d66ba35ea3aac58c7adfbbeb1a20d5c5acef64deb6fa3d9da0fc53e9a4c94920003
theorem shape9_13:validFrom 11171 0 _IQK=true:=by decide+kernel
def _IQL:List Piece:=DZ.decode 58 42 0xa484aa4041ec5a69e81bbd47eba25ea3aac58c7ae55ed9d5b37fd5a4ef64deb6fa3da0dd4906da550947e0003
theorem shape9_14:validFrom 11170 0 _IQL=true:=by decide+kernel
def _IQM:List Piece:=DZ.decode 58 42 0xa484aa4041ec4c2ac8fb3cf72ba15ea3aac58c7af579ee203e8c556aaf64deb6fa3da41995b9cb054946a0003
theorem shape9_15:validFrom 11169 0 _IQM=true:=by decide+kernel
def _IQN:List Piece:=DZ.decode 58 42 0xa484aa4041ec5d16cc1be8f6eba05ea3aac58c7afb74933559387560ef64deb6fa3da755e26cbbb5894560003
theorem shape9_16:validFrom 11168 0 _IQN=true:=by decide+kernel
def _IQO:List Piece:=DZ.decode 58 42 0xa484aa4041ec6e2bf0672506eb9f5ea3aac58c7b016f384a73e495576f64deb6fa3daa922f1fac65c94420003
theorem shape9_17:validFrom 11167 0 _IQO=true:=by decide+kernel
def _IQP:List Piece:=DZ.decode 58 42 0xa484aa4041ec84475df0329b2b9e5ea3aac58c7b07523474dd2da5512f64deb6fa3dadce7bd29d160942d0003
theorem shape9_18:validFrom 11166 0 _IQP=true:=by decide+kernel
def _IQQ:List Piece:=DZ.decode 58 42 0xa484aa4041ec95336110de9aeb9d5ea3aac58c7b0d4cd989f7d9c5476f64deb6fa3db10ac8858dc6494190003
theorem shape9_19:validFrom 11165 0 _IQQ=true:=by decide+kernel
def _IQS:List Piece:=DZ.decode 58 42 0xa484aa4041eca61f64318a9aab9c5ea3aac58c7b132fd5b46122d53daf64deb6fa3db44715387e76894040003
theorem shape9_20:validFrom 11164 0 _IQS=true:=by decide+kernel
def _IQT:List Piece:=DZ.decode 58 42 0xa484aa4041ed10dd306cec03ab9b5ea3aac58c7b1912d1deca6be570af64deb6fa3db78361eb6f26c93ef0003
theorem shape9_21:validFrom 11163 0 _IQT=true:=by decide+kernel
def _IQU:List Piece:=DZ.decode 58 42 0xa484aa4041ed621c501a13f26b9a5ea3aac58c7b1ef5ce0933b4f5926f64deb6fa3dbabfae9e5fd7093da0003
theorem shape9_22:validFrom 11162 0 _IQU=true:=by decide+kernel
def _IQV:List Piece:=DZ.decode 58 42 0xa484aa4041ed7308533abff22b995ea3aac58c7b24d8ca339cfe0588af64deb6fa3dbdfbfb515087493c50003
theorem shape9_23:validFrom 11161 0 _IQV=true:=by decide+kernel
def _IQW:List Piece:=DZ.decode 58 42 0xa484aa4041ed841d7785fc022b985ea3aac58c7b2abbc65e0647157f2f64deb6fa3dc13848044137893b00003
theorem shape9_24:validFrom 11160 0 _IQW=true:=by decide+kernel
def _IQX:List Piece:=DZ.decode 58 42 0xa484aa4041ed95097aa6a801eb975ea3aac58c7b3087199dbe2d15756f64deb6fa3dc47494b731e7c939a0003
theorem shape9_25:validFrom 11159 0 _IQX=true:=by decide+kernel
def _IQY:List Piece:=DZ.decode 58 42 0xa484aa4041eda5f57dc75401ab965ea3aac58c7b36526cdd7613156baf64deb6fa3dc7b0e16a2298093840003
theorem shape9_26:validFrom 11158 0 _IQY=true:=by decide+kernel
def _IQZ:List Piece:=DZ.decode 58 42 0xa484aa4041edb6e180e800016b955ea3aac58c7b3c1dc01d2df91561ef64deb6fa3dcaed2e1d13484936e0003
theorem shape9_27:validFrom 11157 0 _IQZ=true:=by decide+kernel
def _IRA:List Piece:=DZ.decode 58 42 0xa484aa4041edc7cd8408ac012b945ea3aac58c7b41e9135ce5df15582f64deb6fa3dce297ad003f8893580003
theorem shape9_28:validFrom 11156 0 _IRA=true:=by decide+kernel
def _IRB:List Piece:=DZ.decode 58 42 0xa484aa4041edd8b987295800eb935ea3aac58c7b47b4669c9dc5154e6f64deb6fa3dd165c782f4a8c93420003
theorem shape9_29:validFrom 11155 0 _IRB=true:=by decide+kernel
def _IRD:List Piece:=DZ.decode 58 42 0xa484aa4041ede9a58a4a0400ab925ea3aac58c7b4d6810f1a4480544af64deb6fa3dd4a21435e5590932b0003
theorem shape9_30:validFrom 11154 0 _IRD=true:=by decide+kernel
def _IRE:List Piece:=DZ.decode 58 42 0xa484aa4041edfabaae954010ab915ea3aac58c7b533364315c2e053b2f64deb6fa3dd7de60e8d609493150003
theorem shape9_31:validFrom 11153 0 _IRE=true:=by decide+kernel
def _IRF:List Piece:=DZ.decode 58 42 0xa484aa4041ee0ba6b1b5ec106b905ea3aac58c7b58e70e8662b0f5316f64deb6fa3ddb1aad9bc6b9892fe0003
theorem shape9_32:validFrom 11152 0 _IRF=true:=by decide+kernel
def _IRG:List Piece:=DZ.decode 58 42 0xa484aa4041ee1c92b4d698102b8f5ea3aac58c7b5e830ff0b7d0d527af64deb6fa3dde56fa4eb769c92e60003
theorem shape9_33:validFrom 11151 0 _IRG=true:=by decide+kernel
def _IRH:List Piece:=DZ.decode 58 42 0xa484aa4041ee2d7eb7f7440feb8e5ea3aac58c7b6436ba45be53c51def64deb6fa3de1934701a81a092cf0003
theorem shape9_34:validFrom 11150 0 _IRH=true:=by decide+kernel
def _IRI:List Piece:=DZ.decode 58 42 0xa484aa4041ee3e6abb17f00fab8d5ea3aac58c7b69d2bbb01373a5142f64deb6fa3de4cf93b498ca492b70003
theorem shape9_35:validFrom 11149 0 _IRI=true:=by decide+kernel
def _IRJ:List Piece:=DZ.decode 58 42 0xa484aa4041ee4f56be389c0f6b8c5ea3aac58c7b6f6ebd1a6893850a6f64deb6fa3de80be067897a8929f0003
theorem shape9_36:validFrom 11148 0 _IRJ=true:=by decide+kernel
def _IRK:List Piece:=DZ.decode 58 42 0xa484aa4041ee6042c159480f2b8b5ea3aac58c7b750abe84bdb36500af64deb6fa3deb482d1a7a2ac92870003
theorem shape9_37:validFrom 11147 0 _IRK=true:=by decide+kernel
def _IRL:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae28a484aa40410ee7157e5a4841f2b755ea3aac58c43b7aa6bfef12d344f72f64deb6fa30dee8479cd6adb0926f0004
theorem shape9_38:validFrom 11146 0 _IRL=true:=by decide+kernel
def _IRM:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae24a484aa40410ee8243e8c5301eeacd5ea3aac58c43b802b186eb69014ed6f64deb6fa30df1c0c6805b8b492560004
theorem shape9_39:validFrom 11145 0 _IRM=true:=by decide+kernel
def _IRO:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae20a484aa40410ee932febe5dc1eaa1e5ea3aac58c43b85af70ee5a4ce4e3af64deb6fa30df4fd13334c3b8923d0004
theorem shape9_40:validFrom 11144 0 _IRO=true:=by decide+kernel
def _IRP:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae1ca484aa40410eea41bef06881e69675ea3aac58c43b8b33c96dfe09b4d9ef64deb6fa30df8395fe63cebc92240004
theorem shape9_41:validFrom 11143 0 _IRP=true:=by decide+kernel
def _IRQ:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae18a484aa40410eeb507f227341e28a75ea3aac58c43b90a07902f06374d02f64deb6fa30dfb75ac992d9c0920a0004
theorem shape9_42:validFrom 11142 0 _IRQ=true:=by decide+kernel
def _IRR:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae14a484aa40410eec5f3f547e01de7dd5ea3aac58c43b960d2897e2bd34c66f64deb6fa30dfeb1f94c1e4c491f00004
theorem shape9_43:validFrom 11141 0 _IRR=true:=by decide+kernel
def _IRS:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae10a484aa40410eed6dff8688c1da7085ea3aac58c43b9b79d82cd516f4bcaf64deb6fa30e01ee45ff0efc891d60004
theorem shape9_44:validFrom 11140 0 _IRS=true:=by decide+kernel
def _IRT:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae0ca484aa40410eee7f51cb3c82da6275ea3aac58c43ba0ceded7160da4b32f64deb6fa30e052a92b1ffacc91bb0004
theorem shape9_45:validFrom 11139 0 _IRT=true:=by decide+kernel
def _IRU:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae08a484aa40410eef8e11fd4742d65395ea3aac58c43ba623e581570454a96f64deb6fa30e0866df64f05d091a00004
theorem shape9_46:validFrom 11138 0 _IRU=true:=by decide+kernel
def _IRV:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae04a484aa40410ef09cd22f5202d243f5ea3aac58c43bab78ec2b97fb049faf64deb6fa30e0ba32c17e10d491850004
theorem shape9_47:validFrom 11137 0 _IRV=true:=by decide+kernel
def _IRW:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae00a484aa40410ef1ab92615cc2ce3385ea3aac58c43bb0b649eb278ea495ef64deb6fa30e0edf78cad1bd891690004
theorem shape9_48:validFrom 11136 0 _IRW=true:=by decide+kernel
def _IRX:List Piece:=DZ.decode 62 42 0x3782dace9d900000adfca484aa40410ef2ba52936782ca2255ea3aac58c43bb5f3a7aab722448c2f64deb6fa30e121bc57dc26dc914d0004
theorem shape9_49:validFrom 11135 0 _IRX=true:=by decide+kernel
def _IRZ:List Piece:=DZ.decode 62 42 0x3782dace9d900000adf8a484aa40410ef3c912c57242c61045ea3aac58c43bbb195c7f9552d4826f64deb6fa30e15581230b31e091300004
theorem shape9_50:validFrom 11134 0 _IRZ=true:=by decide+kernel
def _ISA:List Piece:=DZ.decode 62 42 0x3782dace9d900000adf4a484aa40410ef4d7d2f77d02c1fd65ea3aac58c43bc056ba3f24e67478af64deb6fa30e18945ee3a3ce491140004
theorem shape9_51:validFrom 11133 0 _ISA=true:=by decide+kernel
def _ISB:List Piece:=DZ.decode 62 41 0x3782dace9d900000adf149095480821debd24a78618783d397a8eab16310e8d0672632ae0a51bc0003
theorem shape9_52:validFrom 11132 0 _ISB=true:=by decide+kernel
def _ISC:List Piece:=DZ.decode 62 41 0x3782dace9d900000aded49095480821dedefcadc77077baa97a8eab16310e8efb683de87afd1950003
theorem shape9_53:validFrom 11131 0 _ISC=true:=by decide+kernel
def _ISD:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7aa484aa40410ecb38a462969001bff0002
theorem shape9_54:validFrom 11130 0 _ISD=true:=by decide+kernel
def _ISE:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b79a484aa40410eccaba56c607799a9d0002
theorem shape9_55:validFrom 11129 0 _ISE=true:=by decide+kernel
def _ISF:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b78a484aa40410ece1ea6762a5f3192d0002
theorem shape9_56:validFrom 11128 0 _ISF=true:=by decide+kernel
def _ISG:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b77a484aa40410ecf91a77ff446c97b00002
theorem shape9_57:validFrom 11127 0 _ISG=true:=by decide+kernel
def _ISH:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b76a484aa40410ed104a889be2e616260002
theorem shape9_58:validFrom 11126 0 _ISH=true:=by decide+kernel
def _ISI:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b75a484aa40410edc4840313dcafd48ebd33aa8b090ed605fd28c3cb8c21e0003
theorem shape9_59:validFrom 11125 0 _ISI=true:=by decide+kernel
def _ISK:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7400000000000f0f8bf742c4ea8d419a484aa40410ed849fdb9378c1d2e90003
theorem shape9_60:validFrom 11124 0 _ISK=true:=by decide+kernel
def _ISL:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7300000000000f0fc6d671ffb6713daa484aa40410edcf8ba3b94babd136bd33aa8b090ed940ee929d9f681420004
theorem shape9_61:validFrom 11123 0 _ISL=true:=by decide+kernel
def _ISM:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7200000000000f1001b4272eeb213995e99d545850f0a69dd5b3d37c8fedbd33aa8b090f07cb62056be27cfb9a484aa40410ee2871b156141b8f76bd33aa8b090eda166eca656de42db0006
theorem shape9_62:validFrom 11122 0 _ISM=true:=by decide+kernel
def _ISN:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7100000000000f103c9061fca53d3555e99d545850f0acea4e2f75ad4fc0bd33aa8b090f034b1546180800f8ca484aa40410ee812e9dc84c7b0da8bd33aa8b090edaebef022d3c604730006
theorem shape9_63:validFrom 11121 0 _ISN=true:=by decide+kernel
def _ISO:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7000000000000f10776b22bec8a530e5e99d545850f0b336af4664f60f92bd33aa8b090efea45a081fefb0f5ca484aa40410eed9eb8a3a84da8bcdbd33aa8b090edbc16f39f50adc60b0006
theorem shape9_64:validFrom 11120 0 _ISO=true:=by decide+kernel
def _ISP:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b6f00000000000f10b244691f74852c45e99d545850f0b9c9ec5895418f62bd33aa8b090edcd5af9cb1d22cf2b0004
theorem shape9_65:validFrom 11119 0 _ISP=true:=by decide+kernel
def _ISQ:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb80000000000788768e1aba42be93b5e99d545850ef5e5965ee89030f300003
theorem shape9_66:validFrom 11118 0 _ISQ=true:=by decide+kernel
def _ISR:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb4000000000078893f943b4105a912de99d545850ef6a18dde12080cefc0003
theorem shape9_67:validFrom 11117 0 _ISR=true:=by decide+kernel
def _ISS:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb00000000000788b163af9299d88e8de99d545850ef76078b59a7da4ec60003
theorem shape9_68:validFrom 11116 0 _ISS=true:=by decide+kernel
def _IST:List Piece:=DZ.decode 62 39 0x3782dace9d900000adac0000000000788cecd5e6b56188bcde99d545850ef826c61b812f78e8d0003
theorem shape9_69:validFrom 11115 0 _IST=true:=by decide+kernel
def _ISV:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada80000000000788ec365013583088f5e99d545850ef8f006d9c6de64e520003
theorem shape9_70:validFrom 11114 0 _ISV=true:=by decide+kernel
def _ISW:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada40000000000789099e84b58adc85fde99d545850ef9bf2fbf3f92e0e150003
theorem shape9_71:validFrom 11113 0 _ISW=true:=by decide+kernel
def _ISX:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada000000000007892705fc2704f082ede99d545850efa92c6644279e4dd50003
theorem shape9_72:validFrom 11112 0 _ISX=true:=by decide+kernel
def _ISY:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad9c0000000000789446cb692afe87fbde99d545850efb6c45304e8ad4d930003
theorem shape9_73:validFrom 11111 0 _ISY=true:=by decide+kernel
def _ISZ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad98000000000078961d2b3cda15a7c75e99d545850efc4bac2363c1e8d4e0003
theorem shape9_74:validFrom 11110 0 _ISZ=true:=by decide+kernel
def _ITA:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad9400000000007897f37f402c358790de99d545850efd2e066ed7f624d060003
theorem shape9_75:validFrom 11109 0 _ITA=true:=by decide+kernel
def _ITB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c80f133938ee0e5adceb10002
theorem shape9_76:validFrom 11108 0 _ITB=true:=by decide+kernel
def _ITC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c60f1374007a0b8ce4e3d0002
theorem shape9_77:validFrom 11107 0 _ITC=true:=by decide+kernel
def _ITD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c40f13aec68ba75108dc60002
theorem shape9_78:validFrom 11106 0 _ITD=true:=by decide+kernel
def _ITE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c20f13e98b2337711cd4c0002
theorem shape9_79:validFrom 11105 0 _ITE=true:=by decide+kernel
def _ITG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c00f14244e40662540cce0002
theorem shape9_80:validFrom 11104 0 _ITG=true:=by decide+kernel
def _ITH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056be0f145f0fe3893608c4c0002
theorem shape9_81:validFrom 11103 0 _ITH=true:=by decide+kernel
def _ITI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056bc0f14991d448105c4bc60002
theorem shape9_82:validFrom 11102 0 _ITI=true:=by decide+kernel
def _ITJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ba0f14cfa97303e05cb3e0002
theorem shape9_83:validFrom 11101 0 _ITJ=true:=by decide+kernel
def _ITK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f15063446fd78c4ab10002
theorem shape9_84:validFrom 11100 0 _ITK=true:=by decide+kernel
def _ITL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f153cbdc0c3943ca220002
theorem shape9_85:validFrom 11099 0 _ITL=true:=by decide+kernel
def _ITM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f157345e00070e498e0002
theorem shape9_86:validFrom 11098 0 _ITM=true:=by decide+kernel
def _ITN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f15a9cca509ceac8f70002
theorem shape9_87:validFrom 11097 0 _ITN=true:=by decide+kernel
def _ITO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b00f15e0520f89eef485d0002
theorem shape9_88:validFrom 11096 0 _ITO=true:=by decide+kernel
def _ITP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ae0f1616d61fd690907be0002
theorem shape9_89:validFrom 11095 0 _ITP=true:=by decide+kernel
def _ITR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ac0f164d58d599f2ec71d0002
theorem shape9_90:validFrom 11094 0 _ITR=true:=by decide+kernel
def _ITS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056aa0f1683da3129d6dc6780002
theorem shape9_91:validFrom 11093 0 _ITS=true:=by decide+kernel
def _ITT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a80f16ba5a32307e645cf0002
theorem shape9_92:validFrom 11092 0 _ITT=true:=by decide+kernel
def _ITU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a60f16f0d8d8d8c6745230002
theorem shape9_93:validFrom 11091 0 _ITU=true:=by decide+kernel
def _ITV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a40f172756254d8e3c4730002
theorem shape9_94:validFrom 11090 0 _ITV=true:=by decide+kernel
def _ITW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a20f175dd217391b803c00002
theorem shape9_95:validFrom 11089 0 _ITW=true:=by decide+kernel
def _ITX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a00f17944caef123fc3090002
theorem shape9_96:validFrom 11088 0 _ITX=true:=by decide+kernel
def _ITY:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569e0f17cac5ec1ff43c24f0002
theorem shape9_97:validFrom 11087 0 _ITY=true:=by decide+kernel
def _ITZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569c0f18013dcf1b3f041910002
theorem shape9_98:validFrom 11086 0 _ITZ=true:=by decide+kernel
def _IUA:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569a0f1837b4578d53880cf0002
theorem shape9_99:validFrom 11085 0 _IUA=true:=by decide+kernel
def _IPZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056980f186e2985cbe25000a0002
theorem shape9_100:validFrom 11084 0 _IPZ=true:=by decide+kernel
def _IQA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3bcb1a7472fb1d20f18a49d598138b80020002
theorem shape9_101:validFrom 11083 0 _IQA=true:=by decide+kernel
def _IQB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3bca40aa8cf3d890f18db0fd30309dc0020002
theorem shape9_102:validFrom 11082 0 _IQB=true:=by decide+kernel
def _IQC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273bc966e611116990f191180f1fba59c0020002
theorem shape9_103:validFrom 11081 0 _IQC=true:=by decide+kernel
def _IQD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233bc88d26fdfd22c0f1947f0b6c0b7500020002
theorem shape9_104:validFrom 11080 0 _IQD=true:=by decide+kernel
def _IQE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3bc7b36d550da540f197e5f20fc96b00020002
theorem shape9_105:validFrom 11079 0 _IQE=true:=by decide+kernel
def _IQF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3bc6d9b914ec4e10f19b4cc3104ec7c0020002
theorem shape9_106:validFrom 11078 0 _IQF=true:=by decide+kernel
def _IQG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bc6000a3eefc950f19eb37e6840dac0020002
theorem shape9_107:validFrom 11077 0 _IQG=true:=by decide+kernel
def _IQH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bc52660d1c168c0f1a21a241cfa5d00020002
theorem shape9_108:validFrom 11076 0 _IQH=true:=by decide+kernel
def row9 (v:ℕ):List Piece:=match v with
 | 0=>d9_0
 | 1=>d9_1
 | 2=>d9_2
 | 3=>d9_3
 | 4=>d9_4
 | 5=>d9_5
 | 6=>d9_6
 | 7=>d9_7
 | 8=>d9_8
 | 9=>d9_9
 | 10=>_IPY
 | 11=>_IQI
 | 12=>_IQJ
 | 13=>_IQK
 | 14=>_IQL
 | 15=>_IQM
 | 16=>_IQN
 | 17=>_IQO
 | 18=>_IQP
 | 19=>_IQQ
 | 20=>_IQS
 | 21=>_IQT
 | 22=>_IQU
 | 23=>_IQV
 | 24=>_IQW
 | 25=>_IQX
 | 26=>_IQY
 | 27=>_IQZ
 | 28=>_IRA
 | 29=>_IRB
 | 30=>_IRD
 | 31=>_IRE
 | 32=>_IRF
 | 33=>_IRG
 | 34=>_IRH
 | 35=>_IRI
 | 36=>_IRJ
 | 37=>_IRK
 | 38=>_IRL
 | 39=>_IRM
 | 40=>_IRO
 | 41=>_IRP
 | 42=>_IRQ
 | 43=>_IRR
 | 44=>_IRS
 | 45=>_IRT
 | 46=>_IRU
 | 47=>_IRV
 | 48=>_IRW
 | 49=>_IRX
 | 50=>_IRZ
 | 51=>_ISA
 | 52=>_ISB
 | 53=>_ISC
 | 54=>_ISD
 | 55=>_ISE
 | 56=>_ISF
 | 57=>_ISG
 | 58=>_ISH
 | 59=>_ISI
 | 60=>_ISK
 | 61=>_ISL
 | 62=>_ISM
 | 63=>_ISN
 | 64=>_ISO
 | 65=>_ISP
 | 66=>_ISQ
 | 67=>_ISR
 | 68=>_ISS
 | 69=>_IST
 | 70=>_ISV
 | 71=>_ISW
 | 72=>_ISX
 | 73=>_ISY
 | 74=>_ISZ
 | 75=>_ITA
 | 76=>_ITB
 | 77=>_ITC
 | 78=>_ITD
 | 79=>_ITE
 | 80=>_ITG
 | 81=>_ITH
 | 82=>_ITI
 | 83=>_ITJ
 | 84=>_ITK
 | 85=>_ITL
 | 86=>_ITM
 | 87=>_ITN
 | 88=>_ITO
 | 89=>_ITP
 | 90=>_ITR
 | 91=>_ITS
 | 92=>_ITT
 | 93=>_ITU
 | 94=>_ITV
 | 95=>_ITW
 | 96=>_ITX
 | 97=>_ITY
 | 98=>_ITZ
 | 99=>_IUA
 | 100=>_IPZ
 | 101=>_IQA
 | 102=>_IQB
 | 103=>_IQC
 | 104=>_IQD
 | 105=>_IQE
 | 106=>_IQF
 | 107=>_IQG
 | 108=>_IQH
 | _=>[]
theorem checked9 (v:ℕ) (hy:9+v≤117):validFrom (11193-9-v) 0 (row9 v)=true:=by
 have hv:v≤108:=by omega
 interval_cases v
 · exact shape9_0
 · exact shape9_1
 · exact shape9_2
 · exact shape9_3
 · exact shape9_4
 · exact shape9_5
 · exact shape9_6
 · exact shape9_7
 · exact shape9_8
 · exact shape9_9
 · exact shape9_10
 · exact shape9_11
 · exact shape9_12
 · exact shape9_13
 · exact shape9_14
 · exact shape9_15
 · exact shape9_16
 · exact shape9_17
 · exact shape9_18
 · exact shape9_19
 · exact shape9_20
 · exact shape9_21
 · exact shape9_22
 · exact shape9_23
 · exact shape9_24
 · exact shape9_25
 · exact shape9_26
 · exact shape9_27
 · exact shape9_28
 · exact shape9_29
 · exact shape9_30
 · exact shape9_31
 · exact shape9_32
 · exact shape9_33
 · exact shape9_34
 · exact shape9_35
 · exact shape9_36
 · exact shape9_37
 · exact shape9_38
 · exact shape9_39
 · exact shape9_40
 · exact shape9_41
 · exact shape9_42
 · exact shape9_43
 · exact shape9_44
 · exact shape9_45
 · exact shape9_46
 · exact shape9_47
 · exact shape9_48
 · exact shape9_49
 · exact shape9_50
 · exact shape9_51
 · exact shape9_52
 · exact shape9_53
 · exact shape9_54
 · exact shape9_55
 · exact shape9_56
 · exact shape9_57
 · exact shape9_58
 · exact shape9_59
 · exact shape9_60
 · exact shape9_61
 · exact shape9_62
 · exact shape9_63
 · exact shape9_64
 · exact shape9_65
 · exact shape9_66
 · exact shape9_67
 · exact shape9_68
 · exact shape9_69
 · exact shape9_70
 · exact shape9_71
 · exact shape9_72
 · exact shape9_73
 · exact shape9_74
 · exact shape9_75
 · exact shape9_76
 · exact shape9_77
 · exact shape9_78
 · exact shape9_79
 · exact shape9_80
 · exact shape9_81
 · exact shape9_82
 · exact shape9_83
 · exact shape9_84
 · exact shape9_85
 · exact shape9_86
 · exact shape9_87
 · exact shape9_88
 · exact shape9_89
 · exact shape9_90
 · exact shape9_91
 · exact shape9_92
 · exact shape9_93
 · exact shape9_94
 · exact shape9_95
 · exact shape9_96
 · exact shape9_97
 · exact shape9_98
 · exact shape9_99
 · exact shape9_100
 · exact shape9_101
 · exact shape9_102
 · exact shape9_103
 · exact shape9_104
 · exact shape9_105
 · exact shape9_106
 · exact shape9_107
 · exact shape9_108
def _EMP:List Piece:=DZ.decode 58 42 0xa484aa4041ebbdde1c904502abaf5ea3aac58c7ab48cc69cf34d25eaaf64deb6fa3d84d0feca8c407152c0003
theorem shape10_0:validFrom 11183 0 _EMP=true:=by decide+kernel
def _EMQ:List Piece:=DZ.decode 58 42 0xa484aa4041ebcfc0e6b05163ebae5ea3aac58c7aba5f072de8bd55e26f64deb6fa3d880d4b7d7cf0b151a0003
theorem shape10_1:validFrom 11182 0 _EMQ=true:=by decide+kernel
def _ENJ:List Piece:=DZ.decode 58 42 0xa484aa4041ebe1ccd1faedd56bad5ea3aac58c7ac0199ed42cca75da6f64deb6fa3d8b4998306da0f15070003
theorem shape10_2:validFrom 11181 0 _ENJ=true:=by decide+kernel
def _ENU:List Piece:=DZ.decode 58 42 0xa484aa4041ebf3d8bd458a46ebac5ea3aac58c7ac5d4367a70d795d26f64deb6fa3d8e85e4e35e51314f40003
theorem shape10_3:validFrom 11180 0 _ENU=true:=by decide+kernel
def _EOF:List Piece:=DZ.decode 58 42 0xa484aa4041ec05bb876596a82bab5ea3aac58c7acba6770b6647c5ca2f64deb6fa3d91c231964f01714e20003
theorem shape10_4:validFrom 11179 0 _EOF=true:=by decide+kernel
def _EOQ:List Piece:=DZ.decode 58 42 0xa484aa4041ec17c772b03319abaa5ea3aac58c7ad1610eb1aa54e5c22f64deb6fa3d94fe7e493fb1b14cf0003
theorem shape10_5:validFrom 11178 0 _EOQ=true:=by decide+kernel
def _EPB:List Piece:=DZ.decode 58 42 0xa484aa4041ec29d35dfacf8b2ba95ea3aac58c7ad71ba657ee6205ba2f64deb6fa3d983acafc3061f14bc0003
theorem shape10_6:validFrom 11177 0 _EPB=true:=by decide+kernel
def _EPM:List Piece:=DZ.decode 58 42 0xa484aa4041ec3bb6281adbec6ba85ea3aac58c7adcbe9513810c15b1ef64deb6fa3d9b7717af2112314a80003
theorem shape10_7:validFrom 11176 0 _EPM=true:=by decide+kernel
def _EPX:List Piece:=DZ.decode 58 42 0xa484aa4041ec4dc21365785deba75ea3aac58c7ae2792cb9c51935a9ef64deb6fa3d9eb3646211c2714950003
theorem shape10_8:validFrom 11175 0 _EPX=true:=by decide+kernel
def _EQI:List Piece:=DZ.decode 58 42 0xa484aa4041ec5fcdfeb014cf6ba65ea3aac58c7ae833c460092655a1ef64deb6fa3da1efb1150272b14820003
theorem shape10_9:validFrom 11174 0 _EQI=true:=by decide+kernel
def _EMR:List Piece:=DZ.decode 58 42 0xa484aa4041ec71d9e9fab140eba55ea3aac58c7aedd6b31b9bd06599ef64deb6fa3da52bfdc7f322f146e0003
theorem shape10_10:validFrom 11173 0 _EMR=true:=by decide+kernel
def _ENA:List Piece:=DZ.decode 58 42 0xa484aa4041ec83bcb41abda22ba45ea3aac58c7af3914ac1dfdd8591af64deb6fa3da8684a7ae3d33145b0003
theorem shape10_11:validFrom 11172 0 _ENA=true:=by decide+kernel
def _ENB:List Piece:=DZ.decode 58 42 0xa484aa4041ec95c89f655a13aba35ea3aac58c7af934397d72879589af64deb6fa3daba4972dd483714470003
theorem shape10_12:validFrom 11171 0 _ENB=true:=by decide+kernel
def _ENC:List Piece:=DZ.decode 58 42 0xa484aa4041eca7d48aaff6852ba25ea3aac58c7afed728390531a581af64deb6fa3daee0e3e0c533b14330003
theorem shape10_13:validFrom 11170 0 _ENC=true:=by decide+kernel
def _END:List Piece:=DZ.decode 58 42 0xa484aa4041ecb9b754d002e66ba15ea3aac58c7b047a16f497dbb5796f64deb6fa3db21d3093b5e3f141f0003
theorem shape10_14:validFrom 11169 0 _END=true:=by decide+kernel
def _ENE:List Piece:=DZ.decode 58 42 0xa484aa4041eca601ce08606d2ba05ea3aac58c7b164a65bbfa596536af64deb6fa3db5597d46a6943140a0003
theorem shape10_15:validFrom 11168 0 _ENE=true:=by decide+kernel
def _ENF:List Piece:=DZ.decode 58 42 0xa484aa4041ecb6edd1290c6ceb9f5ea3aac58c7b1c450ad11505852cef64deb6fa3db895c9f99744713f60003
theorem shape10_16:validFrom 11167 0 _ENF=true:=by decide+kernel
def _ENG:List Piece:=DZ.decode 58 42 0xa484aa4041ecc802f574487ceb9e5ea3aac58c7b222806fb7e4e95236f64deb6fa3dbbd216ac87f4b13e10003
theorem shape10_17:validFrom 11166 0 _ENG=true:=by decide+kernel
def _ENH:List Piece:=DZ.decode 58 42 0xa484aa4041ecde1e62fd56112b9d5ea3aac58c7b2822ac1098fab51d2f64deb6fa3dbf0e635f78a4f13cd0003
theorem shape10_18:validFrom 11165 0 _ENH=true:=by decide+kernel
def _ENI:List Piece:=DZ.decode 58 42 0xa484aa4041ecef0a661e0210eb9c5ea3aac58c7b2e05a83b0243c5136f64deb6fa3dc24ab0126955313b80003
theorem shape10_19:validFrom 11164 0 _ENI=true:=by decide+kernel
def _ENK:List Piece:=DZ.decode 58 42 0xa484aa4041ecfff6693eae10ab9b5ea3aac58c7b33e8a4656b8cd509af64deb6fa3dc586fcc55a05713a30003
theorem shape10_20:validFrom 11163 0 _ENK=true:=by decide+kernel
def _ENL:List Piece:=DZ.decode 58 42 0xa484aa4041ed6ab4357a0f79ab9a5ea3aac58c7b39cba08fd4d5e53caf64deb6fa3dc8c349784ab5b138e0003
theorem shape10_21:validFrom 11162 0 _ENL=true:=by decide+kernel
def _ENM:List Piece:=DZ.decode 58 42 0xa484aa4041edbbf3552737686b995ea3aac58c7b3f96f3cf8cbbe55e6f64deb6fa3dcbff962b3b65f13780003
theorem shape10_22:validFrom 11161 0 _ENM=true:=by decide+kernel
def _ENN:List Piece:=DZ.decode 58 42 0xa484aa4041edccdf5847e3682b985ea3aac58c7b4579eff9f604f554af64deb6fa3dcf3be2de2c16313630003
theorem shape10_23:validFrom 11160 0 _ENN=true:=by decide+kernel
def _ENO:List Piece:=DZ.decode 58 42 0xa484aa4041edddf47c931f782b975ea3aac58c7b4b454339adeaf54b2f64deb6fa3dd2782f911cc67134d0003
theorem shape10_24:validFrom 11159 0 _ENO=true:=by decide+kernel
def _ENP:List Piece:=DZ.decode 58 42 0xa484aa4041edeee07fb3cb77eb965ea3aac58c7b5110967965d0f5416f64deb6fa3dd5b47c440d76b13370003
theorem shape10_25:validFrom 11158 0 _ENP=true:=by decide+kernel
def _ENQ:List Piece:=DZ.decode 58 42 0xa484aa4041edffcc82d47777ab955ea3aac58c7b56dbe9b91db6f537af64deb6fa3dd8f0c8f6fe26f13210003
theorem shape10_26:validFrom 11157 0 _ENQ=true:=by decide+kernel
def _ENR:List Piece:=DZ.decode 58 42 0xa484aa4041ee10b885f523776b945ea3aac58c7b5c8f940e2439e52def64deb6fa3ddc2d15a9eed73130a0003
theorem shape10_27:validFrom 11156 0 _ENR=true:=by decide+kernel
def _ENS:List Piece:=DZ.decode 58 42 0xa484aa4041ee21a48915cf772b935ea3aac58c7b625ae74ddc1fe5242f64deb6fa3ddf69625cdf87712f40003
theorem shape10_28:validFrom 11155 0 _ENS=true:=by decide+kernel
def _ENT:List Piece:=DZ.decode 58 42 0xa484aa4041ee32908c367b76eb925ea3aac58c7b680e91a2e2a2d51a6f64deb6fa3de2a5af0fd037b12dd0003
theorem shape10_29:validFrom 11154 0 _ENT=true:=by decide+kernel
def _ENV:List Piece:=DZ.decode 58 42 0xa484aa4041ee437c8f572776ab915ea3aac58c7b6dc23bf7e925c510af64deb6fa3de5e1fbc2c0e7f12c60003
theorem shape10_30:validFrom 11153 0 _ENV=true:=by decide+kernel
def _ENW:List Piece:=DZ.decode 58 42 0xa484aa4041ee5491b3a26386ab905ea3aac58c7b7375e64cefa8b5072f64deb6fa3de91e4875b198312af0003
theorem shape10_31:validFrom 11152 0 _ENW=true:=by decide+kernel
def _ENX:List Piece:=DZ.decode 58 42 0xa484aa4041ee657db6c30f866b8f5ea3aac58c7b7911e7b744c894fd6f64deb6fa3dec5a9528a248712970003
theorem shape10_32:validFrom 11151 0 _ENX=true:=by decide+kernel
def _ENY:List Piece:=DZ.decode 58 42 0xa484aa4041ee7669b9e3bb862b8e5ea3aac58c7b7eade92199e874f3af64deb6fa3def96e1db92f8b127f0003
theorem shape10_33:validFrom 11150 0 _ENY=true:=by decide+kernel
def _ENZ:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae34a484aa40410ee8755bd046785eb3b5ea3aac58c43b84619376a06b64e9ef64deb6fa30df2d32e8e83a8f12680004
theorem shape10_34:validFrom 11149 0 _ENZ=true:=by decide+kernel
def _EOA:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae30a484aa40410ee9841c0251385aa9c5ea3aac58c43b89e5ebf6442834e02f64deb6fa30df60f7b4174593124f0004
theorem shape10_35:validFrom 11148 0 _EOA=true:=by decide+kernel
def _EOB:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae2ca484aa40410eea92dc345bf8569f75ea3aac58c43b8f81ed60994814d66f64deb6fa30df94bc7f46509712370004
theorem shape10_36:validFrom 11147 0 _EOB=true:=by decide+kernel
def _EOC:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae28a484aa40410eeba19c6666b85294b5ea3aac58c43b950645e03d04e4ccaf64deb6fa30dfc8814a755b9b121e0004
theorem shape10_37:validFrom 11146 0 _EOC=true:=by decide+kernel
def _EOD:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae24a484aa40410eecb05c9871784e8995ea3aac58c43b9a8a9e5fe0c1b4c2ef64deb6fa30dffc4615a4669f12050004
theorem shape10_38:validFrom 11145 0 _EOD=true:=by decide+kernel
def _EOE:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae20a484aa40410eedc1aedd25394e7df5ea3aac58c43ba00ef6df847e84b96f64deb6fa30e0300ae0d371a311ec0004
theorem shape10_39:validFrom 11144 0 _EOE=true:=by decide+kernel
def _EOG:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae1ca484aa40410eeed06f0f2ff94a71c5ea3aac58c43ba57ba67476d844afaf64deb6fa30e063cfac027ca711d20004
theorem shape10_40:validFrom 11143 0 _EOG=true:=by decide+kernel
def _EOH:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae18a484aa40410eefdf2f413ab9466505ea3aac58c43baae85609693204a5ef64deb6fa30e09794773187ab11b80004
theorem shape10_41:validFrom 11142 0 _EOH=true:=by decide+kernel
def _EOI:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae14a484aa40410ef0edef734579425795ea3aac58c43bb055059e5b8bc49c2f64deb6fa30e0cb59426092af119e0004
theorem shape10_42:validFrom 11141 0 _EOI=true:=by decide+kernel
def _EOJ:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae10a484aa40410ef1fcafa550393e4965ea3aac58c43bb5aa0c489c8274926f64deb6fa30e0ff1e0d8f9db311830004
theorem shape10_43:validFrom 11140 0 _EOJ=true:=by decide+kernel
def _EOK:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae0ca484aa40410ef30b6fd75af93a3a85ea3aac58c43bbaff12f2dd792488af64deb6fa30e132e2d8bea8b711680004
theorem shape10_44:validFrom 11139 0 _EOK=true:=by decide+kernel
def _EOL:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae08a484aa40410ef41a300965b9362ad5ea3aac58c43bc054199d1e6fd47eef64deb6fa30e166a7a3edb3bb114d0004
theorem shape10_45:validFrom 11138 0 _EOL=true:=by decide+kernel
def _EOM:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae04a484aa40410ef52b824e197a361a75ea3aac58c43bc591775cae0374756f64deb6fa30e19a6c6f1cbebf11310004
theorem shape10_46:validFrom 11137 0 _EOM=true:=by decide+kernel
def _EON:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae00a484aa40410ef63a4280243a320945ea3aac58c43bcaced51c3d97146baf64deb6fa30e1ce313a4bc9c311150004
theorem shape10_47:validFrom 11136 0 _EON=true:=by decide+kernel
def _EOO:List Piece:=DZ.decode 62 42 0x3782dace9d900000adfca484aa40410ef74902b22efa2df755ea3aac58c43bcff489f11bc7a461ef64deb6fa30e201f6057ad4c710f80004
theorem shape10_48:validFrom 11135 0 _EOO=true:=by decide+kernel
def _EOP:List Piece:=DZ.decode 62 42 0x3782dace9d900000adf8a484aa40410ef857c2e439ba29e4a5ea3aac58c43bd51a3ec5f9f834582f64deb6fa30e235bad0a9dfcb10db0004
theorem shape10_49:validFrom 11134 0 _EOP=true:=by decide+kernel
def _EOR:List Piece:=DZ.decode 62 42 0x3782dace9d900000adf4a484aa40410ef9668316447a25d115ea3aac58c43bda3ff39ad828c44e6f64deb6fa30e2697f9bd8eacf10be0004
theorem shape10_50:validFrom 11133 0 _EOR=true:=by decide+kernel
def _EOS:List Piece:=DZ.decode 62 42 0x3782dace9d900000adf0a484aa40410efa7543484f3a21bcc5ea3aac58c43bdf4dff8504f64444af64deb6fa30e29d446707f5d310a00004
theorem shape10_51:validFrom 11132 0 _EOS=true:=by decide+kernel
def _EOT:List Piece:=DZ.decode 62 41 0x3782dace9d900000aded49095480821df70806f4b3f43b4f57a8eab16310e9772664abb1d690eb0003
theorem shape10_52:validFrom 11131 0 _EOT=true:=by decide+kernel
def _EOU:List Piece:=DZ.decode 62 41 0x3782dace9d900000ade949095480821df92aab7e1b763b2357a8eab16310e99675c2578b7c10c50003
theorem shape10_53:validFrom 11130 0 _EOU=true:=by decide+kernel
def _EOV:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b79a484aa40410ed2ecc3dcb99aa17ae0002
theorem shape10_54:validFrom 11129 0 _EOV=true:=by decide+kernel
def _EOW:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b78a484aa40410ed45fc4e68382396350002
theorem shape10_55:validFrom 11128 0 _EOW=true:=by decide+kernel
def _EOX:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b77a484aa40410ed5d2c5f04d69d14ae0002
theorem shape10_56:validFrom 11127 0 _EOX=true:=by decide+kernel
def _EOY:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7600000000000f0fea193fa5b2493fba484aa40410ed745c6fa17516931a0003
theorem shape10_57:validFrom 11126 0 _EOY=true:=by decide+kernel
def _EOZ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7500000000000f10240a6234472d3bfa484aa40410ed8b8c803e139011790003
theorem shape10_58:validFrom 11125 0 _EOZ=true:=by decide+kernel
def _EPA:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7400000000000f105dfa0e77ad793815e99d545850f0ad2ea5f3891ecfd8bd33aa8b090eda7a1f1868feccfa40004
theorem shape10_59:validFrom 11124 0 _EPA=true:=by decide+kernel
def _EPC:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7300000000000f1097e8446fe1cd33f5e99d545850f0b33cf0f8acfd4fadbd33aa8b090edcdf904a7b042cf780004
theorem shape10_60:validFrom 11123 0 _EPC=true:=by decide+kernel
def _EPD:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7200000000000f10d1d50446cacd2fb5e99d545850f0b962cb4d24a3cf80bd33aa8b090eddb5108242d2a8f4b0004
theorem shape10_61:validFrom 11122 0 _EPD=true:=by decide+kernel
def _EPE:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7100000000000f110bc04da89f092b55e99d545850f0bfb7db63b427cf52bd33aa8b090ede8a90ba0aa124f1c0004
theorem shape10_62:validFrom 11121 0 _EPE=true:=by decide+kernel
def _EPF:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7000000000000f1145aa20bf41d126b5e99d545850f0c6247acc24e5cf22bd33aa8b090edf6010f1d26fa0eeb0004
theorem shape10_63:validFrom 11120 0 _EPF=true:=by decide+kernel
def _EPG:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b6f00000000000f117f927d8ab61921e5e99d545850f0ccc04ff93acd0ef0bd33aa8b090ee03591299a3e1ceb80004
theorem shape10_64:validFrom 11119 0 _EPG=true:=by decide+kernel
def _EPH:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b6e00000000000f11b979640af8511cd5e99d545850f0d373b475a4a24ebcbd33aa8b090ee149d18c57056ce830004
theorem shape10_65:validFrom 11118 0 _EPH=true:=by decide+kernel
def _EPI:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb40000000000788f9af6a34f6a48bd5e99d545850ef881ed2f9e7cd4e860003
theorem shape10_66:validFrom 11117 0 _EPI=true:=by decide+kernel
def _EPJ:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb0000000000078916a16729e7228915e99d545850ef945d0ca9693b0e4e0003
theorem shape10_67:validFrom 11116 0 _EPJ=true:=by decide+kernel
def _EPK:List Piece:=DZ.decode 62 39 0x3782dace9d900000adac00000000007893392a8f9406a8645e99d545850efa0e22292e1334e130003
theorem shape10_68:validFrom 11115 0 _EPK=true:=by decide+kernel
def _EPL:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada8000000000078950832fa3009e834de99d545850efadae14b3c2b04dd60003
theorem shape10_69:validFrom 11114 0 _EPL=true:=by decide+kernel
def _EPN:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada400000000007896d72fb27294a8045e99d545850efbad88986793b4d970003
theorem shape10_70:validFrom 11113 0 _EPN=true:=by decide+kernel
def _EPO:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada000000000007898a620b9aa8967d1de99d545850efc849da9326644d550003
theorem shape10_71:validFrom 11112 0 _EPO=true:=by decide+kernel
def _EPP:List Piece:=DZ.decode 62 39 0x3782dace9d900000ad9c0000000000789a75060d3a00879dde99d545850efd60207d9ca2bcd110003
theorem shape10_72:validFrom 11111 0 _EPP=true:=by decide+kernel
def _EPQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056cc0f13887bf5ce0090ecf0002
theorem shape10_73:validFrom 11110 0 _EPQ=true:=by decide+kernel
def _EPR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ca0f13c255b3a98ee4e5f0002
theorem shape10_74:validFrom 11109 0 _EPR=true:=by decide+kernel
def _EPS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c80f13fc2dfb39ee38ded0002
theorem shape10_75:validFrom 11108 0 _EPS=true:=by decide+kernel
def _EPT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c60f143604cca8f78cd760002
theorem shape10_76:validFrom 11107 0 _EPT=true:=by decide+kernel
def _EPU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c40f146fda27a2f5b8cfd0002
theorem shape10_77:validFrom 11106 0 _EPU=true:=by decide+kernel
def _EPV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c20f14a9ae0c51c2d8c7f0002
theorem shape10_78:validFrom 11105 0 _EPV=true:=by decide+kernel
def _EPW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c00f14e3807ab56070bfe0002
theorem shape10_79:validFrom 11104 0 _EPW=true:=by decide+kernel
def _EPY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056be0f151d5172f7a4dcb7a0002
theorem shape10_80:validFrom 11103 0 _EPY=true:=by decide+kernel
def _EPZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056bc0f155672c27884c4af30002
theorem shape10_81:validFrom 11102 0 _EPZ=true:=by decide+kernel
def _EQA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ba0f158c29db088e38a670002
theorem shape10_82:validFrom 11101 0 _EQA=true:=by decide+kernel
def _EQB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f15c1df9c2ab2d89d90002
theorem shape10_83:validFrom 11100 0 _EQB=true:=by decide+kernel
def _EQC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f15f79406329ed49460002
theorem shape10_84:validFrom 11099 0 _EQC=true:=by decide+kernel
def _EQD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f162d4718cca6648b00002
theorem shape10_85:validFrom 11098 0 _EQD=true:=by decide+kernel
def _EQE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f1662f8d44c766c8170002
theorem shape10_86:validFrom 11097 0 _EQE=true:=by decide+kernel
def _EQF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b00f1698a9385e61c477a0002
theorem shape10_87:validFrom 11096 0 _EQF=true:=by decide+kernel
def _EQG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ae0f16ce58455614586da0002
theorem shape10_88:validFrom 11095 0 _EQG=true:=by decide+kernel
def _EQH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ac0f170405fadfe3806360002
theorem shape10_89:validFrom 11094 0 _EQH=true:=by decide+kernel
def _EQJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056aa0f1739b2594f78a458e0002
theorem shape10_90:validFrom 11093 0 _EQJ=true:=by decide+kernel
def _EQK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a80f176f5d60512b904e30002
theorem shape10_91:validFrom 11092 0 _EQK=true:=by decide+kernel
def _EQL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a60f17a507100ed24c4340002
theorem shape10_92:validFrom 11091 0 _EQL=true:=by decide+kernel
def _EQM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a40f17daaf68b23a003820002
theorem shape10_93:validFrom 11090 0 _EQM=true:=by decide+kernel
def _EQN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a20f18105669e7c4882cc0002
theorem shape10_94:validFrom 11089 0 _EQN=true:=by decide+kernel
def _EQO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a00f1845fc14030ecc2130002
theorem shape10_95:validFrom 11088 0 _EQO=true:=by decide+kernel
def _EQP:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569e0f187ba066b07ae01570002
theorem shape10_96:validFrom 11087 0 _EQP=true:=by decide+kernel
def _EQQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569c0f18b1436243a9500980002
theorem shape10_97:validFrom 11086 0 _EQQ=true:=by decide+kernel
def _EQR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373bca1155bf5c18c0f18e6e50668f9d00020002
theorem shape10_98:validFrom 11085 0 _EQR=true:=by decide+kernel
def _EQS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333bc93ad48b2fd4c0f191c8553740ad00020002
theorem shape10_99:validFrom 11084 0 _EQS=true:=by decide+kernel
def _EMS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3bc86458b4bb03a0f19522449113f180020002
theorem shape10_100:validFrom 11083 0 _EMS=true:=by decide+kernel
def _EMT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3bc78de23aaf3550f1987c1e79432ac0020002
theorem shape10_101:validFrom 11082 0 _EMT=true:=by decide+kernel
def _EMU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273bc6b7711e5ad510f19bd5e2ea94abc0020002
theorem shape10_102:validFrom 11081 0 _EMU=true:=by decide+kernel
def _EMV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233bc5e1055e6f7c70f19f2f91ea420e40020002
theorem shape10_103:validFrom 11080 0 _EMV=true:=by decide+kernel
def _EMW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3bc50a9efc3b8d10f1a2892b7311cbc0020002
theorem shape10_104:validFrom 11079 0 _EMW=true:=by decide+kernel
def _EMX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3bc4343df670aa30f1a5e2af8a3d5740020002
theorem shape10_105:validFrom 11078 0 _EMX=true:=by decide+kernel
def _EMY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bc35de24e5d2ba0f1a93c1e2a8b5180020002
theorem shape10_106:validFrom 11077 0 _EMY=true:=by decide+kernel
def _EMZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bc2878c02b2be80f1ac957759350600020002
theorem shape10_107:validFrom 11076 0 _EMZ=true:=by decide+kernel
def row10 (v:ℕ):List Piece:=match v with
 | 0=>_EMP
 | 1=>_EMQ
 | 2=>_ENJ
 | 3=>_ENU
 | 4=>_EOF
 | 5=>_EOQ
 | 6=>_EPB
 | 7=>_EPM
 | 8=>_EPX
 | 9=>_EQI
 | 10=>_EMR
 | 11=>_ENA
 | 12=>_ENB
 | 13=>_ENC
 | 14=>_END
 | 15=>_ENE
 | 16=>_ENF
 | 17=>_ENG
 | 18=>_ENH
 | 19=>_ENI
 | 20=>_ENK
 | 21=>_ENL
 | 22=>_ENM
 | 23=>_ENN
 | 24=>_ENO
 | 25=>_ENP
 | 26=>_ENQ
 | 27=>_ENR
 | 28=>_ENS
 | 29=>_ENT
 | 30=>_ENV
 | 31=>_ENW
 | 32=>_ENX
 | 33=>_ENY
 | 34=>_ENZ
 | 35=>_EOA
 | 36=>_EOB
 | 37=>_EOC
 | 38=>_EOD
 | 39=>_EOE
 | 40=>_EOG
 | 41=>_EOH
 | 42=>_EOI
 | 43=>_EOJ
 | 44=>_EOK
 | 45=>_EOL
 | 46=>_EOM
 | 47=>_EON
 | 48=>_EOO
 | 49=>_EOP
 | 50=>_EOR
 | 51=>_EOS
 | 52=>_EOT
 | 53=>_EOU
 | 54=>_EOV
 | 55=>_EOW
 | 56=>_EOX
 | 57=>_EOY
 | 58=>_EOZ
 | 59=>_EPA
 | 60=>_EPC
 | 61=>_EPD
 | 62=>_EPE
 | 63=>_EPF
 | 64=>_EPG
 | 65=>_EPH
 | 66=>_EPI
 | 67=>_EPJ
 | 68=>_EPK
 | 69=>_EPL
 | 70=>_EPN
 | 71=>_EPO
 | 72=>_EPP
 | 73=>_EPQ
 | 74=>_EPR
 | 75=>_EPS
 | 76=>_EPT
 | 77=>_EPU
 | 78=>_EPV
 | 79=>_EPW
 | 80=>_EPY
 | 81=>_EPZ
 | 82=>_EQA
 | 83=>_EQB
 | 84=>_EQC
 | 85=>_EQD
 | 86=>_EQE
 | 87=>_EQF
 | 88=>_EQG
 | 89=>_EQH
 | 90=>_EQJ
 | 91=>_EQK
 | 92=>_EQL
 | 93=>_EQM
 | 94=>_EQN
 | 95=>_EQO
 | 96=>_EQP
 | 97=>_EQQ
 | 98=>_EQR
 | 99=>_EQS
 | 100=>_EMS
 | 101=>_EMT
 | 102=>_EMU
 | 103=>_EMV
 | 104=>_EMW
 | 105=>_EMX
 | 106=>_EMY
 | 107=>_EMZ
 | _=>[]
theorem checked10 (v:ℕ) (hy:10+v≤117):validFrom (11193-10-v) 0 (row10 v)=true:=by
 have hv:v≤107:=by omega
 interval_cases v
 · exact shape10_0
 · exact shape10_1
 · exact shape10_2
 · exact shape10_3
 · exact shape10_4
 · exact shape10_5
 · exact shape10_6
 · exact shape10_7
 · exact shape10_8
 · exact shape10_9
 · exact shape10_10
 · exact shape10_11
 · exact shape10_12
 · exact shape10_13
 · exact shape10_14
 · exact shape10_15
 · exact shape10_16
 · exact shape10_17
 · exact shape10_18
 · exact shape10_19
 · exact shape10_20
 · exact shape10_21
 · exact shape10_22
 · exact shape10_23
 · exact shape10_24
 · exact shape10_25
 · exact shape10_26
 · exact shape10_27
 · exact shape10_28
 · exact shape10_29
 · exact shape10_30
 · exact shape10_31
 · exact shape10_32
 · exact shape10_33
 · exact shape10_34
 · exact shape10_35
 · exact shape10_36
 · exact shape10_37
 · exact shape10_38
 · exact shape10_39
 · exact shape10_40
 · exact shape10_41
 · exact shape10_42
 · exact shape10_43
 · exact shape10_44
 · exact shape10_45
 · exact shape10_46
 · exact shape10_47
 · exact shape10_48
 · exact shape10_49
 · exact shape10_50
 · exact shape10_51
 · exact shape10_52
 · exact shape10_53
 · exact shape10_54
 · exact shape10_55
 · exact shape10_56
 · exact shape10_57
 · exact shape10_58
 · exact shape10_59
 · exact shape10_60
 · exact shape10_61
 · exact shape10_62
 · exact shape10_63
 · exact shape10_64
 · exact shape10_65
 · exact shape10_66
 · exact shape10_67
 · exact shape10_68
 · exact shape10_69
 · exact shape10_70
 · exact shape10_71
 · exact shape10_72
 · exact shape10_73
 · exact shape10_74
 · exact shape10_75
 · exact shape10_76
 · exact shape10_77
 · exact shape10_78
 · exact shape10_79
 · exact shape10_80
 · exact shape10_81
 · exact shape10_82
 · exact shape10_83
 · exact shape10_84
 · exact shape10_85
 · exact shape10_86
 · exact shape10_87
 · exact shape10_88
 · exact shape10_89
 · exact shape10_90
 · exact shape10_91
 · exact shape10_92
 · exact shape10_93
 · exact shape10_94
 · exact shape10_95
 · exact shape10_96
 · exact shape10_97
 · exact shape10_98
 · exact shape10_99
 · exact shape10_100
 · exact shape10_101
 · exact shape10_102
 · exact shape10_103
 · exact shape10_104
 · exact shape10_105
 · exact shape10_106
 · exact shape10_107
def _EQT:List Piece:=DZ.decode 58 42 0xa484aa4041ec1d2b89448aa12bae5ea3aac58c7ad3a803bbd7a905bf2f64deb6fa3d9610e65767cf594cd0003
theorem shape11_0:validFrom 11182 0 _EQT=true:=by decide+kernel
def _EQU:List Piece:=DZ.decode 58 42 0xa484aa4041ec2f37748f2712abad5ea3aac58c7ad97a444ccd1935b72f64deb6fa3d994d330a587f994bb0003
theorem shape11_1:validFrom 11181 0 _EQU=true:=by decide+kernel
def _ERM:List Piece:=DZ.decode 58 42 0xa484aa4041ec411a3eaf3373ebac5ea3aac58c7adf34dbf3112655aeef64deb6fa3d9c897fbd492fd94a80003
theorem shape11_2:validFrom 11180 0 _ERM=true:=by decide+kernel
def _ERX:List Piece:=DZ.decode 58 42 0xa484aa4041ec532629f9cfe56bab5ea3aac58c7ae4ef7399553375a6ef64deb6fa3d9fc5cc7039e0194950003
theorem shape11_3:validFrom 11179 0 _ERX=true:=by decide+kernel
def _ESI:List Piece:=DZ.decode 58 42 0xa484aa4041ec653215446c56ebaa5ea3aac58c7aeaaa0b3f9940959eef64deb6fa3da30219232a90594820003
theorem shape11_4:validFrom 11178 0 _ESI=true:=by decide+kernel
def _EST:List Piece:=DZ.decode 58 42 0xa484aa4041ec7714df6478b82ba95ea3aac58c7af064a2e5dd4db596af64deb6fa3da63e65d61b409946f0003
theorem shape11_5:validFrom 11177 0 _EST=true:=by decide+kernel
def _ETE:List Piece:=DZ.decode 58 42 0xa484aa4041ec8920caaf1529aba85ea3aac58c7af60791a16ff7c58eaf64deb6fa3da97ab2890bf0d945b0003
theorem shape11_6:validFrom 11176 0 _ETE=true:=by decide+kernel
def _ETP:List Piece:=DZ.decode 58 42 0xa484aa4041ec9b2cb5f9b19b2ba75ea3aac58c7afbc22947b404e586af64deb6fa3dacb6ff3bfca1194480003
theorem shape11_7:validFrom 11175 0 _ETP=true:=by decide+kernel
def _EUA:List Piece:=DZ.decode 58 42 0xa484aa4041ecad38a1444e0caba65ea3aac58c7b0165180346aef57eaf64deb6fa3daff34beeed51594340003
theorem shape11_8:validFrom 11174 0 _EUA=true:=by decide+kernel
def _EUL:List Piece:=DZ.decode 58 42 0xa484aa4041ecbf1b6b645a6deba55ea3aac58c7b070806bed95905766f64deb6fa3db32f98a1de01994200003
theorem shape11_9:validFrom 11173 0 _EUL=true:=by decide+kernel
def _EQV:List Piece:=DZ.decode 58 42 0xa484aa4041ecd12756aef6df6ba45ea3aac58c7b0cc29e651d66256e6f64deb6fa3db66be554ceb1d940d0003
theorem shape11_10:validFrom 11172 0 _EQV=true:=by decide+kernel
def _ERD:List Piece:=DZ.decode 58 42 0xa484aa4041ece33341f99350eba35ea3aac58c7b12658d20b01035666f64deb6fa3db9a83207bf62193f90003
theorem shape11_11:validFrom 11171 0 _ERD=true:=by decide+kernel
def _ERE:List Piece:=DZ.decode 58 42 0xa484aa4041ecf5160c199fb22ba25ea3aac58c7b17f0d2f19157355e2f64deb6fa3dbce47ebab012593e40003
theorem shape11_12:validFrom 11170 0 _ERE=true:=by decide+kernel
def _ERF:List Piece:=DZ.decode 58 42 0xa484aa4041ed0721f7643c23aba15ea3aac58c7b1d93c1ad240145562f64deb6fa3dc020cb6da0c2993d00003
theorem shape11_13:validFrom 11169 0 _ERF=true:=by decide+kernel
def _ERG:List Piece:=DZ.decode 58 42 0xa484aa4041ed192de2aed8952ba05ea3aac58c7b2336b068b6ab554e2f64deb6fa3dc35d18209172d93bc0003
theorem shape11_14:validFrom 11168 0 _ERG=true:=by decide+kernel
def _ERH:List Piece:=DZ.decode 58 42 0xa484aa4041ecffd8d31583e32b9f5ea3aac58c7b36d3e297a1fd4502af64deb6fa3dc69964d38223193a70003
theorem shape11_15:validFrom 11167 0 _ERH=true:=by decide+kernel
def _ERI:List Piece:=DZ.decode 58 42 0xa484aa4041ed10c4d6362fe2eb9e5ea3aac58c7b3cb6dec20b4654f8ef64deb6fa3dc9d5b18672d3593920003
theorem shape11_16:validFrom 11166 0 _ERI=true:=by decide+kernel
def _ERJ:List Piece:=DZ.decode 58 42 0xa484aa4041ed21b0d956dbe2ab9d5ea3aac58c7b4299daec748f64ef2f64deb6fa3dcd11fe3963839937d0003
theorem shape11_17:validFrom 11165 0 _ERJ=true:=by decide+kernel
def _ERK:List Piece:=DZ.decode 58 42 0xa484aa4041ed37f5680a79872b9c5ea3aac58c7b487cd716ddd874e92f64deb6fa3dd04e4aec5433d93680003
theorem shape11_18:validFrom 11164 0 _ERK=true:=by decide+kernel
def _ERL:List Piece:=DZ.decode 58 42 0xa484aa4041ed48e16b2b2586eb9b5ea3aac58c7b4e5fd341472184df6f64deb6fa3dd38a979f44e4193530003
theorem shape11_19:validFrom 11163 0 _ERL=true:=by decide+kernel
def _ERN:List Piece:=DZ.decode 58 42 0xa484aa4041ed59cd6e4bd186ab9a5ea3aac58c7b5442cf6bb06a94d5af64deb6fa3dd6c6e45235945933e0003
theorem shape11_20:validFrom 11162 0 _ERN=true:=by decide+kernel
def _ERO:List Piece:=DZ.decode 58 42 0xa484aa4041edc48b3a8732efab995ea3aac58c7b5a0e22ab68509508af64deb6fa3dda0331052644993280003
theorem shape11_21:validFrom 11161 0 _ERO=true:=by decide+kernel
def _ERP:List Piece:=DZ.decode 58 42 0xa484aa4041ee15ca5a345ade6b985ea3aac58c7b5fd975eb2036952a6f64deb6fa3ddd3f7db816f4d93120003
theorem shape11_22:validFrom 11160 0 _ERP=true:=by decide+kernel
def _ERQ:List Piece:=DZ.decode 58 42 0xa484aa4041ee26b65d5506de2b975ea3aac58c7b65a4c92ad81c9520af64deb6fa3de07bca6b07a5192fc0003
theorem shape11_23:validFrom 11159 0 _ERQ=true:=by decide+kernel
def _ERR:List Piece:=DZ.decode 58 42 0xa484aa4041ee37a26075b2ddeb965ea3aac58c7b6b701c6a90029516ef64deb6fa3de3b8171df855592e60003
theorem shape11_24:validFrom 11158 0 _ERR=true:=by decide+kernel
def _ERS:List Piece:=DZ.decode 58 42 0xa484aa4041ee48b784c0eeedeb955ea3aac58c7b7123c6bf9685850d6f64deb6fa3de6f463d0e905992cf0003
theorem shape11_25:validFrom 11157 0 _ERS=true:=by decide+kernel
def _ERT:List Piece:=DZ.decode 58 42 0xa484aa4041ee59a387e19aedab945ea3aac58c7b76ef19ff4e6b8503af64deb6fa3dea30b083d9b5d92b90003
theorem shape11_26:validFrom 11156 0 _ERT=true:=by decide+kernel
def _ERU:List Piece:=DZ.decode 58 42 0xa484aa4041ee6a8f8b0246ed6b935ea3aac58c7b7ca2c45454ee74f9ef64deb6fa3ded6cfd36ca66192a20003
theorem shape11_27:validFrom 11155 0 _ERU=true:=by decide+kernel
def _ERV:List Piece:=DZ.decode 58 42 0xa484aa4041ee7b7b8e22f2ed2b925ea3aac58c7b82566ea95b7164f02f64deb6fa3df0a949e9bb165928b0003
theorem shape11_28:validFrom 11154 0 _ERV=true:=by decide+kernel
def _ERW:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae44a484aa40410ee8c6791439eeceb515ea3aac58c43b880a18fe61f454e66f64deb6fa30df3e5969cabc6992740004
theorem shape11_29:validFrom 11153 0 _ERW=true:=by decide+kernel
def _ERY:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae40a484aa40410ee9d5394644aecaabb5ea3aac58c43b8da61a68b71434dcaf64deb6fa30df721e34f9c76d925c0004
theorem shape11_30:validFrom 11152 0 _ERY=true:=by decide+kernel
def _ERZ:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae3ca484aa40410eeae3f9784f6ec6a205ea3aac58c43b93421bd30c3414d2ef64deb6fa30dfa5e30028d27192440004
theorem shape11_31:validFrom 11151 0 _ERZ=true:=by decide+kernel
def _ESA:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae38a484aa40410eebf54bbd032fc69815ea3aac58c43b98de1d3d6153f4c96f64deb6fa30dfd9a7cb57dd75922c0004
theorem shape11_32:validFrom 11150 0 _ESA=true:=by decide+kernel
def _ESB:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae34a484aa40410eed040bef0defc28dc5ea3aac58c43b9e7a1ea7b673d4bfaf64deb6fa30e00d6c9686e87992140004
theorem shape11_33:validFrom 11149 0 _ESB=true:=by decide+kernel
def _ESC:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae30a484aa40410eee12cc2118afbe8325ea3aac58c43ba41620120b93b4b5ef64deb6fa30e0413161b5f37d91fc0004
theorem shape11_34:validFrom 11148 0 _ESC=true:=by decide+kernel
def _ESD:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae2ca484aa40410eef218c53236fba7815ea3aac58c43ba99a7891af5084ac2f64deb6fa30e074f62ce4fe8191e30004
theorem shape11_35:validFrom 11147 0 _ESD=true:=by decide+kernel
def _ESE:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae28a484aa40410ef0304c852e2fb66c95ea3aac58c43baf1ed111530d54a26f64deb6fa30e0a8baf814098591ca0004
theorem shape11_36:validFrom 11146 0 _ESE=true:=by decide+kernel
def _ESF:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae24a484aa40410ef13f0cb738efb26095ea3aac58c43bb48b80a645671498af64deb6fa30e0dc7fc343148991b00004
theorem shape11_37:validFrom 11145 0 _ESF=true:=by decide+kernel
def _ESG:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae20a484aa40410ef24dcce943afae5415ea3aac58c43bba0fd925e923e48eef64deb6fa30e110448e721f8d91970004
theorem shape11_38:validFrom 11144 0 _ESG=true:=by decide+kernel
def _ESH:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae1ca484aa40410ef35f1f2df770ae4715ea3aac58c43bbf7c88badb7da4856f64deb6fa30e1440959a12a91917d0004
theorem shape11_39:validFrom 11143 0 _ESH=true:=by decide+kernel
def _ESJ:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae18a484aa40410ef46ddf600230aa3965ea3aac58c43bc4d18f651c74547baf64deb6fa30e177ce24d0359591620004
theorem shape11_40:validFrom 11142 0 _ESJ=true:=by decide+kernel
def _ESK:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae14a484aa40410ef57c9f920cf0a62b15ea3aac58c43bca26960f5d6b0471ef64deb6fa30e1ab92efff409991470004
theorem shape11_41:validFrom 11141 0 _ESK=true:=by decide+kernel
def _ESL:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae10a484aa40410ef68b5fc417b0a21c25ea3aac58c43bcf7b9cb99e61b4682f64deb6fa30e1df57bb2e4b9d912c0004
theorem shape11_42:validFrom 11140 0 _ESL=true:=by decide+kernel
def _ESM:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae0ca484aa40410ef79a1ff622709e0c85ea3aac58c43bd4d0a363df58645e6f64deb6fa30e2131c865d56a191110004
theorem shape11_43:validFrom 11139 0 _ESM=true:=by decide+kernel
def _ESN:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae08a484aa40410ef8a8e0282d3099fc25ea3aac58c43bda0e01236eec0454af64deb6fa30e246e1518c61a590f50004
theorem shape11_44:validFrom 11138 0 _ESN=true:=by decide+kernel
def _ESO:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae04a484aa40410ef9b7a05a37f095eb05ea3aac58c43bdf4b5ee2fe7fa44aef64deb6fa30e27aa61cbb6ca990d90004
theorem shape11_45:validFrom 11137 0 _ESO=true:=by decide+kernel
def _ESP:List Piece:=DZ.decode 62 42 0x3782dace9d900000ae00a484aa40410efac8f29eebb195d935ea3aac58c43be47113b7dcb034416f64deb6fa30e2ae6ae7ea77ad90bc0004
theorem shape11_46:validFrom 11136 0 _ESP=true:=by decide+kernel
def _ESQ:List Piece:=DZ.decode 62 42 0x3782dace9d900000adfca484aa40410efbd7b2d0f67191c695ea3aac58c43be996c88cbae0c437af64deb6fa30e2e22fb31982b1909f0004
theorem shape11_47:validFrom 11135 0 _ESQ=true:=by decide+kernel
def _ESR:List Piece:=DZ.decode 62 42 0x3782dace9d900000adf8a484aa40410efcf0bb4da5359db335ea3aac58c43bee80cc6da220d42eef64deb6fa30e315f47e488db590820004
theorem shape11_48:validFrom 11134 0 _ESR=true:=by decide+kernel
def _ESS:List Piece:=DZ.decode 62 42 0x3782dace9d900000adf4a484aa40410efe117a024efcb59f15ea3aac58c43bf33721fe46ec4426ef64deb6fa30e349b9497798b990640004
theorem shape11_49:validFrom 11133 0 _ESS=true:=by decide+kernel
def _ESU:List Piece:=DZ.decode 62 42 0x3782dace9d900000adf0a484aa40410eff3238b6f8c3cd8a25ea3aac58c43bf7d5cea43a54a41eef64deb6fa30e37d7e14a6a3bd90450004
theorem shape11_50:validFrom 11132 0 _ESU=true:=by decide+kernel
def _ESV:List Piece:=DZ.decode 62 42 0x3782dace9d900000adeca484aa40410f00506558f989e17465ea3aac58c43bfc747b4a2dbd0416af64deb6fa30e3b142dfd5aec190260004
theorem shape11_51:validFrom 11131 0 _ESV=true:=by decide+kernel
def _ESW:List Piece:=DZ.decode 62 41 0x3782dace9d900000ade949095480821e02e2481b46a1f2bbd7a8eab16310ea177b79bc59bfd03a0003
theorem shape11_52:validFrom 11130 0 _ESW=true:=by decide+kernel
def _ESX:List Piece:=DZ.decode 62 41 0x3782dace9d900000ade549095480821e04658c1fbfe4fa8d17a8eab16310ea3d3500d08f484ff50003
theorem shape11_53:validFrom 11129 0 _ESX=true:=by decide+kernel
def _ESY:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7800000000000f104bf96fc9dd713d3a484aa40410edc107bc344367d2e6bd33aa8b090eda69c0037af2a408f0004
theorem shape11_54:validFrom 11128 0 _ESY=true:=by decide+kernel
def _ESZ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7700000000000f1084fc75d927a1398a484aa40410ee18295cfcdb24d156bd33aa8b090edb4376892dc66c21d0004
theorem shape11_55:validFrom 11127 0 _ESZ=true:=by decide+kernel
def _ETA:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7600000000000f10bdfe09b1756135c5e99d545850f0b93f6790403a0fbca484aa40410ee6c146672319ccfb9bd33aa8b090edc248fa900e0003970005
theorem shape11_56:validFrom 11126 0 _ETA=true:=by decide+kernel
def _ETB:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7500000000000f10f6fe2b29e98931d5e99d545850f0ba88a7ae4e89cf91bd33aa8b090f069cb0cd56cc50f5da484aa40410eebcf1f9bed6e00e0fbd33aa8b090edd0d0b62f43e344fe0006
theorem shape11_57:validFrom 11125 0 _ETB=true:=by decide+kernel
def _ETC:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7400000000000f112ffcda42865d2dc5e99d545850f0c07053cef9cf8f66bd33aa8b090f0277cbecee91e0f31a484aa40410ef0c0b20374b708c58bd33aa8b090eddf9f4e85db58065a0006
theorem shape11_58:validFrom 11124 0 _ETC=true:=by decide+kernel
def _ETD:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7300000000000f1168fa16fb488d2985e99d545850f0c68735f2ffc60f39bd33aa8b090edeee41080e320cf030004
theorem shape11_59:validFrom 11123 0 _ETD=true:=by decide+kernel
def _ETF:List Piece:=DZ.decode 62 39 0x3782dace9d900000adc80000000000788d0faf0aa192c928de99d545850ef6e1d0a7faa644f0b0003
theorem shape11_60:validFrom 11122 0 _ETF=true:=by decide+kernel
def _ETG:List Piece:=DZ.decode 62 39 0x3782dace9d900000adc40000000000788ed781ca6a1489045e99d545850ef79018ea9a7f80edb0003
theorem shape11_61:validFrom 11121 0 _ETG=true:=by decide+kernel
def _ETH:List Piece:=DZ.decode 62 39 0x3782dace9d900000adc0000000000078909f48f5ed23c8ddde99d545850ef842cef4c519dcea90003
theorem shape11_62:validFrom 11120 0 _ETH=true:=by decide+kernel
def _ETI:List Piece:=DZ.decode 62 39 0x3782dace9d900000adbc0000000000789267048fb81f68b5de99d545850ef8fb6d2dcf8b6ce760003
theorem shape11_63:validFrom 11119 0 _ETI=true:=by decide+kernel
def _ETJ:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb8000000000078942eb496844e688bde99d545850ef9b8792e64bf4ce400003
theorem shape11_64:validFrom 11118 0 _ETJ=true:=by decide+kernel
def _ETK:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb400000000007895f6590a51c3c8605e99d545850efa79f2f684b31ce080003
theorem shape11_65:validFrom 11117 0 _ETK=true:=by decide+kernel
def _ETL:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb000000000007897bdf1eb2062e8335e99d545850efb3fda862f6808dcd0003
theorem shape11_66:validFrom 11116 0 _ETL=true:=by decide+kernel
def _ETM:List Piece:=DZ.decode 62 39 0x3782dace9d900000adac00000000007899857f38f03f08045e99d545850efc0baa44b9f430d910003
theorem shape11_67:validFrom 11115 0 _ETM=true:=by decide+kernel
def _ETN:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada80000000000789b4d00f3c14e87d3de99d545850efcdd6232245780d510003
theorem shape11_68:validFrom 11114 0 _ETN=true:=by decide+kernel
def _ETO:List Piece:=DZ.decode 62 39 0x3782dace9d900000ada40000000000789d14771a4d0e87a1de99d545850efdb20d7fc465e0d100003
theorem shape11_69:validFrom 11113 0 _ETO=true:=by decide+kernel
def _ETQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d00f13db7c35e41260edb0002
theorem shape11_70:validFrom 11112 0 _ETQ=true:=by decide+kernel
def _ETR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ce0f141468161eaa94e700002
theorem shape11_71:validFrom 11111 0 _ETR=true:=by decide+kernel
def _ETS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056cc0f144d5283f96a74e020002
theorem shape11_72:validFrom 11110 0 _ETS=true:=by decide+kernel
def _ETT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ca0f14863b7f7450acd8f0002
theorem shape11_73:validFrom 11109 0 _ETT=true:=by decide+kernel
def _ETU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c80f14bf23088f5de8d1a0002
theorem shape11_74:validFrom 11108 0 _ETU=true:=by decide+kernel
def _ETV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c60f14f8091f4a918cca10002
theorem shape11_75:validFrom 11107 0 _ETV=true:=by decide+kernel
def _ETW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c40f1530edc37d1fa4c250002
theorem shape11_76:validFrom 11106 0 _ETW=true:=by decide+kernel
def _ETX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c20f1569d0f578a1ecba50002
theorem shape11_77:validFrom 11105 0 _ETX=true:=by decide+kernel
def _ETY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c00f15a2b2b5144bd4b220002
theorem shape11_78:validFrom 11104 0 _ETY=true:=by decide+kernel
def _ETZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056be0f15db9302501d8ca9b0002
theorem shape11_79:validFrom 11103 0 _ETZ=true:=by decide+kernel
def _EUB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056bc0f1613c84070025ca110002
theorem shape11_80:validFrom 11102 0 _EUB=true:=by decide+kernel
def _EUC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ba0f1648aa430d3c189830002
theorem shape11_81:validFrom 11101 0 _EUC=true:=by decide+kernel
def _EUD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f167d8af157eb748f20002
theorem shape11_82:validFrom 11100 0 _EUD=true:=by decide+kernel
def _EUE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f16b26a4ba1a96c85d0002
theorem shape11_83:validFrom 11099 0 _EUE=true:=by decide+kernel
def _EUF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f16e7485198dd607c40002
theorem shape11_84:validFrom 11098 0 _EUF=true:=by decide+kernel
def _EUG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f171c25038f1ca87280002
theorem shape11_85:validFrom 11097 0 _EUG=true:=by decide+kernel
def _EUH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b00f1751006132d6186890002
theorem shape11_86:validFrom 11096 0 _EUH=true:=by decide+kernel
def _EUI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ae0f1785da6ad598245e70002
theorem shape11_87:validFrom 11095 0 _EUI=true:=by decide+kernel
def _EUJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ac0f17bab32025d40c5410002
theorem shape11_88:validFrom 11094 0 _EUJ=true:=by decide+kernel
def _EUK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056aa0f17ef8a817518dc4970002
theorem shape11_89:validFrom 11093 0 _EUK=true:=by decide+kernel
def _EUM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a80f1824608e71da543e90002
theorem shape11_90:validFrom 11092 0 _EUM=true:=by decide+kernel
def _EUN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a60f1859354744dc843380002
theorem shape11_91:validFrom 11091 0 _EUN=true:=by decide+kernel
def _EUO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a40f188e08ac16e5c82830002
theorem shape11_92:validFrom 11090 0 _EUO=true:=by decide+kernel
def _EUP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a20f18c2dabc966d941cb0002
theorem shape11_93:validFrom 11089 0 _EUP=true:=by decide+kernel
def _EUQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a00f18f7ab7914f99c1100002
theorem shape11_94:validFrom 11088 0 _EUQ=true:=by decide+kernel
def _EUR:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000569e0f192c7ae14103280520002
theorem shape11_95:validFrom 11087 0 _EUR=true:=by decide+kernel
def _EUS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3bc827c6034fb830f196148f56c11f40020002
theorem shape11_96:validFrom 11086 0 _EUS=true:=by decide+kernel
def _EUT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373bc7549303ed78f0f199615b544a1c40020002
theorem shape11_97:validFrom 11085 0 _EUT=true:=by decide+kernel
def _EUU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333bc68165548f32c0f19cae1211c33500020002
theorem shape11_98:validFrom 11084 0 _EUU=true:=by decide+kernel
def _EUV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3bc5ae3cf67aea30f19ffab38a145740020002
theorem shape11_99:validFrom 11083 0 _EUV=true:=by decide+kernel
def _EQW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3bc4db19e86a9200f1a3473fc255b800020002
theorem shape11_100:validFrom 11082 0 _EQW=true:=by decide+kernel
def _EQX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273bc407fc2ba43990f1a693b6b56f19c0020002
theorem shape11_101:validFrom 11081 0 _EQX=true:=by decide+kernel
def _EQY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233bc334e3bee1dd40f1a9e01868788b00020002
theorem shape11_102:validFrom 11080 0 _EQY=true:=by decide+kernel
def _EQZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3bc261d0a36974d0f1ad2c64d65a2cc0020002
theorem shape11_103:validFrom 11079 0 _EQZ=true:=by decide+kernel
def _ERA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3bc18ec2d7f50650f1b0789c042be6c0020002
theorem shape11_104:validFrom 11078 0 _ERA=true:=by decide+kernel
def _ERB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bc0bbba5dca8e00f1b3c4bdecd5c800020002
theorem shape11_105:validFrom 11077 0 _ERB=true:=by decide+kernel
def _ERC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bbfe8b733a41b80f1b710ca956f9200020002
theorem shape11_106:validFrom 11076 0 _ERC=true:=by decide+kernel
def row11 (v:ℕ):List Piece:=match v with
 | 0=>_EQT
 | 1=>_EQU
 | 2=>_ERM
 | 3=>_ERX
 | 4=>_ESI
 | 5=>_EST
 | 6=>_ETE
 | 7=>_ETP
 | 8=>_EUA
 | 9=>_EUL
 | 10=>_EQV
 | 11=>_ERD
 | 12=>_ERE
 | 13=>_ERF
 | 14=>_ERG
 | 15=>_ERH
 | 16=>_ERI
 | 17=>_ERJ
 | 18=>_ERK
 | 19=>_ERL
 | 20=>_ERN
 | 21=>_ERO
 | 22=>_ERP
 | 23=>_ERQ
 | 24=>_ERR
 | 25=>_ERS
 | 26=>_ERT
 | 27=>_ERU
 | 28=>_ERV
 | 29=>_ERW
 | 30=>_ERY
 | 31=>_ERZ
 | 32=>_ESA
 | 33=>_ESB
 | 34=>_ESC
 | 35=>_ESD
 | 36=>_ESE
 | 37=>_ESF
 | 38=>_ESG
 | 39=>_ESH
 | 40=>_ESJ
 | 41=>_ESK
 | 42=>_ESL
 | 43=>_ESM
 | 44=>_ESN
 | 45=>_ESO
 | 46=>_ESP
 | 47=>_ESQ
 | 48=>_ESR
 | 49=>_ESS
 | 50=>_ESU
 | 51=>_ESV
 | 52=>_ESW
 | 53=>_ESX
 | 54=>_ESY
 | 55=>_ESZ
 | 56=>_ETA
 | 57=>_ETB
 | 58=>_ETC
 | 59=>_ETD
 | 60=>_ETF
 | 61=>_ETG
 | 62=>_ETH
 | 63=>_ETI
 | 64=>_ETJ
 | 65=>_ETK
 | 66=>_ETL
 | 67=>_ETM
 | 68=>_ETN
 | 69=>_ETO
 | 70=>_ETQ
 | 71=>_ETR
 | 72=>_ETS
 | 73=>_ETT
 | 74=>_ETU
 | 75=>_ETV
 | 76=>_ETW
 | 77=>_ETX
 | 78=>_ETY
 | 79=>_ETZ
 | 80=>_EUB
 | 81=>_EUC
 | 82=>_EUD
 | 83=>_EUE
 | 84=>_EUF
 | 85=>_EUG
 | 86=>_EUH
 | 87=>_EUI
 | 88=>_EUJ
 | 89=>_EUK
 | 90=>_EUM
 | 91=>_EUN
 | 92=>_EUO
 | 93=>_EUP
 | 94=>_EUQ
 | 95=>_EUR
 | 96=>_EUS
 | 97=>_EUT
 | 98=>_EUU
 | 99=>_EUV
 | 100=>_EQW
 | 101=>_EQX
 | 102=>_EQY
 | 103=>_EQZ
 | 104=>_ERA
 | 105=>_ERB
 | 106=>_ERC
 | _=>[]
theorem checked11 (v:ℕ) (hy:11+v≤117):validFrom (11193-11-v) 0 (row11 v)=true:=by
 have hv:v≤106:=by omega
 interval_cases v
 · exact shape11_0
 · exact shape11_1
 · exact shape11_2
 · exact shape11_3
 · exact shape11_4
 · exact shape11_5
 · exact shape11_6
 · exact shape11_7
 · exact shape11_8
 · exact shape11_9
 · exact shape11_10
 · exact shape11_11
 · exact shape11_12
 · exact shape11_13
 · exact shape11_14
 · exact shape11_15
 · exact shape11_16
 · exact shape11_17
 · exact shape11_18
 · exact shape11_19
 · exact shape11_20
 · exact shape11_21
 · exact shape11_22
 · exact shape11_23
 · exact shape11_24
 · exact shape11_25
 · exact shape11_26
 · exact shape11_27
 · exact shape11_28
 · exact shape11_29
 · exact shape11_30
 · exact shape11_31
 · exact shape11_32
 · exact shape11_33
 · exact shape11_34
 · exact shape11_35
 · exact shape11_36
 · exact shape11_37
 · exact shape11_38
 · exact shape11_39
 · exact shape11_40
 · exact shape11_41
 · exact shape11_42
 · exact shape11_43
 · exact shape11_44
 · exact shape11_45
 · exact shape11_46
 · exact shape11_47
 · exact shape11_48
 · exact shape11_49
 · exact shape11_50
 · exact shape11_51
 · exact shape11_52
 · exact shape11_53
 · exact shape11_54
 · exact shape11_55
 · exact shape11_56
 · exact shape11_57
 · exact shape11_58
 · exact shape11_59
 · exact shape11_60
 · exact shape11_61
 · exact shape11_62
 · exact shape11_63
 · exact shape11_64
 · exact shape11_65
 · exact shape11_66
 · exact shape11_67
 · exact shape11_68
 · exact shape11_69
 · exact shape11_70
 · exact shape11_71
 · exact shape11_72
 · exact shape11_73
 · exact shape11_74
 · exact shape11_75
 · exact shape11_76
 · exact shape11_77
 · exact shape11_78
 · exact shape11_79
 · exact shape11_80
 · exact shape11_81
 · exact shape11_82
 · exact shape11_83
 · exact shape11_84
 · exact shape11_85
 · exact shape11_86
 · exact shape11_87
 · exact shape11_88
 · exact shape11_89
 · exact shape11_90
 · exact shape11_91
 · exact shape11_92
 · exact shape11_93
 · exact shape11_94
 · exact shape11_95
 · exact shape11_96
 · exact shape11_97
 · exact shape11_98
 · exact shape11_99
 · exact shape11_100
 · exact shape11_101
 · exact shape11_102
 · exact shape11_103
 · exact shape11_104
 · exact shape11_105
 · exact shape11_106
def _EUW:List Piece:=DZ.decode 58 42 0xa484aa4041ec7c78f5f8d03fabad5ea3aac58c7af27c461aa7dbb593af64deb6fa3dad663981b68a3146b0003
theorem shape12_0:validFrom 11181 0 _EUW=true:=by decide+kernel
def _EUX:List Piece:=DZ.decode 58 42 0xa484aa4041ec8e84e1436cb12bac5ea3aac58c7af836ddc0ebe8d58baf64deb6fa3db0a28634a73a714580003
theorem shape12_1:validFrom 11180 0 _EUX=true:=by decide+kernel
def _EVO:List Piece:=DZ.decode 58 42 0xa484aa4041eca090cc8e0922abab5ea3aac58c7afdf175672ff5f583af64deb6fa3db3ded2e797eab14450003
theorem shape12_2:validFrom 11179 0 _EVO=true:=by decide+kernel
def _EVZ:List Piece:=DZ.decode 58 42 0xa484aa4041ecb27396ae1583ebaa5ea3aac58c7b03ac0d0d7403157b6f64deb6fa3db71b1f9a889af14320003
theorem shape12_3:validFrom 11178 0 _EVZ=true:=by decide+kernel
def _EWK:List Piece:=DZ.decode 58 42 0xa484aa4041ecc47f81f8b1f56ba95ea3aac58c7b094efbc906ad25736f64deb6fa3dba576c4d794b3141e0003
theorem shape12_4:validFrom 11177 0 _EWK=true:=by decide+kernel
def _EWV:List Piece:=DZ.decode 58 42 0xa484aa4041ecd68b6d434e66eba85ea3aac58c7b0f09936f4aba456b6f64deb6fa3dbd93b90069fb7140b0003
theorem shape12_5:validFrom 11176 0 _EWV=true:=by decide+kernel
def _EXG:List Piece:=DZ.decode 58 42 0xa484aa4041ece897588dead86ba75ea3aac58c7b14ac822add6455636f64deb6fa3dc0d005b35aabb13f70003
theorem shape12_6:validFrom 11175 0 _EXG=true:=by decide+kernel
def _EXR:List Piece:=DZ.decode 58 42 0xa484aa4041ecfa7a22adf739aba65ea3aac58c7b1a4f70e6700e655b2f64deb6fa3dc40c52664b5bf13e30003
theorem shape12_7:validFrom 11174 0 _EXR=true:=by decide+kernel
def _EYC:List Piece:=DZ.decode 58 42 0xa484aa4041ed0c860df893ab2ba55ea3aac58c7b1ff25fa202b875532f64deb6fa3dc7489f193c0c313cf0003
theorem shape12_8:validFrom 11173 0 _EYC=true:=by decide+kernel
def _EYN:List Piece:=DZ.decode 58 42 0xa484aa4041ed1e91f943301caba45ea3aac58c7b25954e5d9562854b2f64deb6fa3dca84ebcc2cbc713bb0003
theorem shape12_9:validFrom 11172 0 _EYN=true:=by decide+kernel
def _EUY:List Piece:=DZ.decode 58 42 0xa484aa4041ed3074c3633c7deba35ea3aac58c7b2b383d19280c9542ef64deb6fa3dcdc1387f1d6cb13a70003
theorem shape12_10:validFrom 11171 0 _EUY=true:=by decide+kernel
def _EVF:List Piece:=DZ.decode 58 42 0xa484aa4041ed4280aeadd8ef6ba25ea3aac58c7b30db2bd4bab6a53aef64deb6fa3dd0fd85320e1cf13930003
theorem shape12_11:validFrom 11170 0 _EVF=true:=by decide+kernel
def _EVG:List Piece:=DZ.decode 58 42 0xa484aa4041ed548c99f87560eba15ea3aac58c7b366671a59bfda532ef64deb6fa3dd439d1e4fecd3137e0003
theorem shape12_12:validFrom 11169 0 _EVG=true:=by decide+kernel
def _EVH:List Piece:=DZ.decode 58 42 0xa484aa4041ed666f641881c22ba05ea3aac58c7b3c0960612ea7b52aaf64deb6fa3dd7761e97ef7d7136a0003
theorem shape12_13:validFrom 11168 0 _EVH=true:=by decide+kernel
def _EVI:List Piece:=DZ.decode 58 42 0xa484aa4041ed787b4f631e33ab9f5ea3aac58c7b4194a6320feeb522af64deb6fa3ddab26b4ae02db13550003
theorem shape12_14:validFrom 11167 0 _EVI=true:=by decide+kernel
def _EVJ:List Piece:=DZ.decode 58 42 0x29212a90107b56a9a7c881eeaae7af64deb6fa3dddeeb7fdd0ddf13400002
theorem shape12_15:validFrom 11166 0 _EVJ=true:=by decide+kernel
def _EVK:List Piece:=DZ.decode 58 42 0x29212a90107b5b9375859133aae76f64deb6fa3de12b04b0c18e3132a0002
theorem shape12_16:validFrom 11165 0 _EVK=true:=by decide+kernel
def _EVL:List Piece:=DZ.decode 58 42 0x29212a90107b60878b8d447cbae72f64deb6fa3de4675163b23e713150002
theorem shape12_17:validFrom 11164 0 _EVL=true:=by decide+kernel
def _EVM:List Piece:=DZ.decode 58 42 0x29212a90107b6637881a17f20ae6ef64deb6fa3de7a39e16a2eeb13000002
theorem shape12_18:validFrom 11163 0 _EVM=true:=by decide+kernel
def _EVN:List Piece:=DZ.decode 58 42 0x29212a90107b6b2155d727370ae6af64deb6fa3deadfeac9939ef12ea0002
theorem shape12_19:validFrom 11162 0 _EVN=true:=by decide+kernel
def _EVP:List Piece:=DZ.decode 58 42 0x29212a90107b700b2394367c0ae66f64deb6fa3dee1c377c844f312d40002
theorem shape12_20:validFrom 11161 0 _EVP=true:=by decide+kernel
def _EVQ:List Piece:=DZ.decode 58 42 0x29212a90107b81a6c4be43402ae62f64deb6fa3df1c6a1fb89326d2be0002
theorem shape12_21:validFrom 11160 0 _EVQ=true:=by decide+kernel
def _EVR:List Piece:=DZ.decode 58 42 0x29212a90107b8fa836e2f6be0ae5ef64deb6fa3df502eeae79e2ad2a80002
theorem shape12_22:validFrom 11159 0 _EVR=true:=by decide+kernel
def _EVS:List Piece:=DZ.decode 58 42 0x29212a90107b9487bc5561fefae5af64deb6fa3df83f3b616a92ed2910002
theorem shape12_23:validFrom 11158 0 _EVS=true:=by decide+kernel
def _EVT:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b9529212a901043b996741c7cd3feac36f64deb6fa30dfb7b88145b432d27a0003
theorem shape12_24:validFrom 11157 0 _EVT=true:=by decide+kernel
def _EVU:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b9429212a901043b9e46c73a3880da9f2f64deb6fa30dfeb7d4c74bf36d2630003
theorem shape12_25:validFrom 11156 0 _EVU=true:=by decide+kernel
def _EVV:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b9329212a901043ba3264caca3c1ca79ef64deb6fa30e01f4217a3ca3ad24c0003
theorem shape12_26:validFrom 11155 0 _EVV=true:=by decide+kernel
def _EVW:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b9229212a901043ba805d21f0f02ba53af64deb6fa30e05306e2d2d53ed2350003
theorem shape12_27:validFrom 11154 0 _EVW=true:=by decide+kernel
def _EVX:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b9129212a901043bacdb0f46d63f9a2c2f64deb6fa30e086cbae01e042d21d0003
theorem shape12_28:validFrom 11153 0 _EVX=true:=by decide+kernel
def _EVY:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b9029212a901043bb1b04c6e9d7c7a036f64deb6fa30e0ba907930eb46d2050003
theorem shape12_29:validFrom 11152 0 _EVY=true:=by decide+kernel
def _EWA:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8f29212a901043bb685899664b959d96f64deb6fa30e0ee55445ff64ad1ed0003
theorem shape12_30:validFrom 11151 0 _EWA=true:=by decide+kernel
def _EWB:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8e29212a901043bbb5ac6be2bf639adef64deb6fa30e1221a0f8f014ed1d50003
theorem shape12_31:validFrom 11150 0 _EWB=true:=by decide+kernel
def _EWC:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8d29212a901043bc025bb9b4f2f09812f64deb6fa30e155dedabe0c52d1bc0003
theorem shape12_32:validFrom 11149 0 _EWC=true:=by decide+kernel
def _EWD:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8c29212a901043bc4f0b0787267d952af64deb6fa30e189a3a5ed1756d1a30003
theorem shape12_33:validFrom 11148 0 _EWD=true:=by decide+kernel
def _EWE:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8b29212a901043bc9bba55595a0a922af64deb6fa30e1bd68711c225ad18a0003
theorem shape12_34:validFrom 11147 0 _EWE=true:=by decide+kernel
def _EWF:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8a29212a901043bce869a32b8d978f0af64deb6fa30e1f12d3c4b2d5ed1710003
theorem shape12_35:validFrom 11146 0 _EWF=true:=by decide+kernel
def _EWG:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8929212a901043bd34746c5380e38bcef64deb6fa30e224f2077a3862d1570003
theorem shape12_36:validFrom 11145 0 _EWG=true:=by decide+kernel
def _EWH:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8829212a901043bd807f357b742f8876f64deb6fa30e258b6d2a94366d13d0003
theorem shape12_37:validFrom 11144 0 _EWH=true:=by decide+kernel
def _EWI:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8729212a901043bdcbe579f9273a84fef64deb6fa30e28c7b9dd84e6ad1220003
theorem shape12_38:validFrom 11143 0 _EWI=true:=by decide+kernel
def _EWJ:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8629212a901043be17f043211a86815ef64deb6fa30e2c0406907596ed1080003
theorem shape12_39:validFrom 11142 0 _EWJ=true:=by decide+kernel
def _EWL:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8529212a901043be6356879ecd917d9ef64deb6fa30e2f40534366472d0ed0003
theorem shape12_40:validFrom 11141 0 _EWL=true:=by decide+kernel
def _EWM:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8429212a901043beae184772405b79b6f64deb6fa30e327c9ff656f76d0d10003
theorem shape12_41:validFrom 11140 0 _EWM=true:=by decide+kernel
def _EWN:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8329212a901043bef8da0745b32575a6f64deb6fa30e35b8eca947a7ad0b50003
theorem shape12_42:validFrom 11139 0 _EWN=true:=by decide+kernel
def _EWO:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8229212a901043bf39f8011f6220716af64deb6fa30e38f5395c3857ed08a0003
theorem shape12_43:validFrom 11138 0 _EWO=true:=by decide+kernel
def _EWP:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8129212a901043bf773adefb8f956cfef64deb6fa30e3c31860f29082d0590003
theorem shape12_44:validFrom 11137 0 _EWP=true:=by decide+kernel
def _EWQ:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b8029212a901043bfb3d9382d7cc96866f64deb6fa30e3f6dd2c219b86d0270003
theorem shape12_45:validFrom 11136 0 _EWQ=true:=by decide+kernel
def _EWR:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7f29212a901043bff077915f69fd639ef64deb6fa30e42b7644638c798ff50003
theorem shape12_46:validFrom 11135 0 _EWR=true:=by decide+kernel
def _EWS:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b7e29212a901043c02d15ea9157315ea6f64deb6fa30e45f3b0f92977d8fc30003
theorem shape12_47:validFrom 11134 0 _EWS=true:=by decide+kernel
def _EWT:List Piece:=DZ.decode 62 41 0x3782dace9d900000adf549095480821dfb9c8e48691932cbf7a8eab16310eaa94e6cda352a8e120003
theorem shape12_48:validFrom 11133 0 _EWT=true:=by decide+kernel
def _EWU:List Piece:=DZ.decode 62 41 0x3782dace9d900000adf149095480821dfdde0bb1bca762a117a8eab16310eac73ef11feec7cdf20003
theorem shape12_49:validFrom 11132 0 _EWU=true:=by decide+kernel
def _EWW:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7b00000000000f107981b97bba213d6a484aa40410edc88fea9d811813a50003
theorem shape12_50:validFrom 11131 0 _EWW=true:=by decide+kernel
def _EWX:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7a00000000000f10b1980211b83d39fa484aa40410eddfbffb3a1f9192340003
theorem shape12_51:validFrom 11130 0 _EWX=true:=by decide+kernel
def _EWY:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7900000000000f10e9acdc33353d365a484aa40410edf6f00bd6be0b10b70003
theorem shape12_52:validFrom 11129 0 _EWY=true:=by decide+kernel
def _EWZ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7800000000000f1121c047e0312132a5e99d545850f0b80f1e7495580f97a484aa40410ee0e201c735c848f2d0004
theorem shape12_53:validFrom 11128 0 _EWZ=true:=by decide+kernel
def _EXA:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7700000000000f1159d24518abe52ed5e99d545850f09c005cc9f6e6cf6ea484aa40410ee44a4707bb75ecd96bd33aa8b090ee20a3018cc36a80c30005
theorem shape12_54:validFrom 11127 0 _EXA=true:=by decide+kernel
def _EXB:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7600000000000f1191e2d3dca69d2ae5e99d545850f09aeb624798c70f44bd33aa8b090f062ffcfd574b2cd21a484aa40410ee9d615cedefbe4bf2bd33aa8b090ee2dfb05094052425b0006
theorem shape12_55:validFrom 11126 0 _EXB=true:=by decide+kernel
def _EXC:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7500000000000f11c9f1f42c1f2d26c5e99d545850f0a198ef9b5c074f18bd33aa8b090f020276d8a044a0cfda484aa40410eef61e4960281dca40bd33aa8b090ee3b530885bd3a03f30006
theorem shape12_56:validFrom 11125 0 _EXC=true:=by decide+kernel
def _EXD:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7400000000000f1201ffa60716092285e99d545850f0a8ebf37bc6544eebbd33aa8b090efdae8235450040cdca484aa40410ef4f0456fcf08d8881bd33aa8b090ee48ab0c023a21c58c0006
theorem shape12_57:validFrom 11124 0 _EXD=true:=by decide+kernel
def _EXE:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7300000000000f123a0be96d8c5d1e25e99d545850f0b0b520fe34f58ebdbd33aa8b090ee56030f7eb7098cbe0004
theorem shape12_58:validFrom 11123 0 _EXE=true:=by decide+kernel
def _EXF:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7200000000000f127216be5f81951985e99d545850f0b90c1e9a654c8e8dbd33aa8b090ee635b12fb33f14ca30004
theorem shape12_59:validFrom 11122 0 _EXF=true:=by decide+kernel
def _EXH:List Piece:=DZ.decode 62 39 0x3782dace9d900000adc400000000007895510126e7ad88a5de99d545850ef994c0ac7c0810e5b0003
theorem shape12_60:validFrom 11121 0 _EXH=true:=by decide+kernel
def _EXI:List Piece:=DZ.decode 62 39 0x3782dace9d900000adc0000000000078971140e72f45687dde99d545850efa4c6f6a52e9d0e270003
theorem shape12_61:validFrom 11120 0 _EXI=true:=by decide+kernel
def _EXJ:List Piece:=DZ.decode 62 39 0x3782dace9d900000adbc00000000007898d17533d2d468545e99d545850efb07118c4accdcdf10003
theorem shape12_62:validFrom 11119 0 _EXJ=true:=by decide+kernel
def _EXK:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb80000000000789a919e0cd25a8828de99d545850efbc79be10de034db90003
theorem shape12_63:validFrom 11118 0 _EXK=true:=by decide+kernel
def _EXL:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb40000000000789c51bb722de147fbde99d545850efc8c9401470d34d7f0003
theorem shape12_64:validFrom 11117 0 _EXL=true:=by decide+kernel
def _EXM:List Piece:=DZ.decode 62 39 0x3782dace9d900000adb00000000000789e11cd63e555a7cd5e99d545850efd5774547224ccd420003
theorem shape12_65:validFrom 11116 0 _EXM=true:=by decide+kernel
def _EXN:List Piece:=DZ.decode 62 39 0x3782dace9d900000adac0000000000789fd1d3e1f8c1079d5e99d545850efe25480b978368d030003
theorem shape12_66:validFrom 11115 0 _EXN=true:=by decide+kernel
def _EXO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d40f143239dd8d0478ed60002
theorem shape12_67:validFrom 11114 0 _EXO=true:=by decide+kernel
def _EXP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d20f146a37d0666fa8e6e0002
theorem shape12_68:validFrom 11113 0 _EXP=true:=by decide+kernel
def _EXQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d00f14a23454cb59c0e040002
theorem shape12_69:validFrom 11112 0 _EXQ=true:=by decide+kernel
def _EXS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ce0f14da2f6abbc2bcd960002
theorem shape12_70:validFrom 11111 0 _EXS=true:=by decide+kernel
def _EXT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056cc0f1512291237aa98d250002
theorem shape12_71:validFrom 11110 0 _EXT=true:=by decide+kernel
def _EXU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ca0f154a214b3f1158cb00002
theorem shape12_72:validFrom 11109 0 _EXU=true:=by decide+kernel
def _EXV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c80f15821815aa3324c380002
theorem shape12_73:validFrom 11108 0 _EXV=true:=by decide+kernel
def _EXW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c60f15ba0d71c89998bbd0002
theorem shape12_74:validFrom 11107 0 _EXW=true:=by decide+kernel
def _EXX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c40f15f2015f727d9cb3e0002
theorem shape12_75:validFrom 11106 0 _EXX=true:=by decide+kernel
def _EXY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c20f1629f3dea7dfecabc0002
theorem shape12_76:validFrom 11105 0 _EXY=true:=by decide+kernel
def _EXZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c00f1661e4ef68c1b4a350002
theorem shape12_77:validFrom 11104 0 _EXZ=true:=by decide+kernel
def _EYA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056be0f1699d491b522609ac0002
theorem shape12_78:validFrom 11103 0 _EYA=true:=by decide+kernel
def _EYB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056bc0f16d11dbe677ff091f0002
theorem shape12_79:validFrom 11102 0 _EYB=true:=by decide+kernel
def _EYD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ba0f17052aab11e9fc8900002
theorem shape12_80:validFrom 11101 0 _EYD=true:=by decide+kernel
def _EYE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f173936468525887fc0002
theorem shape12_81:validFrom 11100 0 _EYE=true:=by decide+kernel
def _EYF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f176d409110b28c7650002
theorem shape12_82:validFrom 11099 0 _EYF=true:=by decide+kernel
def _EYG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f17a1498a65145c6c90002
theorem shape12_83:validFrom 11098 0 _EYG=true:=by decide+kernel
def _EYH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f17d55132d1c46462b0002
theorem shape12_84:validFrom 11097 0 _EYH=true:=by decide+kernel
def _EYI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b00f1809578a0748e85890002
theorem shape12_85:validFrom 11096 0 _EYI=true:=by decide+kernel
def _EYJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ae0f183d5c90551bf04e40002
theorem shape12_86:validFrom 11095 0 _EYJ=true:=by decide+kernel
def _EYK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ac0f187160456bc4a043d0002
theorem shape12_87:validFrom 11094 0 _EYK=true:=by decide+kernel
def _EYL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056aa0f18a562a99abaa03910002
theorem shape12_88:validFrom 11093 0 _EYL=true:=by decide+kernel
def _EYM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a80f18d963bc9287842e10002
theorem shape12_89:validFrom 11092 0 _EYM=true:=by decide+kernel
def _EYO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a60f190d637e7ae6c422c0002
theorem shape12_90:validFrom 11091 0 _EYO=true:=by decide+kernel
def _EYP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a40f194161ef7b91901750002
theorem shape12_91:validFrom 11090 0 _EYP=true:=by decide+kernel
def _EYQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a20f19755f0f45169c0ba0002
theorem shape12_92:validFrom 11089 0 _EYQ=true:=by decide+kernel
def _EYR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433bc7077e60646e50f19a95ade26e46c0020002
theorem shape12_93:validFrom 11088 0 _EYR=true:=by decide+kernel
def _EYS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3bc6379469b9d230f19dd555bd18b740020002
theorem shape12_94:validFrom 11087 0 _EYS=true:=by decide+kernel
def _EYT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3bc567afb6ae0f00f1a114e88947c400020002
theorem shape12_95:validFrom 11086 0 _EYT=true:=by decide+kernel
def _EYU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373bc497d0487edfd0f1a45466420480c0020002
theorem shape12_96:validFrom 11085 0 _EYU=true:=by decide+kernel
def _EYV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333bc3c7f61dee90b0f1a793ceec45bd40020002
theorem shape12_97:validFrom 11084 0 _EYV=true:=by decide+kernel
def _EYW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3bc2f821383ad0c0f1aad3228314bd00020002
theorem shape12_98:validFrom 11083 0 _EYW=true:=by decide+kernel
def _EYX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3bc228519625f5a0f1ae12610b682980020002
theorem shape12_99:validFrom 11082 0 _EYX=true:=by decide+kernel
def _EUZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273bc1588738eda500f1b1518a80496c00020002
theorem shape12_100:validFrom 11081 0 _EUZ=true:=by decide+kernel
def _EVA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233bc088c21f5436f0f1b4909ee6af2440020002
theorem shape12_101:validFrom 11080 0 _EVA=true:=by decide+kernel
def _EVB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3bbfb9024a975570f1b7cf9e39a2aa40020002
theorem shape12_102:validFrom 11079 0 _EVB=true:=by decide+kernel
def _EVC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3bbee947b9796260f1bb0e887e1a7680020002
theorem shape12_103:validFrom 11078 0 _EVC=true:=by decide+kernel
def _EVD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bbe19926d37f050f1be4d5daf203ec0020002
theorem shape12_104:validFrom 11077 0 _EVD=true:=by decide+kernel
def _EVE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bbd49e264957140f1c18c1dd1aa3b00020002
theorem shape12_105:validFrom 11076 0 _EVE=true:=by decide+kernel
def row12 (v:ℕ):List Piece:=match v with
 | 0=>_EUW
 | 1=>_EUX
 | 2=>_EVO
 | 3=>_EVZ
 | 4=>_EWK
 | 5=>_EWV
 | 6=>_EXG
 | 7=>_EXR
 | 8=>_EYC
 | 9=>_EYN
 | 10=>_EUY
 | 11=>_EVF
 | 12=>_EVG
 | 13=>_EVH
 | 14=>_EVI
 | 15=>_EVJ
 | 16=>_EVK
 | 17=>_EVL
 | 18=>_EVM
 | 19=>_EVN
 | 20=>_EVP
 | 21=>_EVQ
 | 22=>_EVR
 | 23=>_EVS
 | 24=>_EVT
 | 25=>_EVU
 | 26=>_EVV
 | 27=>_EVW
 | 28=>_EVX
 | 29=>_EVY
 | 30=>_EWA
 | 31=>_EWB
 | 32=>_EWC
 | 33=>_EWD
 | 34=>_EWE
 | 35=>_EWF
 | 36=>_EWG
 | 37=>_EWH
 | 38=>_EWI
 | 39=>_EWJ
 | 40=>_EWL
 | 41=>_EWM
 | 42=>_EWN
 | 43=>_EWO
 | 44=>_EWP
 | 45=>_EWQ
 | 46=>_EWR
 | 47=>_EWS
 | 48=>_EWT
 | 49=>_EWU
 | 50=>_EWW
 | 51=>_EWX
 | 52=>_EWY
 | 53=>_EWZ
 | 54=>_EXA
 | 55=>_EXB
 | 56=>_EXC
 | 57=>_EXD
 | 58=>_EXE
 | 59=>_EXF
 | 60=>_EXH
 | 61=>_EXI
 | 62=>_EXJ
 | 63=>_EXK
 | 64=>_EXL
 | 65=>_EXM
 | 66=>_EXN
 | 67=>_EXO
 | 68=>_EXP
 | 69=>_EXQ
 | 70=>_EXS
 | 71=>_EXT
 | 72=>_EXU
 | 73=>_EXV
 | 74=>_EXW
 | 75=>_EXX
 | 76=>_EXY
 | 77=>_EXZ
 | 78=>_EYA
 | 79=>_EYB
 | 80=>_EYD
 | 81=>_EYE
 | 82=>_EYF
 | 83=>_EYG
 | 84=>_EYH
 | 85=>_EYI
 | 86=>_EYJ
 | 87=>_EYK
 | 88=>_EYL
 | 89=>_EYM
 | 90=>_EYO
 | 91=>_EYP
 | 92=>_EYQ
 | 93=>_EYR
 | 94=>_EYS
 | 95=>_EYT
 | 96=>_EYU
 | 97=>_EYV
 | 98=>_EYW
 | 99=>_EYX
 | 100=>_EUZ
 | 101=>_EVA
 | 102=>_EVB
 | 103=>_EVC
 | 104=>_EVD
 | 105=>_EVE
 | _=>[]
theorem checked12 (v:ℕ) (hy:12+v≤117):validFrom (11193-12-v) 0 (row12 v)=true:=by
 have hv:v≤105:=by omega
 interval_cases v
 · exact shape12_0
 · exact shape12_1
 · exact shape12_2
 · exact shape12_3
 · exact shape12_4
 · exact shape12_5
 · exact shape12_6
 · exact shape12_7
 · exact shape12_8
 · exact shape12_9
 · exact shape12_10
 · exact shape12_11
 · exact shape12_12
 · exact shape12_13
 · exact shape12_14
 · exact shape12_15
 · exact shape12_16
 · exact shape12_17
 · exact shape12_18
 · exact shape12_19
 · exact shape12_20
 · exact shape12_21
 · exact shape12_22
 · exact shape12_23
 · exact shape12_24
 · exact shape12_25
 · exact shape12_26
 · exact shape12_27
 · exact shape12_28
 · exact shape12_29
 · exact shape12_30
 · exact shape12_31
 · exact shape12_32
 · exact shape12_33
 · exact shape12_34
 · exact shape12_35
 · exact shape12_36
 · exact shape12_37
 · exact shape12_38
 · exact shape12_39
 · exact shape12_40
 · exact shape12_41
 · exact shape12_42
 · exact shape12_43
 · exact shape12_44
 · exact shape12_45
 · exact shape12_46
 · exact shape12_47
 · exact shape12_48
 · exact shape12_49
 · exact shape12_50
 · exact shape12_51
 · exact shape12_52
 · exact shape12_53
 · exact shape12_54
 · exact shape12_55
 · exact shape12_56
 · exact shape12_57
 · exact shape12_58
 · exact shape12_59
 · exact shape12_60
 · exact shape12_61
 · exact shape12_62
 · exact shape12_63
 · exact shape12_64
 · exact shape12_65
 · exact shape12_66
 · exact shape12_67
 · exact shape12_68
 · exact shape12_69
 · exact shape12_70
 · exact shape12_71
 · exact shape12_72
 · exact shape12_73
 · exact shape12_74
 · exact shape12_75
 · exact shape12_76
 · exact shape12_77
 · exact shape12_78
 · exact shape12_79
 · exact shape12_80
 · exact shape12_81
 · exact shape12_82
 · exact shape12_83
 · exact shape12_84
 · exact shape12_85
 · exact shape12_86
 · exact shape12_87
 · exact shape12_88
 · exact shape12_89
 · exact shape12_90
 · exact shape12_91
 · exact shape12_92
 · exact shape12_93
 · exact shape12_94
 · exact shape12_95
 · exact shape12_96
 · exact shape12_97
 · exact shape12_98
 · exact shape12_99
 · exact shape12_100
 · exact shape12_101
 · exact shape12_102
 · exact shape12_103
 · exact shape12_104
 · exact shape12_105
def _EYY:List Piece:=DZ.decode 58 42 0xa484aa4041ecdbef83d7a5ee6bac5ea3aac58c7b10f1e4ceb28225686f64deb6fa3dbea6210e9219194050003
theorem shape13_0:validFrom 11180 0 _EYY=true:=by decide+kernel
def _EYZ:List Piece:=DZ.decode 58 42 0xa484aa4041ecedd24df7b24fabab5ea3aac58c7b1694d38a452c35602f64deb6fa3dc1e26dc182c9593f10003
theorem shape13_1:validFrom 11179 0 _EYZ=true:=by decide+kernel
def _EZP:List Piece:=DZ.decode 58 42 0xa484aa4041ecffde39424ec12baa5ea3aac58c7b1c4f6b30893955582f64deb6fa3dc51eba747379993de0003
theorem shape13_2:validFrom 11178 0 _EZP=true:=by decide+kernel
def _FAA:List Piece:=DZ.decode 58 42 0xa484aa4041ed11ea248ceb32aba95ea3aac58c7b21f259ec1be365502f64deb6fa3dc85b07276429d93ca0003
theorem shape13_3:validFrom 11177 0 _FAA=true:=by decide+kernel
def _FAL:List Piece:=DZ.decode 58 42 0xa484aa4041ed23f60fd787a42ba85ea3aac58c7b27acf1925ff085482f64deb6fa3dcb9753da54da193b70003
theorem shape13_4:validFrom 11176 0 _FAL=true:=by decide+kernel
def _FAW:List Piece:=DZ.decode 58 42 0xa484aa4041ed35d8d9f794056ba75ea3aac58c7b2d4fe04df29a953fef64deb6fa3dced3a08d458a593a30003
theorem shape13_5:validFrom 11175 0 _FAW=true:=by decide+kernel
def _FBH:List Piece:=DZ.decode 58 42 0xa484aa4041ed47e4c5423076eba65ea3aac58c7b32f2cf098544a537ef64deb6fa3dd20fed40363a9938f0003
theorem shape13_6:validFrom 11174 0 _FBH=true:=by decide+kernel
def _FBS:List Piece:=DZ.decode 58 42 0xa484aa4041ed59f0b08ccce86ba55ea3aac58c7b387e14da668ba52fef64deb6fa3dd54c39f326ead937a0003
theorem shape13_7:validFrom 11173 0 _FBS=true:=by decide+kernel
def _FCD:List Piece:=DZ.decode 58 42 0xa484aa4041ed6bd37aacd949aba45ea3aac58c7b3e210395f935b527af64deb6fa3dd88886a6179b193660003
theorem shape13_8:validFrom 11172 0 _FCD=true:=by decide+kernel
def _FCO:List Piece:=DZ.decode 58 42 0xa484aa4041ed7ddf65f775bb2ba35ea3aac58c7b43c3f2518bdfc51faf64deb6fa3ddbc4d359084b593520003
theorem shape13_9:validFrom 11171 0 _FCO=true:=by decide+kernel
def _EZA:List Piece:=DZ.decode 58 42 0xa484aa4041ed8feb5142122caba25ea3aac58c7b494f38226d26c517af64deb6fa3ddf01200bf8fb9933d0003
theorem shape13_10:validFrom 11170 0 _EZA=true:=by decide+kernel
def _EZG:List Piece:=DZ.decode 58 42 0xa484aa4041eda1ce1b621e8deba15ea3aac58c7b4eda7df34e6dc50f6f64deb6fa3de23d6cbee9abd93280003
theorem shape13_11:validFrom 11169 0 _EZG=true:=by decide+kernel
def _EZH:List Piece:=DZ.decode 58 42 0xa484aa4041edb3da06acbaff6ba05ea3aac58c7b5465c3c42fb4c5076f64deb6fa3de579b971da5c193130003
theorem shape13_12:validFrom 11168 0 _EZH=true:=by decide+kernel
def _EZI:List Piece:=DZ.decode 58 42 0xa484aa4041edc5e5f1f75770eb9f5ea3aac58c7b59f1099510fbc4ff6f64deb6fa3de8b60624cb0c592fe0003
theorem shape13_13:validFrom 11167 0 _EZI=true:=by decide+kernel
def _EZJ:List Piece:=DZ.decode 58 42 0xa484aa4041edd7f1dd41f3e26b9e5ea3aac58c7b5f7c4f65f242c4f76f64deb6fa3debf252d7bbbc992e90003
theorem shape13_14:validFrom 11166 0 _EZJ=true:=by decide+kernel
def _EZK:List Piece:=DZ.decode 58 42 0x29212a90107b7123a633dc626ae76f64deb6fa3def2e9f8aac6cd92d40002
theorem shape13_15:validFrom 11165 0 _EZK=true:=by decide+kernel
def _EZL:List Piece:=DZ.decode 58 42 0x29212a90107b760d73f0eba76ae72f64deb6fa3df26aec3d9d1d192be0002
theorem shape13_16:validFrom 11164 0 _EZL=true:=by decide+kernel
def _EZM:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b9b29212a901043b7af741adfaec6ade2f64deb6fa30df5a738f08dcd592a80003
theorem shape13_17:validFrom 11163 0 _EZM=true:=by decide+kernel
def _EZN:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b9a29212a901043b809cf5f02a5daabbaf64deb6fa30df8e385a37e7d992920003
theorem shape13_18:validFrom 11162 0 _EZN=true:=by decide+kernel
def _EZO:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b9929212a901043b8586c3ad39a2aa986f64deb6fa30dfc1fd2566f2dd927c0003
theorem shape13_19:validFrom 11161 0 _EZO=true:=by decide+kernel
def _EZQ:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b9829212a901043b8a66491fa4e39a746f64deb6fa30dff5c1f095fde192650003
theorem shape13_20:validFrom 11160 0 _EZQ=true:=by decide+kernel
def _EZR:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b9729212a901043b9c01ea49b1a7ba4f2f64deb6fa30e04ecceb0e4654924f0003
theorem shape13_21:validFrom 11159 0 _EZR=true:=by decide+kernel
def _EZS:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b96000000000003c2dfc5ff7dfa275f305e99d545850f0404b1f10b39d92e02f4ceaa2c243bf40dc4164f3ce4acef64deb6fa30e131f76c61475112380005
theorem shape13_22:validFrom 11158 0 _EZS=true:=by decide+kernel
def _EZT:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b95000000000003c2ed98db901a015ea05e99d545850f044cc754286cd92c62f4ceaa2c243bf653cab04699e4a66f64deb6fa30e165bc3790525512210005
theorem shape13_23:validFrom 11157 0 _EZT=true:=by decide+kernel
def _EZU:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b94000000000003c2fb6b5cffefb75e0c5e99d545850f0491e681fda2b12ac2f4ceaa2c243bf899d14a3df6e49faf64deb6fa30e1998102bf5d59120a0005
theorem shape13_24:validFrom 11156 0 _EZU=true:=by decide+kernel
def _EZV:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b93000000000003c3093d83cd7aff5d785e99d545850f04d9f917df32892912f4ceaa2c243bfad404a98ca354992f64deb6fa30e1cd45cdee685d11f20005
theorem shape13_25:validFrom 11155 0 _EZV=true:=by decide+kernel
def _EZW:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b92000000000003c3170f4ff8bc235ce05e99d545850f051f157878c4b52762f4ceaa2c243bfd0e3808db4fc4922f64deb6fa30e2010a991d736111da0005
theorem shape13_26:validFrom 11154 0 _EZW=true:=by decide+kernel
def _EZX:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9100000000000f0c9383062d9d597125e99d545850f056725411eb21125bbd33aa8b090ecb52dcf026a7c522d0004
theorem shape13_27:validFrom 11153 0 _EZX=true:=by decide+kernel
def _EZY:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9000000000000f0ccac761c84e796eb5e99d545850f05adb93bd1b7c523fbd33aa8b090ecc285d27ee76412110004
theorem shape13_28:validFrom 11152 0 _EZY=true:=by decide+kernel
def _EZZ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8f00000000000f0d020a52d9d7016c45e99d545850f05f7409e9116d9223bd33aa8b090eccfddd5fb644bd1f50004
theorem shape13_29:validFrom 11151 0 _EZZ=true:=by decide+kernel
def _FAB:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8e00000000000f0d394bd96235d169e5e99d545850f063f4c335d8f85207bd33aa8b090ecdd35d977e13391d80004
theorem shape13_30:validFrom 11150 0 _FAB=true:=by decide+kernel
def _FAC:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8d00000000000f0d708bf5616c116775e99d545850f068a4b303662c91eabd33aa8b090ecea8ddcf45e1b51bc0004
theorem shape13_31:validFrom 11149 0 _FAC=true:=by decide+kernel
def _FAD:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8c00000000000f0da7caa6d7789964f5e99d545850f06d3ce5f1c4ddd1cdbd33aa8b090ecf7e5e070db03119e0004
theorem shape13_32:validFrom 11148 0 _FAD=true:=by decide+kernel
def _FAE:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8b00000000000f0ddf07edeb29c56265e99d545850f071eca8eb97d491afbd33aa8b090ed053de3ed57ead1810004
theorem shape13_33:validFrom 11147 0 _FAE=true:=by decide+kernel
def _FAF:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8a00000000000f0e1643ca4ee3fd5fc5e99d545850f07684af063c541191bd33aa8b090ed1295e769d4d291630004
theorem shape13_34:validFrom 11146 0 _FAF=true:=by decide+kernel
def _FAG:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8900000000000f0e4d7e3c29747d5d25e99d545850f07b1c9eb703c39173bd33aa8b090ed1fedeae651ba51440004
theorem shape13_35:validFrom 11145 0 _FAG=true:=by decide+kernel
def _FAH:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8800000000000f0e84b7437adc695a65e99d545850f07fcc1e733f7bd155bd33aa8b090ed2d45ee62cea211250004
theorem shape13_36:validFrom 11144 0 _FAH=true:=by decide+kernel
def _FAI:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8700000000000f0ebbeee0431a9d57a5e99d545850f084932e3aef665135bd33aa8b090ed3a9df1df4b89d1060004
theorem shape13_37:validFrom 11143 0 _FAI=true:=by decide+kernel
def _FAJ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8600000000000f0ef32512822fad54e5e99d545850f0895a2798c24d9116bd33aa8b090ed47f5f55bc87190e60004
theorem shape13_38:validFrom 11142 0 _FAJ=true:=by decide+kernel
def _FAK:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8500000000000f0f2a59da381c2d5215e99d545850f08e5057775ade90f6bd33aa8b090ed5de2956cf32a50c60004
theorem shape13_39:validFrom 11141 0 _FAK=true:=by decide+kernel
def _FAM:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8400000000000f0f618d378ba9694f35e99d545850f093172401738b10d5bd33aa8b090ed6b3a98e9701210a50004
theorem shape13_40:validFrom 11140 0 _FAM=true:=by decide+kernel
def _FAN:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae0c0000000000787cc5f9517a182a62de99d545850ef1173fd7aa38690b40003
theorem shape13_41:validFrom 11139 0 _FAN=true:=by decide+kernel
def _FAO:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae080000000000787e7f7d924d976a4a5e99d545850ef19765f3b224d10920003
theorem shape13_42:validFrom 11138 0 _FAO=true:=by decide+kernel
def _FAP:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae040000000000788038f67ed7cd6a31de99d545850ef21a7f77c66b450700003
theorem shape13_43:validFrom 11137 0 _FAP=true:=by decide+kernel
def _FAQ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae0000000000007881f2641718beea185e99d545850ef2a08c63e70ce504d0003
theorem shape13_44:validFrom 11136 0 _FAQ=true:=by decide+kernel
def _FAR:List Piece:=DZ.decode 62 39 0x3782dace9d900000adfc00000000007883abc65b1062a9ff5e99d545850ef6330bb60632a50290003
theorem shape13_45:validFrom 11135 0 _FAR=true:=by decide+kernel
def _FAS:List Piece:=DZ.decode 62 1 0x6f05b59d3b2000015bf03c42b28ea5fa7ce4f281e5748a0e5db8001f7e0f10aca3a97e9f38de80004
theorem shape13_46:validFrom 11134 0 _FAS=true:=by decide+kernel
def _FAT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fa0f10e3cd1ceb40d1394079b2bdb2c7f00007cf83cd718c5c7500003c2c1e5748a0e5db8001c4a0f10e3cd1ceb40d0de70006
theorem shape13_47:validFrom 11133 0 _FAT=true:=by decide+kernel
def _FAU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f80f111af525ceb84d35d079b2bdb2c7f00007ba83cd718c5c7500003c2c1e5748a0e5db8001c4a0f111af525ceb84cde70006
theorem shape13_48:validFrom 11132 0 _FAU=true:=by decide+kernel
def _FAV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f60f11521bc4290829324079b2bdb2c7f000079403cd718c5c7500003c2c1e5748a0e5db8001c4a0f11521bc4290828de70006
theorem shape13_49:validFrom 11131 0 _FAV=true:=by decide+kernel
def _FAX:List Piece:=DZ.decode 62 1 0x6f05b59d3b2000015bd03c462503dfe8b934ba81e5748a0e5db8001c080f118940f7fa2e4cde70004
theorem shape13_50:validFrom 11130 0 _FAX=true:=by decide+kernel
def _FAY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f20f11c064c1422be52af0002
theorem shape13_51:validFrom 11129 0 _FAY=true:=by decide+kernel
def _FAZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f00f11f7872027c3412710002
theorem shape13_52:validFrom 11128 0 _FAZ=true:=by decide+kernel
def _FBA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ee0f122ea8145d6d612310002
theorem shape13_53:validFrom 11127 0 _FBA=true:=by decide+kernel
def _FBB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ec0f1265c79e09eef11ef0002
theorem shape13_54:validFrom 11126 0 _FBB=true:=by decide+kernel
def _FBC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ea0f129ce5bd2d46c91ab0002
theorem shape13_55:validFrom 11125 0 _FBC=true:=by decide+kernel
def _FBD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e80f12d40271c776111640002
theorem shape13_56:validFrom 11124 0 _FBD=true:=by decide+kernel
def _FBE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e60f130b1dbbd87b991190002
theorem shape13_57:validFrom 11123 0 _FBE=true:=by decide+kernel
def _FBF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e40f1342379b6058010cc0002
theorem shape13_58:validFrom 11122 0 _FBF=true:=by decide+kernel
def _FBG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e20f1379501085cb4d07c0002
theorem shape13_59:validFrom 11121 0 _FBG=true:=by decide+kernel
def _FBI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e00f13b0671afb54d50290002
theorem shape13_60:validFrom 11120 0 _FBI=true:=by decide+kernel
def _FBJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056de0f13e77cbae7b5c8fd20002
theorem shape13_61:validFrom 11119 0 _FBJ=true:=by decide+kernel
def _FBK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056dc0f141e90f04aebe0f790002
theorem shape13_62:validFrom 11118 0 _FBK=true:=by decide+kernel
def _FBL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056da0f1455a3bb24f9f4f1c0002
theorem shape13_63:validFrom 11117 0 _FBL=true:=by decide+kernel
def _FBM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d80f148cb51b75df74ebc0002
theorem shape13_64:validFrom 11116 0 _FBM=true:=by decide+kernel
def _FBN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d60f14c3c51164573ce580002
theorem shape13_65:validFrom 11115 0 _FBN=true:=by decide+kernel
def _FBO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d40f14fad39ca2e9e0df20002
theorem shape13_66:validFrom 11114 0 _FBO=true:=by decide+kernel
def _FBP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d20f1531e0bd5852ccd880002
theorem shape13_67:validFrom 11113 0 _FBP=true:=by decide+kernel
def _FBQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d00f1568ec73849294d1b0002
theorem shape13_68:validFrom 11112 0 _FBQ=true:=by decide+kernel
def _FBR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ce0f159ff6bf27a9c8caa0002
theorem shape13_69:validFrom 11111 0 _FBR=true:=by decide+kernel
def _FBT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056cc0f15d6ffa0419744c360002
theorem shape13_70:validFrom 11110 0 _FBT=true:=by decide+kernel
def _FBU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ca0f160e0716f914b8bbf0002
theorem shape13_71:validFrom 11109 0 _FBU=true:=by decide+kernel
def _FBV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c80f16450d2300af54b440002
theorem shape13_72:validFrom 11108 0 _FBV=true:=by decide+kernel
def _FBW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c60f167c11c47f20ccac60002
theorem shape13_73:validFrom 11107 0 _FBW=true:=by decide+kernel
def _FBX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c40f16b314fb7469b4a450002
theorem shape13_74:validFrom 11106 0 _FBX=true:=by decide+kernel
def _FBY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c20f16ea16c7e088e09c00002
theorem shape13_75:validFrom 11105 0 _FBY=true:=by decide+kernel
def _FBZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c00f17211729c37f7c9380002
theorem shape13_76:validFrom 11104 0 _FBZ=true:=by decide+kernel
def _FCA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056be0f175816211d4af48ac0002
theorem shape13_77:validFrom 11103 0 _FCA=true:=by decide+kernel
def _FCB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056bc0f178e733c5efd8481c0002
theorem shape13_78:validFrom 11102 0 _FCB=true:=by decide+kernel
def _FCC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ba0f17c1ab131697dc78a0002
theorem shape13_79:validFrom 11101 0 _FCC=true:=by decide+kernel
def _FCE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f17f4e19bb25f986f50002
theorem shape13_80:validFrom 11100 0 _FCE=true:=by decide+kernel
def _FCF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f182816d67fbd2465b0002
theorem shape13_81:validFrom 11099 0 _FCF=true:=by decide+kernel
def _FCG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f185b4ac33149d85be0002
theorem shape13_82:validFrom 11098 0 _FCG=true:=by decide+kernel
def _FCH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f188e7d62146aa051c0002
theorem shape13_83:validFrom 11097 0 _FCH=true:=by decide+kernel
def _FCI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b00f18c1aeb2dbbbb44780002
theorem shape13_84:validFrom 11096 0 _FCI=true:=by decide+kernel
def _FCJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ae0f18f4deb5d49fb83d10002
theorem shape13_85:validFrom 11095 0 _FCJ=true:=by decide+kernel
def _FCK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ac0f19280d6ab1b5303270002
theorem shape13_86:validFrom 11094 0 _FCK=true:=by decide+kernel
def _FCL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056aa0f195b3ad1c05c6c2790002
theorem shape13_87:validFrom 11093 0 _FCL=true:=by decide+kernel
def _FCM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a80f198e66eab336441c70002
theorem shape13_88:validFrom 11092 0 _FCM=true:=by decide+kernel
def _FCN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a60f19c191b5b0f2941100002
theorem shape13_89:validFrom 11091 0 _FCN=true:=by decide+kernel
def _FCP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a40f19f4bb32e03ef40560002
theorem shape13_90:validFrom 11090 0 _FCP=true:=by decide+kernel
def _FCQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473bc50d5c51310160f1a27e361f3bfa80020002
theorem shape13_91:validFrom 11089 0 _FCQ=true:=by decide+kernel
def _FCR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433bc440c0cc1cc9a0f1a5b0a4338cd980020002
theorem shape13_92:validFrom 11088 0 _FCR=true:=by decide+kernel
def _FCS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3bc3742a7f77b7b0f1a8e2fd66212140020002
theorem shape13_93:validFrom 11087 0 _FCS=true:=by decide+kernel
def _FCT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3bc2a7996a0c6c80f1ac1541bbce4e00020002
theorem shape13_94:validFrom 11086 0 _FCT=true:=by decide+kernel
def _FCU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373bc1db0d8d1046c0f1af47712fbee500020002
theorem shape13_95:validFrom 11085 0 _FCU=true:=by decide+kernel
def _FCV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333bc10e86e74deea0f1b2798bc6c84580020002
theorem shape13_96:validFrom 11084 0 _FCV=true:=by decide+kernel
def _FCW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3bc0420579fab750f1b5ab917c1522c0020002
theorem shape13_97:validFrom 11083 0 _FCW=true:=by decide+kernel
def _FCX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3bbf758943e15260f1b8dd82547ab680020002
theorem shape13_98:validFrom 11082 0 _FCX=true:=by decide+kernel
def _FCY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273bbea91246370980f1bc0f5e4b23da00020002
theorem shape13_99:validFrom 11081 0 _FCY=true:=by decide+kernel
def _EZB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233bbddca07fc697b0f1bf412564e5a140020002
theorem shape13_100:validFrom 11080 0 _EZB=true:=by decide+kernel
def _EZC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3bbd1033f1c53d50f1c272d79ceb0ac0020002
theorem shape13_101:validFrom 11079 0 _EZC=true:=by decide+kernel
def _EZD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3bbc43cc9afdbe80f1c5a474f8090600020002
theorem shape13_102:validFrom 11078 0 _EZD=true:=by decide+kernel
def _EZE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bbb776a7ca552a0f1c8d5fd716ab580020002
theorem shape13_103:validFrom 11077 0 _EZE=true:=by decide+kernel
def _EZF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bbaab0d9586c700f1cc07710de4e400020002
theorem shape13_104:validFrom 11076 0 _EZF=true:=by decide+kernel
def row13 (v:ℕ):List Piece:=match v with
 | 0=>_EYY
 | 1=>_EYZ
 | 2=>_EZP
 | 3=>_FAA
 | 4=>_FAL
 | 5=>_FAW
 | 6=>_FBH
 | 7=>_FBS
 | 8=>_FCD
 | 9=>_FCO
 | 10=>_EZA
 | 11=>_EZG
 | 12=>_EZH
 | 13=>_EZI
 | 14=>_EZJ
 | 15=>_EZK
 | 16=>_EZL
 | 17=>_EZM
 | 18=>_EZN
 | 19=>_EZO
 | 20=>_EZQ
 | 21=>_EZR
 | 22=>_EZS
 | 23=>_EZT
 | 24=>_EZU
 | 25=>_EZV
 | 26=>_EZW
 | 27=>_EZX
 | 28=>_EZY
 | 29=>_EZZ
 | 30=>_FAB
 | 31=>_FAC
 | 32=>_FAD
 | 33=>_FAE
 | 34=>_FAF
 | 35=>_FAG
 | 36=>_FAH
 | 37=>_FAI
 | 38=>_FAJ
 | 39=>_FAK
 | 40=>_FAM
 | 41=>_FAN
 | 42=>_FAO
 | 43=>_FAP
 | 44=>_FAQ
 | 45=>_FAR
 | 46=>_FAS
 | 47=>_FAT
 | 48=>_FAU
 | 49=>_FAV
 | 50=>_FAX
 | 51=>_FAY
 | 52=>_FAZ
 | 53=>_FBA
 | 54=>_FBB
 | 55=>_FBC
 | 56=>_FBD
 | 57=>_FBE
 | 58=>_FBF
 | 59=>_FBG
 | 60=>_FBI
 | 61=>_FBJ
 | 62=>_FBK
 | 63=>_FBL
 | 64=>_FBM
 | 65=>_FBN
 | 66=>_FBO
 | 67=>_FBP
 | 68=>_FBQ
 | 69=>_FBR
 | 70=>_FBT
 | 71=>_FBU
 | 72=>_FBV
 | 73=>_FBW
 | 74=>_FBX
 | 75=>_FBY
 | 76=>_FBZ
 | 77=>_FCA
 | 78=>_FCB
 | 79=>_FCC
 | 80=>_FCE
 | 81=>_FCF
 | 82=>_FCG
 | 83=>_FCH
 | 84=>_FCI
 | 85=>_FCJ
 | 86=>_FCK
 | 87=>_FCL
 | 88=>_FCM
 | 89=>_FCN
 | 90=>_FCP
 | 91=>_FCQ
 | 92=>_FCR
 | 93=>_FCS
 | 94=>_FCT
 | 95=>_FCU
 | 96=>_FCV
 | 97=>_FCW
 | 98=>_FCX
 | 99=>_FCY
 | 100=>_EZB
 | 101=>_EZC
 | 102=>_EZD
 | 103=>_EZE
 | 104=>_EZF
 | _=>[]
theorem checked13 (v:ℕ) (hy:13+v≤117):validFrom (11193-13-v) 0 (row13 v)=true:=by
 have hv:v≤104:=by omega
 interval_cases v
 · exact shape13_0
 · exact shape13_1
 · exact shape13_2
 · exact shape13_3
 · exact shape13_4
 · exact shape13_5
 · exact shape13_6
 · exact shape13_7
 · exact shape13_8
 · exact shape13_9
 · exact shape13_10
 · exact shape13_11
 · exact shape13_12
 · exact shape13_13
 · exact shape13_14
 · exact shape13_15
 · exact shape13_16
 · exact shape13_17
 · exact shape13_18
 · exact shape13_19
 · exact shape13_20
 · exact shape13_21
 · exact shape13_22
 · exact shape13_23
 · exact shape13_24
 · exact shape13_25
 · exact shape13_26
 · exact shape13_27
 · exact shape13_28
 · exact shape13_29
 · exact shape13_30
 · exact shape13_31
 · exact shape13_32
 · exact shape13_33
 · exact shape13_34
 · exact shape13_35
 · exact shape13_36
 · exact shape13_37
 · exact shape13_38
 · exact shape13_39
 · exact shape13_40
 · exact shape13_41
 · exact shape13_42
 · exact shape13_43
 · exact shape13_44
 · exact shape13_45
 · exact shape13_46
 · exact shape13_47
 · exact shape13_48
 · exact shape13_49
 · exact shape13_50
 · exact shape13_51
 · exact shape13_52
 · exact shape13_53
 · exact shape13_54
 · exact shape13_55
 · exact shape13_56
 · exact shape13_57
 · exact shape13_58
 · exact shape13_59
 · exact shape13_60
 · exact shape13_61
 · exact shape13_62
 · exact shape13_63
 · exact shape13_64
 · exact shape13_65
 · exact shape13_66
 · exact shape13_67
 · exact shape13_68
 · exact shape13_69
 · exact shape13_70
 · exact shape13_71
 · exact shape13_72
 · exact shape13_73
 · exact shape13_74
 · exact shape13_75
 · exact shape13_76
 · exact shape13_77
 · exact shape13_78
 · exact shape13_79
 · exact shape13_80
 · exact shape13_81
 · exact shape13_82
 · exact shape13_83
 · exact shape13_84
 · exact shape13_85
 · exact shape13_86
 · exact shape13_87
 · exact shape13_88
 · exact shape13_89
 · exact shape13_90
 · exact shape13_91
 · exact shape13_92
 · exact shape13_93
 · exact shape13_94
 · exact shape13_95
 · exact shape13_96
 · exact shape13_97
 · exact shape13_98
 · exact shape13_99
 · exact shape13_100
 · exact shape13_101
 · exact shape13_102
 · exact shape13_103
 · exact shape13_104
def _FCZ:List Piece:=DZ.decode 58 41 0x14909548083da7679e117d719d7577a8eab1631e57cb0ba50d9c694f30002
theorem shape14_0:validFrom 11179 0 _FCZ=true:=by decide+kernel
def _FDA:List Piece:=DZ.decode 58 41 0x14909548083da9a91b7ad0ffcd7557a8eab1631e59aa13e969363d4d30002
theorem shape14_1:validFrom 11178 0 _FDA=true:=by decide+kernel
def _FDP:List Piece:=DZ.decode 58 41 0x14909548083dabea98e4248dfd7537a8eab1631e5b891c2dc4d0114b30002
theorem shape14_2:validFrom 11177 0 _FDP=true:=by decide+kernel
def _FEA:List Piece:=DZ.decode 58 41 0x14909548083dae26f228261a257517a8eab1631e5d6824722069e54920002
theorem shape14_3:validFrom 11176 0 _FEA=true:=by decide+kernel
def _FEL:List Piece:=DZ.decode 58 41 0x14909548083db0686f9179a85574f7a8eab1631e5f472cb67c03b94720002
theorem shape14_4:validFrom 11175 0 _FEL=true:=by decide+kernel
def _FEW:List Piece:=DZ.decode 58 41 0x14909548083db2a9ecfacd368574d7a8eab1631e612634fad79d8d4520002
theorem shape14_5:validFrom 11174 0 _FEW=true:=by decide+kernel
def _FFH:List Piece:=DZ.decode 58 41 0x14909548083db4e6463ecec2ad74b7a8eab1631e63053d3f3337614310002
theorem shape14_6:validFrom 11173 0 _FFH=true:=by decide+kernel
def _FFS:List Piece:=DZ.decode 58 41 0x14909548083db727c3a82250dd7497a8eab1631e64e445838ed1354110002
theorem shape14_7:validFrom 11172 0 _FFS=true:=by decide+kernel
def _FGD:List Piece:=DZ.decode 58 41 0x14909548083db969411175df0d7477a8eab1631e66c34dc7ea6b093f10002
theorem shape14_8:validFrom 11171 0 _FGD=true:=by decide+kernel
def _FGO:List Piece:=DZ.decode 58 41 0x14909548083dbba59a55776b357457a8eab1631e68a2560c4604dd3d00002
theorem shape14_9:validFrom 11170 0 _FGO=true:=by decide+kernel
def _FDB:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8549095480821dbde717becaf9656c57a8eab16310e6a815e50a19eb13b00003
theorem shape14_10:validFrom 11169 0 _FDB=true:=by decide+kernel
def _FDG:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8149095480821dc02895281e87955b77a8eab16310e6c606694fd38853900003
theorem shape14_11:validFrom 11168 0 _FDG=true:=by decide+kernel
def _FDH:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7d49095480821dc26a12917215c54a57a8eab16310e6e3f6ed958d2593700003
theorem shape14_12:validFrom 11167 0 _FDH=true:=by decide+kernel
def _FDI:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7949095480821dc4a66bd573a1ed38b7a8eab16310e701e771db46c2d34f0003
theorem shape14_13:validFrom 11166 0 _FDI=true:=by decide+kernel
def _FDJ:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7549095480821dc6e7e93ec7301d26d7a8eab16310e71fd7f6210060132f0003
theorem shape14_14:validFrom 11165 0 _FDJ=true:=by decide+kernel
def _FDK:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7149095480821dc0de1672cd77651477a8eab16310e7940de5da6e4c11720003
theorem shape14_15:validFrom 11164 0 _FDK=true:=by decide+kernel
def _FDL:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6d49095480821dc2fb96d6e2f75d01b7a8eab16310e7b35d438647f1914b0003
theorem shape14_16:validFrom 11163 0 _FDL=true:=by decide+kernel
def _FDM:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6949095480821dc519173af87754ee97a8eab16310e7d2aca132219711240003
theorem shape14_17:validFrom 11162 0 _FDM=true:=by decide+kernel
def _FDN:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6549095480821dc53b05d3231fc4daf7a8eab16310e80d6b5bf0687850880003
theorem shape14_18:validFrom 11161 0 _FDN=true:=by decide+kernel
def _FDO:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b98a484aa40410eb991bf7982ad5a6360002
theorem shape14_19:validFrom 11160 0 _FDO=true:=by decide+kernel
def _FDQ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b97a484aa40410ebb04c0834c94f25920002
theorem shape14_20:validFrom 11159 0 _FDQ=true:=by decide+kernel
def _FDR:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b96a484aa40410ebfa4366855dc524ea0002
theorem shape14_21:validFrom 11158 0 _FDR=true:=by decide+kernel
def _FDS:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9500000000000f0ca77ef3cb8e3570a5e99d545850f05913261075d99258bd33aa8b090ecb9b7dc8e4d29922a0004
theorem shape14_22:validFrom 11157 0 _FDS=true:=by decide+kernel
def _FDT:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9400000000000f0cddd77eebb8456e45e99d545850f05d854e6cfc4c123dbd33aa8b090ecc70fe00aca11520f0004
theorem shape14_23:validFrom 11156 0 _FDT=true:=by decide+kernel
def _FDU:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9300000000000f0d142ea36e11556bf5e99d545850f061f7609e5b215221bd33aa8b090ecd467e38746f911f30004
theorem shape14_24:validFrom 11155 0 _FDU=true:=by decide+kernel
def _FDV:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9200000000000f0d4a846152983d6995e99d545850f066695ca492579206bd33aa8b090ece1bfe703c3e0d1d70004
theorem shape14_25:validFrom 11154 0 _FDV=true:=by decide+kernel
def _FDW:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9100000000000f0d80d8b8994da16735e99d545850f06af2e8f4f35211eabd33aa8b090ecef17ea8040c891bb0004
theorem shape14_26:validFrom 11153 0 _FDW=true:=by decide+kernel
def _FDX:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9000000000000f0db72ba942320d64c5e99d545850f06f94058f7e0e51cdbd33aa8b090ecfc6fedfcbdb0519f0004
theorem shape14_27:validFrom 11152 0 _FDX=true:=by decide+kernel
def _FDY:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8f00000000000f0ded7d334d44e56255e99d545850f07405bf143e6bd1b1bd33aa8b090ed09c7f1793a9811820004
theorem shape14_28:validFrom 11151 0 _FDY=true:=by decide+kernel
def _FDZ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8e00000000000f0e23cd56ba84f55fc5e99d545850f0788f08e3288cd194bd33aa8b090ed171ff4f5b77fd1650004
theorem shape14_29:validFrom 11150 0 _FDZ=true:=by decide+kernel
def _FEB:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8d00000000000f0e5a1c1389f4b15d35e99d545850f07d183c86eb0d5176bd33aa8b090ed2477f872346791470004
theorem shape14_30:validFrom 11149 0 _FEB=true:=by decide+kernel
def _FEC:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8c00000000000f0e906969bb92dd5a95e99d545850f081b90074d7535159bd33aa8b090ed31cffbeeb14f51290004
theorem shape14_31:validFrom 11148 0 _FEC=true:=by decide+kernel
def _FED:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8b00000000000f0ec6b5594f5eed57e5e99d545850f0867154aced5a113abd33aa8b090ed3f27ff6b2e37110b0004
theorem shape14_32:validFrom 11147 0 _FED=true:=by decide+kernel
def _FEE:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8a00000000000f0efcffe24559415535e99d545850f08b11ec448a64511cbd33aa8b090ed4c8002e7ab1ed0ec0004
theorem shape14_33:validFrom 11146 0 _FEE=true:=by decide+kernel
def _FEF:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8900000000000f0f3349049d82355285e99d545850f08fe1ba9ba29bd0fdbd33aa8b090ed59d80664280690cd0004
theorem shape14_34:validFrom 11145 0 _FEF=true:=by decide+kernel
def _FEG:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8800000000000f0f6990c057da294fc5e99d545850f09499cc5241bf50ddbd33aa8b090ed673009e0a4ee50ad0004
theorem shape14_35:validFrom 11144 0 _FEG=true:=by decide+kernel
def _FEH:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8700000000000f0f9fd7157460954cf5e99d545850f099696e530ab250bdbd33aa8b090ed74880d5d21d6108d0004
theorem shape14_36:validFrom 11143 0 _FEH=true:=by decide+kernel
def _FEI:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8600000000000f0fd61c03f314114a15e99d545850f09e2153b35aa2109dbd33aa8b090ed81e010d99ebdd06c0004
theorem shape14_37:validFrom 11142 0 _FEI=true:=by decide+kernel
def _FEJ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8500000000000f100c5f8bd3f7594725e99d545850f0a2f0c95dd459107cbd33aa8b090ed8f3814561ba5904a0004
theorem shape14_38:validFrom 11141 0 _FEJ=true:=by decide+kernel
def _FEK:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae1000000000007882150d68b848aa20de99d545850ef29d61e5ab2ec105a0003
theorem shape14_39:validFrom 11140 0 _FEK=true:=by decide+kernel
def _FEM:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae0c00000000007883c7133de2458a08de99d545850ef31f8d02e4f1d10380003
theorem shape14_40:validFrom 11139 0 _FEM=true:=by decide+kernel
def _FEN:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae0800000000007885790ddf4b9b29efde99d545850ef3a33124c151a50150003
theorem shape14_41:validFrom 11138 0 _FEN=true:=by decide+kernel
def _FEO:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae04000000000078872afd4a987f29d6de99d545850ef429c8b2956250ff10003
theorem shape14_42:validFrom 11137 0 _FEO=true:=by decide+kernel
def _FEP:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae0000000000007888dce180f6d249bcde99d545850ef4b1d9450c10a4fcd0003
theorem shape14_43:validFrom 11136 0 _FEP=true:=by decide+kernel
def _FEQ:List Piece:=DZ.decode 62 39 0x3782dace9d900000adfc0000000000788a8eba82669d89a1de99d545850ef53b62dc2559b0fa80003
theorem shape14_44:validFrom 11135 0 _FEQ=true:=by decide+kernel
def _FER:List Piece:=DZ.decode 62 39 0x1bc16d674ec8000056fd7a675516143c46262879437834c300000000000788c40884ee7d4e87ede99d545850ef918dee8675decf830004
theorem shape14_45:validFrom 11134 0 _FER=true:=by decide+kernel
def _FES:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7d5e99d545850f30043f92646eb52d4e8d4a510000f2ba55073adc014f5c00000000000f11be495ccf5054de80004
theorem shape14_46:validFrom 11133 0 _FES=true:=by decide+kernel
def _FET:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7c00000000000f368aa30043300129b00000000000f368a0c2073e00129000000000000f36893055ab000128000000000000f3688548ae2200127000000000000f368778c019400126000000000000f36869cf550600125000000000000f3685c12a87800124000000000000f3684e55fbea00123000000000000f36840994f5c00122000000000000f36832dca2ce00121000000000000f368251ff64000120000000000000f368176349b20011f000000000000f36809a69d240011e000000000000f367fbe9f0960011d000000000000f367ee2d44080011c000000000000f367e070977a0011b000000000000f367d2b3eaec0011a000000000000f367c4f73e5e00119000000000000f367b73a91d000118000000000000f367a97de54200117000000000000f3679bc138b400116000000000000f3678e048c2600115000000000000f3678047df9800114000000000000f367728b330a00113000000000000f36764ce867c00112000000000000f3675711d9ee00111000000000000f36749552d6000110000000000000f3673b9880d20010f000000000000f3672ddbd4440010e000000000000f367201f27b60010d000000000000f36712627b280010c000000000000f36704a5ce9a0010b000000000000f366f6f808be8010a000000000000f366e93b5c3080109000000000000f366db7eafa280108000000000000f366cdc2031480107000000000000f366c005568680106000000000000f366b248a9f880105000000000000f366a48bfd6a80104000000000000f36696cf50dc80103000000000000f3668912a44e80102000000000000f3667b55f7c080101000000000000f3666d994b3280100000000000000f3665fdc9ea4800ff000000000000f366521ff216800fe000000000000f36644634588800fd000000000000f36636a698fa800fc000000000000f36628e9ec6c800fb000000000000f3661b2d3fde800fa000000000000f3660d709350800f9000000000000f365ffb3e6c2800f8000000000000f365f1f73a34800f7000000000000f365e43a8da6800f6000000000000f365d67de118800f5000000000000f365c8c1348a800f4000000000000f3660331f898800f3500000000000f365fa949966800f3000000000000f365df1b404a800f2000000000000f365c3a1e72e800f1000000000000f35e84f63435000f0000000000000f35e6cfaecef000ef000000000000f35e550e8c5b800ee000000000000f35e3d134515800ed000000000000f35e2517fdcf800ec000000000000f35e0d1cb689800eb000000000000f35df53055f6000ea000000000000f35ddd350eb0000e9000000000000f35dc539c76a000e8000000000000f35dad3e8024000e7000000000000f35d95521f90800e6000000000000f35d7d56d84a800e5000000000000f35d655b9104800e4000000000000f35d4d6049be800e30e8d4a510000f35c73172940014e29e8d4a510000f2ba55073adc014e2500000000000f11f4804923d50cde7004d
theorem shape14_47:validFrom 11132 0 _FET=true:=by decide+kernel
def _FEU:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7b00000000000f369405d032500126000000000000f3692f7bacf000125000000000000f3691e9a56bb00124000000000000f3690db9008600123000000000000f368fcd7aa5100122000000000000f368ebf6541c00121000000000000f368db06173480120000000000000f368ca24c0ff8011f000000000000f368b9436aca8011e000000000000f368a86214958011d000000000000f3689780be608011c000000000000f368869f682b8011b000000000000f36875be11f68011a000000000000f36864dcbbc180119000000000000f36853ec7eda00118000000000000f368430b28a500117000000000000f3683229d27000116000000000000f36821487c3b00115000000000000f3681067260600114000000000000f367ff85cfd100113000000000000f367eea4799c00112000000000000f367ddc3236700111000000000000f367cce1cd3200110000000000000f367bbf1904a8010f000000000000f367ab103a158010e000000000000f3679a2ee3e08010d000000000000f367894d8dab8010c000000000000f367786c37768010b000000000000f367678ae1418010a000000000000f36756a98b0c80109000000000000f36745c834d780108000000000000f36734d7f7f000107000000000000f36723f6a1bb00106000000000000f36713154b8600105000000000000f3670233f55100104000000000000f366f1529f1c00103000000000000f366e07148e700102000000000000f366cf8ff2b200101000000000000f366beae9c7d00100000000000000f366adbe5f95800ff000000000000f3669cdd0960800fe000000000000f3668bfbb32b800fd000000000000f3667b1a5cf6800fc000000000000f3666a3906c1800fb000000000000f3665957b08c800fa000000000000f36648765a57800f9000000000000f36637950422800f8000000000000f36626a4c73b000f7000000000000f36615c37106000f6000000000000f36613aaffec000f5e00000000000f36604e21ad1000f5000000000000f365f400c49c000f4000000000000f365e31f6e67000f3000000000000f365d23e1832000f2000000000000f36607450d67800f1000000000000f35eb2b68442000f0000000000000f35e90e4f125800ef000000000000f35f703cb28e000ee000000000000f35f52c8b5bd000ed000000000000f35f35639f9e800ec000000000000f35f17fe8980000eb000000000000f35efa8a8caf000ea000000000000f35edd257690800e9000000000000f35ebfc06072000e8000000000000f35ea25b4a53800e7000000000000f35e84e74d82800e6000000000000f35e67823764000e5000000000000f35e3221d9ff800e4000000000000f35e14da9146000e30e8d4a510000f35c7f17314001ce2ce8d4a510000f2ba610742dc01ce2500000000000f122ab5ceda8838de70049
theorem shape14_48:validFrom 11131 0 _FEU=true:=by decide+kernel
def _FEV:List Piece:=DZ.decode 62 41 0x3782dace9d900000ade800000000001e6d37a70018f00244600000000000f369b96f6d750012200000000000079b4d2b4b6cc800908000000000003cda6458db6f400480000000000001e6d2fa9d0e5d0023e000000000000f369694887528011e00000000000079b4aaa143bb4008e8000000000003cda504b683a000470000000000001e6d25a4f421800236000000000000f3691921a1300011a00000000000079b4828dd0aa0008c8000000000003cda3c41aeb1600460000000000001e6d1ba0175d30022e000000000000f368c8fabb0d8011600000000000079b45a7a5d98c008a8000000000003cda2837f528c00450000000000001e6d119b3a98e00226000000000000f36878d3d4eb0011200000000000079b43266ea87800888000000000003cda142e3ba0200440000000000001e6d07965dd490021e000000000000f36828aceec88010e00000000000079b40a537776400868000000000003cda00248217800430000000000001e6cfd918110400216000000000000f367d88608a60010a00000000000079b3e2400465000848000000000003cd9ec1ac88ee00420000000000001e6cf38ca44bf0020e000000000000f367885f22838010600000000000079b3ba2c9153c00828000000000003cd9d8110f06400410000000000001e6ce987c787a00206000000000000f36738383c610010200000000000079b39211aae9400808000000000003cd9c407557da00400000000000001e6cdf82eac35001fe000000000000f366e811563e800fe00000000000079b369fe37d80007e8000000000003cd9affd9bf50003f0000000000001e6cd57e0dff0001f6000000000000f36697ea701c000fa02829cd1d00079b341eac4c6c007c8800000000003cd9a0a7273a4003e3c00000000001e6ccdf9f1363001f0000000000000f3665bc989d5800f700000000000079b323e1c4fcc007b0000000000003cd98ceba8dac003d4000000000001e6cc3f51471e001e8000000000000f3660ba2a3b3000f300000000000079b2fbce51eb800790000000000003cd978e1ef522003c4000000000001e6bbae8a4722001e0000000000000f35f23584377800ef00000000000079af7d9eae86800770000000000003cd7b4c89da8a003b4000000000001e6bd562cedd5001d8000000000000f36023844622000eb00000000000079b000533d3c400750000000000003cd7f7722bb3c003a4000000000001e6bf75d5c64b001d0000000000000f35f980d177c000e700000000000079afba9f1942800730000000000003cd7d26d083dc00394000000000001e6bdf2fca844001c81409b988a000f35ea9576dff800e31746a528800079ae458b9ca0012717f46a52880003caec65c6f5900d3895d1a94a20001e574da0e95b8049bd200000000000f1260e9edf36848de70047
theorem shape14_49:validFrom 11130 0 _FEV=true:=by decide+kernel
def _FEX:List Piece:=DZ.decode 62 41 0x1bc16d674ec8000056f200000000000f36a1f7929c38011e40000000000079b50cdaf95e0008f0000000000003cda809f18a1a00474000000000001e6d3d6a3720700238000000000000f369d41828ce0011b00000000000079b4de76bfa58008d0000000000003cda6970b572000464000000000001e6d31d128b2500230000000000000f369775e9c0f8011700000000000079b4b01285ed0008b0000000000003cda523e9895c00454000000000001e6d2639f71a800228000000000000f3691a96289e8011300000000000079b481b5bf8dc00890000000000003cda3b0c7bb9800444000000000001e6d1aa0e8ac600220000000000000f368bddc9be00010f00000000000079b4535185d5400870000000000003cda23de1889e00434000000000001e6d0f07da3e400218000000000000f3686114286f0010b00000000000079b424f4bf76000850000000000003cda0cabfbada00424000000000001e6d0370a8a6700210000000000000f368044bb4fe0010700000000000079b3f69085bd800830000000000003cd9f57d987e000414000000000001e6cf7d79a38500208000000000000f367a792283f8010300000000000079b3c82c4c05000810000000000003cd9de4b7ba1c00404000000000001e6cec4068a0800200000000000000f3674ac9b4ce800ff00000000000079b399cf85a5c007f0000000000003cd9c7195ec58003f4000000000001e6ce0a75a326001f8000000000000f366ee102810000fb00000000000079b36b6b4bed4007d0000000000003cd9afeafb95e003e4000000000001e6cd50e4bc44001f0000000000000f3669147b49f000f700000000000079b33d0e858e0007b0000000000003cd998b8deb9a003d4000000000001e6cc9771a2c7001e8000000000000f366347f412e000f300000000000079b30eaa4bd5800790000000000003cd9818a7b8a0003c4000000000001e6bc47f9bd20001e0000000000000f35e0cd2350d000ef00000000000079aefacc526bc00770000000000003cd7779b7ed52003b4000000000001e6bb8e86a3a3001d8000000000000f35f258e81f6800ebe0000000000079af7e7e32fc000758000000000003cd7b3a60b0fe003a8000000000001e6c1be3d6ed7001d2000000000000f360b6c83637000e800000000000079b047404dda800738000000000003cd8198e404cc00398000000000001e6c03e88fa77001ca000000000000f35fc27c09ca800e400000000000079afb2d257d3800718746a52880003cd730c5d65000d38afa3529440001e5754a0ed5b8069c4a00000000000f12971ca66e7858de70042
theorem shape14_50:validFrom 11129 0 _FEX=true:=by decide+kernel
def _FEY:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b780000000000079b533dac0890008d2000000000003cda98486b11e00468000000000001e6d48d86e4d600232000000000000f36a2c741f410011800000000000079b5090af2b24008b8000000000003cda7df1a48ea00458000000000001e6d3bad0b0bc0022a000000000000f369c31905340011400000000000079b4d45d65abc00898000000000003cda6397245ec00448000000000001e6d2e81a7ca200222000000000000f36959af04748011000000000000079b49fafd8a5400878000000000003cda49405ddb800438000000000001e6d2156448880021a000000000000f368f053ea678010c00000000000079b46b024b9ec00858000000000003cda2ee99758400428000000000001e6d142ae146e00212000000000000f36886f8d05a8010800000000000079b43654be98400838000000000003cda1492d0d5000418000000000001e6d06fda12ef0020a000000000000f3681d9db64d8010400000000000079b4019fbe38800818000000000003cd9fa3c0a51c00408000000000001e6cf9d23ded500202000000000000f367b4429c408010000000000000079b3ccf231320007f8000000000003cd9dfe543ce8003f8000000000001e6ceca6daabb001fa000000000000f3674ae78233800fc00000000000079b39844a42b8007d8000000000003cd9c58e7d4b4003e8000000000001e6cdf7b776a1001f2000000000000f366e18c6826800f800000000000079b3639717250007b8000000000003cd9ab33fd1b6003d8000000000001e6cd25014287001ea000000000000f36678226767000f400000000000079b32ee98a1e800798000000000003cd990dd36982003c8000000000001e6cc524b0e6d001e2000000000000f35e711ce870800f000000000000079af2b66caa3400778000000000003cd78f1bd6da8003b8000000000001e6bc44401080001da000000000000f35e07c1ce63800ec00000000000079aef6b93d9cc00758000000000003cd774c510574003a8000000000001e6be1cc7b0e7001d2000000000000f35ed9b64b6d000e800000000000079af52845f33400738000000000003cd855f5ee63200398000000000001e6c1ecce5ca7001ca000000000000f3608cfd2d94000e400000000000079b011c9966a400718746a52880003cd744c5e15001138b3a3529440001e575ea0f2db8089c4a00000000000f12cd4df84bb6d8de7003d
theorem shape14_51:validFrom 11128 0 _FEY=true:=by decide+kernel
def _FEZ:List Piece:=DZ.decode 62 62 0xde0b6b3a76400002b77ced4c2217f3988003cdaa463dc19e0045880000000000000000f36a8fc180ca00116000000000000000003cda9c8fa751a0045400000000000000000f36a54bbb9c300114000000000000000003cda8dd1ef3c80044c00000000000000000f36a19c4d96e80112000000000000000003cda7f107d7ac0044400000000000000000f369decdf91a00110000000000000000003cda7052c565a0043c00000000000000000f369a3c832130010e000000000000000003cda61950d5080043400000000000000000f36968d151be8010c000000000000000003cda52d39b8ec0042c00000000000000000f3692dda716a0010a000000000000000003cda4415e379a0042400000000000000000f368f2d4aa6300108000000000000000003cda355471b7e0041c00000000000000000f368b7ddca0e80106000000000000000003cda2696b9a2c0041400000000000000000f3687cd8030780104000000000000000003cda17d9018da0040c00000000000000000f36841e122b300102000000000000000003cda09178fcbe0040400000000000000000f36806ea425e80100000000000000000003cd9fa59d7b6c003fc00000000000000000f367cbe47b57800fe000000000000000003cd9eb9c1fa1a003f400000000000000000f36790ed9b03000fc000000000000000003cd9dcdaaddfe003ec00000000000000000f36755f6baae800fa000000000000000003cd9ce1cf5cac003e400000000000000000f3671af0f3a7800f8000000000000000003cd9bf5f3db5a003dc00000000000000000f366dffa1353000f6000000000000000003cd9b09dcbf3e003d400000000000000000f366a50332fe800f4000000000000000003cd9a1e013dec003cc00000000000000000f36669fd6bf7800f2000000000000000003cd993225bc9a003c400000000000000000f35ebea54132800f0000000000000000003cd7a84c51186003bc0000006e9834ce000f35e858b372e000ee200000000000000003cd7a0eb98378003b800000000000000000f35e662b7d5a800ed000000000000000003cd7922de0226003b000000000000000000f35e2b349d06000eb000000000000000003cd7836c6e60a003a800000000000000000f35df03dbcb1800e9000000000000000003cd774aeb64b8003a000000000000000000f35f0758ce15000e7000000000000000003cd7b3187b7020039800000000000000000f35e915c26b9800e5000000000000000003cd79599519940039000000000000000000f360e313fed5800e3000000746a52880003cd75ec5ef5001538b400003a3529440000f2bcc5dcb7ec064e2500000800044000103caed741f3b701537a40000000000000000f13037de38b2340de7003b
theorem shape14_52:validFrom 11127 0 _FEZ=true:=by decide+kernel
def _FFA:List Piece:=DZ.decode 62 42 0x3782dace9d900000add800000000000f36a9b56d58b80111b000000000003cdaa137bf19a00444000000000000f36a644655ee801100000000000003cda90e7b23100043c000000000000f36a22f73b998010e0000000000003cda8093eb9bc00434000000000000f369e1a821448010c0000000000003cda7040250680042c000000000000f369a067eda20010a0000000000003cda5ff0181de00424000000000000f3695f18d34d001080000000000003cda4f9c5188a0041c000000000000f3691dc9b8f8001060000000000003cda3f4c44a0000414000000000000f368dc898555801040000000000003cda2ef87e0ac0040c000000000000f3689b3a6b00801020000000000003cda1ea4b775800404000000000000f36859eb50ab801000000000000003cda0e54aa8ce003fc000000000000f36818ab1d09000fe0000000000003cd9fe00e3f7a003f4000000000000f367d75c02b4000fc0000000000003cd9edad1d626003ec000000000000f367961bcf11800fa0000000000003cd9dd5d1079c003e4000000000000f36754ccb4bc800f80000000000003cd9cd0949e48003dc000000000000f367137d9a67800f60000000000003cd9bcb93cfbe003d4000000000000f366d23d66c5000f40000000000003cd9ac657666a003cc000000000000f36690ee4c70000f20000000000003cd99c11afd16003c4000000000000f35f0c95e8d6000f00000000000003cd7bafb96eae003bc000000000000f35ecb55b533800ee0000000000003cd7aaab8a024003b4000000000000f35e8a069ade800ec0000000000003cd79a57c36d0003ac000000000000f35e48b78089800ea0000000000003cd78a03fcd7c003a4000000000000f35e07774ce7000e80000000000003cd779b3efef20039c000000000000f35dc6283292000e60000000000003cd769602959e00394000000000000f35ea69b133a000e40000000000003cd79956b7e5e0038c1a90b795de70f35dfb180140064e27e8d4a5100003caef74204b7019389400000000000f1339ac682cbea4de70034
theorem shape14_53:validFrom 11126 0 _FFA=true:=by decide+kernel
def _FFB:List Piece:=DZ.decode 62 42 0x3782dace9d900000add400000000000f36a8573ff5f8010d3000000000003cda9facdd9f600434000000000000f36a5ae73fac0010c0000000000003cda8dc6c236a0042c000000000000f36a134ed2090010a0000000000003cda7be4607a800424000000000000f369cbc54b18801080000000000003cda69fe4511c0041c000000000000f369842cdd75801060000000000003cda581829a9000414000000000000f3693c946fd2801040000000000003cda46320e4040040c000000000000f368f4fc022f801020000000000003cda344bf2d7800404000000000000f368ad63948c801000000000000003cda2265d76ec003fc000000000000f36865cb26e9800fe0000000000003cda107fbc060003f4000000000000f3681e32b946800fc0000000000003cd9fe99a09d4003ec000000000000f367d69a4ba3800fa0000000000003cd9ecb385348003e4000000000000f3678f01de00800f80000000000003cd9dacd69cbc003dc000000000000f3674769705d800f60000000000003cd9c8eb080fa003d4000000000000f366ffdfe96d000f40000000000003cd9b704eca6e003cc000000000000f366b8477bca000f20000000000003cd9a51ed13e2003c4000000000000f35f5aeedf5b000f00000000000003cd7cdc8aa226003bc000000000000f35f135671b8000ee0000000000003cd7bbe28eb9a003b4000000000000f35ecbbe0415000ec0000000000003cd7a9fc7350e003ac000000000000f35e84259672000ea0000000000003cd7981657e82003a4000000000000f35e4e7ab791000e88000000000003cd78f234a33c003a0000000000000f35e18c0f1fd800e70000000000003cd77d3d2ecb000398000000000000f35dd128845a800e50000000000003cd76b571362400390000000000000f35d899016b7800e30e8d4a5100003caf1d4218b701d389400000000000f136fd98630876cde70030
theorem shape14_54:validFrom 11125 0 _FFB=true:=by decide+kernel
def _FFC:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b74000000000003cda93ab804fc00422400000000000f36a38cb2b13001080000000000003cda847692a6a0041c000000000000f369eae96a22001060000000000003cda70fe226a600414000000000000f3699d07a931001040000000000003cda5d85b22e20040c000000000000f3694f17018d801020000000000003cda4a098845400404000000000000f3690135409c801000000000000003cda369118090003fc000000000000f368b3537fab800fe0000000000003cda2318a7ccc003f4000000000000f3686571beba800fc0000000000003cda0fa037908003ec000000000000f368178ffdc9800fa0000000000003cd9fc27c7544003e4000000000000f367c9ae3cd8800f80000000000003cd9e8ab9d6b6003dc000000000000f3677bbd9535000f60000000000003cd9d5332d2f2003d4000000000000f3672ddbd444000f40000000000003cd9c1babcf2e003cc000000000000f366dffa1353000f20000000000003cd9ae424cb6a003c4000000000000f35fa9a13e0f000f00000000000003cd7e0ac1765a003bc000000000000f35f5bbf7d1e000ee0000000000003cd7cd33a7296003b4000000000000f35f0dddbc2d000ec0000000000003cd7b9bb36ed2003ac000000000000f35ebfed1489800ea026f0e0788003cd7a63f0d044003a4400000000000f35e9699417a800e8f000000000003cd79c82d4e62003a0000000000000f35e4b1a7320000e70000000000003cd7890a64a9e00398000000000000f35dfd38b22f000e50000000000003cd77591f46da00390000000000000f35daf56f13e000e30e8d4a5100003caf49422fb7021389400000000000f13a6053d967f24de7002b
theorem shape14_55:validFrom 11124 0 _FFC=true:=by decide+kernel
def _FFD:List Piece:=DZ.decode 62 43 0x3782dace9d900000adcc0000000000079b4f8565094c0081d800000000000f369d3bec09f001030000000000001e6d353526cff002040000000000003cda5fe1316b60040400000000000079b4aab79dc7000800000000000000f3692b59b16e800ff0000000000001e6d202884e9e001fc0000000000003cda35cba74be003f400000000000079b45685162ec007e0000000000000f36882f4a23e000fb0000000000001e6d0b1be303d001f40000000000003cda0bb2637fc003e400000000000079b402528e968007c0000000000000f367da8f930d800f70000000000001e6cf60f411dc001ec0000000000003cd9e1991fb3a003d400000000000079b3ae277a578007a0000000000000f367322a83dd000f30000000000001e6ce1029f37b001e40000000000003cd9b77fdbe78003c400000000000079affc5df5d2400780000000000000f35fcea66185000ef0000000000001e6bf4921aecb001dc0000000000003cd7de9b19a4e003b400000000000079afa82b6e3a000760000000000000f35f26415254800eb0000000000001e6bdf857906a001d40000000000003cd7b8771d42c003a580000000000079af6903abb1800748000000000000f35ea7f1cd43800e80000000000001e6bcfbb88648001ce0000000000003cd794f1ae4120039800000000000079af14d12419400728000000000000f35dff8cbe13000e40000000000001e6bbaaee67e7001c615d3ef7980003cb00a92249d0293895d1a94a20000795ef684936e04a6f4800000000000f13dc2f8e5ea5dcde70027
theorem shape14_56:validFrom 11123 0 _FFD=true:=by decide+kernel
def _FFE:List Piece:=DZ.decode 62 43 0xde0b6b3a76400002b72000000000001e6d2d7b05c01001fd4000000000003cda53e38dc86003f800000000000079b4912a01ad8007e8000000000000f368f519cf94800fc0000000000001e6d18fa16a37001f60000000000003cda26a5a0554003e800000000000079b436a6b36e0007c8000000000000f36840133315800f80000000000001e6d025b1fe9e001ee0000000000003cd9f963f9358003d800000000000079b3dc2ad887c007a8000000000000f3678b1b7d49000f40000000000001e6cebba4c5a0001e60000000000003cd9cc260bc26003c800000000000079b381aefda1800788000000000000f360483ee81b800f00000000000001e6c035eb9b45001de0000000000003cd7fb6ee6770003b800000000000079afe040b30ac00768000000000000f35f93384b9c800ec0000000000001e6becbfc2fac001d60000000000003cd7ce30f903e003a800000000000079af85bd64cb400748000000000000f35ede4095d0000e80000000000001e6bd6d579758001ce4000000000003cd7ac41988260039c00000000000079af41dea3c8400730000000000000f35e568313ca000e50000000000001e6bc5273f2a2001c80000000000003cd77efff162a0038c2ba7def30000795f6684cd6e052712800000000000f1412587888fb08de70021
theorem shape14_57:validFrom 11122 0 _FFE=true:=by decide+kernel
def _FFF:List Piece:=DZ.decode 62 43 0x1bc16d674ec8000056e2000000000003cda305e1ec6c003e5c0000000000079b456243aa68007c8000000000000f3687be997df800f80000000000001e6d096f7a77f001ee0000000000003cda06c73d948003d800000000000079b3f55799190007a8000000000000f367ba5054c4800f40000000000001e6cf13c52149001e60000000000003cd9d660eccdc003c800000000000079b3948af78b800788000000000000f360981b4cc1800f00000000000001e6c0cf78dea8001de0000000000003cd80dd3aacd0003b800000000000079b00377e6e3400768000000000000f35fd68209a6800ec0000000000001e6bf4c465872001d60000000000003cd7dd6d5a064003a800000000000079afa2ab4555c00748000000000000f35f14e8c68b800e80000000000001e6bdf373ddd8001cee000000000003cd7b9227a4780039c00000000000079af5a0e127f000730000000000000f35e83bd4790800e50000000000001e6bca69f06e1001c80000000000003cd788bc2980c0038c2ba7def30000795fe2850d6e05a712800000000000f14487ffc157cf8de7001c
theorem shape14_58:validFrom 11121 0 _FFF=true:=by decide+kernel
def _FFG:List Piece:=DZ.decode 62 62 0xde0b6b3a76400002b70ced4ec68658850003cd9fb4842dec003d080000000000000000f367e9de946f000f4000000000000000003cd9ed96c356a003cc00000000000000000f36782c89f93800f2000000000000000003cd9d3cd8c732003c400000000000000000f360e86ee6fb800f0000000000000000003cd82d371e4d2003bc00000000000000000f360814a0b6d800ee000000000000000003cd81371a1164003b400000000000000000f3601a341692000ec000000000000000003cd7f9ac23df6003ac00000000000000000f35fb31e21b6800ea000000000000000003cd7dfe2ecfbe003a400000000000000000f35f4c082cdb000e8000000000000000003cd7cefa236da0039ec0000000000000000f35f1875bf14000e7000000000000000003cd7b938d45340039800000000000000000f35eb15fca38800e5000000000000000003cd79f73571c60039000000000000000000f35e4a3aeeaa800e30000015d3ef7980003cb03542a9b703138940000000000000000f147ea619042f08de70017
theorem shape14_59:validFrom 11120 0 _FFG=true:=by decide+kernel
def _FFI:List Piece:=DZ.decode 62 43 0x1bc16d674ec8000056de000000000003cd838e686c70003b9c0000000000079b065d6dd44400770000000000000f360950589cd000ed0000000000001e6c0bc9ce4be001d80000000000003cd809e5d6bc4003ac00000000000079aff87021c1800750000000000000f35fba292c15000e90000000000001e6bf0701f6b3001d00000000000003cd7d33278fae0039c00000000000079af8b09663ec00730000000000000f35edf5bb50f800e50000000000001e6bd516708a8001c80000000000003cd79c7f1b3980038c2ba7def300007960fe859f6e06a712800000000000f14b4cacf550ef8de70010
theorem shape14_60:validFrom 11119 0 _FFI=true:=by decide+kernel
def _FFJ:List Piece:=DZ.decode 62 43 0x1bc16d674ec8000056dc000000000003cd7f8c8e5bd4003a2c0000000000079afe4e8cad2c00742000000000000f35fbb533207000e80000000000001e6bf02eee1e4001ce0000000000003cd7d1eaa5a3e0039800000000000079af86e76abd400728000000000000f35ed3f31465800e40000000000001e6bd342ea6a1001c61d1a94a200003cb199ad773f03d3896ba7def3000079619e85f16e0726f4800000000000f14eaee1f081df0de7000c
theorem shape14_61:validFrom 11118 0 _FFJ=true:=by decide+kernel
def _FFK:List Piece:=DZ.decode 62 43 0x1bc16d674ec8000056dbd1a94a200003cd9acc7205003d38afa352944000079624a86496e07a712800000000000f152110081d5a28de70004
theorem shape14_62:validFrom 11117 0 _FFK=true:=by decide+kernel
def _FFL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d80f1557308a94c56cdc80002
theorem shape14_63:validFrom 11116 0 _FFL=true:=by decide+kernel
def _FFM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d60f158d4fa66e5fb4d620002
theorem shape14_64:validFrom 11115 0 _FFM=true:=by decide+kernel
def _FFN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d40f15c36d5baa286ccf90002
theorem shape14_65:validFrom 11114 0 _FFN=true:=by decide+kernel
def _FFO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d20f15f989aa481dccc8c0002
theorem shape14_66:validFrom 11113 0 _FFO=true:=by decide+kernel
def _FFP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d00f162fa492484368c1c0002
theorem shape14_67:validFrom 11112 0 _FFP=true:=by decide+kernel
def _FFQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ce0f1665be13aa9774ba90002
theorem shape14_68:validFrom 11111 0 _FFQ=true:=by decide+kernel
def _FFR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056cc0f169bd62e6f196cb330002
theorem shape14_69:validFrom 11110 0 _FFR=true:=by decide+kernel
def _FFT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ca0f16d1ece295c910ab90002
theorem shape14_70:validFrom 11109 0 _FFT=true:=by decide+kernel
def _FFU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c80f170802301ea874a3c0002
theorem shape14_71:validFrom 11108 0 _FFU=true:=by decide+kernel
def _FFV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c60f173e161709b5b89bb0002
theorem shape14_72:validFrom 11107 0 _FFV=true:=by decide+kernel
def _FFW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c40f1774289756f2009380002
theorem shape14_73:validFrom 11106 0 _FFW=true:=by decide+kernel
def _FFX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c20f17aa39b1065b5c8b10002
theorem shape14_74:validFrom 11105 0 _FFX=true:=by decide+kernel
def _FFY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c00f17e0496417f3f88260002
theorem shape14_75:validFrom 11104 0 _FFY=true:=by decide+kernel
def _FFZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056be0f181657b08bbb947980002
theorem shape14_76:validFrom 11103 0 _FFZ=true:=by decide+kernel
def _FGA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056bc0f184bc8ba567c887060002
theorem shape14_77:validFrom 11102 0 _FGA=true:=by decide+kernel
def _FGB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ba0f187e2b7b1b45b86710002
theorem shape14_78:validFrom 11101 0 _FGB=true:=by decide+kernel
def _FGC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f18b08cf0df99ac5da0002
theorem shape14_79:validFrom 11100 0 _FGC=true:=by decide+kernel
def _FGE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f18e2ed1beec7c053e0002
theorem shape14_80:validFrom 11099 0 _FGE=true:=by decide+kernel
def _FGF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f19154bfbfd80d449f0002
theorem shape14_81:validFrom 11098 0 _FGF=true:=by decide+kernel
def _FGG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f1947a9915710e03fb0002
theorem shape14_82:validFrom 11097 0 _FGG=true:=by decide+kernel
def _FGH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b00f197a05dbb02e883540002
theorem shape14_83:validFrom 11096 0 _FGH=true:=by decide+kernel
def _FGI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ae0f19ac60db5423802aa0002
theorem shape14_84:validFrom 11095 0 _FGI=true:=by decide+kernel
def _FGJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ac0f19deba8ff7a5c41fe0002
theorem shape14_85:validFrom 11094 0 _FGJ=true:=by decide+kernel
def _FGK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056aa0f1a1112f9e5fca414e0002
theorem shape14_86:validFrom 11093 0 _FGK=true:=by decide+kernel
def _FGL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056a80f1a436a18d3e37009a0002
theorem shape14_87:validFrom 11092 0 _FGL=true:=by decide+kernel
def _FGM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4f3bc3d5ea25640cb0f1a75bfece6fcd40020002
theorem shape14_88:validFrom 11091 0 _FGM=true:=by decide+kernel
def _FGN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4b3bc30c97ffec5520f1aa8147644eab80020002
theorem shape14_89:validFrom 11090 0 _FGN=true:=by decide+kernel
def _FGP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473bc2434b06765d40f1ada67b4a268b00020002
theorem shape14_90:validFrom 11089 0 _FGP=true:=by decide+kernel
def _FGQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433bc17a0337d51e70f1b0cb9a84ab8640020002
theorem shape14_91:validFrom 11088 0 _FGQ=true:=by decide+kernel
def _FGR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3bc0b0c095359680f1b3f0a50f29a600020002
theorem shape14_92:validFrom 11087 0 _FGR=true:=by decide+kernel
def _FGS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3bbfe7831d6ac350f1b7159aee54f2c0020002
theorem shape14_93:validFrom 11086 0 _FGS=true:=by decide+kernel
def _FGT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373bbf1e4ad1a1a6d0f1ba3a7c1d7964c0020002
theorem shape14_94:validFrom 11085 0 _FGT=true:=by decide+kernel
def _FGU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333bbe5517b0ad4ca0f1bd5f48a14acd80020002
theorem shape14_95:validFrom 11084 0 _FGU=true:=by decide+kernel
def _FGV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3bbd8be9bbba9de0f1c0840075158880020002
theorem shape14_96:validFrom 11083 0 _FGV=true:=by decide+kernel
def _FGW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3bbcc2c0f19caf10f1c3a8a39d8d43c0020002
theorem shape14_97:validFrom 11082 0 _FGW=true:=by decide+kernel
def _FGX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273bbbf99d53806e00f1c6cd3215fe4800020002
theorem shape14_98:validFrom 11081 0 _FGX=true:=by decide+kernel
def _FGY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233bbb307ee038f870f1c9f1abe31c1e40020002
theorem shape14_99:validFrom 11080 0 _FGY=true:=by decide+kernel
def _FDC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3bba676598f32510f1cd161100336bc0020002
theorem shape14_100:validFrom 11079 0 _FDC=true:=by decide+kernel
def _FDD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3bb99e517c821ab0f1d03a6171f79540020002
theorem shape14_101:validFrom 11078 0 _FDD=true:=by decide+kernel
def _FDE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bb8d5428c12b4f0f1d35e9d33b52c40020002
theorem shape14_102:validFrom 11077 0 _FDE=true:=by decide+kernel
def _FDF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bb80c38c6782400f1d682c44a1f7000020002
theorem shape14_103:validFrom 11076 0 _FDF=true:=by decide+kernel
def row14 (v:ℕ):List Piece:=match v with
 | 0=>_FCZ
 | 1=>_FDA
 | 2=>_FDP
 | 3=>_FEA
 | 4=>_FEL
 | 5=>_FEW
 | 6=>_FFH
 | 7=>_FFS
 | 8=>_FGD
 | 9=>_FGO
 | 10=>_FDB
 | 11=>_FDG
 | 12=>_FDH
 | 13=>_FDI
 | 14=>_FDJ
 | 15=>_FDK
 | 16=>_FDL
 | 17=>_FDM
 | 18=>_FDN
 | 19=>_FDO
 | 20=>_FDQ
 | 21=>_FDR
 | 22=>_FDS
 | 23=>_FDT
 | 24=>_FDU
 | 25=>_FDV
 | 26=>_FDW
 | 27=>_FDX
 | 28=>_FDY
 | 29=>_FDZ
 | 30=>_FEB
 | 31=>_FEC
 | 32=>_FED
 | 33=>_FEE
 | 34=>_FEF
 | 35=>_FEG
 | 36=>_FEH
 | 37=>_FEI
 | 38=>_FEJ
 | 39=>_FEK
 | 40=>_FEM
 | 41=>_FEN
 | 42=>_FEO
 | 43=>_FEP
 | 44=>_FEQ
 | 45=>_FER
 | 46=>_FES
 | 47=>_FET
 | 48=>_FEU
 | 49=>_FEV
 | 50=>_FEX
 | 51=>_FEY
 | 52=>_FEZ
 | 53=>_FFA
 | 54=>_FFB
 | 55=>_FFC
 | 56=>_FFD
 | 57=>_FFE
 | 58=>_FFF
 | 59=>_FFG
 | 60=>_FFI
 | 61=>_FFJ
 | 62=>_FFK
 | 63=>_FFL
 | 64=>_FFM
 | 65=>_FFN
 | 66=>_FFO
 | 67=>_FFP
 | 68=>_FFQ
 | 69=>_FFR
 | 70=>_FFT
 | 71=>_FFU
 | 72=>_FFV
 | 73=>_FFW
 | 74=>_FFX
 | 75=>_FFY
 | 76=>_FFZ
 | 77=>_FGA
 | 78=>_FGB
 | 79=>_FGC
 | 80=>_FGE
 | 81=>_FGF
 | 82=>_FGG
 | 83=>_FGH
 | 84=>_FGI
 | 85=>_FGJ
 | 86=>_FGK
 | 87=>_FGL
 | 88=>_FGM
 | 89=>_FGN
 | 90=>_FGP
 | 91=>_FGQ
 | 92=>_FGR
 | 93=>_FGS
 | 94=>_FGT
 | 95=>_FGU
 | 96=>_FGV
 | 97=>_FGW
 | 98=>_FGX
 | 99=>_FGY
 | 100=>_FDC
 | 101=>_FDD
 | 102=>_FDE
 | 103=>_FDF
 | _=>[]
theorem checked14 (v:ℕ) (hy:14+v≤117):validFrom (11193-14-v) 0 (row14 v)=true:=by
 have hv:v≤103:=by omega
 interval_cases v
 · exact shape14_0
 · exact shape14_1
 · exact shape14_2
 · exact shape14_3
 · exact shape14_4
 · exact shape14_5
 · exact shape14_6
 · exact shape14_7
 · exact shape14_8
 · exact shape14_9
 · exact shape14_10
 · exact shape14_11
 · exact shape14_12
 · exact shape14_13
 · exact shape14_14
 · exact shape14_15
 · exact shape14_16
 · exact shape14_17
 · exact shape14_18
 · exact shape14_19
 · exact shape14_20
 · exact shape14_21
 · exact shape14_22
 · exact shape14_23
 · exact shape14_24
 · exact shape14_25
 · exact shape14_26
 · exact shape14_27
 · exact shape14_28
 · exact shape14_29
 · exact shape14_30
 · exact shape14_31
 · exact shape14_32
 · exact shape14_33
 · exact shape14_34
 · exact shape14_35
 · exact shape14_36
 · exact shape14_37
 · exact shape14_38
 · exact shape14_39
 · exact shape14_40
 · exact shape14_41
 · exact shape14_42
 · exact shape14_43
 · exact shape14_44
 · exact shape14_45
 · exact shape14_46
 · exact shape14_47
 · exact shape14_48
 · exact shape14_49
 · exact shape14_50
 · exact shape14_51
 · exact shape14_52
 · exact shape14_53
 · exact shape14_54
 · exact shape14_55
 · exact shape14_56
 · exact shape14_57
 · exact shape14_58
 · exact shape14_59
 · exact shape14_60
 · exact shape14_61
 · exact shape14_62
 · exact shape14_63
 · exact shape14_64
 · exact shape14_65
 · exact shape14_66
 · exact shape14_67
 · exact shape14_68
 · exact shape14_69
 · exact shape14_70
 · exact shape14_71
 · exact shape14_72
 · exact shape14_73
 · exact shape14_74
 · exact shape14_75
 · exact shape14_76
 · exact shape14_77
 · exact shape14_78
 · exact shape14_79
 · exact shape14_80
 · exact shape14_81
 · exact shape14_82
 · exact shape14_83
 · exact shape14_84
 · exact shape14_85
 · exact shape14_86
 · exact shape14_87
 · exact shape14_88
 · exact shape14_89
 · exact shape14_90
 · exact shape14_91
 · exact shape14_92
 · exact shape14_93
 · exact shape14_94
 · exact shape14_95
 · exact shape14_96
 · exact shape14_97
 · exact shape14_98
 · exact shape14_99
 · exact shape14_100
 · exact shape14_101
 · exact shape14_102
 · exact shape14_103
end EP

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace EP
open DZ
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def _FGZ:List Piece:=DZ.decode 58 41 0x14909548083db3566fcd5827757557a8eab1631e61c3c6b2bba41d4460002
theorem shape15_0:validFrom 11178 0 _FGZ=true:=by decide+kernel
def _FHA:List Piece:=DZ.decode 58 41 0x14909548083db592c91159b39d7537a8eab1631e63a2cef7173df14250002
theorem shape15_1:validFrom 11177 0 _FHA=true:=by decide+kernel
def _FHO:List Piece:=DZ.decode 62 41 0x3782dace9d900000aea149095480821db7d4467aad41cd69b7a8eab16310e6581d73b72d7c54050003
theorem shape15_2:validFrom 11176 0 _FHO=true:=by decide+kernel
def _FHZ:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9d49095480821dba15c3e400cffd5957a8eab16310e6760df7fce71993e50003
theorem shape15_3:validFrom 11175 0 _FHZ=true:=by decide+kernel
def _FIK:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9949095480821dbc521d28025c254897a8eab16310e693fe7c42a0b6d3c40003
theorem shape15_4:validFrom 11174 0 _FIK=true:=by decide+kernel
def _FIV:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9549095480821dbe939a9155ea553797a8eab16310e6b1ef00885a5413a40003
theorem shape15_5:validFrom 11173 0 _FIV=true:=by decide+kernel
def _FJG:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9149095480821dc0d517faa978852637a8eab16310e6cfdf84ce13f153840003
theorem shape15_6:validFrom 11172 0 _FJG=true:=by decide+kernel
def _FJR:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8d49095480821dc311713eab04ad1497a8eab16310e6edd00913cd8e93630003
theorem shape15_7:validFrom 11171 0 _FJR=true:=by decide+kernel
def _FKC:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8949095480821dc552eea7fe92dd0297a8eab16310e70bc08d59872bd3430003
theorem shape15_8:validFrom 11170 0 _FKC=true:=by decide+kernel
def _FKN:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8549095480821dc7946c1152210cf037a8eab16310e729b1119f40c913230003
theorem shape15_9:validFrom 11169 0 _FKN=true:=by decide+kernel
def _FHB:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8149095480821dc9d5e97aa5af3cdd97a8eab16310e747a195e4fa6653030003
theorem shape15_10:validFrom 11168 0 _FHB=true:=by decide+kernel
def _FHF:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7d49095480821dcc1242bea73b64ca77a8eab16310e765921a2ab40392e20003
theorem shape15_11:validFrom 11167 0 _FHF=true:=by decide+kernel
def _FHG:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7949095480821dce53c027fac994b6f7a8eab16310e783829e706da0d2c20003
theorem shape15_12:validFrom 11166 0 _FHG=true:=by decide+kernel
def _FHH:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7549095480821dd0953d914e57c4a337a8eab16310e7a17322b6273e12a20003
theorem shape15_13:validFrom 11165 0 _FHH=true:=by decide+kernel
def _FHI:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7149095480821dd2d196d54fe3ec8ef7a8eab16310e7bf63a6fbe0db52810003
theorem shape15_14:validFrom 11164 0 _FHI=true:=by decide+kernel
def _FHJ:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6d49095480821dcc18f71471e6247a57a8eab16310e83acd2453721850a20003
theorem shape15_15:validFrom 11163 0 _FHJ=true:=by decide+kernel
def _FHK:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6949095480821dce36777887661c6537a8eab16310e85a1c81ff4bbdd07b0003
theorem shape15_16:validFrom 11162 0 _FHK=true:=by decide+kernel
def _FHL:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6549095480821dd053f7dc9ce6144fb7a8eab16310e8796bdfab256350540003
theorem shape15_17:validFrom 11161 0 _FHL=true:=by decide+kernel
def _FHM:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6149095480821dd129d78efdd59c39d7a8eab16310e8acf70ccb48f38fdb0003
theorem shape15_18:validFrom 11160 0 _FHM=true:=by decide+kernel
def _FHN:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b97a484aa40410ec145def3a5b7fa11b0002
theorem shape15_19:validFrom 11159 0 _FHN=true:=by decide+kernel
def _FHP:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b96a484aa40410ec2b8dffd6f9f920640002
theorem shape15_20:validFrom 11158 0 _FHP=true:=by decide+kernel
def _FHQ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b95a484aa40410ec75855e278e6f1fa80002
theorem shape15_21:validFrom 11157 0 _FHQ=true:=by decide+kernel
def _FHR:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9400000000000f0dce0189d8be9163c5e99d545850f05c65b3f2c9c691c5bd33aa8b090ed49bf93a654d910a20004
theorem shape15_22:validFrom 11156 0 _FHR=true:=by decide+kernel
def _FHS:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9300000000000f0e036737a41cc96155e99d545850f05cff062d22b651a9bd33aa8b090ed57179722d1c0d05d0004
theorem shape15_23:validFrom 11155 0 _FHS=true:=by decide+kernel
def _FHT:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9200000000000f0e38cb82bd012d5ed5e99d545850f05df6dc504f0b518dbd33aa8b090ed646f9a9f4ea8901a0004
theorem shape15_24:validFrom 11154 0 _FHT=true:=by decide+kernel
def _FHU:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae44000000000078737173591b5d0ae2de99d545850eee850f03afdd111700003
theorem shape15_25:validFrom 11153 0 _FHU=true:=by decide+kernel
def _FHV:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae40000000000078751c7f86bae22ace5e99d545850eeef90d1aee3aed1530003
theorem shape15_26:validFrom 11152 0 _FHV=true:=by decide+kernel
def _FHW:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae3c00000000007876c7809ec6978ab95e99d545850eef6e843aba8d711360003
theorem shape15_27:validFrom 11151 0 _FHW=true:=by decide+kernel
def _FHX:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae38000000000078787276a13e7ecaa4de99d545850eefe5746314d3d51180003
theorem shape15_28:validFrom 11150 0 _FHX=true:=by decide+kernel
def _FHY:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae340000000000787a1d618e22972a8fde99d545850ef05c632ca7f8510fa0003
theorem shape15_29:validFrom 11149 0 _FHY=true:=by decide+kernel
def _FIA:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae300000000000787bc8416572df4a7a5e99d545850ef0d4cafec910a10db0003
theorem shape15_30:validFrom 11148 0 _FIA=true:=by decide+kernel
def _FIB:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae2c0000000000787d7316272f598a645e99d545850ef14eabd9781c690bc0003
theorem shape15_31:validFrom 11147 0 _FIB=true:=by decide+kernel
def _FIC:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae280000000000787f1ddfd358038a4dde99d545850ef1c88b5560076509c0003
theorem shape15_32:validFrom 11146 0 _FIC=true:=by decide+kernel
def _FID:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae2400000000007880c89e69ecdfea375e99d545850ef2455e412afb2d07c0003
theorem shape15_33:validFrom 11145 0 _FID=true:=by decide+kernel
def _FIE:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae20000000000078827351eaedf1aa1fde99d545850ef2c3aa3583e3bd05c0003
theorem shape15_34:validFrom 11144 0 _FIE=true:=by decide+kernel
def _FIF:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae1c000000000078841dfa565b2a0a085e99d545850ef3436f326ac01103a0003
theorem shape15_35:validFrom 11143 0 _FIF=true:=by decide+kernel
def _FIG:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae1800000000007885c897ac349989f05e99d545850ef3c4ad37df8fd90190003
theorem shape15_36:validFrom 11142 0 _FIG=true:=by decide+kernel
def _FIH:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae14000000000078877329ec7a3809d85e99d545850ef4476445e254fcff70003
theorem shape15_37:validFrom 11141 0 _FIH=true:=by decide+kernel
def _FII:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae10000000000078891db1172c0989bf5e99d545850ef4cb945c730cc8fd40003
theorem shape15_38:validFrom 11140 0 _FII=true:=by decide+kernel
def _FIJ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae0c0000000000788ac82d2b2480c9a55e99d545850ef5513d7b91b9f8fb00003
theorem shape15_39:validFrom 11139 0 _FIJ=true:=by decide+kernel
def _FIL:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae080000000000788c729e2aaeb8c98b5e99d545850ef5d9da0a936fd8f8c0003
theorem shape15_40:validFrom 11138 0 _FIL=true:=by decide+kernel
def _FIM:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae040000000000788e1d0414a5264970de99d545850ef663efa246bd68f670003
theorem shape15_41:validFrom 11137 0 _FIM=true:=by decide+kernel
def _FIN:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae000000000000788fc75ee907b949555e99d545850ef6f0f8a9b971b8f420003
theorem shape15_42:validFrom 11136 0 _FIN=true:=by decide+kernel
def _FIO:List Piece:=DZ.decode 62 39 0x3782dace9d900000adfc0000000000789171aea7d688e9395e99d545850ef77f7ab9ba192cf1b0003
theorem shape15_43:validFrom 11135 0 _FIO=true:=by decide+kernel
def _FIP:List Piece:=DZ.decode 62 39 0x3782dace9d900000adf8000000000078931bf351117da91cde99d545850ef810f0399dcc24ef40003
theorem shape15_44:validFrom 11134 0 _FIP=true:=by decide+kernel
def _FIQ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7d5e99d545850f13c560e5791e591fde8d4a510000f129c32140d402908a00000000000f1298c59c97155d0385e99d545850efb52efe039f790ecc0005
theorem shape15_45:validFrom 11133 0 _FIQ=true:=by decide+kernel
def _FIR:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7c5e99d545850f34ab4ca817de591c1e8d4a510000f2ba650746dc02906300000000000f12ce0b6c5981b0de80004
theorem shape15_46:validFrom 11132 0 _FIR=true:=by decide+kernel
def _FIS:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b7b00000000000f36ada34169780118300000000000f36ad461f8dd80118000000000000f36ab56a8deb80117000000000000f36a96643c4700116000000000000f36a775deaa280115000000000000f36a58667fb080114000000000000f36a39602e0c00113000000000000f36a1a68c31a00112000000000000f369fb62717580111000000000000f369dc5c1fd100110000000000000f369bd64b4df0010f000000000000f3699e5e633a8010e000000000000f3697f66f8488010d000000000000f3696060a6a40010c000000000000f36941693bb20010b000000000000f3692262ea0d8010a000000000000f369035c986900109000000000000f368e4652d7700108000000000000f368c55edbd280107000000000000f368a66770e080106000000000000f36887611f3c00105000000000000f368685acd9780104000000000000f368609cf2db00103c00000000000f368496362a580103000000000000f3682a5d110100102000000000000f3680b65a60f00101000000000000f367ec5f546a80100000000000000f367cd67e978800ff000000000000f367ae6197d4000fe000000000000f3678f5b462f800fd000000000000f3677063db3d800fc000000000000f367515d8999000fb000000000000f36732661ea7000fa000000000000f367135fcd02800f9000000000000f366f4597b5e000f8000000000000f366d562106c000f7000000000000f366b65bbec7800f6000000000000f366976453d5800f5000000000000f366785e0231000f4000000000000f3665966973f000f3000000000000f3663a60459a800f2000000000000f3661b59f3f6000f1000000000000f35eb289d02a800f0000000000000f35e9a8e88e4800ef000000000000f35e82a22851000ee000000000000f35e6aa6e10b000ed000000000000f35e52ab99c5000ec000000000000f35e3ab0527f000eb000000000000f35e22c3f1eb800ea000000000000f35e0ac8aaa5800e9000000000000f35ef03d0b44800e8000000000000f35eb23f4eae000e7000000000000f35e74419217800e6000000000000f360dc714358800e5000000000000f3606075ca2b800e40e8d4a510000f35c83173540028e36e8d4a510000f2ba650746dc028e2500000000000f13034fd96972a0de7003b
theorem shape15_47:validFrom 11131 0 _FIS=true:=by decide+kernel
def _FIT:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b7a0000000000079b58c2f43a2c008a1000000000003cdac507af97c00450000000000001e6d5e3e7862700226000000000000f36acfc8c7c80011200000000000079b556d65997800888000000000003cdaa2e06df8e00440000000000001e6d4d2ad79300021e000000000000f36a472bc14c8010e00000000000079b51287d659c00868000000000003cda80b92c5a000430000000000001e6d3c1736c3900216000000000000f369be9da1838010a00000000000079b4ce39531c000848000000000003cda5e91eabb200420000000000001e6d2b0395f420020e000000000000f36951b58eee00106d0000000000079b49b004d84000830000000000003cda44f567ef200414000000000001e6d1e35548e200208000000000000f368cf7fa9258010300000000000079b456b1ca46400810000000000003cda22ce2650400404000000000001e6d0d21b3beb00200000000000000f36846f1895c800ff00000000000079b4126347088007f0000000000003cda00a6e4b16003f4000000000001e6cfc0e12ef4001f8000000000000f367be5482e1000fb00000000000079b3ce14c3cac007d0000000000003cd9de7fa3128003e4000000000001e6ceafc4ef62001f0000000000000f36735b77c65800f700000000000079b389c6408d0007b0000000000003cd9bc586173a003d4000000000001e6cd9e8ae26b001e8000000000000f366ad1a75ea000f300000000000079b34577bd4f400790000000000003cd99a34d9816003c4000000000001e6bf72934f3f001e0000000000000f35fab8cfb11800ef00000000000079afcee82741c00770000000000003cd7e017146ca003b4000000000001e6bec5ee7728001d8000000000000f35f45922575800eb00000000000079af940f1452400750000000000003cd7c2ae44a18003a4000000000001e6bddaa7f8cf001d0000000000000f35ecfeee649000e700000000000079af593d74bc000730000000000003cd7b803a15b600394000000000001e6bd378eeb12001c8000000000000f35e5b66c65c000e30746a528800079ae478b9ea0018716f46a52880003caeca5c72590123896200140000c1e574e20e9db8061bd200000000000f133892e3c6eb38de70039
theorem shape15_48:validFrom 11130 0 _FIT=true:=by decide+kernel
def _FIU:List Piece:=DZ.decode 62 41 0x3782dace9d900000ade400000000001e6d67601704a00220000000000000f36b15b113328010f00000000000079b57830b720000870000000000003cdab2c47253600434000000000001e6d54ba2161b00218000000000000f36a8081661b0010b00000000000079b52d98e094400850000000000003cda8d78870d800424000000000001e6d42124ee8700210000000000000f369eb42d2510010700000000000079b4e2f996af400830000000000003cda682c9bc7a00414000000000001e6d2f6c5945800208000000000000f369561325398010300000000000079b49861c023800810000000000003cda42dcf6d5200404000000000001e6d1cc486cc400200000000000000f368c0d4916f800ff00000000000079b44dc9e997c007f0000000000003cda1d910b8f4003f4000000000001e6d0a1e91295001f8000000000000f3682ba4e458000fb00000000000079b4032a9fb2c007d0000000000003cd9f841669cc003e4000000000001e6cf776beb01001f0000000000000f36796753740800f700000000000079b3b892c9270007b0000000000003cd9d2f57b56e003d4000000000001e6ce4d0c90d2001e8000000000000f3670136a376800f300000000000079b36df37f4200079022fb990e8003cd9ae3ad95d6003c4800000000001e6cd6d2eb323001e2000000000000f36095c740dd800f000000000000079b044054a27c00778000000000003cd81e9379f06003b8000000000001e6c0d9227667001da000000000000f3605ed48ea5800ec00000000000079b0288bf10bc00758000000000003cd80b8e859b8003a8000000000001e6c016b89589001d2000000000000f35fe87e7f1b000e800000000000079afe2d059b8c00738000000000003cd7e8b4739ea00398000000000001e6beee8f79d9001ca000000000000f35f2711f017800e400000000000079af6506f0ee400718746a52880003cd734c5d95001238aba3529440001e5756a0eedb8091c4a00000000000f136dd48b71e864de70033
theorem shape15_49:validFrom 11129 0 _FIU=true:=by decide+kernel
def _FIW:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b78000000000003cdacfbd7fe3c0042f000000000000f36b20a27e488010b0000000000003cdabe0b8bebc00428000000000000f36acfb9e115801090000000000003cdaa9d1649f000420000000000000f36a7ed143e2801070000000000003cda95973d52400418000000000000f36a2de8a6af801050000000000003cda815d1605800410000000000000f369dd00097c801030000000000003cda6d22eeb8c00408000000000000f3698c176c49801010000000000003cda58e8c76c000400000000000000f3693b2ecf16800ff0000000000003cda44aea01f4003f8000000000000f368ea4631e3800fd0000000000003cda307478d28003f0000000000000f368995d94b0800fb0000000000003cda1c3a5185c003e8000000000000f3684874f77d800f90000000000003cda08002a390003e0000000000000f367f78c5a4a800f70000000000003cd9f3c602ec4003d8000000000000f367a6a3bd17800f50000000000003cd9df8bdb9f8003d0000000000000f36755bb1fe4800f30000000000003cd9cb51b452c003c8000000000000f367168476a9800f1711b1f3f80003cd9c134a0ac6003c4400000000000f3670251c2b6000f0f000000000003cd85b36c2d0c003c0000000000000f3615f1e5eb5000ef0000000000003cd854586c89c003b8000000000000f36143a50599000ed0000000000003cd84d7a1642c003b0000000000000f361282bac7d000eb0000000000003cd8469bbffbc003a8000000000000f3610cb25361000e90000000000003cd83916f48b2003a0000000000000f360bc1437aa800e70000000000003cd824f3274a200398000000000000f3604cd81931000e50000000000003cd7fc03e970000390000000000000f35f89ca4ea7800e30746a52880003cd74dc5e75001838afa3529440000f2bc85dc9bec078e25840048000183caec641ebb701837a400000000000f13a314d06a6d38de70031
theorem shape15_50:validFrom 11128 0 _FIW=true:=by decide+kernel
def _FIX:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b77000000000003cdac819b8dfa0041d400000000000f36b12c80455801070000000000003cdab9c80958a00418000000000000f36abb872d22001050000000000003cdaa3fb8d38600410000000000000f36a64553ca1001030000000000003cda8e2f1118200408000000000000f36a0d234c20001010000000000003cda786294f7e00400000000000000f369b5e274ec800ff0000000000003cda62925f2b0003f8000000000000f3695eb0846b800fd0000000000003cda4cc5e30ac003f0000000000000f369077e93ea800fb0000000000003cda36f966ea8003e8000000000000f368b04ca369800f90000000000003cda212ceaca4003e0000000000000f368590bcc36000f70000000000003cda0b5cb4fd6003d8000000000000f36801d9dbb5000f50000000000003cd9f59038dd2003d0000000000000f367aaa7eb34000f30000000000003cd9dfc3bcbce003c8000000000000f3675375fab3000f10000000000003cd883b284c38003c0000000000000f362010d6680000ef0000000000003cd87cd42e7c8003b8000000000000f361e5940d64000ed0000000000003cd875f5d8358003b0000000000000f361ca1ab448000eb0000000000003cd86f1781ee8003a8000000000000f361b9ce610c000e9d000000000003cd86ba856cb0003a4000000000000f361a0e4ae9e000e80000000000003cd864ca008400039c000000000000f361856b5582000e60000000000003cd848feb292400394000000000000f360ba90c989800e40000000000003cd811b651d7e0038c3a3529440000f35dbb17e540078e28e8d4a5100003caee741fdb701e389400000000000f13d853b2b076a0de7002b
theorem shape15_51:validFrom 11127 0 _FIX=true:=by decide+kernel
def _FIY:List Piece:=DZ.decode 62 42 0x3782dace9d900000add800000000000f36ae05f9c8080102c000000000003cdaaf518d83400408000000000000f36a8e889425801010000000000003cda97f2bc8f800400000000000000f36a310d5056800ff0000000000003cda809031ef2003f8000000000000f369d38325d5000fd0000000000003cda693160fb6003f0000000000000f3697607e206000fb0000000000003cda51ced65b0003e8000000000000f369187db784800f90000000000003cda3a7005674003e0000000000000f368baf38d03000f70000000000003cda230d7ac6e003d8000000000000f3685d784934000f50000000000003cda0baea9d32003d0000000000000f367ffee1eb2800f30000000000003cd9f44c1f32c003c8000000000000f367a272dae3800f10000000000003cd89490214be003c0000000000000f362415f2efa800ef0000000000003cd88c1f76316003b8000000000000f3621f9c8290800ed0000000000003cd883aecb16e003b0000000000000f361fdd9d626800eb0000000000003cd87c4a58896003a9000000000000f361ecf87ff1800ea0000000000003cd87705ca6f2003a4000000000000f361cb26ecd5000e80000000000003cd86e9165a800039c000000000000f361a964406b000e60000000000003cd851fced4c800394000000000000f36113374179000e40000000000003cd8350f0cc200038c3a3529440000f35e5f183d40090e28e8d4a5100003caf104213b7024389400000000000f140d913244072cde70026
theorem shape15_52:validFrom 11126 0 _FIY=true:=by decide+kernel
def _FIZ:List Piece:=DZ.decode 62 43 0x6f05b59d3b2000015ba800000000000f36a7aa061ae800fe0000000000001e6d4917c2c40001fa0000000000003cda85b338f7c003f000000000000079b4f2754c284007d8000000000000f369b2f9660f800fa0000000000001e6d3022e3502001f20000000000003cda53cd33bca003e000000000000079b48ea1ce58c007b8000000000000f368eb615123000f60000000000001e6d172e03dc4001ea0000000000003cda21e374d4e003d000000000000079b42ad5c3e2800798000000000000f36823ba5584000f20000000000001e6cfe3b013eb001e20000000000003cd8a58b8b394003c000000000000079b1410ca32b400778000000000000f3626e13467a800ee0000000000001e6c4b41a8d3d001da0000000000003cd89181d1b0a003b000000000000079b118f9301a000758000000000000f3622cf0e03d000eac000000000001e6c43bd8c0b0001d40000000000003cd88279981f0003a400000000000079b0fae8bcf6c00740000000000000f361e1cb7a11800e70000000000001e6c39b8af46b001cc0000000000003cd85b153bbf20039400000000000079b09bea0b06c00720000000000000f36126e3d926000e30746a52880001e6be46314a80151c515d3ef7980003cafd192099d0303895d1a94a20000795e82845b6e0546f4800000000000f1442cd4f251e68de70022
theorem shape15_53:validFrom 11125 0 _FIZ=true:=by decide+kernel
def _FJA:List Piece:=DZ.decode 62 43 0x1bc16d674ec8000056e8000000000003cda7c2ee1f70003e480000000000079b4f50c662f8007c8000000000000f369b502f077000f80000000000001e6d2fff7f683001ee0000000000003cda52b987d66003d800000000000079b48aef95120007a8000000000000f368e0c94e3c000f40000000000001e6d15784b20d001e60000000000003cda1dab1f47a003c800000000000079b420d2c3f4800788000000000000f362da753cc9800f00000000000001e6c586775928001de0000000000003cd8ab0440c44003b800000000000079b14a6bb96dc00768000000000000f3627dacc958800ec0000000000001e6c4cd043fab001d60000000000003cd893d223e80003a800000000000079b11c0ef30e800748000000000000f36220e455e7800e80000000000001e6c4137358c9001ce0000000000003cd87ca3c0b860039800000000000079b0c88f3bd4400728000000000000f3615cca52d1000e40000000000001e6c2916ad885001c61419c4f027403cd801c64750030389eba7def30000795ef484976e060712800000000000f1478080953ba24de7001c
theorem shape15_54:validFrom 11124 0 _FJA=true:=by decide+kernel
def _FJB:List Piece:=DZ.decode 62 43 0x1bc16d674ec8000056e6000000000003cda505e08992003d080000000000079b49d368c030007a0000000000000f36902329277000f30000000000001e6d1940de735001e40000000000003cda24731b82e003c400000000000079b18f8ada6e800780000000000000f36304c661b3000ef0000000000001e6c5d4d04fad001dc0000000000003cd8b406352b2003b400000000000079b15add4d68000760000000000000f3629b6b47a6000eb0000000000001e6c5021a1b93001d40000000000003cd899abb4fb4003a400000000000079b12a4a4889c00742800000000000f3624c5f80c3000e80000000000001e6c464028dcd001ce0000000000003cd885ec7cef20039800000000000079b0db20b441c00728000000000000f3618219f7c3800e40000000000001e6c2d5de9c81001c605fd5a9007283cd842c66950036389eba7def30000795f7684db6e06c712800000000000f14ad4160cfdda0de70018
theorem shape15_55:validFrom 11123 0 _FJB=true:=by decide+kernel
def _FJC:List Piece:=DZ.decode 62 43 0xde0b6b3a76400002b72000000000001e6c685ff7227001ddc000000000003cd8ca49e6df6003b800000000000079b185d9cf56400768000000000000f362ee30bb29000ec0000000000001e6c5a15baf4b001d60000000000003cd8acce76b52003a800000000000079b14adb7ba8800748000000000000f36288cae886000e89000000000001e6c4f068279b001d00000000000003cd896b005bf20039c00000000000079b11e9e99bc800730000000000000f361dbcca840000e50000000000001e6c34fc1a494001c80000000000003cd86360a61b60038c2ba7def3000079600885276e078712800000000000f14e27955998598de70011
theorem shape15_56:validFrom 11122 0 _FJC=true:=by decide+kernel
def _FJD:List Piece:=DZ.decode 62 43 0xde0b6b3a76400002b71000000000001e6c5aae779a5001d30000000000003cd8b14620b90003a400000000000079b15f7df1d6c00746800000000000f362a470f5b9800e80000000000001e6c507b09e83001ce0000000000003cd898cc3085c0039800000000000079b100e01b6f000728000000000000f361ce0114ff800e40000000000001e6c360fc62f8001c61d1a94a200003cb122ad3e3f0483896c80170000307960aa857b6e0846f4800000000000f1517afe7b0b554de7000d
theorem shape15_57:validFrom 11121 0 _FJD=true:=by decide+kernel
def _FJE:List Piece:=DZ.decode 62 43 0xde0b6b3a76400002b70000000000001e6c3e9134d2d001c7e000000000003cd874f8865b00038c3a352944000079615c85d76e090712800000000000f154ce51715698cde70005
theorem shape15_58:validFrom 11120 0 _FJE=true:=by decide+kernel
def _FJF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056de0f158218e3c7a58cde20002
theorem shape15_59:validFrom 11119 0 _FJF=true:=by decide+kernel
def _FJH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056dc0f15b74b4dc76720d830002
theorem shape15_60:validFrom 11118 0 _FJH=true:=by decide+kernel
def _FJI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056da0f15ec7c5514ada8d210002
theorem shape15_61:validFrom 11117 0 _FJI=true:=by decide+kernel
def _FJJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d80f1621abf9af7c0ccbb0002
theorem shape15_62:validFrom 11116 0 _FJJ=true:=by decide+kernel
def _FJK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d60f1656da3b97ced0c530002
theorem shape15_63:validFrom 11115 0 _FJK=true:=by decide+kernel
def _FJL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d40f168c071acda974be70002
theorem shape15_64:validFrom 11114 0 _FJL=true:=by decide+kernel
def _FJM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d20f16c132975109b0b780002
theorem shape15_65:validFrom 11113 0 _FJM=true:=by decide+kernel
def _FJN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d00f16f65cb121ef58b060002
theorem shape15_66:validFrom 11112 0 _FJN=true:=by decide+kernel
def _FJO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ce0f172b8568405bd4a910002
theorem shape15_67:validFrom 11111 0 _FJO=true:=by decide+kernel
def _FJP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056cc0f1760acbcac4d28a180002
theorem shape15_68:validFrom 11110 0 _FJP=true:=by decide+kernel
def _FJQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ca0f1795d2ae65c67499c0002
theorem shape15_69:validFrom 11109 0 _FJQ=true:=by decide+kernel
def _FJS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c80f17caf73d6cc40491c0002
theorem shape15_70:validFrom 11108 0 _FJS=true:=by decide+kernel
def _FJT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c60f18001a69c1499089a0002
theorem shape15_71:validFrom 11107 0 _FJT=true:=by decide+kernel
def _FJU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c40f18353c336354b48140002
theorem shape15_72:validFrom 11106 0 _FJU=true:=by decide+kernel
def _FJV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c20f186a5c9a52e52478a0002
theorem shape15_73:validFrom 11105 0 _FJV=true:=by decide+kernel
def _FJW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c00f189f7b9e8ffc8c6fe0002
theorem shape15_74:validFrom 11104 0 _FJW=true:=by decide+kernel
def _FJX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056be0f18d499401a98ac66d0002
theorem shape15_75:validFrom 11103 0 _FJX=true:=by decide+kernel
def _FJY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056bc0f19091e384dfa1c5da0002
theorem shape15_76:validFrom 11102 0 _FJY=true:=by decide+kernel
def _FJZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ba0f193aabe31ff5085430002
theorem shape15_77:validFrom 11101 0 _FJZ=true:=by decide+kernel
def _FKA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f196c38460cd3bc4a80002
theorem shape15_78:validFrom 11100 0 _FKA=true:=by decide+kernel
def _FKB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f199dc3615dd25840b0002
theorem shape15_79:validFrom 11099 0 _FKB=true:=by decide+kernel
def _FKD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f19cf4d34c9b6543690002
theorem shape15_80:validFrom 11098 0 _FKD=true:=by decide+kernel
def _FKE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f1a00d5c099b89c2c40002
theorem shape15_81:validFrom 11097 0 _FKE=true:=by decide+kernel
def _FKF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b00f1a325d0484a15821b0002
theorem shape15_82:validFrom 11096 0 _FKF=true:=by decide+kernel
def _FKG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ae0f1a63e300d3a74c16f0002
theorem shape15_83:validFrom 11095 0 _FKG=true:=by decide+kernel
def _FKH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ac0f1a9567b53d96500c00002
theorem shape15_84:validFrom 11094 0 _FKH=true:=by decide+kernel
def _FKI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056aa0f1ac6eb220b9e6800e0002
theorem shape15_85:validFrom 11093 0 _FKI=true:=by decide+kernel
def _FKJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad533bc1cb34bd2db740f1af86d46f492300020002
theorem shape15_86:validFrom 11092 0 _FKJ=true:=by decide+kernel
def _FKK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4f3bc10531488be3d0f1b29ee241d070c0020002
theorem shape15_87:validFrom 11091 0 _FKK=true:=by decide+kernel
def _FKL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4b3bc03f32f259a610f1b5b6db9a9967c0020002
theorem shape15_88:validFrom 11090 0 _FKL=true:=by decide+kernel
def _FKM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473bbf7939bbbbb910f1b8cec075111bc0020002
theorem shape15_89:validFrom 11089 0 _FKM=true:=by decide+kernel
def _FKO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433bbeb345a38d7320f1bbe690d5ca3380020002
theorem shape15_90:validFrom 11088 0 _FKO=true:=by decide+kernel
def _FKP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3bbded56aaf37550f1befe4cb8322ac0020002
theorem shape15_91:validFrom 11087 0 _FKP=true:=by decide+kernel
def _FKQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3bbd276cd0c920d0f1c215f420db7cc0020002
theorem shape15_92:validFrom 11086 0 _FKQ=true:=by decide+kernel
def _FKR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373bbc618816330db0f1c52d870b33c940020002
theorem shape15_93:validFrom 11085 0 _FKR=true:=by decide+kernel
def _FKS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333bbb9ba87a0caa90f1c845057bcd55c0020002
theorem shape15_94:validFrom 11084 0 _FKS=true:=by decide+kernel
def _FKT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3bbad5cdfd7a8470f1cb5c6f6e15ee40020002
theorem shape15_95:validFrom 11083 0 _FKT=true:=by decide+kernel
def _FKU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3bba0ff89f580bc0f1ce73c4e69fd100020002
theorem shape15_96:validFrom 11082 0 _FKU=true:=by decide+kernel
def _FKV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273bb94a2860c9d970f1d18b05e0d89a40020002
theorem shape15_97:validFrom 11081 0 _FKV=true:=by decide+kernel
def _FKW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233bb8845d40ab5220f1d4a2326152b780020002
theorem shape15_98:validFrom 11080 0 _FKW=true:=by decide+kernel
def _FKX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3bb7be9740210cd0f1d7b94a637bccc0020002
theorem shape15_99:validFrom 11079 0 _FKX=true:=by decide+kernel
def _FHC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3bb6f8d65e0676c0f1dad04debe62500020002
theorem shape15_100:validFrom 11078 0 _FHC=true:=by decide+kernel
def _FHD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bb6331a9b801e90f1dde73cf5ff85c0020002
theorem shape15_101:validFrom 11077 0 _FHD=true:=by decide+kernel
def _FHE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bb56d63f76979c0f1e0fe17865a1900020002
theorem shape15_102:validFrom 11076 0 _FHE=true:=by decide+kernel
def row15 (v:ℕ):List Piece:=match v with
 | 0=>_FGZ
 | 1=>_FHA
 | 2=>_FHO
 | 3=>_FHZ
 | 4=>_FIK
 | 5=>_FIV
 | 6=>_FJG
 | 7=>_FJR
 | 8=>_FKC
 | 9=>_FKN
 | 10=>_FHB
 | 11=>_FHF
 | 12=>_FHG
 | 13=>_FHH
 | 14=>_FHI
 | 15=>_FHJ
 | 16=>_FHK
 | 17=>_FHL
 | 18=>_FHM
 | 19=>_FHN
 | 20=>_FHP
 | 21=>_FHQ
 | 22=>_FHR
 | 23=>_FHS
 | 24=>_FHT
 | 25=>_FHU
 | 26=>_FHV
 | 27=>_FHW
 | 28=>_FHX
 | 29=>_FHY
 | 30=>_FIA
 | 31=>_FIB
 | 32=>_FIC
 | 33=>_FID
 | 34=>_FIE
 | 35=>_FIF
 | 36=>_FIG
 | 37=>_FIH
 | 38=>_FII
 | 39=>_FIJ
 | 40=>_FIL
 | 41=>_FIM
 | 42=>_FIN
 | 43=>_FIO
 | 44=>_FIP
 | 45=>_FIQ
 | 46=>_FIR
 | 47=>_FIS
 | 48=>_FIT
 | 49=>_FIU
 | 50=>_FIW
 | 51=>_FIX
 | 52=>_FIY
 | 53=>_FIZ
 | 54=>_FJA
 | 55=>_FJB
 | 56=>_FJC
 | 57=>_FJD
 | 58=>_FJE
 | 59=>_FJF
 | 60=>_FJH
 | 61=>_FJI
 | 62=>_FJJ
 | 63=>_FJK
 | 64=>_FJL
 | 65=>_FJM
 | 66=>_FJN
 | 67=>_FJO
 | 68=>_FJP
 | 69=>_FJQ
 | 70=>_FJS
 | 71=>_FJT
 | 72=>_FJU
 | 73=>_FJV
 | 74=>_FJW
 | 75=>_FJX
 | 76=>_FJY
 | 77=>_FJZ
 | 78=>_FKA
 | 79=>_FKB
 | 80=>_FKD
 | 81=>_FKE
 | 82=>_FKF
 | 83=>_FKG
 | 84=>_FKH
 | 85=>_FKI
 | 86=>_FKJ
 | 87=>_FKK
 | 88=>_FKL
 | 89=>_FKM
 | 90=>_FKO
 | 91=>_FKP
 | 92=>_FKQ
 | 93=>_FKR
 | 94=>_FKS
 | 95=>_FKT
 | 96=>_FKU
 | 97=>_FKV
 | 98=>_FKW
 | 99=>_FKX
 | 100=>_FHC
 | 101=>_FHD
 | 102=>_FHE
 | _=>[]
theorem checked15 (v:ℕ) (hy:15+v≤117):validFrom (11193-15-v) 0 (row15 v)=true:=by
 have hv:v≤102:=by omega
 interval_cases v
 · exact shape15_0
 · exact shape15_1
 · exact shape15_2
 · exact shape15_3
 · exact shape15_4
 · exact shape15_5
 · exact shape15_6
 · exact shape15_7
 · exact shape15_8
 · exact shape15_9
 · exact shape15_10
 · exact shape15_11
 · exact shape15_12
 · exact shape15_13
 · exact shape15_14
 · exact shape15_15
 · exact shape15_16
 · exact shape15_17
 · exact shape15_18
 · exact shape15_19
 · exact shape15_20
 · exact shape15_21
 · exact shape15_22
 · exact shape15_23
 · exact shape15_24
 · exact shape15_25
 · exact shape15_26
 · exact shape15_27
 · exact shape15_28
 · exact shape15_29
 · exact shape15_30
 · exact shape15_31
 · exact shape15_32
 · exact shape15_33
 · exact shape15_34
 · exact shape15_35
 · exact shape15_36
 · exact shape15_37
 · exact shape15_38
 · exact shape15_39
 · exact shape15_40
 · exact shape15_41
 · exact shape15_42
 · exact shape15_43
 · exact shape15_44
 · exact shape15_45
 · exact shape15_46
 · exact shape15_47
 · exact shape15_48
 · exact shape15_49
 · exact shape15_50
 · exact shape15_51
 · exact shape15_52
 · exact shape15_53
 · exact shape15_54
 · exact shape15_55
 · exact shape15_56
 · exact shape15_57
 · exact shape15_58
 · exact shape15_59
 · exact shape15_60
 · exact shape15_61
 · exact shape15_62
 · exact shape15_63
 · exact shape15_64
 · exact shape15_65
 · exact shape15_66
 · exact shape15_67
 · exact shape15_68
 · exact shape15_69
 · exact shape15_70
 · exact shape15_71
 · exact shape15_72
 · exact shape15_73
 · exact shape15_74
 · exact shape15_75
 · exact shape15_76
 · exact shape15_77
 · exact shape15_78
 · exact shape15_79
 · exact shape15_80
 · exact shape15_81
 · exact shape15_82
 · exact shape15_83
 · exact shape15_84
 · exact shape15_85
 · exact shape15_86
 · exact shape15_87
 · exact shape15_88
 · exact shape15_89
 · exact shape15_90
 · exact shape15_91
 · exact shape15_92
 · exact shape15_93
 · exact shape15_94
 · exact shape15_95
 · exact shape15_96
 · exact shape15_97
 · exact shape15_98
 · exact shape15_99
 · exact shape15_100
 · exact shape15_101
 · exact shape15_102
def _FKY:List Piece:=DZ.decode 62 41 0x3782dace9d900000aea549095480821dbf401d63e0db44f177a8eab16310e6bbc81c069abd13980003
theorem shape16_0:validFrom 11177 0 _FKY=true:=by decide+kernel
def _FKZ:List Piece:=DZ.decode 62 41 0x3782dace9d900000aea149095480821dc1819acd346974df97a8eab16310e6d9b8a04c545a53780003
theorem shape16_1:validFrom 11176 0 _FKZ=true:=by decide+kernel
def _FLM:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9d49095480821dc3bdf41135f59ccd57a8eab16310e6f7a924920df793570003
theorem shape16_2:validFrom 11175 0 _FLM=true:=by decide+kernel
def _FLX:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9949095480821dc5ff717a8983ccbad7a8eab16310e71599a8d7c794d3370003
theorem shape16_3:validFrom 11174 0 _FLX=true:=by decide+kernel
def _FMI:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9549095480821dc840eee3dd11fca817a8eab16310e7338a2d1d813213170003
theorem shape16_4:validFrom 11173 0 _FMI=true:=by decide+kernel
def _FMT:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9149095480821dca7d4827de9e2494f7a8eab16310e7517ab1633acf52f60003
theorem shape16_5:validFrom 11172 0 _FMT=true:=by decide+kernel
def _FNE:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8d49095480821dccbec591322c548177a8eab16310e76f6b35a8f46c92d60003
theorem shape16_6:validFrom 11171 0 _FNE=true:=by decide+kernel
def _FNP:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8949095480821dcf0042fa85ba846db7a8eab16310e78d5bb9eeae09d2b60003
theorem shape16_7:validFrom 11170 0 _FNP=true:=by decide+kernel
def _FOA:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8549095480821dd141c063d948b45977a8eab16310e7ab4c3e3467a712960003
theorem shape16_8:validFrom 11169 0 _FOA=true:=by decide+kernel
def _FOL:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8149095480821dd37e19a7dad4dc44f7a8eab16310e7c93cc27a214452750003
theorem shape16_9:validFrom 11168 0 _FOL=true:=by decide+kernel
def _FLA:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7d49095480821dd5bf97112e630c3017a8eab16310e7e72d46bfdae192550003
theorem shape16_10:validFrom 11167 0 _FLA=true:=by decide+kernel
def _FLD:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7949095480821dd801147a81f13c1ad7a8eab16310e8051dcb05947ed2350003
theorem shape16_11:validFrom 11166 0 _FLD=true:=by decide+kernel
def _FLE:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7549095480821dda3d6dbe837d640537a8eab16310e8230e4f4b4e1c12140003
theorem shape16_12:validFrom 11165 0 _FLE=true:=by decide+kernel
def _FLF:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7149095480821ddc7eeb27d70b93ef17a8eab16310e840fed39107b951f40003
theorem shape16_13:validFrom 11164 0 _FLF=true:=by decide+kernel
def _FLG:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6d49095480821ddec068912a99c3d897a8eab16310e85eef57d6c15691d40003
theorem shape16_14:validFrom 11163 0 _FLG=true:=by decide+kernel
def _FLH:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6949095480821dd753d7b61654e3c1b7a8eab16310e8e18c62cc75e48fd20003
theorem shape16_15:validFrom 11162 0 _FLH=true:=by decide+kernel
def _FLI:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6549095480821dd971581a2bd4dbaa57a8eab16310e900dbc0784f8a0fab0003
theorem shape16_16:validFrom 11161 0 _FLI=true:=by decide+kernel
def _FLJ:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6149095480821ddb8ed87e4154d39297a8eab16310e9202b1e24292f8f840003
theorem shape16_17:validFrom 11160 0 _FLJ=true:=by decide+kernel
def _FLK:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae5d49095480821ddd13852586896b7a57a8eab16310e94c82bda6296ecf2d0003
theorem shape16_18:validFrom 11159 0 _FLK=true:=by decide+kernel
def _FLL:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b96a484aa40410ec8f9fe6dc8c299b0c0002
theorem shape16_19:validFrom 11158 0 _FLL=true:=by decide+kernel
def _FLN:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b95a484aa40410eca6cff7792aa31a430002
theorem shape16_20:validFrom 11157 0 _FLN=true:=by decide+kernel
def _FLO:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b94a484aa40410ecf0c755c9bf1919750002
theorem shape16_21:validFrom 11156 0 _FLO=true:=by decide+kernel
def _FLP:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9300000000000f0ef29fcbd5f6095565e99d545850f068bf5caeb739d127bd33aa8b090ed9101b2a0a80d0f630004
theorem shape16_22:validFrom 11155 0 _FLP=true:=by decide+kernel
def _FLQ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9200000000000f0f2712a41f054952e5e99d545850f06a1e5c2cf3a2d10abd33aa8b090ed9e59b61d24f4cf220004
theorem shape16_23:validFrom 11154 0 _FLQ=true:=by decide+kernel
def _FLR:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9100000000000f0f5b841da0f28d5045e99d545850f06b94ec74eec350ecbd33aa8b090edabb1b999a1dc8ee20004
theorem shape16_24:validFrom 11153 0 _FLR=true:=by decide+kernel
def _FLS:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae400000000000787c7fa1c2dded4a6d5e99d545850ef12f9a65e5c3690ce0003
theorem shape16_25:validFrom 11152 0 _FLS=true:=by decide+kernel
def _FLT:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae3c0000000000787e2317a27b314a57de99d545850ef1a88f587af3250af0003
theorem shape16_26:validFrom 11151 0 _FLT=true:=by decide+kernel
def _FLU:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae380000000000787fc6828bdf69ea41de99d545850ef22182f056f7690900003
theorem shape16_27:validFrom 11150 0 _FLU=true:=by decide+kernel
def _FLV:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae340000000000788169e27f0a90ea2b5e99d545850ef29bef94ac46610710003
theorem shape16_28:validFrom 11149 0 _FLV=true:=by decide+kernel
def _FLW:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae30000000000078830d377bfca8aa14de99d545850ef3194facad5ad10510003
theorem shape16_29:validFrom 11148 0 _FLW=true:=by decide+kernel
def _FLY:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae2c00000000007884b08182b5ae69fdde99d545850ef396ae69f5410d0310003
theorem shape16_30:validFrom 11147 0 _FLY=true:=by decide+kernel
def _FLZ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae280000000000788653c093359f49e65e99d545850ef4158633b673690100003
theorem shape16_31:validFrom 11146 0 _FLZ=true:=by decide+kernel
def _FMA:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae2400000000007887f6f4ad7c89c9cede99d545850ef495d709ce55f4fef0003
theorem shape16_32:validFrom 11145 0 _FMA=true:=by decide+kernel
def _FMB:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae20000000000078899a1dd18a5969b65e99d545850ef5191b53d734e4fcd0003
theorem shape16_33:validFrom 11144 0 _FMB=true:=by decide+kernel
def _FMC:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae1c0000000000788b3d3bff5f1ea99d5e99d545850ef59dd8aa595f38faa0003
theorem shape16_34:validFrom 11143 0 _FMC=true:=by decide+kernel
def _FMD:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae180000000000788ce04f36fad16983de99d545850ef62294a5ffc028f870003
theorem shape16_35:validFrom 11142 0 _FMD=true:=by decide+kernel
def _FME:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae140000000000788e8357785d6f2969de99d545850ef6aa441551e858f640003
theorem shape16_36:validFrom 11141 0 _FME=true:=by decide+kernel
def _FMF:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae10000000000078902654c38707294f5e99d545850ef734e6f8950b60f3f0003
theorem shape16_37:validFrom 11140 0 _FMF=true:=by decide+kernel
def _FMG:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae0c00000000007891c947187783c9345e99d545850ef7bf8880fc6438f1a0003
theorem shape16_38:validFrom 11139 0 _FMG=true:=by decide+kernel
def _FMH:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae08000000000078936c2e772efae918de99d545850ef84d1d7d0f86a8ef40003
theorem shape16_39:validFrom 11138 0 _FMH=true:=by decide+kernel
def _FMJ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae04000000000078950f0adfad5648fc5e99d545850ef8dda5ed13a34cece0003
theorem shape16_40:validFrom 11137 0 _FMJ=true:=by decide+kernel
def _FMK:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae0000000000007896b1dc530fbe88df5e99d545850ef96e2d023bf4d8ea60003
theorem shape16_41:validFrom 11136 0 _FMK=true:=by decide+kernel
def _FML:List Piece:=DZ.decode 62 39 0x3782dace9d900000adfc0000000000789854a2cf1bfb88c15e99d545850efa0321f26527a0e7e0003
theorem shape16_42:validFrom 11135 0 _FML=true:=by decide+kernel
def _FMM:List Piece:=DZ.decode 62 39 0x3782dace9d900000adf800000000007899f75e54ef2108a2de99d545850efa998fef2a3c18e550003
theorem shape16_43:validFrom 11134 0 _FMM=true:=by decide+kernel
def _FMN:List Piece:=DZ.decode 62 39 0x3782dace9d900000adf40000000000789b9a0ee4894168835e99d545850efb3176f8689d64e2a0003
theorem shape16_44:validFrom 11133 0 _FMN=true:=by decide+kernel
def _FMO:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b7c2f4ceaa2c2878a2e90d11e27f0862f46a52880003c4eaa128d4e0153dbc00000000001e274f2d1f7a9159eac5e99d545850efd8d00d80c9134dff0005
theorem shape16_45:validFrom 11132 0 _FMO=true:=by decide+kernel
def _FMP:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015bd97a675516143cd4a1c8837e09e420fa3529440001e575620eedb80a9e6c00000000000f13dbe9e42247a4de80004
theorem shape16_46:validFrom 11131 0 _FMP=true:=by decide+kernel
def _FMQ:List Piece:=DZ.decode 62 42 0x3782dace9d900000ade800000000000f36a800a308700103f000000000003cda94b3ff3020040c000000000000f36a228eecb8001020000000000003cda7c93772be00404000000000000f369c1fde5f4801000000000000003cda646f357b0003fc000000000000f369617bc5e3800fe0000000000003cda4c4ead76c003f4000000000000f36900f9a5d2800fc0000000000003cda342e25728003ec000000000000f368a0689f0f000fa0000000000003cda1c09e3c1a003e4000000000000f3683fe67efe000f80000000000003cda03e95bbd6003dc000000000000f367df645eed000f60000000000003cd9ebc51a0c8003d4000000000000f367a9159660800f4e000000000003cd9dfb4d60a6003d0000000000000f3674e924821000f30000000000003cd9c7944e062003c8000000000000f366ee102810000f10000000000003cd86848125a0003c0000000000000f36193639cda000ef0000000000003cd86169bc130003b8000000000000f36177ea43be000ed0000000000003cd85a8b65cc0003b0000000000000f3615c70eaa2000eb0000000000003cd853ad0f850003a8000000000000f36140f79186000e90000000000003cd84cceb93e0003a0000000000000f361257e386a000e70000000000003cd845f062f7000398000000000000f3610a04df4e000e50000000000003cd8223a8631400390000000000000f35ee9e4d144000e30746a52880003cd733c5d95001538aba3529440000f2bbb9dc2fec064e25746a52880003caeac41ddb701537a400000000000f14103bd9c024f8de70028
theorem shape16_47:validFrom 11130 0 _FMQ=true:=by decide+kernel
def _FMR:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b79000000000003cda94f70d536003fe400000000000f36a36ee54c3000ff0000000000003cda80de6d184003f8000000000000f369d013fab1800fd0000000000003cda672b90408003f0000000000000f3696939a0a0000fb0000000000003cda4d74f9bc2003e8000000000000f369026e2d41000f90000000000003cda33be6337c003e0000000000000f3689b93d32f800f70000000000003cda1a0b86600003d8000000000000f36834b9791e000f50000000000003cda0054efdba003d0000000000000f367cdee05bf000f30000000000003cd9e6a21303e003c8000000000000f3676713abad800f10000000000003cd879f292f8c003c0000000000000f361d6da0efb800ef0000000000003cd8717e2e31a003b8000000000000f361b5176291800ed0000000000003cd8690d83172003b003f5476a0000f3619460eeb4800eb2000000000003cd864d52d89e003ac000000000000f36182735ff2800ea0000000000003cd85c64826f6003a4000000000000f36160b0b388800e80000000000003cd853f01da840039c000000000000f3613edf206c000e60000000000003cd84b7f728dc00394000000000000f360abaa1709800e40000000000003cd7c2b971a760038c3a3529440000f35cef177940064e28e8d4a5100003caeb441e2b7019389400000000000f14448c7096dfc4de70023
theorem shape16_48:validFrom 11129 0 _FMR=true:=by decide+kernel
def _FMS:List Piece:=DZ.decode 62 42 0x3782dace9d900000ade000000000000f36a0231e10a000fb0000000000003cda72e9df6ce003e8000000000000f369950e33aa800f90000000000003cda57a0f4150003e0000000000000f36927ea864b000f70000000000003cda3c5808bd2003d8000000000000f368bac6d8eb800f50000000000003cda210f1d654003d0000000000000f3684da32b8c000f30000000000003cda05c6320d6003c8000000000000f367e07f7e2c800f10000000000003cd88bb36da34003c0000000000000f3621ac7b6b1000ef0000000000003cd881acb408a003b8000000000000f361f2acd046800ed0000000000003cd877a9b41aa003b0000000000000f361d5dcbd21000eb9000000000003cd872a83423a003ac000000000000f361b68bea00000ea0000000000003cd868a17a890003a4000000000000f3618e7fea48000e80000000000003cd85e9ac0ee60039c000000000000f361666503dd800e60000000000003cd85497c100600394000000000000f360cee14ae2000e40000000000003cd7d0637dd640038c3a3529440000f35d1a18c840c68e28e8d4a5100003caebf02367731a389400000000000f1478dba8a678fcde7001e
theorem shape16_49:validFrom 11128 0 _FMS=true:=by decide+kernel
def _FMU:List Piece:=DZ.decode 62 42 0x3782dace9d900000addc00000000000f3699092cffa000f66000000000003cda5ebae5260003d8000000000000f369413c879a800f50000000000003cda41dfa4faa003d0000000000000f368cdcf86ed000f30000000000003cda250464cf4003c8000000000000f3685a539f8d000f10000000000003cd89d8e5c062003c0000000000000f3625f0ec695800ef0000000000003cd891f54d980003b8000000000000f36230aa8cdd000ed015c508c70003cd886b961058003b0800000000000f3621970fca7800ec0000000000003cd8809194c92003ac000000000000f361eb1ba9a1800ea0000000000003cd874f8865b0003a4000000000000f361bcb76fe9000e80000000000003cd8695f77ece0039c000000000000f3618e533630800e60000000000003cd85dca232b600394000000000000f360f271e6e9800e40000000000003cd8016644ef40038c3a3529440000f35d9f99d3c13c8e28e8d4a5100003caee06279574f2389400000000000f14ad2981eeefa4de7001a
theorem shape16_50:validFrom 11127 0 _FMU=true:=by decide+kernel
def _FMV:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b76000000000003cda3ea85af48003c6800000000000f368d4900fcf000f10000000000003cd8d0c7619e2003c0000000000000f36324261b86800ef0000000000003cd8c147f2788003b8000000000000f362e6285ef0000ed0000000000003cd8b5a770b12003b2000000000000f362c7220d4b800ec0000000000003cd8aa06eee9c003ac000000000000f362892450b5000ea0000000000003cd89a877fc42003a4000000000000f3624b26941e800e80000000000003cd88b08109e80039c000000000000f3620d28d788000e60000000000003cd86aee1313c00394000000000000f361424e4b8f800e40000000000003cd83066f4fa00038c3a3529440000f35e4b1b22c1cf0e28e8d4a5100003caf0b42cd1773c389400000000000f14e175fc7043b0de70015
theorem shape16_51:validFrom 11126 0 _FMV=true:=by decide+kernel
def _FMW:List Piece:=DZ.decode 62 43 0x1bc16d674ec8000056ea000000000003cd8d0ced4f76003b2c0000000000079b194cf6888c00760000000000000f3630773d5c6000eb0000000000001e6c5caaf825a001d40000000000003cd8b0cb31786003a400000000000079b15080e54b000740000000000000f3627ee5b5fd000e70000000000001e6c4b9757563001cc0000000000003cd87ed28bde20039400000000000079b0cf1429ec400720000000000000f3617f30e8e6800e30746a52880001e6be39396a84fc1c515d3ef7980003cafd4d3651dd263895ef03ac01970795e7f46636f3f06f4800000000000f1515c1182a76b4de70010
theorem shape16_52:validFrom 11125 0 _FMW=true:=by decide+kernel
def _FMX:List Piece:=DZ.decode 62 43 0x6f05b59d3b2000015ba000000000000f362f75436a1800e7a000000000001e6c5a409235e001ce0000000000003cd8ab2d3b2f20039800000000000079b125a230c1c00728000000000000f361ee5e20ad800e40000000000001e6c398664ac4001c615d3ef7980003cd80507a2d0d26389eba7def30000795efb074e6fa4c712800000000000f154a0ad51d8720de7000a
theorem shape16_53:validFrom 11124 0 _FMX=true:=by decide+kernel
def _FMY:List Piece:=DZ.decode 62 43 0x1bc16d674ec8000056e75d3ef7980003cd84c6829310c6389eba7def30000795f89c85b3018c712800000000000f157e5333497608de70004
theorem shape16_54:validFrom 11123 0 _FMY=true:=by decide+kernel
def _FMZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e40f15b29a32ae424cdd10002
theorem shape16_55:validFrom 11122 0 _FMZ=true:=by decide+kernel
def _FNA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e20f15e6dfd34bed18d780002
theorem shape16_56:validFrom 11121 0 _FNA=true:=by decide+kernel
def _FNB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e00f161b2415227538d1c0002
theorem shape16_57:validFrom 11120 0 _FNB=true:=by decide+kernel
def _FNC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056de0f164f66f831dab8cbe0002
theorem shape16_58:validFrom 11119 0 _FNC=true:=by decide+kernel
def _FND:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056dc0f1683a87c7a1fd8c5c0002
theorem shape16_59:validFrom 11118 0 _FND=true:=by decide+kernel
def _FNF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056da0f16b7e8a1fb4134bf70002
theorem shape16_60:validFrom 11117 0 _FNF=true:=by decide+kernel
def _FNG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d80f16ec2768b541b0b900002
theorem shape16_61:validFrom 11116 0 _FNG=true:=by decide+kernel
def _FNH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d60f172064d0a81f6cb260002
theorem shape16_62:validFrom 11115 0 _FNH=true:=by decide+kernel
def _FNI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d40f1754a0d9d3da8cab80002
theorem shape16_63:validFrom 11114 0 _FNI=true:=by decide+kernel
def _FNJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d20f1788db84387560a460002
theorem shape16_64:validFrom 11113 0 _FNJ=true:=by decide+kernel
def _FNK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d00f17bd14cfd5ec589d30002
theorem shape16_65:validFrom 11112 0 _FNK=true:=by decide+kernel
def _FNL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ce0f17f14cbccfd8ec95c0002
theorem shape16_66:validFrom 11111 0 _FNL=true:=by decide+kernel
def _FNM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056cc0f1825834adf0b388e10002
theorem shape16_67:validFrom 11110 0 _FNM=true:=by decide+kernel
def _FNN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ca0f1859b87a271bf88620002
theorem shape16_68:validFrom 11109 0 _FNN=true:=by decide+kernel
def _FNO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c80f188dec4aa80b6c7e10002
theorem shape16_69:validFrom 11108 0 _FNO=true:=by decide+kernel
def _FNQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c60f18c21ebc61d77c75d0002
theorem shape16_70:validFrom 11107 0 _FNQ=true:=by decide+kernel
def _FNR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c40f18f64fcf5483586d50002
theorem shape16_71:validFrom 11106 0 _FNR=true:=by decide+kernel
def _FNS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c20f192a7f83800b4064a0002
theorem shape16_72:validFrom 11105 0 _FNS=true:=by decide+kernel
def _FNT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c00f195eadd8e4719c5bb0002
theorem shape16_73:validFrom 11104 0 _FNT=true:=by decide+kernel
def _FNU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056be0f1992dacf81b6c45290002
theorem shape16_74:validFrom 11103 0 _FNU=true:=by decide+kernel
def _FNV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056bc0f19c673b64577b04930002
theorem shape16_75:validFrom 11102 0 _FNV=true:=by decide+kernel
def _FNW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ba0f19f72c4b24a2e83fb0002
theorem shape16_76:validFrom 11101 0 _FNW=true:=by decide+kernel
def _FNX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f1a27e39b3a0dcc35e0002
theorem shape16_77:validFrom 11100 0 _FNX=true:=by decide+kernel
def _FNY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f1a5899a6ccdb782be0002
theorem shape16_78:validFrom 11099 0 _FNY=true:=by decide+kernel
def _FNZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f1a894e6d95ed5021b0002
theorem shape16_79:validFrom 11098 0 _FNZ=true:=by decide+kernel
def _FOB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f1aba01efdc5ed81740002
theorem shape16_80:validFrom 11097 0 _FOB=true:=by decide+kernel
def _FOC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b00f1aeab42d5915ac0ca0002
theorem shape16_81:validFrom 11096 0 _FOC=true:=by decide+kernel
def _FOD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ae0f1b1b6526532b1801c0002
theorem shape16_82:validFrom 11095 0 _FOD=true:=by decide+kernel
def _FOE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5b3bc07c966ef1eaa0f1b4c14da8385580020002
theorem shape16_83:validFrom 11094 0 _FOE=true:=by decide+kernel
def _FOF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad573bbfb9dcb03aff40f1b7cc34a3140300020002
theorem shape16_84:validFrom 11093 0 _FOF=true:=by decide+kernel
def _FOG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad533bbef72804ab0280f1bad7075153f600020002
theorem shape16_85:validFrom 11092 0 _FOG=true:=by decide+kernel
def _FOH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4f3bbe34786bb3b470f1bde1c5b5312e40020002
theorem shape16_86:validFrom 11091 0 _FOH=true:=by decide+kernel
def _FOI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4b3bbd71cde4c6f6e0f1c0ec6fd0e42480020002
theorem shape16_87:validFrom 11090 0 _FOI=true:=by decide+kernel
def _FOJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473bbcaf28710114f0f1c3f7059ffbac40020002
theorem shape16_88:validFrom 11089 0 _FOJ=true:=by decide+kernel
def _FOK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433bbbec880f45c7e0f1c7018726e8e080020002
theorem shape16_89:validFrom 11088 0 _FOK=true:=by decide+kernel
def _FOM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3bbb29ecc0b15ad0f1ca0bf4613a94c0020002
theorem shape16_90:validFrom 11087 0 _FOM=true:=by decide+kernel
def _FON:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3bba6756842777a0f1cd164d53622180020002
theorem shape16_91:validFrom 11086 0 _FON=true:=by decide+kernel
def _FOO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373bb9a4c55ac474a0f1d02091f8ee2d80020002
theorem shape16_92:validFrom 11085 0 _FOO=true:=by decide+kernel
def _FOP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333bb8e239436c01c0f1d32ac2564ff900020002
theorem shape16_93:validFrom 11084 0 _FOP=true:=by decide+kernel
def _FOQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3bb81fb23f3a6b00f1d634de67165400020002
theorem shape16_94:validFrom 11083 0 _FOQ=true:=by decide+kernel
def _FOR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3bb75d304d136f70f1d93ee62fb24240020002
theorem shape16_95:validFrom 11082 0 _FOR=true:=by decide+kernel
def _FOS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273bb69ab36e133df0f1dc48d9abb30840020002
theorem shape16_96:validFrom 11081 0 _FOS=true:=by decide+kernel
def _FOT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233bb5d83ba11db2e0f1df52b8df893480020002
theorem shape16_97:validFrom 11080 0 _FOT=true:=by decide+kernel
def _FOU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3bb515c8e74eed80f1e25c83c6c44a00020002
theorem shape16_98:validFrom 11079 0 _FOU=true:=by decide+kernel
def _FOV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3bb4535b3f8ad2e0f1e5663a65d4b480020002
theorem shape16_99:validFrom 11078 0 _FOV=true:=by decide+kernel
def _FLB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bb390f2aaed80d0f1e86fdcb849fcc0020002
theorem shape16_100:validFrom 11077 0 _FLB=true:=by decide+kernel
def _FLC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bb2ce8f285acf70f1eb796ac294c240020002
theorem shape16_101:validFrom 11076 0 _FLC=true:=by decide+kernel
def row16 (v:ℕ):List Piece:=match v with
 | 0=>_FKY
 | 1=>_FKZ
 | 2=>_FLM
 | 3=>_FLX
 | 4=>_FMI
 | 5=>_FMT
 | 6=>_FNE
 | 7=>_FNP
 | 8=>_FOA
 | 9=>_FOL
 | 10=>_FLA
 | 11=>_FLD
 | 12=>_FLE
 | 13=>_FLF
 | 14=>_FLG
 | 15=>_FLH
 | 16=>_FLI
 | 17=>_FLJ
 | 18=>_FLK
 | 19=>_FLL
 | 20=>_FLN
 | 21=>_FLO
 | 22=>_FLP
 | 23=>_FLQ
 | 24=>_FLR
 | 25=>_FLS
 | 26=>_FLT
 | 27=>_FLU
 | 28=>_FLV
 | 29=>_FLW
 | 30=>_FLY
 | 31=>_FLZ
 | 32=>_FMA
 | 33=>_FMB
 | 34=>_FMC
 | 35=>_FMD
 | 36=>_FME
 | 37=>_FMF
 | 38=>_FMG
 | 39=>_FMH
 | 40=>_FMJ
 | 41=>_FMK
 | 42=>_FML
 | 43=>_FMM
 | 44=>_FMN
 | 45=>_FMO
 | 46=>_FMP
 | 47=>_FMQ
 | 48=>_FMR
 | 49=>_FMS
 | 50=>_FMU
 | 51=>_FMV
 | 52=>_FMW
 | 53=>_FMX
 | 54=>_FMY
 | 55=>_FMZ
 | 56=>_FNA
 | 57=>_FNB
 | 58=>_FNC
 | 59=>_FND
 | 60=>_FNF
 | 61=>_FNG
 | 62=>_FNH
 | 63=>_FNI
 | 64=>_FNJ
 | 65=>_FNK
 | 66=>_FNL
 | 67=>_FNM
 | 68=>_FNN
 | 69=>_FNO
 | 70=>_FNQ
 | 71=>_FNR
 | 72=>_FNS
 | 73=>_FNT
 | 74=>_FNU
 | 75=>_FNV
 | 76=>_FNW
 | 77=>_FNX
 | 78=>_FNY
 | 79=>_FNZ
 | 80=>_FOB
 | 81=>_FOC
 | 82=>_FOD
 | 83=>_FOE
 | 84=>_FOF
 | 85=>_FOG
 | 86=>_FOH
 | 87=>_FOI
 | 88=>_FOJ
 | 89=>_FOK
 | 90=>_FOM
 | 91=>_FON
 | 92=>_FOO
 | 93=>_FOP
 | 94=>_FOQ
 | 95=>_FOR
 | 96=>_FOS
 | 97=>_FOT
 | 98=>_FOU
 | 99=>_FOV
 | 100=>_FLB
 | 101=>_FLC
 | _=>[]
theorem checked16 (v:ℕ) (hy:16+v≤117):validFrom (11193-16-v) 0 (row16 v)=true:=by
 have hv:v≤101:=by omega
 interval_cases v
 · exact shape16_0
 · exact shape16_1
 · exact shape16_2
 · exact shape16_3
 · exact shape16_4
 · exact shape16_5
 · exact shape16_6
 · exact shape16_7
 · exact shape16_8
 · exact shape16_9
 · exact shape16_10
 · exact shape16_11
 · exact shape16_12
 · exact shape16_13
 · exact shape16_14
 · exact shape16_15
 · exact shape16_16
 · exact shape16_17
 · exact shape16_18
 · exact shape16_19
 · exact shape16_20
 · exact shape16_21
 · exact shape16_22
 · exact shape16_23
 · exact shape16_24
 · exact shape16_25
 · exact shape16_26
 · exact shape16_27
 · exact shape16_28
 · exact shape16_29
 · exact shape16_30
 · exact shape16_31
 · exact shape16_32
 · exact shape16_33
 · exact shape16_34
 · exact shape16_35
 · exact shape16_36
 · exact shape16_37
 · exact shape16_38
 · exact shape16_39
 · exact shape16_40
 · exact shape16_41
 · exact shape16_42
 · exact shape16_43
 · exact shape16_44
 · exact shape16_45
 · exact shape16_46
 · exact shape16_47
 · exact shape16_48
 · exact shape16_49
 · exact shape16_50
 · exact shape16_51
 · exact shape16_52
 · exact shape16_53
 · exact shape16_54
 · exact shape16_55
 · exact shape16_56
 · exact shape16_57
 · exact shape16_58
 · exact shape16_59
 · exact shape16_60
 · exact shape16_61
 · exact shape16_62
 · exact shape16_63
 · exact shape16_64
 · exact shape16_65
 · exact shape16_66
 · exact shape16_67
 · exact shape16_68
 · exact shape16_69
 · exact shape16_70
 · exact shape16_71
 · exact shape16_72
 · exact shape16_73
 · exact shape16_74
 · exact shape16_75
 · exact shape16_76
 · exact shape16_77
 · exact shape16_78
 · exact shape16_79
 · exact shape16_80
 · exact shape16_81
 · exact shape16_82
 · exact shape16_83
 · exact shape16_84
 · exact shape16_85
 · exact shape16_86
 · exact shape16_87
 · exact shape16_88
 · exact shape16_89
 · exact shape16_90
 · exact shape16_91
 · exact shape16_92
 · exact shape16_93
 · exact shape16_94
 · exact shape16_95
 · exact shape16_96
 · exact shape16_97
 · exact shape16_98
 · exact shape16_99
 · exact shape16_100
 · exact shape16_101
def _FOW:List Piece:=DZ.decode 62 41 0x3782dace9d900000aea149095480821dcb29cafa698f143a77a8eab16310e75b53cce17b3852ea0003
theorem shape17_0:validFrom 11176 0 _FOW=true:=by decide+kernel
def _FOX:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9d49095480821dcd6b4863bd1d442677a8eab16310e77944512734d592ca0003
theorem shape17_1:validFrom 11175 0 _FOX=true:=by decide+kernel
def _FPJ:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9949095480821dcfacc5cd10ab741237a8eab16310e79734d56cee72d2aa0003
theorem shape17_2:validFrom 11174 0 _FPJ=true:=by decide+kernel
def _FPU:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9549095480821dd1e91f1112379bfdb7a8eab16310e7b52559b2a81012890003
theorem shape17_3:validFrom 11173 0 _FPU=true:=by decide+kernel
def _FQF:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9149095480821dd42a9c7a65c5cbe8b7a8eab16310e7d315ddf861ad52690003
theorem shape17_4:validFrom 11172 0 _FQF=true:=by decide+kernel
def _FQQ:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8d49095480821dd66c19e3b953fbd377a8eab16310e7f106623e1b4a92490003
theorem shape17_5:validFrom 11171 0 _FQQ=true:=by decide+kernel
def _FRB:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8949095480821dd8ad974d0ce22bbdf7a8eab16310e80ef6e683d4e7d2290003
theorem shape17_6:validFrom 11170 0 _FRB=true:=by decide+kernel
def _FRM:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8549095480821ddae9f0910e6e53a7f7a8eab16310e82ce76ac98e8512080003
theorem shape17_7:validFrom 11169 0 _FRM=true:=by decide+kernel
def _FRX:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8149095480821ddd2b6dfa61fc8391b7a8eab16310e84ad7ef0f482251e80003
theorem shape17_8:validFrom 11168 0 _FRX=true:=by decide+kernel
def _FSI:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7d49095480821ddf6ceb63b58ab37af7a8eab16310e868c8735501bf91c80003
theorem shape17_9:validFrom 11167 0 _FSI=true:=by decide+kernel
def _FOY:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7949095480821de1a944a7b716db63f7a8eab16310e886b8f79abb5cd1a70003
theorem shape17_10:validFrom 11166 0 _FOY=true:=by decide+kernel
def _FPA:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7549095480821de3eac2110aa50b4c77a8eab16310e8a4a97be074fa11870003
theorem shape17_11:validFrom 11165 0 _FPA=true:=by decide+kernel
def _FPB:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae7149095480821de62c3f7a5e333b3497a8eab16310e8c29a00262e9751670003
theorem shape17_12:validFrom 11164 0 _FPB=true:=by decide+kernel
def _FPC:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6d49095480821de86898be5fbf631c57a8eab16310e8e08a846be83491460003
theorem shape17_13:validFrom 11163 0 _FPC=true:=by decide+kernel
def _FPD:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6949095480821deaaa1627b34d9303b7a8eab16310e8fe7b08b1a1d1d1260003
theorem shape17_14:validFrom 11162 0 _FPD=true:=by decide+kernel
def _FPE:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6549095480821de28eb857bac3a2ea97a8eab16310e9884ba14579b0cf020003
theorem shape17_15:validFrom 11161 0 _FPE=true:=by decide+kernel
def _FPF:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6149095480821de4ac38bbd0439ad0f7a8eab16310e9a79afef153564edb0003
theorem shape17_16:validFrom 11160 0 _FPF=true:=by decide+kernel
def _FPG:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae5d49095480821de6c9b91fe5c392b6f7a8eab16310e9c6ea5c9d2cfbceb40003
theorem shape17_17:validFrom 11159 0 _FPG=true:=by decide+kernel
def _FPH:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015cb000000000003c3d1d303985cb4540149095480821de8fd32bc0f3d3a9c77a8eab16310e9ec0e6e8109ea0e7f0004
theorem shape17_18:validFrom 11158 0 _FPH=true:=by decide+kernel
def _FPI:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9500000000000f0f7ad1847cbd554d6a484aa40410ed0ae1de7ebcd3940b0003
theorem shape17_19:validFrom 11157 0 _FPI=true:=by decide+kernel
def _FPK:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9400000000000f0fae559f999b814aca484aa40410ed2211ef1b5b4d132f0003
theorem shape17_20:validFrom 11156 0 _FPK=true:=by decide+kernel
def _FPL:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9300000000000f0fe1d85ffd50a1481a484aa40410ed6c094d6befc3124f0003
theorem shape17_21:validFrom 11155 0 _FPL=true:=by decide+kernel
def _FPM:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9200000000000f101559c5853c294565e99d545850f07d62ed554d3ad078bd33aa8b090edd843d19afb410e510004
theorem shape17_22:validFrom 11154 0 _FPM=true:=by decide+kernel
def _FPN:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9100000000000f1048d9d00ebc494295e99d545850f07f40a736987a5059bd33aa8b090ede59bd5177828ce130004
theorem shape17_23:validFrom 11153 0 _FPN=true:=by decide+kernel
def _FPO:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9000000000000f107c587fdf11cd3fc5e99d545850f081653f0ae9d4503abd33aa8b090edf2f3d893f5108dd60004
theorem shape17_24:validFrom 11152 0 _FPO=true:=by decide+kernel
def _FPP:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae3c000000000078857eaea69ce929e7de99d545850ef41f3502e878dd01a0003
theorem shape17_25:validFrom 11151 0 _FPP=true:=by decide+kernel
def _FPQ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae38000000000078871a8e764df9a9d05e99d545850ef49e9b403d183cffa0003
theorem shape17_26:validFrom 11150 0 _FPQ=true:=by decide+kernel
def _FPR:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae3400000000007888b6637035ae69b8de99d545850ef51e0026a14408fd90003
theorem shape17_27:validFrom 11149 0 _FPR=true:=by decide+kernel
def _FPS:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae300000000000788a522d933f0829a0de99d545850ef59ede1d488354fb80003
theorem shape17_28:validFrom 11148 0 _FPS=true:=by decide+kernel
def _FPT:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae2c0000000000788bedecde552c6987de99d545850ef622af8bcb0c30f960003
theorem shape17_29:validFrom 11147 0 _FPT=true:=by decide+kernel
def _FPV:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae280000000000788d89a153a1df096ede99d545850ef6a67fa33b92f4f730003
theorem shape17_30:validFrom 11146 0 _FPV=true:=by decide+kernel
def _FPW:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae240000000000788f254af2104209555e99d545850ef72d43328761d0f500003
theorem shape17_31:validFrom 11145 0 _FPW=true:=by decide+kernel
def _FPX:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae2000000000007890c0e9b88b75e93b5e99d545850ef7b4056ac130e0f2c0003
theorem shape17_32:validFrom 11144 0 _FPX=true:=by decide+kernel
def _FPY:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae1c000000000078925c7da93d2ba9205e99d545850ef83dbb1ad646bcf080003
theorem shape17_33:validFrom 11143 0 _FPY=true:=by decide+kernel
def _FPZ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae1800000000007893f806c3108be904de99d545850ef8c8e9db2e7218ee30003
theorem shape17_34:validFrom 11142 0 _FPZ=true:=by decide+kernel
def _FQA:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae140000000000789593850605a108e95e99d545850ef95591ac0cce70ebd0003
theorem shape17_35:validFrom 11141 0 _FQA=true:=by decide+kernel
def _FQB:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae10000000000078972ef871078ee8ccde99d545850ef9e3b28d4fcdc8e970003
theorem shape17_36:validFrom 11140 0 _FQB=true:=by decide+kernel
def _FQC:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae0c00000000007898ca61063ff248af5e99d545850efa74c6e62afab4e6f0003
theorem shape17_37:validFrom 11139 0 _FQC=true:=by decide+kernel
def _FQD:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae080000000000789a65bec49a042891de99d545850efb05d9e837400ce470003
theorem shape17_38:validFrom 11138 0 _FQD=true:=by decide+kernel
def _FQE:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae040000000000789c0111ab010188735e99d545850efb9b5ac930ca88e1e0003
theorem shape17_39:validFrom 11137 0 _FQE=true:=by decide+kernel
def _FQG:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae000000000000789d9c59bb9e6f4853de99d545850eff5d2e2553a948dc30003
theorem shape17_40:validFrom 11136 0 _FQG=true:=by decide+kernel
def _FQH:List Piece:=DZ.decode 62 39 0x3782dace9d900000adfc0000000000789f3796f55d8448345e99d545850f000284497d6710d760003
theorem shape17_41:validFrom 11135 0 _FQH=true:=by decide+kernel
def _FQI:List Piece:=DZ.decode 62 39 0x3782dace9d900000adf8000000000078a0d2c957299148135e99d545850f00aacded378e78d270003
theorem shape17_42:validFrom 11134 0 _FQI=true:=by decide+kernel
def _FQJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fa0f144dbe1c657f64fe30002
theorem shape17_43:validFrom 11133 0 _FQJ=true:=by decide+kernel
def _FQK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f80f148121b30a0360f9f0002
theorem shape17_44:validFrom 11132 0 _FQK=true:=by decide+kernel
def _FQL:List Piece:=DZ.decode 62 42 0x3782dace9d900000adec5e99d545850f15ccb14d8618d0f59e8d4a5100003c5303ea1eb80243b9800000000000f14b483eeb026f4ed30004
theorem shape17_45:validFrom 11131 0 _FQL=true:=by decide+kernel
def _FQM:List Piece:=DZ.decode 62 42 0x3782dace9d900000ade85e99d545850f368f23602ac6f0f11e8d4a5100003caed141f3b70243a9c00000000000f14e7e4cf9d1498de80004
theorem shape17_46:validFrom 11130 0 _FQM=true:=by decide+kernel
def _FQN:List Piece:=DZ.decode 62 42 0xde0b6b3a76400002b79000000000003cd8a26e54eb8003b1c00000000000f3626ac1e8bc000ec0000000000003cd892eee5c5e003ac000000000000f3622cb54573000ea0000000000003cd8836f76a04003a4000000000000f361eeb788dc800e80000000000003cd873f0077aa0039c000000000000f361b0b9cc46000e60000000000003cd864709855000394000000000000f3610a22acb3000e40000000000003cd7d85939b020038c3a3529440000f35d6317bd40090e28e8d4a5100003caed141f3b7024389400000000000f151b4455ae3808de7000f
theorem shape17_47:validFrom 11129 0 _FQN=true:=by decide+kernel
def _FQO:List Piece:=DZ.decode 62 42 0x3782dace9d900000ade000000000000f36247c64fad800e7c000000000003cd88966d51880039c000000000000f362037f3fc9000e60000000000003cd87855111f600394000000000000f361588a89ea800e40000000000003cd7ef69cf7ac0038c3a3529440000f35d9f17e1400a8e28e8d4a5100003caee041fcb702a389400000000000f154ea280c0fe90de7000a
theorem shape17_48:validFrom 11128 0 _FQO=true:=by decide+kernel
def _FQP:List Piece:=DZ.decode 62 43 0xde0b6b3a76400002b77746a52880001e6bb8a344382b71c5d5d3ef7980003caf7632b0bd8283895d1a94a20000795dd38519aeadc6f4800000000000f1581ff511a8c9cde70005
theorem shape17_49:validFrom 11127 0 _FQP=true:=by decide+kernel
def _FQR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ec0f15b55ac6985074ddf0002
theorem shape17_50:validFrom 11126 0 _FQR=true:=by decide+kernel
def _FQS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ea0f15e8b4e117b7ecd8d0002
theorem shape17_51:validFrom 11125 0 _FQS=true:=by decide+kernel
def _FQT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e80f161c0da0dde65cd390002
theorem shape17_52:validFrom 11124 0 _FQT=true:=by decide+kernel
def _FQU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e60f164f6505c84bb4ce30002
theorem shape17_53:validFrom 11123 0 _FQU=true:=by decide+kernel
def _FQV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e40f1682bb0fd6e4bcc8b0002
theorem shape17_54:validFrom 11122 0 _FQV=true:=by decide+kernel
def _FQW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e20f16b60fbee723f8c300002
theorem shape17_55:validFrom 11121 0 _FQW=true:=by decide+kernel
def _FQX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e00f16e963133e289cbd20002
theorem shape17_56:validFrom 11120 0 _FQX=true:=by decide+kernel
def _FQY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056de0f171cb50cb96334b720002
theorem shape17_57:validFrom 11119 0 _FQY=true:=by decide+kernel
def _FQZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056dc0f175005ab364464b0f0002
theorem shape17_58:validFrom 11118 0 _FQZ=true:=by decide+kernel
def _FRA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056da0f178354eef9e970aa90002
theorem shape17_59:validFrom 11117 0 _FRA=true:=by decide+kernel
def _FRC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d80f17b6a2d7e1c348a400002
theorem shape17_60:validFrom 11116 0 _FRC=true:=by decide+kernel
def _FRD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d60f17e9ef65cb47a09d40002
theorem shape17_61:validFrom 11115 0 _FRD=true:=by decide+kernel
def _FRE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d40f181d3a98fb8d109650002
theorem shape17_62:validFrom 11114 0 _FRE=true:=by decide+kernel
def _FRF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d20f185084715007508f20002
theorem shape17_63:validFrom 11113 0 _FRF=true:=by decide+kernel
def _FRG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d00f1883cceea62c6487d0002
theorem shape17_64:validFrom 11112 0 _FRG=true:=by decide+kernel
def _FRH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ce0f18b7141143123c8050002
theorem shape17_65:validFrom 11111 0 _FRH=true:=by decide+kernel
def _FRI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056cc0f18ea59d9042e2c7890002
theorem shape17_66:validFrom 11110 0 _FRI=true:=by decide+kernel
def _FRJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ca0f191d9e45c6f5347090002
theorem shape17_67:validFrom 11109 0 _FRJ=true:=by decide+kernel
def _FRK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c80f1950e157d07b786860002
theorem shape17_68:validFrom 11108 0 _FRK=true:=by decide+kernel
def _FRL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c60f1984230efe36806000002
theorem shape17_69:validFrom 11107 0 _FRL=true:=by decide+kernel
def _FRN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c40f19b7636b2da0d45780002
theorem shape17_70:validFrom 11106 0 _FRN=true:=by decide+kernel
def _FRO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c20f19eaa26ca3c7804eb0002
theorem shape17_71:validFrom 11105 0 _FRO=true:=by decide+kernel
def _FRP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c00f1a1de0133e22f445a0002
theorem shape17_72:validFrom 11104 0 _FRP=true:=by decide+kernel
def _FRQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056be0f1a511c5eda2de03c60002
theorem shape17_73:validFrom 11103 0 _FRQ=true:=by decide+kernel
def _FRR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056bc0f1a83c9343cf6b032f0002
theorem shape17_74:validFrom 11102 0 _FRR=true:=by decide+kernel
def _FRS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ba0f1ab3acb32950c82960002
theorem shape17_75:validFrom 11101 0 _FRS=true:=by decide+kernel
def _FRT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f1ae38ef06747e01f80002
theorem shape17_76:validFrom 11100 0 _FRT=true:=by decide+kernel
def _FRU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b60f1b136fec3be6101560002
theorem shape17_77:validFrom 11099 0 _FRU=true:=by decide+kernel
def _FRV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b40f1b434fa66222d00b10002
theorem shape17_78:validFrom 11098 0 _FRV=true:=by decide+kernel
def _FRW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b20f1b732e1f1f06980080002
theorem shape17_79:validFrom 11097 0 _FRW=true:=by decide+kernel
def _FRY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad633bbf20bc8049de10f1ba30b562d887c0020002
theorem shape17_80:validFrom 11096 0 _FRY=true:=by decide+kernel
def _FRZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5f3bbe614ca9b54470f1bd2e74bd2aee40020002
theorem shape17_81:validFrom 11095 0 _FRZ=true:=by decide+kernel
def _FSA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5b3bbda1e1d9da2860f1c02c1ffc975e80020002
theorem shape17_82:validFrom 11094 0 _FSA=true:=by decide+kernel
def _FSB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad573bbce27c0fa47820f1c329b7256e1f80020002
theorem shape17_83:validFrom 11093 0 _FSB=true:=by decide+kernel
def _FSC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad533bbc231b4c284780f1c6273a335ee200020002
theorem shape17_84:validFrom 11092 0 _FSC=true:=by decide+kernel
def _FSD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4f3bbb63bf8edb8b80f1c924a92891d200020002
theorem shape17_85:validFrom 11091 0 _FSD=true:=by decide+kernel
def _FSE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4b3bbaa468d73447d0f1cc2204072ee0c0020002
theorem shape17_86:validFrom 11090 0 _FSE=true:=by decide+kernel
def _FSF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473bb9e517264670d0f1cf1f4acae63cc0020002
theorem shape17_87:validFrom 11089 0 _FSF=true:=by decide+kernel
def _FSG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433bb925ca7afe1cb0f1d21c7d78078d40020002
theorem shape17_88:validFrom 11088 0 _FSG=true:=by decide+kernel
def _FSH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3bb86682d66f39b0f1d5199c0a431940020002
theorem shape17_89:validFrom 11087 0 _FSH=true:=by decide+kernel
def _FSJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3bb7a7403785d520f1d816a685e8ab80020002
theorem shape17_90:validFrom 11086 0 _FSJ=true:=by decide+kernel
def _FSK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373bb6e8029f55db80f1db139ce6a89200020002
theorem shape17_91:validFrom 11085 0 _FSK=true:=by decide+kernel
def _FSL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333bb628ca0ccb5fc0f1de107f30d28100020002
theorem shape17_92:validFrom 11084 0 _FSL=true:=by decide+kernel
def _FSM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3bb5699680fa5190f1e10d4d6016b9c0020002
theorem shape17_93:validFrom 11083 0 _FSM=true:=by decide+kernel
def _FSN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3bb4aa67facecc20f1e40a0778c4cf80020002
theorem shape17_94:validFrom 11082 0 _FSN=true:=by decide+kernel
def _FSO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273bb3eb3e7b5ca970f1e706ad768d5a40020002
theorem shape17_95:validFrom 11081 0 _FSO=true:=by decide+kernel
def _FSP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233bb32c1a01900c90f1ea033f5dbfcdc0020002
theorem shape17_96:validFrom 11080 0 _FSP=true:=by decide+kernel
def _FSQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3bb26cfa8e7cd540f1ecffbd2a0cab00020002
theorem shape17_97:validFrom 11079 0 _FSQ=true:=by decide+kernel
def _FSR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3bb1ade0210f2f00f1effc26dfc34400020002
theorem shape17_98:validFrom 11078 0 _FSR=true:=by decide+kernel
def _FSS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bb0eecaba5ae320f1f2f87c7a947380020002
theorem shape17_99:validFrom 11077 0 _FSS=true:=by decide+kernel
def _FOZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bb02fba594c2c80f1f5f4bdfecf4e00020002
theorem shape17_100:validFrom 11076 0 _FOZ=true:=by decide+kernel
def row17 (v:ℕ):List Piece:=match v with
 | 0=>_FOW
 | 1=>_FOX
 | 2=>_FPJ
 | 3=>_FPU
 | 4=>_FQF
 | 5=>_FQQ
 | 6=>_FRB
 | 7=>_FRM
 | 8=>_FRX
 | 9=>_FSI
 | 10=>_FOY
 | 11=>_FPA
 | 12=>_FPB
 | 13=>_FPC
 | 14=>_FPD
 | 15=>_FPE
 | 16=>_FPF
 | 17=>_FPG
 | 18=>_FPH
 | 19=>_FPI
 | 20=>_FPK
 | 21=>_FPL
 | 22=>_FPM
 | 23=>_FPN
 | 24=>_FPO
 | 25=>_FPP
 | 26=>_FPQ
 | 27=>_FPR
 | 28=>_FPS
 | 29=>_FPT
 | 30=>_FPV
 | 31=>_FPW
 | 32=>_FPX
 | 33=>_FPY
 | 34=>_FPZ
 | 35=>_FQA
 | 36=>_FQB
 | 37=>_FQC
 | 38=>_FQD
 | 39=>_FQE
 | 40=>_FQG
 | 41=>_FQH
 | 42=>_FQI
 | 43=>_FQJ
 | 44=>_FQK
 | 45=>_FQL
 | 46=>_FQM
 | 47=>_FQN
 | 48=>_FQO
 | 49=>_FQP
 | 50=>_FQR
 | 51=>_FQS
 | 52=>_FQT
 | 53=>_FQU
 | 54=>_FQV
 | 55=>_FQW
 | 56=>_FQX
 | 57=>_FQY
 | 58=>_FQZ
 | 59=>_FRA
 | 60=>_FRC
 | 61=>_FRD
 | 62=>_FRE
 | 63=>_FRF
 | 64=>_FRG
 | 65=>_FRH
 | 66=>_FRI
 | 67=>_FRJ
 | 68=>_FRK
 | 69=>_FRL
 | 70=>_FRN
 | 71=>_FRO
 | 72=>_FRP
 | 73=>_FRQ
 | 74=>_FRR
 | 75=>_FRS
 | 76=>_FRT
 | 77=>_FRU
 | 78=>_FRV
 | 79=>_FRW
 | 80=>_FRY
 | 81=>_FRZ
 | 82=>_FSA
 | 83=>_FSB
 | 84=>_FSC
 | 85=>_FSD
 | 86=>_FSE
 | 87=>_FSF
 | 88=>_FSG
 | 89=>_FSH
 | 90=>_FSJ
 | 91=>_FSK
 | 92=>_FSL
 | 93=>_FSM
 | 94=>_FSN
 | 95=>_FSO
 | 96=>_FSP
 | 97=>_FSQ
 | 98=>_FSR
 | 99=>_FSS
 | 100=>_FOZ
 | _=>[]
theorem checked17 (v:ℕ) (hy:17+v≤117):validFrom (11193-17-v) 0 (row17 v)=true:=by
 have hv:v≤100:=by omega
 interval_cases v
 · exact shape17_0
 · exact shape17_1
 · exact shape17_2
 · exact shape17_3
 · exact shape17_4
 · exact shape17_5
 · exact shape17_6
 · exact shape17_7
 · exact shape17_8
 · exact shape17_9
 · exact shape17_10
 · exact shape17_11
 · exact shape17_12
 · exact shape17_13
 · exact shape17_14
 · exact shape17_15
 · exact shape17_16
 · exact shape17_17
 · exact shape17_18
 · exact shape17_19
 · exact shape17_20
 · exact shape17_21
 · exact shape17_22
 · exact shape17_23
 · exact shape17_24
 · exact shape17_25
 · exact shape17_26
 · exact shape17_27
 · exact shape17_28
 · exact shape17_29
 · exact shape17_30
 · exact shape17_31
 · exact shape17_32
 · exact shape17_33
 · exact shape17_34
 · exact shape17_35
 · exact shape17_36
 · exact shape17_37
 · exact shape17_38
 · exact shape17_39
 · exact shape17_40
 · exact shape17_41
 · exact shape17_42
 · exact shape17_43
 · exact shape17_44
 · exact shape17_45
 · exact shape17_46
 · exact shape17_47
 · exact shape17_48
 · exact shape17_49
 · exact shape17_50
 · exact shape17_51
 · exact shape17_52
 · exact shape17_53
 · exact shape17_54
 · exact shape17_55
 · exact shape17_56
 · exact shape17_57
 · exact shape17_58
 · exact shape17_59
 · exact shape17_60
 · exact shape17_61
 · exact shape17_62
 · exact shape17_63
 · exact shape17_64
 · exact shape17_65
 · exact shape17_66
 · exact shape17_67
 · exact shape17_68
 · exact shape17_69
 · exact shape17_70
 · exact shape17_71
 · exact shape17_72
 · exact shape17_73
 · exact shape17_74
 · exact shape17_75
 · exact shape17_76
 · exact shape17_77
 · exact shape17_78
 · exact shape17_79
 · exact shape17_80
 · exact shape17_81
 · exact shape17_82
 · exact shape17_83
 · exact shape17_84
 · exact shape17_85
 · exact shape17_86
 · exact shape17_87
 · exact shape17_88
 · exact shape17_89
 · exact shape17_90
 · exact shape17_91
 · exact shape17_92
 · exact shape17_93
 · exact shape17_94
 · exact shape17_95
 · exact shape17_96
 · exact shape17_97
 · exact shape17_98
 · exact shape17_99
 · exact shape17_100
def _FST:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9d49095480821dcd416d474c619b6497a8eab16310e861442c71f9d450530003
theorem shape18_0:validFrom 11175 0 _FST=true:=by decide+kernel
def _FSU:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9949095480821dcf5eedab61e1934e97a8eab16310e880938a1dd379d02c0003
theorem shape18_1:validFrom 11174 0 _FSU=true:=by decide+kernel
def _FTF:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9549095480821dd17c6e0f77618b3857a8eab16310e89fe2e7c9ad1f50050003
theorem shape18_2:validFrom 11173 0 _FTF=true:=by decide+kernel
def _FTQ:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae9149095480821dd399ee738ce18321b7a8eab16310e8bf32457586c4cfde0003
theorem shape18_3:validFrom 11172 0 _FTQ=true:=by decide+kernel
def _FUB:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8d49095480821dd5b76ed7a2617b0ab7a8eab16310e8de81a321606a4fb70003
theorem shape18_4:validFrom 11171 0 _FUB=true:=by decide+kernel
def _FUM:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8949095480821dd7da136109e37af357a8eab16310e8fdd100cd3a0fcf910003
theorem shape18_5:validFrom 11170 0 _FUM=true:=by decide+kernel
def _FUX:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8549095480821dd9f793c51f6372db97a8eab16310e91d205e7913b54f6a0003
theorem shape18_6:validFrom 11169 0 _FUX=true:=by decide+kernel
def _FVI:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8149095480821ddb8520143caa8ac397a8eab16310e94244705cf0a38f270003
theorem shape18_7:validFrom 11168 0 _FVI=true:=by decide+kernel
def _FVT:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015cf800000000003c39c7a45ab7681560d49095480821dddc69d7d9038baab17a8eab16310e96034f4a2aa40cf070004
theorem shape18_8:validFrom 11167 0 _FVT=true:=by decide+kernel
def _FWE:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015cf000000000003c3a922472c676f557149095480821de002f6c191c4e29257a8eab16310e97e2578e863de0ee60004
theorem shape18_9:validFrom 11166 0 _FWE=true:=by decide+kernel
def _FSV:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015ce800000000003c3b5c9f2e8d53654d549095480821de244742ae553127917a8eab16310e99c15fd2e1d7b4ec60004
theorem shape18_10:validFrom 11165 0 _FSV=true:=by decide+kernel
def _FSW:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015ce000000000003c3c27148f18cb9543549095480821de485f19438e1425f77a8eab16310e9ba068173d7188ea60004
theorem shape18_11:validFrom 11164 0 _FSW=true:=by decide+kernel
def _FSX:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015cd800000000003c3cf184935c177539149095480821de6c24ad83a6d6a4577a8eab16310e9d7f705b990b5ce850004
theorem shape18_12:validFrom 11163 0 _FSX=true:=by decide+kernel
def _FSY:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015cd000000000003c3dbbef3c63f8f52ed49095480821de903c8418dfb9a2af7a8eab16310e9f5e789ff4a530e650004
theorem shape18_13:validFrom 11162 0 _FSY=true:=by decide+kernel
def _FSZ:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b9900000000000787d0ca91247644a4897a675516143c29a8e329f280442b549095480821deb4545aae189ca1017a8eab16310ea13d80e4503f04e450005
theorem shape18_14:validFrom 11161 0 _FSZ=true:=by decide+kernel
def _FTA:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae6000000000001e1fa85a3d53fe8a8ce5e99d545850f0aaaa5f2c4ac2508f5e99d545848784ca5febc36b1682ddea3aac58c43bfeaf6d36838fc40f149095480821ded86c3143517f9f4d7a8eab16310ea31c8928abd8d8e250007
theorem shape18_15:validFrom 11160 0 _FTA=true:=by decide+kernel
def _FTB:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae5c00000000001e200d8788353dd28765e99d545850f0af3f03426aac90715e99d545848784e54e3bb4aa8881e5ea3aac58c43bf1a712c21e0f3401949095480821defc31c5836a421d917a8eab16310ea4fb916d0772ace040007
theorem shape18_16:validFrom 11159 0 _FTB=true:=by decide+kernel
def _FTC:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae5800000000001e2072b224f26af281e5e99d545850f0b41a8586247a90535e99d545848785003c8ba5e9fa80f5ea3aac58c43be44014a2f30263f4149095480821df20499c18a3251bcd7a8eab16310ea6da99b1630c80de40007
theorem shape18_17:validFrom 11158 0 _FTC=true:=by decide+kernel
def _FTD:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b950000000000078835f6850477ba9f197a675516143c2e31a96bba78940d17a675516121e1466c1d1084d69ffd7a8eab16310ea8b9a1f5bea654f990005
theorem shape18_18:validFrom 11157 0 _FTD=true:=by decide+kernel
def _FTE:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9400000000000f109e7faa86a1dd3b55e99d545850f0bda1fd9200501014bd33aa8b090f00a72f60b2f2c4fdfa484aa40410ed8623d620ed7d8c160005
theorem shape18_19:validFrom 11156 0 _FTE=true:=by decide+kernel
def _FTG:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9300000000000f10d110f43576293875e99d545850f0b45ac42721fc0ff5bd33aa8b090eff7898400aff84f26a484aa40410ed9d53e6bd8bf70b280005
theorem shape18_20:validFrom 11155 0 _FTG=true:=by decide+kernel
def _FTH:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9200000000000f1103a0e6d243653585e99d545850f0b6cf09c159a28fd4bd33aa8b090efd82ad1af513f8eeba484aa40410ede74b450e206d0a360005
theorem shape18_21:validFrom 11154 0 _FTH=true:=by decide+kernel
def _FTI:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9100000000000f11362f82a032093285e99d545850f09c8801a35a0a8fb4bd33aa8b090ee1f85f0954e750d780004
theorem shape18_22:validFrom 11153 0 _FTI=true:=by decide+kernel
def _FTJ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9000000000000f1168bcc75c1b192f85e99d545850f09f2b69c588ae4f92bd33aa8b090ee2cddf411cb5ccd3e0004
theorem shape18_23:validFrom 11152 0 _FTJ=true:=by decide+kernel
def _FTK:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8f00000000000f119b48b54923952c65e99d545850f0a1fe09a208698f70bd33aa8b090ee3a35f78e48448d050004
theorem shape18_24:validFrom 11151 0 _FTK=true:=by decide+kernel
def _FTL:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae380000000000788e6e9a61213fe94a5e99d545850ef7659bbeb70c48f4e0003
theorem shape18_25:validFrom 11150 0 _FTL=true:=by decide+kernel
def _FTM:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae340000000000789002e461825a69305e99d545850ef7e9f8e710e924f2b0003
theorem shape18_26:validFrom 11149 0 _FTM=true:=by decide+kernel
def _FTN:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae30000000000078919723aa5fd849165e99d545850ef86fcf23db4430f080003
theorem shape18_27:validFrom 11148 0 _FTN=true:=by decide+kernel
def _FTO:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae2c000000000078932b583aad4188fbde99d545850ef8f898dc2a2d64ee30003
theorem shape18_28:validFrom 11147 0 _FTO=true:=by decide+kernel
def _FTP:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae2800000000007894bf8214839608e05e99d545850ef981614173fbe0ebe0003
theorem shape18_29:validFrom 11146 0 _FTP=true:=by decide+kernel
def _FTR:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae240000000000789653a135c9d9c8c4de99d545850efa0ba2bb0dc5c0e990003
theorem shape18_30:validFrom 11145 0 _FTR=true:=by decide+kernel
def _FTS:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae2000000000007897e7b5a098fd08a85e99d545850efdd67e222321ace500003
theorem shape18_31:validFrom 11144 0 _FTS=true:=by decide+kernel
def _FTT:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae1c000000000078997bbf52d821e88bde99d545850efe413e3e0708ece290003
theorem shape18_32:validFrom 11143 0 _FTT=true:=by decide+kernel
def _FTU:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae180000000000789b0fbe4ea01be86e5e99d545850efeabfe59eaf02ce030003
theorem shape18_33:validFrom 11142 0 _FTU=true:=by decide+kernel
def _FTV:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae140000000000789ca3b291d81148505e99d545850eff16be75ced76cddd0003
theorem shape18_34:validFrom 11141 0 _FTV=true:=by decide+kernel
def _FTW:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae100000000000789e379c1e98dde831de99d545850eff817e91b2beacdb70003
theorem shape18_35:validFrom 11140 0 _FTW=true:=by decide+kernel
def _FTX:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae0c0000000000789fcb7af3d611e812de99d545850effec3ead96a5ecd910003
theorem shape18_36:validFrom 11139 0 _FTX=true:=by decide+kernel
def _FTY:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae08000000000078a15f4f10835147f2de99d545850f0056fec97a8d2cd6b0003
theorem shape18_37:validFrom 11138 0 _FTY=true:=by decide+kernel
def _FTZ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae04000000000078a2f31876b95407d2de99d545850f00c1bee55e746cd450003
theorem shape18_38:validFrom 11137 0 _FTZ=true:=by decide+kernel
def _FUA:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae00000000000078a486d7245f6e07b15e99d545850f012c7f01425bacd1f0003
theorem shape18_39:validFrom 11136 0 _FUA=true:=by decide+kernel
def _FUC:List Piece:=DZ.decode 62 39 0x3782dace9d900000adfc000000000078a61a8b1b8e47478fde99d545850f01973f1d2642eccf50003
theorem shape18_40:validFrom 11135 0 _FUC=true:=by decide+kernel
def _FUD:List Piece:=DZ.decode 62 39 0x3782dace9d900000adf8000000000078a7ae345a2d37e76d5e99d545850f023c95415000b4cab0003
theorem shape18_41:validFrom 11134 0 _FUD=true:=by decide+kernel
def _FUE:List Piece:=DZ.decode 62 39 0x3782dace9d900000adf4000000000078a941d2e254e40749de99d545850f02e4dee50a281cc5c0003
theorem shape18_42:validFrom 11133 0 _FUE=true:=by decide+kernel
def _FUF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f80f155aacd63d966ce4b0002
theorem shape18_43:validFrom 11132 0 _FUF=true:=by decide+kernel
def _FUG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f60f158d1df961a5c0e010002
theorem shape18_44:validFrom 11131 0 _FUG=true:=by decide+kernel
def _FUH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f40f15bf8dc5954284db60002
theorem shape18_45:validFrom 11130 0 _FUH=true:=by decide+kernel
def _FUI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f20f15f1fc3ab6e530d690002
theorem shape18_46:validFrom 11129 0 _FUI=true:=by decide+kernel
def _FUJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f00f16246959099c48d1a0002
theorem shape18_47:validFrom 11128 0 _FUJ=true:=by decide+kernel
def _FUK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ee0f1656d5204a59c8cc90002
theorem shape18_48:validFrom 11127 0 _FUK=true:=by decide+kernel
def _FUL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ec0f16893f90bc2b34c760002
theorem shape18_49:validFrom 11126 0 _FUL=true:=by decide+kernel
def _FUN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ea0f16bba8aa1c0598c220002
theorem shape18_50:validFrom 11125 0 _FUN=true:=by decide+kernel
def _FUO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e80f16ee106cacf0dcbcb0002
theorem shape18_51:validFrom 11124 0 _FUO=true:=by decide+kernel
def _FUP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e60f172076d82be590b730002
theorem shape18_52:validFrom 11123 0 _FUP=true:=by decide+kernel
def _FUQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e40f1752dbecdbeba8b180002
theorem shape18_53:validFrom 11122 0 _FUQ=true:=by decide+kernel
def _FUR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e20f17853faa9b7eb0abb0002
theorem shape18_54:validFrom 11121 0 _FUR=true:=by decide+kernel
def _FUS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e00f17b7a211491ba0a5b0002
theorem shape18_55:validFrom 11120 0 _FUS=true:=by decide+kernel
def _FUT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056de0f17ea032127c8fc9f90002
theorem shape18_56:validFrom 11119 0 _FUT=true:=by decide+kernel
def _FUU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056dc0f181c62d9f481c49950002
theorem shape18_57:validFrom 11118 0 _FUU=true:=by decide+kernel
def _FUV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056da0f184ec13bf248f492e0002
theorem shape18_58:validFrom 11117 0 _FUV=true:=by decide+kernel
def _FUW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d80f18811e46de1d0c8c40002
theorem shape18_59:validFrom 11116 0 _FUW=true:=by decide+kernel
def _FUY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d60f18b379fafaff148570002
theorem shape18_60:validFrom 11115 0 _FUY=true:=by decide+kernel
def _FUZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d40f18e5d45805ee847e70002
theorem shape18_61:validFrom 11114 0 _FUZ=true:=by decide+kernel
def _FVA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d20f19182d5e41ea607740002
theorem shape18_62:validFrom 11113 0 _FVA=true:=by decide+kernel
def _FVB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d00f194a850d6bf5286fe0002
theorem shape18_63:validFrom 11112 0 _FVB=true:=by decide+kernel
def _FVC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ce0f197cdb65c70bd86850002
theorem shape18_64:validFrom 11111 0 _FVC=true:=by decide+kernel
def _FVD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056cc0f19af306731aef46090002
theorem shape18_65:validFrom 11110 0 _FVD=true:=by decide+kernel
def _FVE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ca0f19e184118a627c5890002
theorem shape18_66:validFrom 11109 0 _FVE=true:=by decide+kernel
def _FVF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c80f1a13d6651420705050002
theorem shape18_67:validFrom 11108 0 _FVF=true:=by decide+kernel
def _FVG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c60f1a4627618bf02447e0002
theorem shape18_68:validFrom 11107 0 _FVG=true:=by decide+kernel
def _FVH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c40f1a78770734c86c3f50002
theorem shape18_69:validFrom 11106 0 _FVH=true:=by decide+kernel
def _FVJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c20f1aaac555cbb2a03670002
theorem shape18_70:validFrom 11105 0 _FVJ=true:=by decide+kernel
def _FVK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c00f1add124d93a5442d60002
theorem shape18_71:validFrom 11104 0 _FVK=true:=by decide+kernel
def _FVL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056be0f1b0f5dee49aa4c2400002
theorem shape18_72:validFrom 11103 0 _FVL=true:=by decide+kernel
def _FVM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056bc0f1b411eb23474441a80002
theorem shape18_73:validFrom 11102 0 _FVM=true:=by decide+kernel
def _FVN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ba0f1b702d1b2dfea410e0002
theorem shape18_74:validFrom 11101 0 _FVN=true:=by decide+kernel
def _FVO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056b80f1b9f3a459481f00700002
theorem shape18_75:validFrom 11100 0 _FVO=true:=by decide+kernel
def _FVP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6f3bbe73d112543d60f1bce4631aaf0a80020002
theorem shape18_76:validFrom 11099 0 _FVP=true:=by decide+kernel
def _FVQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6b3bbdb7a65c4698e0f1bfd50df2e59c80020002
theorem shape18_77:validFrom 11098 0 _FVQ=true:=by decide+kernel
def _FVR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad673bbcfb809f794cb0f1c2c5a4e61acd40020002
theorem shape18_78:validFrom 11097 0 _FVR=true:=by decide+kernel
def _FVS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad633bbc3f5fdcf812e0f1c5b627f01fb480020002
theorem shape18_79:validFrom 11096 0 _FVS=true:=by decide+kernel
def _FVU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5f3bbb834413b73550f1c8a69715232ac0020002
theorem shape18_80:validFrom 11095 0 _FVU=true:=by decide+kernel
def _FVV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5b3bbac72d44c26620f1cb96f250f66780020002
theorem shape18_81:validFrom 11094 0 _FVV=true:=by decide+kernel
def _FVW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad573bba0b1b6f0df750f1ce8739a7c822c0020002
theorem shape18_82:validFrom 11093 0 _FVW=true:=by decide+kernel
def _FVX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad533bb94f0e93a592c0f1d1776d1569b500020002
theorem shape18_83:validFrom 11092 0 _FVX=true:=by decide+kernel
def _FVY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4f3bb89306b2036290f1d4678c9bf275c0020002
theorem shape18_84:validFrom 11091 0 _FVY=true:=by decide+kernel
def _FVZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4b3bb7d703c9a198b0f1d757983d799d40020002
theorem shape18_85:validFrom 11090 0 _FVZ=true:=by decide+kernel
def _FWA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473bb71b05db8bd320f1da478ff5d0b380020002
theorem shape18_86:validFrom 11089 0 _FWA=true:=by decide+kernel
def _FWB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433bb65f0ce6b67160f1dd3773c9263a80020002
theorem shape18_87:validFrom 11088 0 _FWB=true:=by decide+kernel
def _FWC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3bb5a318ec2d1870f1e02743b34b9e40020002
theorem shape18_88:validFrom 11087 0 _FWC=true:=by decide+kernel
def _FWD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3bb4e729eae42bf0f1e316ffb86f5040020002
theorem shape18_89:validFrom 11086 0 _FWD=true:=by decide+kernel
def _FWF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373bb42b3fe3e73ba0f1e606a7d4631180020002
theorem shape18_90:validFrom 11085 0 _FWF=true:=by decide+kernel
def _FWG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333bb36f5ad62abdb0f1e8f63c0b550940020002
theorem shape18_91:validFrom 11084 0 _FWG=true:=by decide+kernel
def _FWH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3bb2b37ac2ba3820f1ebe5bc59171f80020002
theorem shape18_92:validFrom 11083 0 _FWH=true:=by decide+kernel
def _FWI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3bb1f79fa88a28d0f1eed528c1d75cc0020002
theorem shape18_93:validFrom 11082 0 _FWI=true:=by decide+kernel
def _FWJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273bb13bc988a60de0f1f1c4814167c880020002
theorem shape18_94:validFrom 11081 0 _FWJ=true:=by decide+kernel
def _FWK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233bb07ff862026d50f1f4b3c5dbf64ac0020002
theorem shape18_95:validFrom 11080 0 _FWK=true:=by decide+kernel
def _FWL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3bafc42c35aabd00f1f7a2f68d550c00020002
theorem shape18_96:validFrom 11079 0 _FWL=true:=by decide+kernel
def _FWM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3baf086502938b10f1fa921359b1d3c0020002
theorem shape18_97:validFrom 11078 0 _FWM=true:=by decide+kernel
def _FWN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173bae4ca2c9c84570f1fd811c3cdeea40020002
theorem shape18_98:validFrom 11077 0 _FWN=true:=by decide+kernel
def _FWO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133bad90e58a3d8240f20070113b09f700020002
theorem shape18_99:validFrom 11076 0 _FWO=true:=by decide+kernel
def row18 (v:ℕ):List Piece:=match v with
 | 0=>_FST
 | 1=>_FSU
 | 2=>_FTF
 | 3=>_FTQ
 | 4=>_FUB
 | 5=>_FUM
 | 6=>_FUX
 | 7=>_FVI
 | 8=>_FVT
 | 9=>_FWE
 | 10=>_FSV
 | 11=>_FSW
 | 12=>_FSX
 | 13=>_FSY
 | 14=>_FSZ
 | 15=>_FTA
 | 16=>_FTB
 | 17=>_FTC
 | 18=>_FTD
 | 19=>_FTE
 | 20=>_FTG
 | 21=>_FTH
 | 22=>_FTI
 | 23=>_FTJ
 | 24=>_FTK
 | 25=>_FTL
 | 26=>_FTM
 | 27=>_FTN
 | 28=>_FTO
 | 29=>_FTP
 | 30=>_FTR
 | 31=>_FTS
 | 32=>_FTT
 | 33=>_FTU
 | 34=>_FTV
 | 35=>_FTW
 | 36=>_FTX
 | 37=>_FTY
 | 38=>_FTZ
 | 39=>_FUA
 | 40=>_FUC
 | 41=>_FUD
 | 42=>_FUE
 | 43=>_FUF
 | 44=>_FUG
 | 45=>_FUH
 | 46=>_FUI
 | 47=>_FUJ
 | 48=>_FUK
 | 49=>_FUL
 | 50=>_FUN
 | 51=>_FUO
 | 52=>_FUP
 | 53=>_FUQ
 | 54=>_FUR
 | 55=>_FUS
 | 56=>_FUT
 | 57=>_FUU
 | 58=>_FUV
 | 59=>_FUW
 | 60=>_FUY
 | 61=>_FUZ
 | 62=>_FVA
 | 63=>_FVB
 | 64=>_FVC
 | 65=>_FVD
 | 66=>_FVE
 | 67=>_FVF
 | 68=>_FVG
 | 69=>_FVH
 | 70=>_FVJ
 | 71=>_FVK
 | 72=>_FVL
 | 73=>_FVM
 | 74=>_FVN
 | 75=>_FVO
 | 76=>_FVP
 | 77=>_FVQ
 | 78=>_FVR
 | 79=>_FVS
 | 80=>_FVU
 | 81=>_FVV
 | 82=>_FVW
 | 83=>_FVX
 | 84=>_FVY
 | 85=>_FVZ
 | 86=>_FWA
 | 87=>_FWB
 | 88=>_FWC
 | 89=>_FWD
 | 90=>_FWF
 | 91=>_FWG
 | 92=>_FWH
 | 93=>_FWI
 | 94=>_FWJ
 | 95=>_FWK
 | 96=>_FWL
 | 97=>_FWM
 | 98=>_FWN
 | 99=>_FWO
 | _=>[]
theorem checked18 (v:ℕ) (hy:18+v≤117):validFrom (11193-18-v) 0 (row18 v)=true:=by
 have hv:v≤99:=by omega
 interval_cases v
 · exact shape18_0
 · exact shape18_1
 · exact shape18_2
 · exact shape18_3
 · exact shape18_4
 · exact shape18_5
 · exact shape18_6
 · exact shape18_7
 · exact shape18_8
 · exact shape18_9
 · exact shape18_10
 · exact shape18_11
 · exact shape18_12
 · exact shape18_13
 · exact shape18_14
 · exact shape18_15
 · exact shape18_16
 · exact shape18_17
 · exact shape18_18
 · exact shape18_19
 · exact shape18_20
 · exact shape18_21
 · exact shape18_22
 · exact shape18_23
 · exact shape18_24
 · exact shape18_25
 · exact shape18_26
 · exact shape18_27
 · exact shape18_28
 · exact shape18_29
 · exact shape18_30
 · exact shape18_31
 · exact shape18_32
 · exact shape18_33
 · exact shape18_34
 · exact shape18_35
 · exact shape18_36
 · exact shape18_37
 · exact shape18_38
 · exact shape18_39
 · exact shape18_40
 · exact shape18_41
 · exact shape18_42
 · exact shape18_43
 · exact shape18_44
 · exact shape18_45
 · exact shape18_46
 · exact shape18_47
 · exact shape18_48
 · exact shape18_49
 · exact shape18_50
 · exact shape18_51
 · exact shape18_52
 · exact shape18_53
 · exact shape18_54
 · exact shape18_55
 · exact shape18_56
 · exact shape18_57
 · exact shape18_58
 · exact shape18_59
 · exact shape18_60
 · exact shape18_61
 · exact shape18_62
 · exact shape18_63
 · exact shape18_64
 · exact shape18_65
 · exact shape18_66
 · exact shape18_67
 · exact shape18_68
 · exact shape18_69
 · exact shape18_70
 · exact shape18_71
 · exact shape18_72
 · exact shape18_73
 · exact shape18_74
 · exact shape18_75
 · exact shape18_76
 · exact shape18_77
 · exact shape18_78
 · exact shape18_79
 · exact shape18_80
 · exact shape18_81
 · exact shape18_82
 · exact shape18_83
 · exact shape18_84
 · exact shape18_85
 · exact shape18_86
 · exact shape18_87
 · exact shape18_88
 · exact shape18_89
 · exact shape18_90
 · exact shape18_91
 · exact shape18_92
 · exact shape18_93
 · exact shape18_94
 · exact shape18_95
 · exact shape18_96
 · exact shape18_97
 · exact shape18_98
 · exact shape18_99
def _FWP:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015d3000000000003c384229b3718fc566d49095480821dd7aea814207f1a6ff7a8eab16310e9103c834fbdd20f5b0004
theorem shape19_0:validFrom 11174 0 _FWP=true:=by decide+kernel
def _FWQ:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015d2800000000003c390908586428755d549095480821dd9f0257d740d4a57f7a8eab16310e92e2d0795776f4f3b0004
theorem shape19_1:validFrom 11173 0 _FWQ=true:=by decide+kernel
def _FXB:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015d2000000000003c39cfe1b142552553949095480821ddc31a2e6c79b7a3f97a8eab16310e94c1d8bdb310c8f1b0004
theorem shape19_2:validFrom 11172 0 _FXB=true:=by decide+kernel
def _FXM:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015d1800000000003c3a96b5be0c183549d49095480821dde7320501b29aa26d7a8eab16310e96a0e1020eaa9cefb0004
theorem shape19_3:validFrom 11171 0 _FXM=true:=by decide+kernel
def _FXX:List Piece:=DZ.decode 62 41 0x6f05b59d3b2000015d1000000000003c3b5d847ec172553fcbd33aa8b0a1e132bc1756679fa20ebd33aa8b090f0735c1306b95850d2bd47558b1887810ff3d4a552328645ea3aac58c43be6b8e50812a2a430d49095480821de0af79941cb5d20dd7a8eab16310e987fe9466a4470eda0008
theorem shape19_4:validFrom 11170 0 _FXX=true:=by decide+kernel
def _FYI:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8400000000001e1e1226f9f24c2a9ae5e99d545850f09dfc0f7e119e50eb5e99d545848783b5cee8270a3485b5ea3aac58c43bdb5a6b1426193424949095480821de2f0f6fd704401f457a8eab16310e9a5ef18ac5de44eba0007
theorem shape19_5:validFrom 11169 0 _FYI=true:=by decide+kernel
def _FYT:List Piece:=DZ.decode 62 41 0x3782dace9d900000ae8000000000001e1e75890e388c7a95c5e99d545850f0a28257ea01d450cf5e99d545848783d52c6e178bdc84cdea3aac58c43bcfcc9f4ad6c9a417d49095480821de5327466c3d231da97a8eab16310e9c3df9cf217818e9a0007
theorem shape19_6:validFrom 11168 0 _FYT=true:=by decide+kernel
def _FZE:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b9f00000000000787b63a1f1d25d6a4217a675516143c29c80c75ebcbc42c97a675516121e0fd227d02036120f97a8eab16310e9e1d02137d11ed02c0005
theorem shape19_7:validFrom 11167 0 _FZE=true:=by decide+kernel
def _FZP:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b9e00000000000787cf1151299b34a2d17a675516143c2af56752c270142557a675516121e104f9de7e23cb20bf7a8eab16310e9ffc0a57d8abc0ff90005
theorem shape19_8:validFrom 11166 0 _FZP=true:=by decide+kernel
def _GAA:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b9d00000000000787e7e7d9b38338a1797a675516143c2c1cd355ddae341dd7a675516121e10c140c4fb92c20837a8eab16310ea1db129c344594fc40005
theorem shape19_9:validFrom 11165 0 _GAA=true:=by decide+kernel
def _FWR:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b9c0000000000078800bdb8badde2a0197a675516143c2d4a23b9683cc41657a675516121e1132e3a214e8d20477a8eab16310ea3ba1ae08fdf68f8f0005
theorem shape19_10:validFrom 11164 0 _FWR=true:=by decide+kernel
def _FWS:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b9b000000000007881992ee4ff0d29eb97a675516143c2e718543b561140ed7a675516121e119e9ce1d9e69a0097a8eab16310ea5992324eb793cf590005
theorem shape19_11:validFrom 11163 0 _FWS=true:=by decide+kernel
def _FWT:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b9a0000000000078832677a5230869d517a675516143c2fa4b4cc4428240717a675516121e12046c844a8c19fcb7a8eab16310ea7782b69471310f220005
theorem shape19_12:validFrom 11162 0 _FWT=true:=by decide+kernel
def _FWU:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b99000000000007884b3b5cd1e2de9be97a675516143c30d1f57a9992a3ff57a675516121e1264528966d951f8b7a8eab16310ea95733ada2ace4eea0005
theorem shape19_13:validFrom 11161 0 _FWU=true:=by decide+kernel
def _FWV:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b9800000000000788640e95cf07dc9a717a675516143c31ff30ed05e783f757a675516121e12be4ef12ece41f4b7a8eab16310eab363bf1fe46b8eb10005
theorem shape19_14:validFrom 11160 0 _FWV=true:=by decide+kernel
def _FWW:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b97000000000007887ce125499f8298f97a675516143c333250c05f86e3ef57a675516121e13184b58f6c331f097a8eab16310ead15443659e08ce780005
theorem shape19_15:validFrom 11159 0 _FWW=true:=by decide+kernel
def _FWX:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b960000000000078895b30b51ee3497817a675516143c34656b56d429c3e717a675516121e13667486160791ec77a8eab16310eaef44c7ab57a60e3d0005
theorem shape19_16:validFrom 11158 0 _FWX=true:=by decide+kernel
def _FWY:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b9500000000000788ae8447c76ae695f97a675516143c3510838ecbbfc3ded7a675516121e13b49db3354bf1e557a8eab16310eb0d354bf111434e020005
theorem shape19_17:validFrom 11157 0 _FWY=true:=by decide+kernel
def _FWZ:List Piece:=DZ.decode 62 41 0xde0b6b3a76400002b9400000000000788c754daba5a7a94717a675516143c35bb968a5c4843d657a675516121e13f6f3a5abdfc1de17a8eab16310eb2b25d036cae08dc50005
theorem shape19_18:validFrom 11156 0 _FWZ=true:=by decide+kernel
def _FXA:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9300000000000f11c0498855785525c5e99d545850f0d9e18484138acf37bd33aa8b090eeb7f8cafda20fceb8a484aa40410ee0165cdc31e27832d0005
theorem shape19_19:validFrom 11155 0 _FXA=true:=by decide+kernel
def _FXC:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9200000000000f11f1e80831218d2295e99d545850f0dcec406462c0cf14bd33aa8b090ee9603e3d75cb78e80a484aa40410ee1895de5fbca1022d0005
theorem shape19_20:validFrom 11154 0 _FXC=true:=by decide+kernel
def _FXD:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9100000000000f122385352836811f55e99d545850f0e00e8dc8672a8ef1bd33aa8b090ee3c718ccfb8fa0e490004
theorem shape19_21:validFrom 11153 0 _FXD=true:=by decide+kernel
def _FXE:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9000000000000f1255210ef9a9d91c05e99d545850f0c64640c857e78ecdbd33aa8b090ee66c80f8fa1a90cd80004
theorem shape19_22:validFrom 11152 0 _FXE=true:=by decide+kernel
def _FXF:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8f00000000000f1286bb95c6027918b5e99d545850f0c9c6fe1e696f0ea8bd33aa8b090ee7420130c1e90cca30004
theorem shape19_23:validFrom 11151 0 _FXF=true:=by decide+kernel
def _FXG:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8e00000000000f12b854c98d40691555e99d545850f0cd8e99e2d2df4e83bd33aa8b090ee817816889b788c6f0004
theorem shape19_24:validFrom 11150 0 _FXG=true:=by decide+kernel
def _FXH:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae34000000000078974f65527b20e88ede99d545850efb01543d9583a4e5d0003
theorem shape19_25:validFrom 11149 0 _FXH=true:=by decide+kernel
def _FXI:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae3000000000007898dc19c06364c872de99d545850efb8c22c0462690e370003
theorem shape19_26:validFrom 11148 0 _FXI=true:=by decide+kernel
def _FXJ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae2c0000000000789a68c39726e988565e99d545850efddf3b47e94110e100003
theorem shape19_27:validFrom 11147 0 _FXJ=true:=by decide+kernel
def _FXK:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae280000000000789bf562d4bd7e4838de99d545850efe736d64f42a68de80003
theorem shape19_28:validFrom 11146 0 _FXK=true:=by decide+kernel
def _FXL:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae240000000000789d81f77a2b3d481b5e99d545850eff3b0ee22decd0dbf0003
theorem shape19_29:validFrom 11145 0 _FXL=true:=by decide+kernel
def _FXN:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae200000000000789f0e81877026c7fd5e99d545850effa5cefe11d410d960003
theorem shape19_30:validFrom 11144 0 _FXN=true:=by decide+kernel
def _FXO:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae1c000000000078a09b00fc8c3a87de5e99d545850f00108f19f5bb50d6c0003
theorem shape19_31:validFrom 11143 0 _FXO=true:=by decide+kernel
def _FXP:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae18000000000078a22775da838507bf5e99d545850f007b4f35d9a290d410003
theorem shape19_32:validFrom 11142 0 _FXP=true:=by decide+kernel
def _FXQ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae14000000000078a3b3e01f4de9879f5e99d545850f00e60f51bd89d0d160003
theorem shape19_33:validFrom 11141 0 _FXQ=true:=by decide+kernel
def _FXR:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae10000000000078a5403fcbef78677ede99d545850f0150cf6da17110cea0003
theorem shape19_34:validFrom 11140 0 _FXR=true:=by decide+kernel
def _FXS:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae0c000000000078a6cc94e06831a75dde99d545850f01bb8f89855850cbc0003
theorem shape19_35:validFrom 11139 0 _FXS=true:=by decide+kernel
def _FXT:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae08000000000078a858df5cb80e673c5e99d545850f02264fa5693f90c8e0003
theorem shape19_36:validFrom 11138 0 _FXT=true:=by decide+kernel
def _FXU:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae04000000000078a9e51f41e3116719de99d545850f02910fc14d26d0c600003
theorem shape19_37:validFrom 11137 0 _FXU=true:=by decide+kernel
def _FXV:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae00000000000078ab71548de145a6f6de99d545850f02fbcfdd310e10c300003
theorem shape19_38:validFrom 11136 0 _FXV=true:=by decide+kernel
def _FXW:List Piece:=DZ.decode 62 39 0x3782dace9d900000adfc000000000078acfd7f41b6a426d35e99d545850f03668ff914f550bff0003
theorem shape19_39:validFrom 11135 0 _FXW=true:=by decide+kernel
def _FXY:List Piece:=DZ.decode 62 39 0x3782dace9d900000adf8000000000078ae899f5d6330e6aede99d545850f03d15014f8dc90bcd0003
theorem shape19_40:validFrom 11134 0 _FXY=true:=by decide+kernel
def _FXZ:List Piece:=DZ.decode 62 39 0x3782dace9d900000adf4000000000078b015b4e0e6e42689de99d545850f0476a639229a58b9b0003
theorem shape19_41:validFrom 11133 0 _FXZ=true:=by decide+kernel
def _FYA:List Piece:=DZ.decode 62 39 0x3782dace9d900000adf0000000000078b1a1bfcd45a38663de99d545850f051eefdcdcc1c0b670003
theorem shape19_42:validFrom 11132 0 _FYA=true:=by decide+kernel
def _FYB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f60f1665b8040ef4f4c7a0002
theorem shape19_43:validFrom 11131 0 _FYB=true:=by decide+kernel
def _FYC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f40f169736bb7019c4c2b0002
theorem shape19_44:validFrom 11130 0 _FYC=true:=by decide+kernel
def _FYD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f20f16c8b41fcc24d4bdb0002
theorem shape19_45:validFrom 11129 0 _FYD=true:=by decide+kernel
def _FYE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f00f16fa3031231530b890002
theorem shape19_46:validFrom 11128 0 _FYE=true:=by decide+kernel
def _FYF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ee0f172baaef74eb54b350002
theorem shape19_47:validFrom 11127 0 _FYF=true:=by decide+kernel
def _FYG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ec0f175d245ae21f9cadf0002
theorem shape19_48:validFrom 11126 0 _FYG=true:=by decide+kernel
def _FYH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ea0f178e9c7329bf5ca880002
theorem shape19_49:validFrom 11125 0 _FYH=true:=by decide+kernel
def _FYJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e80f17c013386c446ca2e0002
theorem shape19_50:validFrom 11124 0 _FYJ=true:=by decide+kernel
def _FYK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e60f17f188aaa9aebc9d30002
theorem shape19_51:validFrom 11123 0 _FYK=true:=by decide+kernel
def _FYL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e40f1822fcc9e1fd449760002
theorem shape19_52:validFrom 11122 0 _FYL=true:=by decide+kernel
def _FYM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e20f18546f9635a9149160002
theorem shape19_53:validFrom 11121 0 _FYM=true:=by decide+kernel
def _FYN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e00f1885e10f63c3488b50002
theorem shape19_54:validFrom 11120 0 _FYN=true:=by decide+kernel
def _FYO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056de0f18b751358cc24c8510002
theorem shape19_55:validFrom 11119 0 _FYO=true:=by decide+kernel
def _FYP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056dc0f18e8c008b0a6987ea0002
theorem shape19_56:validFrom 11118 0 _FYP=true:=by decide+kernel
def _FYQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056da0f191a2d88cf70307820002
theorem shape19_57:validFrom 11117 0 _FYQ=true:=by decide+kernel
def _FYR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d80f194b99b609938c7160002
theorem shape19_58:validFrom 11116 0 _FYR=true:=by decide+kernel
def _FYS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d60f197d04901e273c6a90002
theorem shape19_59:validFrom 11115 0 _FYS=true:=by decide+kernel
def _FYU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d40f19ae6e172da0386380002
theorem shape19_60:validFrom 11114 0 _FYU=true:=by decide+kernel
def _FYV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d20f19dfd64b37fdbc5c50002
theorem shape19_61:validFrom 11113 0 _FYV=true:=by decide+kernel
def _FYW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d00f1a113d2c3d414854e0002
theorem shape19_62:validFrom 11112 0 _FYW=true:=by decide+kernel
def _FYX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ce0f1a42a2ba5ddc304d50002
theorem shape19_63:validFrom 11111 0 _FYX=true:=by decide+kernel
def _FYY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056cc0f1a7406f558e9d44590002
theorem shape19_64:validFrom 11110 0 _FYY=true:=by decide+kernel
def _FYZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ca0f1aa569dd4edcc83d90002
theorem shape19_65:validFrom 11109 0 _FYZ=true:=by decide+kernel
def _FZA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c80f1ad6cb723fb5043560002
theorem shape19_66:validFrom 11108 0 _FZA=true:=by decide+kernel
def _FZB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c60f1b082bb42b728c2d00002
theorem shape19_67:validFrom 11107 0 _FZB=true:=by decide+kernel
def _FZC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c40f1b398aa31215d82460002
theorem shape19_68:validFrom 11106 0 _FZC=true:=by decide+kernel
def _FZD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c20f1b6ae83f140bbc1b90002
theorem shape19_69:validFrom 11105 0 _FZD=true:=by decide+kernel
def _FZF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c00f1b9c4487f078a41280002
theorem shape19_70:validFrom 11104 0 _FZF=true:=by decide+kernel
def _FZG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056be0f1bcd9f7dc7cad40930002
theorem shape19_71:validFrom 11103 0 _FZG=true:=by decide+kernel
def _FZH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7b3bbdb319185038a0f1bfe74302bf1d80020002
theorem shape19_72:validFrom 11102 0 _FZH=true:=by decide+kernel
def _FZI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad773bbcfa33cc354df0f1c2cad8332ac840020002
theorem shape19_73:validFrom 11101 0 _FZI=true:=by decide+kernel
def _FZJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad733bbc41536df90ff0f1c5ae59ac1bc040020002
theorem shape19_74:validFrom 11100 0 _FZJ=true:=by decide+kernel
def _FZK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6f3bbb8877fc981300f1c891c7719fb400020002
theorem shape19_75:validFrom 11099 0 _FZK=true:=by decide+kernel
def _FZL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6b3bbacfa17915bcf0f1cb75217fa90c40020002
theorem shape19_76:validFrom 11098 0 _FZL=true:=by decide+kernel
def _FZM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad673bba16cfe26eb3c0f1ce5867da453100020002
theorem shape19_77:validFrom 11097 0 _FZM=true:=by decide+kernel
def _FZN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad633bb95e0339a647a0f1d13b9a7d66e180020002
theorem shape19_78:validFrom 11096 0 _FZN=true:=by decide+kernel
def _FZO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5f3bb8a53b7db92630f1d41eb96d1b6740020002
theorem shape19_79:validFrom 11095 0 _FZO=true:=by decide+kernel
def _FZQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5b3bb7ec78afaaa3e0f1d701c4a5557080020002
theorem shape19_80:validFrom 11094 0 _FZQ=true:=by decide+kernel
def _FZR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad573bb733bace777020f1d9e4bc2a223f80020002
theorem shape19_81:validFrom 11093 0 _FZR=true:=by decide+kernel
def _FZS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad533bb67b01db22d7b0f1dcc79ff774a140020002
theorem shape19_82:validFrom 11092 0 _FZS=true:=by decide+kernel
def _FZT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4f3bb5c24dd52b3340f1dfaa700f533300020002
theorem shape19_83:validFrom 11091 0 _FZT=true:=by decide+kernel
def _FZU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4b3bb5099ebc0ee330f1e28d2c73c47340020002
theorem shape19_84:validFrom 11090 0 _FZU=true:=by decide+kernel
def _FZV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473bb450f490d12f10f1e56fd520bb43c0020002
theorem shape19_85:validFrom 11089 0 _FZV=true:=by decide+kernel
def _FZW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433bb3984f526eccc0f1e8526a1a44cd00020002
theorem shape19_86:validFrom 11088 0 _FZW=true:=by decide+kernel
def _FZX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3bb2dfaf01eafdf0f1eb34eb5c540840020002
theorem shape19_87:validFrom 11087 0 _FZX=true:=by decide+kernel
def _FZY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3bb227139e428960f1ee1758eaf5da80020002
theorem shape19_88:validFrom 11086 0 _FZY=true:=by decide+kernel
def _FZZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373bb16e7d2878a280f1f0f9b2c21d7600020002
theorem shape19_89:validFrom 11085 0 _FZZ=true:=by decide+kernel
def _GAB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333bb0b5eb9f8a1bb0f1f3dbf8e5d79140020002
theorem shape19_90:validFrom 11084 0 _GAB=true:=by decide+kernel
def _GAC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3baffd5f047a1eb0f1f6be2b52178540020002
theorem shape19_91:validFrom 11083 0 _GAC=true:=by decide+kernel
def _GAD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3baf44d756458590f1f9a04a0ae9e9c0020002
theorem shape19_92:validFrom 11082 0 _GAD=true:=by decide+kernel
def _GAE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273bae8c5495ef7260f1fc82550c423680020002
theorem shape19_93:validFrom 11081 0 _GAE=true:=by decide+kernel
def _GAF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233badd3d6c274ce10f1ff644c5a2cc7c0020002
theorem shape19_94:validFrom 11080 0 _GAF=true:=by decide+kernel
def _GAG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3bad1b5ddcd8a4d0f202462ff09d6cc0020002
theorem shape19_95:validFrom 11079 0 _GAG=true:=by decide+kernel
def _GAH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3bac62e9e417e740f20527ffd3a06300020002
theorem shape19_96:validFrom 11078 0 _GAH=true:=by decide+kernel
def _GAI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173babaa7ad935a7d0f20809bbff2960c0020002
theorem shape19_97:validFrom 11077 0 _GAI=true:=by decide+kernel
def _GAJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133baaf210bb2ed7f0f20aeb647744a040020002
theorem shape19_98:validFrom 11076 0 _GAJ=true:=by decide+kernel
def row19 (v:ℕ):List Piece:=match v with
 | 0=>_FWP
 | 1=>_FWQ
 | 2=>_FXB
 | 3=>_FXM
 | 4=>_FXX
 | 5=>_FYI
 | 6=>_FYT
 | 7=>_FZE
 | 8=>_FZP
 | 9=>_GAA
 | 10=>_FWR
 | 11=>_FWS
 | 12=>_FWT
 | 13=>_FWU
 | 14=>_FWV
 | 15=>_FWW
 | 16=>_FWX
 | 17=>_FWY
 | 18=>_FWZ
 | 19=>_FXA
 | 20=>_FXC
 | 21=>_FXD
 | 22=>_FXE
 | 23=>_FXF
 | 24=>_FXG
 | 25=>_FXH
 | 26=>_FXI
 | 27=>_FXJ
 | 28=>_FXK
 | 29=>_FXL
 | 30=>_FXN
 | 31=>_FXO
 | 32=>_FXP
 | 33=>_FXQ
 | 34=>_FXR
 | 35=>_FXS
 | 36=>_FXT
 | 37=>_FXU
 | 38=>_FXV
 | 39=>_FXW
 | 40=>_FXY
 | 41=>_FXZ
 | 42=>_FYA
 | 43=>_FYB
 | 44=>_FYC
 | 45=>_FYD
 | 46=>_FYE
 | 47=>_FYF
 | 48=>_FYG
 | 49=>_FYH
 | 50=>_FYJ
 | 51=>_FYK
 | 52=>_FYL
 | 53=>_FYM
 | 54=>_FYN
 | 55=>_FYO
 | 56=>_FYP
 | 57=>_FYQ
 | 58=>_FYR
 | 59=>_FYS
 | 60=>_FYU
 | 61=>_FYV
 | 62=>_FYW
 | 63=>_FYX
 | 64=>_FYY
 | 65=>_FYZ
 | 66=>_FZA
 | 67=>_FZB
 | 68=>_FZC
 | 69=>_FZD
 | 70=>_FZF
 | 71=>_FZG
 | 72=>_FZH
 | 73=>_FZI
 | 74=>_FZJ
 | 75=>_FZK
 | 76=>_FZL
 | 77=>_FZM
 | 78=>_FZN
 | 79=>_FZO
 | 80=>_FZQ
 | 81=>_FZR
 | 82=>_FZS
 | 83=>_FZT
 | 84=>_FZU
 | 85=>_FZV
 | 86=>_FZW
 | 87=>_FZX
 | 88=>_FZY
 | 89=>_FZZ
 | 90=>_GAB
 | 91=>_GAC
 | 92=>_GAD
 | 93=>_GAE
 | 94=>_GAF
 | 95=>_GAG
 | 96=>_GAH
 | 97=>_GAI
 | 98=>_GAJ
 | _=>[]
theorem checked19 (v:ℕ) (hy:19+v≤117):validFrom (11193-19-v) 0 (row19 v)=true:=by
 have hv:v≤98:=by omega
 interval_cases v
 · exact shape19_0
 · exact shape19_1
 · exact shape19_2
 · exact shape19_3
 · exact shape19_4
 · exact shape19_5
 · exact shape19_6
 · exact shape19_7
 · exact shape19_8
 · exact shape19_9
 · exact shape19_10
 · exact shape19_11
 · exact shape19_12
 · exact shape19_13
 · exact shape19_14
 · exact shape19_15
 · exact shape19_16
 · exact shape19_17
 · exact shape19_18
 · exact shape19_19
 · exact shape19_20
 · exact shape19_21
 · exact shape19_22
 · exact shape19_23
 · exact shape19_24
 · exact shape19_25
 · exact shape19_26
 · exact shape19_27
 · exact shape19_28
 · exact shape19_29
 · exact shape19_30
 · exact shape19_31
 · exact shape19_32
 · exact shape19_33
 · exact shape19_34
 · exact shape19_35
 · exact shape19_36
 · exact shape19_37
 · exact shape19_38
 · exact shape19_39
 · exact shape19_40
 · exact shape19_41
 · exact shape19_42
 · exact shape19_43
 · exact shape19_44
 · exact shape19_45
 · exact shape19_46
 · exact shape19_47
 · exact shape19_48
 · exact shape19_49
 · exact shape19_50
 · exact shape19_51
 · exact shape19_52
 · exact shape19_53
 · exact shape19_54
 · exact shape19_55
 · exact shape19_56
 · exact shape19_57
 · exact shape19_58
 · exact shape19_59
 · exact shape19_60
 · exact shape19_61
 · exact shape19_62
 · exact shape19_63
 · exact shape19_64
 · exact shape19_65
 · exact shape19_66
 · exact shape19_67
 · exact shape19_68
 · exact shape19_69
 · exact shape19_70
 · exact shape19_71
 · exact shape19_72
 · exact shape19_73
 · exact shape19_74
 · exact shape19_75
 · exact shape19_76
 · exact shape19_77
 · exact shape19_78
 · exact shape19_79
 · exact shape19_80
 · exact shape19_81
 · exact shape19_82
 · exact shape19_83
 · exact shape19_84
 · exact shape19_85
 · exact shape19_86
 · exact shape19_87
 · exact shape19_88
 · exact shape19_89
 · exact shape19_90
 · exact shape19_91
 · exact shape19_92
 · exact shape19_93
 · exact shape19_94
 · exact shape19_95
 · exact shape19_96
 · exact shape19_97
 · exact shape19_98
def _GEX:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba500000000000f0f42775af182dd4595e99d545850f0aa6f11811b9350a5bd33aa8b090ef889c25b06dcc506da484aa40410ecc126efb10b1c0ae40005
theorem shape20_0:validFrom 11173 0 _GEX=true:=by decide+kernel
def _GEY:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba400000000000f0f733bf7c072a542e5e99d545850f0aee6925b97949088bd33aa8b090ef6f565d9e0a1dd04fa484aa40410ecd857004da9958a130005
theorem shape20_1:validFrom 11172 0 _GEY=true:=by decide+kernel
def _GFJ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba300000000000f0fa3ff459522294035e99d545850f0b38d4b6dcfa2906abd33aa8b090ef55b1fbb660ead032a484aa40410ecef8710ea480f09400005
theorem shape20_2:validFrom 11171 0 _GFJ=true:=by decide+kernel
def _GFU:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba200000000000f0fd4c144500e513d85e99d545850f0b81c4957cf95504dbd33aa8b090ef3b7fb30ecf711013a484aa40410ed06b72186e688886a0005
theorem shape20_3:validFrom 11170 0 _GFU=true:=by decide+kernel
def _GGF:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba100000000000f100581f3d1b5953ac5e99d545850f0bcab3290d01a502ebd33aa8b090ef20bf83a755b08ff4a484aa40410ed1de73223850207910005
theorem shape20_4:validFrom 11169 0 _GGF=true:=by decide+kernel
def _GGQ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba000000000000f10364154591b2937f5e99d545850f0c151ad8a53fed00fbd33aa8b090ef05716d7ff3a94fd5a484aa40410ed351742c0237b86b50005
theorem shape20_5:validFrom 11168 0 _GGQ=true:=by decide+kernel
def _GHB:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9f00000000000f1066ff65c6bd493525e99d545850f0c60fba4642970ff0bd33aa8b090eee96623ae06990fb6a484aa40410ed4c47535cc1f505d50005
theorem shape20_6:validFrom 11167 0 _GHB=true:=by decide+kernel
def _GHM:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9e00000000000f1097bc27fb1ba13245e99d545850f0cab60bd9f912cfd1bd33aa8b090eeccfc4006d4044f96a484aa40410ed637763f9606e84f30005
theorem shape20_7:validFrom 11166 0 _GHM=true:=by decide+kernel
def _GHX:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9d00000000000f10c8779b35374d2f55e99d545850f0cf5c48bac8e90fb1bd33aa8b090eeb004759fb928cf75a484aa40410ed7aa77495fee8040e0005
theorem shape20_8:validFrom 11165 0 _GHX=true:=by decide+kernel
def _GII:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9c00000000000f10f931bf558f812c65e99d545850f0d41a175fea7a0f90bd33aa8b090ee924f778e13444f54a484aa40410ed91d785329d6183250005
theorem shape20_9:validFrom 11164 0 _GII=true:=by decide+kernel
def _GEZ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9b00000000000f1129ea943ca5bd2965e99d545850f0d7eb50bb106e8f6fbd33aa8b090ee743bdfa727db4f29a484aa40410eda90795cf3bdb023a0005
theorem shape20_10:validFrom 11163 0 _GEZ=true:=by decide+kernel
def _GFA:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9a00000000000f115aa21a29777d2665e99d545850f0da59b4838af44f4ebd33aa8b090ee553bc72b0ea70eeea484aa40410edc037a66bda54814a0005
theorem shape20_11:validFrom 11162 0 _GFA=true:=by decide+kernel
def _GFB:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9900000000000f118b5850fc85c52345e99d545850f0dcdfaa0e702f8f2cbd33aa8b090ee35dd14d9afee4eb3a484aa40410edd767b70878ce00580005
theorem shape20_12:validFrom 11161 0 _GFB=true:=by decide+kernel
def _GFC:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9800000000000f11bc0d389652fd2025e99d545850f0df7d315bc00f8f09bd33aa8b090ee32f2a7ae3a100e790004
theorem shape20_13:validFrom 11160 0 _GFC=true:=by decide+kernel
def _GFD:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9700000000000f11ecc0d135dacd1d05e99d545850f0e249f0e0cc068ee7bd33aa8b090ee404aab2ab6f7ce400004
theorem shape20_14:validFrom 11159 0 _GFD=true:=by decide+kernel
def _GFE:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9600000000000f121d731abb9f2919c5e99d545850f0e545e89f7b03cec3bd33aa8b090ee4da2aea733df8e080004
theorem shape20_15:validFrom 11158 0 _GFE=true:=by decide+kernel
def _GFF:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9500000000000f124e24150824651685e99d545850f0e8711893ff07ce9fbd33aa8b090ee5afab223b0c74dd10004
theorem shape20_16:validFrom 11157 0 _GFF=true:=by decide+kernel
def _GFG:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9400000000000f127ed3c05a62351335e99d545850f0ebcb80c03f234e7bbd33aa8b090ee6852b5a02daf0d9b0004
theorem shape20_17:validFrom 11156 0 _GFG=true:=by decide+kernel
def _GFH:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9300000000000f12af821c92dca50fd5e99d545850f0ef25d43998810e56bd33aa8b090ee75aab91caa96cd650004
theorem shape20_18:validFrom 11155 0 _GFH=true:=by decide+kernel
def _GFI:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9200000000000f12e02f299219550c65e99d545850f0f2c7065fff588e30bd33aa8b090ee8302bc99277e8d300004
theorem shape20_19:validFrom 11154 0 _GFI=true:=by decide+kernel
def _GFK:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9100000000000f1310dae7970cb508e5e99d545850f0f67fca48d0d30e0abd33aa8b090ee905ac015a4664cfc0004
theorem shape20_20:validFrom 11153 0 _GFK=true:=by decide+kernel
def _GFL:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9000000000000f13418556823d3d0565e99d545850f0f772f7c119034de3bd33aa8b090eea0b22b0d77f54ca90004
theorem shape20_21:validFrom 11152 0 _GFL=true:=by decide+kernel
def _GFM:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8f00000000000f13722e7634316d01d5e99d545850f0fb7285a41131cdbcbd33aa8b090eeae0a2e89f4dd0c760004
theorem shape20_22:validFrom 11151 0 _GFM=true:=by decide+kernel
def _GFN:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8e00000000000f13a2d646ebdb80fe35e99d545850f0ffb8f23416e20d94bd33aa8b090eebb62320671c4cc450004
theorem shape20_23:validFrom 11150 0 _GFN=true:=by decide+kernel
def _GFO:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8d00000000000f13d37cc889c1e4fa75e99d545850f1042e96fbd88e8d6bbd33aa8b090eec8ba3582eeac8c150004
theorem shape20_24:validFrom 11149 0 _GFO=true:=by decide+kernel
def _GFP:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae30000000000078a0210fd7736c87b5de99d545850eff1bd322f3b430d420003
theorem shape20_25:validFrom 11148 0 _GFP=true:=by decide+kernel
def _GFQ:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae2c000000000078a1a62ef2c66dc7975e99d545850eff86933ed79b70d180003
theorem shape20_26:validFrom 11147 0 _GFQ=true:=by decide+kernel
def _GFR:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae28000000000078a32b43954b4d87785e99d545850f00194c3fbbdab4ced0003
theorem shape20_27:validFrom 11146 0 _GFR=true:=by decide+kernel
def _GFS:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae24000000000078a4b04dbe0666a758de99d545850f00ad7e5cc6c40ccc20003
theorem shape20_28:validFrom 11145 0 _GFS=true:=by decide+kernel
def _GFT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057100f14c6a9addde310e710002
theorem shape20_29:validFrom 11144 0 _GFT=true:=by decide+kernel
def _GFV:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570e0f14f74854e13510e300002
theorem shape20_30:validFrom 11143 0 _GFV=true:=by decide+kernel
def _GFW:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570c0f1527e5acab4fb8ded0002
theorem shape20_31:validFrom 11142 0 _GFW=true:=by decide+kernel
def _GFX:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570a0f155881b57b1c80daa0002
theorem shape20_32:validFrom 11141 0 _GFX=true:=by decide+kernel
def _GFY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057080f15891c6f312558d650002
theorem shape20_33:validFrom 11140 0 _GFY=true:=by decide+kernel
def _GFZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057060f15b9b5d9adf6a4d200002
theorem shape20_34:validFrom 11139 0 _GFZ=true:=by decide+kernel
def _GGA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057040f15ea4df5307908cd90002
theorem shape20_35:validFrom 11138 0 _GGA=true:=by decide+kernel
def _GGB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057020f161ae4c19937f8c900002
theorem shape20_36:validFrom 11137 0 _GGB=true:=by decide+kernel
def _GGC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057000f164b7a3ec8c0b8c470002
theorem shape20_37:validFrom 11136 0 _GGC=true:=by decide+kernel
def _GGD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fe0f167c0e6cfdf92cbfc0002
theorem shape20_38:validFrom 11135 0 _GGD=true:=by decide+kernel
def _GGE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fc0f16aca14c196ea8bb00002
theorem shape20_39:validFrom 11134 0 _GGE=true:=by decide+kernel
def _GGG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fa0f16dd32dbfbafc8b620002
theorem shape20_40:validFrom 11133 0 _GGG=true:=by decide+kernel
def _GGH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f80f170dc31ce39d64b130002
theorem shape20_41:validFrom 11132 0 _GGH=true:=by decide+kernel
def _GGI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f60f173e520eb1c878ac20002
theorem shape20_42:validFrom 11131 0 _GGI=true:=by decide+kernel
def _GGJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f40f176edfb146c114a700002
theorem shape20_43:validFrom 11130 0 _GGJ=true:=by decide+kernel
def _GGK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f20f179f6c04e164b8a1c0002
theorem shape20_44:validFrom 11129 0 _GGK=true:=by decide+kernel
def _GGL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f00f17cff7096245e49c70002
theorem shape20_45:validFrom 11128 0 _GGL=true:=by decide+kernel
def _GGM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ee0f180080bea9f6749700002
theorem shape20_46:validFrom 11127 0 _GGM=true:=by decide+kernel
def _GGN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ec0f18310924f750209180002
theorem shape20_47:validFrom 11126 0 _GGN=true:=by decide+kernel
def _GGO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ea0f1861903c2ae7608bd0002
theorem shape20_48:validFrom 11125 0 _GGO=true:=by decide+kernel
def _GGP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e80f18921604254ef48610002
theorem shape20_49:validFrom 11124 0 _GGP=true:=by decide+kernel
def _GGR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e60f18c29a7d255fc08030002
theorem shape20_50:validFrom 11123 0 _GGR=true:=by decide+kernel
def _GGS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e40f18f31da70bac007a30002
theorem shape20_51:validFrom 11122 0 _GGS=true:=by decide+kernel
def _GGT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e20f19239f81b8cb087410002
theorem shape20_52:validFrom 11121 0 _GGT=true:=by decide+kernel
def _GGU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e00f1954200d6b92646dd0002
theorem shape20_53:validFrom 11120 0 _GGU=true:=by decide+kernel
def _GGV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056de0f19849f4a0494a86770002
theorem shape20_54:validFrom 11119 0 _GGV=true:=by decide+kernel
def _GGW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056dc0f19b51d37646b3460f0002
theorem shape20_55:validFrom 11118 0 _GGW=true:=by decide+kernel
def _GGX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056da0f19e599d5c9e82c5a40002
theorem shape20_56:validFrom 11117 0 _GGX=true:=by decide+kernel
def _GGY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d80f1a16152515a0745370002
theorem shape20_57:validFrom 11116 0 _GGY=true:=by decide+kernel
def _GGZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d60f1a468f25282e7c4c80002
theorem shape20_58:validFrom 11115 0 _GGZ=true:=by decide+kernel
def _GHA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d40f1a7707d64061884560002
theorem shape20_59:validFrom 11114 0 _GHA=true:=by decide+kernel
def _GHC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d20f1aa77f383ed1943e20002
theorem shape20_60:validFrom 11113 0 _GHC=true:=by decide+kernel
def _GHD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d00f1ad7f54b0415d836b0002
theorem shape20_61:validFrom 11112 0 _GHD=true:=by decide+kernel
def _GHE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ce0f1b086a0ecefef42f10002
theorem shape20_62:validFrom 11111 0 _GHE=true:=by decide+kernel
def _GHF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056cc0f1b38dd838024a02750002
theorem shape20_63:validFrom 11110 0 _GHF=true:=by decide+kernel
def _GHG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ca0f1b694fa8f820541f50002
theorem shape20_64:validFrom 11109 0 _GHG=true:=by decide+kernel
def _GHH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c80f1b99c07f75bf881730002
theorem shape20_65:validFrom 11108 0 _GHH=true:=by decide+kernel
def _GHI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c60f1bca3006d99b400ed0002
theorem shape20_66:validFrom 11107 0 _GHI=true:=by decide+kernel
def _GHJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056c40f1bfa9e3f044fc00640002
theorem shape20_67:validFrom 11106 0 _GHJ=true:=by decide+kernel
def _GHK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad873bbd00bd382d6f70f1c2b0b2834a4240020002
theorem shape20_68:validFrom 11105 0 _GHK=true:=by decide+kernel
def _GHL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad833bbc3f0ecfd32820f1c5b76c24b35f80020002
theorem shape20_69:validFrom 11104 0 _GHL=true:=by decide+kernel
def _GHN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7f3bbb7d65a45d7830f1c8be10d28a1f40020002
theorem shape20_70:validFrom 11103 0 _GHN=true:=by decide+kernel
def _GHO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7b3bbabdc320724250f1cbbc9ae236f6c0020002
theorem shape20_71:validFrom 11102 0 _GHO=true:=by decide+kernel
def _GHP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad773bba08322c229670f1ce92deb375a640020002
theorem shape20_72:validFrom 11101 0 _GHP=true:=by decide+kernel
def _GHQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad733bb952a6194427b0f1d1690efeef6140020002
theorem shape20_73:validFrom 11100 0 _GHQ=true:=by decide+kernel
def _GHR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6f3bb89d1ee6dbee80f1d43f2bc8904600020002
theorem shape20_74:validFrom 11099 0 _GHR=true:=by decide+kernel
def _GHS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6b3bb7e79c95e4e700f1d715350c6c6400020002
theorem shape20_75:validFrom 11098 0 _GHS=true:=by decide+kernel
def _GHT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad673bb7321f256414d0f1d9eb2ace6facc0020002
theorem shape20_76:validFrom 11097 0 _GHT=true:=by decide+kernel
def _GHU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad633bb67ca696547650f1dcc10d0aae26c0020002
theorem shape20_77:validFrom 11096 0 _GHU=true:=by decide+kernel
def _GHV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5f3bb5c732e7bb1700f1df96dbc513a400020002
theorem shape20_78:validFrom 11095 0 _GHV=true:=by decide+kernel
def _GHW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5b3bb511c41a92e190f1e26c96f9b479c0020002
theorem shape20_79:validFrom 11094 0 _GHW=true:=by decide+kernel
def _GHY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad573bb45c5a2de0e910f1e5423eac7c5bc0020002
theorem shape20_80:validFrom 11093 0 _GHY=true:=by decide+kernel
def _GHZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad533bb3a6f522a02300f1e817d2d97f7400020002
theorem shape20_81:validFrom 11092 0 _GHZ=true:=by decide+kernel
def _GIA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4f3bb2f194f8530a50f1eaed5382b3d6c0020002
theorem shape20_82:validFrom 11091 0 _GIA=true:=by decide+kernel
def _GIB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4b3bb23c39ae7c3410f1edc2c0aa0f2fc0020002
theorem shape20_83:validFrom 11090 0 _GIB=true:=by decide+kernel
def _GIC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473bb186e346168ae0f1f0981a4ba5d480020002
theorem shape20_84:validFrom 11089 0 _GIC=true:=by decide+kernel
def _GID:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433bb0d191be272180f1f36d606b637a00020002
theorem shape20_85:validFrom 11088 0 _GID=true:=by decide+kernel
def _GIE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3bb01c4517a8dcd0f1f64293055c8cc0020002
theorem shape20_86:validFrom 11087 0 _GIE=true:=by decide+kernel
def _GIF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3baf66fd51a0e030f1f917b21d7c7f40020002
theorem shape20_87:validFrom 11086 0 _GIF=true:=by decide+kernel
def _GIG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373baeb1ba6d0a0960f1fbecbdafd7da80020002
theorem shape20_88:validFrom 11085 0 _GIG=true:=by decide+kernel
def _GIH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333badfc7c68e979a0f1fec1b5c05a1980020002
theorem shape20_89:validFrom 11084 0 _GIH=true:=by decide+kernel
def _GIJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3bad4743463a0540f201969a4b17eb00020002
theorem shape20_90:validFrom 11083 0 _GIJ=true:=by decide+kernel
def _GIK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3bac920f0400e930f2046b6b53fc5b40020002
theorem shape20_91:validFrom 11082 0 _GIK=true:=by decide+kernel
def _GIL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273babdcdfa338dde0f2074028d71c8880020002
theorem shape20_92:validFrom 11081 0 _GIL=true:=by decide+kernel
def _GIM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233bab27b522e727c0f20a14d2d8636100020002
theorem shape20_93:validFrom 11080 0 _GIM=true:=by decide+kernel
def _GIN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3baa728f84068580f20ce96953e5ea00020002
theorem shape20_94:validFrom 11079 0 _GIN=true:=by decide+kernel
def _GIO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3ba9bd6ec59c4350f20fbdec4d8ef2c0020002
theorem shape20_95:validFrom 11078 0 _GIO=true:=by decide+kernel
def _GIP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173ba90852e8a30a20f212925bc173d780020002
theorem shape20_96:validFrom 11077 0 _GIP=true:=by decide+kernel
def _GIQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133ba8533bec202da0f21566b7b37f4980020002
theorem shape20_97:validFrom 11076 0 _GIQ=true:=by decide+kernel
def row20 (v:ℕ):List Piece:=match v with
 | 0=>_GEX
 | 1=>_GEY
 | 2=>_GFJ
 | 3=>_GFU
 | 4=>_GGF
 | 5=>_GGQ
 | 6=>_GHB
 | 7=>_GHM
 | 8=>_GHX
 | 9=>_GII
 | 10=>_GEZ
 | 11=>_GFA
 | 12=>_GFB
 | 13=>_GFC
 | 14=>_GFD
 | 15=>_GFE
 | 16=>_GFF
 | 17=>_GFG
 | 18=>_GFH
 | 19=>_GFI
 | 20=>_GFK
 | 21=>_GFL
 | 22=>_GFM
 | 23=>_GFN
 | 24=>_GFO
 | 25=>_GFP
 | 26=>_GFQ
 | 27=>_GFR
 | 28=>_GFS
 | 29=>_GFT
 | 30=>_GFV
 | 31=>_GFW
 | 32=>_GFX
 | 33=>_GFY
 | 34=>_GFZ
 | 35=>_GGA
 | 36=>_GGB
 | 37=>_GGC
 | 38=>_GGD
 | 39=>_GGE
 | 40=>_GGG
 | 41=>_GGH
 | 42=>_GGI
 | 43=>_GGJ
 | 44=>_GGK
 | 45=>_GGL
 | 46=>_GGM
 | 47=>_GGN
 | 48=>_GGO
 | 49=>_GGP
 | 50=>_GGR
 | 51=>_GGS
 | 52=>_GGT
 | 53=>_GGU
 | 54=>_GGV
 | 55=>_GGW
 | 56=>_GGX
 | 57=>_GGY
 | 58=>_GGZ
 | 59=>_GHA
 | 60=>_GHC
 | 61=>_GHD
 | 62=>_GHE
 | 63=>_GHF
 | 64=>_GHG
 | 65=>_GHH
 | 66=>_GHI
 | 67=>_GHJ
 | 68=>_GHK
 | 69=>_GHL
 | 70=>_GHN
 | 71=>_GHO
 | 72=>_GHP
 | 73=>_GHQ
 | 74=>_GHR
 | 75=>_GHS
 | 76=>_GHT
 | 77=>_GHU
 | 78=>_GHV
 | 79=>_GHW
 | 80=>_GHY
 | 81=>_GHZ
 | 82=>_GIA
 | 83=>_GIB
 | 84=>_GIC
 | 85=>_GID
 | 86=>_GIE
 | 87=>_GIF
 | 88=>_GIG
 | 89=>_GIH
 | 90=>_GIJ
 | 91=>_GIK
 | 92=>_GIL
 | 93=>_GIM
 | 94=>_GIN
 | 95=>_GIO
 | 96=>_GIP
 | 97=>_GIQ
 | _=>[]
theorem checked20 (v:ℕ) (hy:20+v≤117):validFrom (11193-20-v) 0 (row20 v)=true:=by
 have hv:v≤97:=by omega
 interval_cases v
 · exact shape20_0
 · exact shape20_1
 · exact shape20_2
 · exact shape20_3
 · exact shape20_4
 · exact shape20_5
 · exact shape20_6
 · exact shape20_7
 · exact shape20_8
 · exact shape20_9
 · exact shape20_10
 · exact shape20_11
 · exact shape20_12
 · exact shape20_13
 · exact shape20_14
 · exact shape20_15
 · exact shape20_16
 · exact shape20_17
 · exact shape20_18
 · exact shape20_19
 · exact shape20_20
 · exact shape20_21
 · exact shape20_22
 · exact shape20_23
 · exact shape20_24
 · exact shape20_25
 · exact shape20_26
 · exact shape20_27
 · exact shape20_28
 · exact shape20_29
 · exact shape20_30
 · exact shape20_31
 · exact shape20_32
 · exact shape20_33
 · exact shape20_34
 · exact shape20_35
 · exact shape20_36
 · exact shape20_37
 · exact shape20_38
 · exact shape20_39
 · exact shape20_40
 · exact shape20_41
 · exact shape20_42
 · exact shape20_43
 · exact shape20_44
 · exact shape20_45
 · exact shape20_46
 · exact shape20_47
 · exact shape20_48
 · exact shape20_49
 · exact shape20_50
 · exact shape20_51
 · exact shape20_52
 · exact shape20_53
 · exact shape20_54
 · exact shape20_55
 · exact shape20_56
 · exact shape20_57
 · exact shape20_58
 · exact shape20_59
 · exact shape20_60
 · exact shape20_61
 · exact shape20_62
 · exact shape20_63
 · exact shape20_64
 · exact shape20_65
 · exact shape20_66
 · exact shape20_67
 · exact shape20_68
 · exact shape20_69
 · exact shape20_70
 · exact shape20_71
 · exact shape20_72
 · exact shape20_73
 · exact shape20_74
 · exact shape20_75
 · exact shape20_76
 · exact shape20_77
 · exact shape20_78
 · exact shape20_79
 · exact shape20_80
 · exact shape20_81
 · exact shape20_82
 · exact shape20_83
 · exact shape20_84
 · exact shape20_85
 · exact shape20_86
 · exact shape20_87
 · exact shape20_88
 · exact shape20_89
 · exact shape20_90
 · exact shape20_91
 · exact shape20_92
 · exact shape20_93
 · exact shape20_94
 · exact shape20_95
 · exact shape20_96
 · exact shape20_97
def _GIR:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba400000000000f10727f834b9f212d85e99d545850f0cf8460af53e20faebd33aa8b090ee2168e97910f0cf70a484aa40410ed3c68e7533bc601520005
theorem shape21_0:validFrom 11172 0 _GIR=true:=by decide+kernel
def _GIS:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba300000000000f10a2511ba1fdf52aa5e99d545850f0d433a51e12980f8ebd33aa8b090ee052e52bc811e4f50a484aa40410ed5398f7efda3f80710005
theorem shape21_1:validFrom 11171 0 _GIS=true:=by decide+kernel
def _GJD:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba200000000000f10d22168c9f16d27b5e99d545850f0d8cb2ea5252b8f6dbd33aa8b090edfda562a72647cf2f0004
theorem shape21_2:validFrom 11170 0 _GJD=true:=by decide+kernel
def _GJO:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba100000000000f1101f06ac3794524b5e99d545850f0dd62a3b63017cf4dbd33aa8b090ee0afd6623a32f8f0d0004
theorem shape21_3:validFrom 11169 0 _GJO=true:=by decide+kernel
def _GJZ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba000000000000f1131be21ad0a4121b5e99d545850f0e229513f82f1cf2bbd33aa8b090ee185569a020174eec0004
theorem shape21_4:validFrom 11168 0 _GJZ=true:=by decide+kernel
def _GKK:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9f00000000000f11618a8d49bb211ea5e99d545850f0e6c09d682b690f09bd33aa8b090ee25ad6d1c9cff0ec90004
theorem shape21_5:validFrom 11167 0 _GKK=true:=by decide+kernel
def _GKV:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9e00000000000f119155adb801291b85e99d545850f0eb8722091bcd4ee7bd33aa8b090ee3305709919e6cea70004
theorem shape21_6:validFrom 11166 0 _GKV=true:=by decide+kernel
def _GLG:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9d00000000000f11c11f82f7db7d1865e99d545850f0f035ebc0898ecec4bd33aa8b090ee405d741596ce8e840004
theorem shape21_7:validFrom 11165 0 _GLG=true:=by decide+kernel
def _GLR:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9c00000000000f11f0e80d094b791535e99d545850f0f456ba42076f8ea1bd33aa8b090ee4db5779213b64e590004
theorem shape21_8:validFrom 11164 0 _GLR=true:=by decide+kernel
def _GMC:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9b00000000000f1220af4c0ac10d11f5e99d545850f0f744005c08844e7ebd33aa8b090ee5b0d7b0e909e0e210004
theorem shape21_9:validFrom 11163 0 _GMC=true:=by decide+kernel
def _GIT:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9a00000000000f1250753fbf59a10eb5e99d545850f0fa198b8ab0a58e5abd33aa8b090ee68657e8b0d85cde80004
theorem shape21_10:validFrom 11162 0 _GIT=true:=by decide+kernel
def _GIU:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9900000000000f128039e84586750b65e99d545850f0fd4d9c1c4359ce35bd33aa8b090ee75bd82078a6d8db10004
theorem shape21_11:validFrom 11161 0 _GIU=true:=by decide+kernel
def _GIV:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9800000000000f12affd459d488d0805e99d545850f100819837ce99ce10bd33aa8b090ee8315858407554d7a0004
theorem shape21_12:validFrom 11160 0 _GIV=true:=by decide+kernel
def _GIW:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9700000000000f12dfbf57c69edd04a5e99d545850f103e4cccba1944deabd33aa8b090ee906d8900843d0d440004
theorem shape21_13:validFrom 11159 0 _GIW=true:=by decide+kernel
def _GIX:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9600000000000f130f801ec18a750135e99d545850f1078ee04961434dc4bd33aa8b090ee9dc58c7d0124cd100004
theorem shape21_14:validFrom 11158 0 _GIX=true:=by decide+kernel
def _GIY:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9500000000000f133f3f9aac7a48fdb5e99d545850f10b2138df748ccd9ebd33aa8b090eeab1d8ff97e0c8cdb0004
theorem shape21_15:validFrom 11157 0 _GIY=true:=by decide+kernel
def _GIZ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9400000000000f136efdcb4a8e60fa25e99d545850f10f1216d4c5f18d77bd33aa8b090eeb8759375faf44ca80004
theorem shape21_16:validFrom 11156 0 _GIZ=true:=by decide+kernel
def _GJA:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9300000000000f139ebab0ba37c8f685e99d545850f11302e057bc440d4fbd33aa8b090eec5cd96f277dc0c750004
theorem shape21_17:validFrom 11155 0 _GJA=true:=by decide+kernel
def _GJB:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9200000000000f13ce764afb7554f2e5e99d545850f1173a88c49f5e0d26bd33aa8b090eed3259a6ef4c3cc440004
theorem shape21_18:validFrom 11154 0 _GJB=true:=by decide+kernel
def _GJC:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9100000000000f13fe309a0e4840ef25e99d545850f11b89c33478af8cfebd33aa8b090eee07d9deb71ab8c130004
theorem shape21_19:validFrom 11153 0 _GJC=true:=by decide+kernel
def _GJE:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9000000000000f142de99df2af48eb65e99d545850f120083618ed890cd4bd33aa8b090eeedd5a167ee934be30004
theorem shape21_20:validFrom 11152 0 _GJE=true:=by decide+kernel
def _GJF:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b8f00000000000f145da156c71804e795e99d545850f12486948b07208caabd33aa8b090eefb2da4e46b7b0bb30004
theorem shape21_21:validFrom 11151 0 _GJF=true:=by decide+kernel
def _GJG:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae38000000000078a46abe227540871dde99d545850f018f2f2e9e9c00c7f0003
theorem shape21_22:validFrom 11150 0 _GJG=true:=by decide+kernel
def _GJH:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae34000000000078a5e867353e6fe6fe5e99d545850f0222751d2d745cc540003
theorem shape21_23:validFrom 11149 0 _GJH=true:=by decide+kernel
def _GJI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057180f14ecc0bdd28784dbc0002
theorem shape21_24:validFrom 11148 0 _GJI=true:=by decide+kernel
def _GJJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057160f151c7349ced680d7c0002
theorem shape21_25:validFrom 11147 0 _GJJ=true:=by decide+kernel
def _GJK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057140f154c248abb2388d3a0002
theorem shape21_26:validFrom 11146 0 _GJK=true:=by decide+kernel
def _GJL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057120f157bd4805a9b90cf70002
theorem shape21_27:validFrom 11145 0 _GJL=true:=by decide+kernel
def _GJM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057100f15ab832acba798cb30002
theorem shape21_28:validFrom 11144 0 _GJM=true:=by decide+kernel
def _GJN:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570e0f15db308a0e491cc6e0002
theorem shape21_29:validFrom 11143 0 _GJN=true:=by decide+kernel
def _GJP:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570c0f160adc9e227f14c280002
theorem shape21_30:validFrom 11142 0 _GJP=true:=by decide+kernel
def _GJQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570a0f163a8767084a1cbe10002
theorem shape21_31:validFrom 11141 0 _GJQ=true:=by decide+kernel
def _GJR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057080f166a30e4de1140b990002
theorem shape21_32:validFrom 11140 0 _GJR=true:=by decide+kernel
def _GJS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057060f1699d917670480b4f0002
theorem shape21_33:validFrom 11139 0 _GJS=true:=by decide+kernel
def _GJT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057040f16c97ffec18d5cb050002
theorem shape21_34:validFrom 11138 0 _GJT=true:=by decide+kernel
def _GJU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057020f16f9259aedaa1cab90002
theorem shape21_35:validFrom 11137 0 _GJU=true:=by decide+kernel
def _GJV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057000f1728c9ebeb5c78a6c0002
theorem shape21_36:validFrom 11136 0 _GJV=true:=by decide+kernel
def _GJW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fe0f17586cf1d90830a1d0002
theorem shape21_37:validFrom 11135 0 _GJW=true:=by decide+kernel
def _GJX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fc0f17880eac79e39c9ce0002
theorem shape21_38:validFrom 11134 0 _GJX=true:=by decide+kernel
def _GJY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fa0f17b7af1bec52d897d0002
theorem shape21_39:validFrom 11133 0 _GJY=true:=by decide+kernel
def _GKA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f80f17e74e403057c492a0002
theorem shape21_40:validFrom 11132 0 _GKA=true:=by decide+kernel
def _GKB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f60f1816ec1945f0788d60002
theorem shape21_41:validFrom 11131 0 _GKB=true:=by decide+kernel
def _GKC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f40f184688a72d1ee48810002
theorem shape21_42:validFrom 11130 0 _GKC=true:=by decide+kernel
def _GKD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f20f187623ea04436c82a0002
theorem shape21_43:validFrom 11129 0 _GKD=true:=by decide+kernel
def _GKE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f00f18a5bde18e9ae47d20002
theorem shape21_44:validFrom 11128 0 _GKE=true:=by decide+kernel
def _GKF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ee0f18d5568dea868c7780002
theorem shape21_45:validFrom 11127 0 _GKF=true:=by decide+kernel
def _GKG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ec0f1904edef18078c71c0002
theorem shape21_46:validFrom 11126 0 _GKG=true:=by decide+kernel
def _GKH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ea0f19348405171c386bf0002
theorem shape21_47:validFrom 11125 0 _GKH=true:=by decide+kernel
def _GKI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e80f196418d00626c86600002
theorem shape21_48:validFrom 11124 0 _GKI=true:=by decide+kernel
def _GKJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e60f1993ac4fa865945ff0002
theorem shape21_49:validFrom 11123 0 _GKJ=true:=by decide+kernel
def _GKL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e40f19c33e841c380859c0002
theorem shape21_50:validFrom 11122 0 _GKL=true:=by decide+kernel
def _GKM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e20f19f2cf6d61a0585380002
theorem shape21_51:validFrom 11121 0 _GKM=true:=by decide+kernel
def _GKN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e00f1a225f0b789cb44d10002
theorem shape21_52:validFrom 11120 0 _GKN=true:=by decide+kernel
def _GKO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056de0f1a51ed5e612e844690002
theorem shape21_53:validFrom 11119 0 _GKO=true:=by decide+kernel
def _GKP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056dc0f1a817a6639b1443ff0002
theorem shape21_54:validFrom 11118 0 _GKP=true:=by decide+kernel
def _GKQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056da0f1ab10622c56c203920002
theorem shape21_55:validFrom 11117 0 _GKQ=true:=by decide+kernel
def _GKR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d80f1ae0909422ba8c3230002
theorem shape21_56:validFrom 11116 0 _GKR=true:=by decide+kernel
def _GKS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d60f1b1019ba519eec2b20002
theorem shape21_57:validFrom 11115 0 _GKS=true:=by decide+kernel
def _GKT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d40f1b3fa1955216d023f0002
theorem shape21_58:validFrom 11114 0 _GKT=true:=by decide+kernel
def _GKU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d20f1b6f2825427fc41ca0002
theorem shape21_59:validFrom 11113 0 _GKU=true:=by decide+kernel
def _GKW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d00f1b9ead69e621241520002
theorem shape21_60:validFrom 11112 0 _GKW=true:=by decide+kernel
def _GKX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ce0f1bce31635b58100d70002
theorem shape21_61:validFrom 11111 0 _GKX=true:=by decide+kernel
def _GKY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056cc0f1bfdb411a2227405a0002
theorem shape21_62:validFrom 11110 0 _GKY=true:=by decide+kernel
def _GKZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad973bbcf8140615f480f1c2d3574ba82e00020002
theorem shape21_63:validFrom 11109 0 _GKZ=true:=by decide+kernel
def _GLA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad933bbc3a13a66e2500f1c5cb58ca476c00020002
theorem shape21_64:validFrom 11108 0 _GLA=true:=by decide+kernel
def _GLB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8f3bbb7c1873069bc0f1c8c34597e59100020002
theorem shape21_65:validFrom 11107 0 _GLB=true:=by decide+kernel
def _GLC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8b3bbabe226cd22830f1cbbb1db0b75f40020002
theorem shape21_66:validFrom 11106 0 _GLC=true:=by decide+kernel
def _GLD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad873bba003193575a80f1ceb2e116a29600020002
theorem shape21_67:validFrom 11105 0 _GLD=true:=by decide+kernel
def _GLE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad833bb94245e6963b70f1d1aa8fc9a71240020002
theorem shape21_68:validFrom 11104 0 _GLE=true:=by decide+kernel
def _GLF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7f3bb8845f668ecf00f1d4a229c9c4c400020002
theorem shape21_69:validFrom 11103 0 _GLF=true:=by decide+kernel
def _GLH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7b3bb7c86d28944650f1d791f2c1aee6c0020002
theorem shape21_70:validFrom 11102 0 _GLH=true:=by decide+kernel
def _GLI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad773bb716308c0fdef0f1da5ae533c08440020002
theorem shape21_71:validFrom 11101 0 _GLI=true:=by decide+kernel
def _GLJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad733bb663f8c48f3f60f1dd23c451c30280020002
theorem shape21_72:validFrom 11100 0 _GLJ=true:=by decide+kernel
def _GLK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6f3bb5b1c5d11fc420f1dfec901f80ef80020002
theorem shape21_73:validFrom 11099 0 _GLK=true:=by decide+kernel
def _GLL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6b3bb4ff97b2b40b10f1e2b548992fd3c0020002
theorem shape21_74:validFrom 11098 0 _GLL=true:=by decide+kernel
def _GLM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad673bb44d6e68597bd0f1e57dedc29a10c0020002
theorem shape21_75:validFrom 11097 0 _GLM=true:=by decide+kernel
def _GLN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad633bb39b49f302ab00f1e8467f97f55400020002
theorem shape21_76:validFrom 11096 0 _GLN=true:=by decide+kernel
def _GLO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5f3bb2e92a51bd07d0f1eb0efe1d0be0c0020002
theorem shape21_77:validFrom 11095 0 _GLO=true:=by decide+kernel
def _GLP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5b3bb2370f857b1f60f1edd7694e138280020002
theorem shape21_78:validFrom 11094 0 _GLP=true:=by decide+kernel
def _GLQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad573bb184f98d4a6830f1f09fc12ed65f40020002
theorem shape21_79:validFrom 11093 0 _GLQ=true:=by decide+kernel
def _GLS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad533bb0d2e86a1d67f0f1f36805bb8a6040020002
theorem shape21_80:validFrom 11092 0 _GLS=true:=by decide+kernel
def _GLT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4f3bb020dc1b7ae150f1f63036f6147ac0020002
theorem shape21_81:validFrom 11091 0 _GLT=true:=by decide+kernel
def _GLU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4b3baf6ed4a0e984f0f1f8f854e059ec40020002
theorem shape21_82:validFrom 11090 0 _GLU=true:=by decide+kernel
def _GLV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473baebcd1fb5be6c0f1fbc05f76906500020002
theorem shape21_83:validFrom 11089 0 _GLV=true:=by decide+kernel
def _GLW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433bae0ad429df7640f1fe8856bc822700020002
theorem shape21_84:validFrom 11088 0 _GLW=true:=by decide+kernel
def _GLX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3bad58db2d66bbb0f201503aae651140020002
theorem shape21_85:validFrom 11087 0 _GLX=true:=by decide+kernel
def _GLY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3baca6e704ff3db0f204180b50030940020002
theorem shape21_86:validFrom 11086 0 _GLY=true:=by decide+kernel
def _GLZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373babf4f7b19b6990f206dfc89d9259c0020002
theorem shape21_87:validFrom 11085 0 _GLZ=true:=by decide+kernel
def _GMA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333bab430d3248d7a0f209a7729adca180020002
theorem shape21_88:validFrom 11084 0 _GMA=true:=by decide+kernel
def _GMB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3baa912787f9ebd0f20c6f09441850c0020002
theorem shape21_89:validFrom 11083 0 _GMB=true:=by decide+kernel
def _GMD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3ba9df46b1bc45f0f20f368c9d0ee840020002
theorem shape21_90:validFrom 11082 0 _GMD=true:=by decide+kernel
def _GME:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273ba92d6ab0824250f211fdfca1f6f6c0020002
theorem shape21_91:validFrom 11081 0 _GME=true:=by decide+kernel
def _GMF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233ba87b9383598880f214c5595699de00020002
theorem shape21_92:validFrom 11080 0 _GMF=true:=by decide+kernel
def _GMG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3ba7c9c12b346d40f2178ca2b72e4b00020002
theorem shape21_93:validFrom 11079 0 _GMG=true:=by decide+kernel
def _GMH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3ba717f3a7209f70f21a53d8c77d8240020002
theorem shape21_94:validFrom 11078 0 _GMH=true:=by decide+kernel
def _GMI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173ba6662af8106c70f21d1afb83be4e40020002
theorem shape21_95:validFrom 11077 0 _GMI=true:=by decide+kernel
def _GMJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133ba5b4671d118ac0f21fe20aefb9d500020002
theorem shape21_96:validFrom 11076 0 _GMJ=true:=by decide+kernel
def row21 (v:ℕ):List Piece:=match v with
 | 0=>_GIR
 | 1=>_GIS
 | 2=>_GJD
 | 3=>_GJO
 | 4=>_GJZ
 | 5=>_GKK
 | 6=>_GKV
 | 7=>_GLG
 | 8=>_GLR
 | 9=>_GMC
 | 10=>_GIT
 | 11=>_GIU
 | 12=>_GIV
 | 13=>_GIW
 | 14=>_GIX
 | 15=>_GIY
 | 16=>_GIZ
 | 17=>_GJA
 | 18=>_GJB
 | 19=>_GJC
 | 20=>_GJE
 | 21=>_GJF
 | 22=>_GJG
 | 23=>_GJH
 | 24=>_GJI
 | 25=>_GJJ
 | 26=>_GJK
 | 27=>_GJL
 | 28=>_GJM
 | 29=>_GJN
 | 30=>_GJP
 | 31=>_GJQ
 | 32=>_GJR
 | 33=>_GJS
 | 34=>_GJT
 | 35=>_GJU
 | 36=>_GJV
 | 37=>_GJW
 | 38=>_GJX
 | 39=>_GJY
 | 40=>_GKA
 | 41=>_GKB
 | 42=>_GKC
 | 43=>_GKD
 | 44=>_GKE
 | 45=>_GKF
 | 46=>_GKG
 | 47=>_GKH
 | 48=>_GKI
 | 49=>_GKJ
 | 50=>_GKL
 | 51=>_GKM
 | 52=>_GKN
 | 53=>_GKO
 | 54=>_GKP
 | 55=>_GKQ
 | 56=>_GKR
 | 57=>_GKS
 | 58=>_GKT
 | 59=>_GKU
 | 60=>_GKW
 | 61=>_GKX
 | 62=>_GKY
 | 63=>_GKZ
 | 64=>_GLA
 | 65=>_GLB
 | 66=>_GLC
 | 67=>_GLD
 | 68=>_GLE
 | 69=>_GLF
 | 70=>_GLH
 | 71=>_GLI
 | 72=>_GLJ
 | 73=>_GLK
 | 74=>_GLL
 | 75=>_GLM
 | 76=>_GLN
 | 77=>_GLO
 | 78=>_GLP
 | 79=>_GLQ
 | 80=>_GLS
 | 81=>_GLT
 | 82=>_GLU
 | 83=>_GLV
 | 84=>_GLW
 | 85=>_GLX
 | 86=>_GLY
 | 87=>_GLZ
 | 88=>_GMA
 | 89=>_GMB
 | 90=>_GMD
 | 91=>_GME
 | 92=>_GMF
 | 93=>_GMG
 | 94=>_GMH
 | 95=>_GMI
 | 96=>_GMJ
 | _=>[]
theorem checked21 (v:ℕ) (hy:21+v≤117):validFrom (11193-21-v) 0 (row21 v)=true:=by
 have hv:v≤96:=by omega
 interval_cases v
 · exact shape21_0
 · exact shape21_1
 · exact shape21_2
 · exact shape21_3
 · exact shape21_4
 · exact shape21_5
 · exact shape21_6
 · exact shape21_7
 · exact shape21_8
 · exact shape21_9
 · exact shape21_10
 · exact shape21_11
 · exact shape21_12
 · exact shape21_13
 · exact shape21_14
 · exact shape21_15
 · exact shape21_16
 · exact shape21_17
 · exact shape21_18
 · exact shape21_19
 · exact shape21_20
 · exact shape21_21
 · exact shape21_22
 · exact shape21_23
 · exact shape21_24
 · exact shape21_25
 · exact shape21_26
 · exact shape21_27
 · exact shape21_28
 · exact shape21_29
 · exact shape21_30
 · exact shape21_31
 · exact shape21_32
 · exact shape21_33
 · exact shape21_34
 · exact shape21_35
 · exact shape21_36
 · exact shape21_37
 · exact shape21_38
 · exact shape21_39
 · exact shape21_40
 · exact shape21_41
 · exact shape21_42
 · exact shape21_43
 · exact shape21_44
 · exact shape21_45
 · exact shape21_46
 · exact shape21_47
 · exact shape21_48
 · exact shape21_49
 · exact shape21_50
 · exact shape21_51
 · exact shape21_52
 · exact shape21_53
 · exact shape21_54
 · exact shape21_55
 · exact shape21_56
 · exact shape21_57
 · exact shape21_58
 · exact shape21_59
 · exact shape21_60
 · exact shape21_61
 · exact shape21_62
 · exact shape21_63
 · exact shape21_64
 · exact shape21_65
 · exact shape21_66
 · exact shape21_67
 · exact shape21_68
 · exact shape21_69
 · exact shape21_70
 · exact shape21_71
 · exact shape21_72
 · exact shape21_73
 · exact shape21_74
 · exact shape21_75
 · exact shape21_76
 · exact shape21_77
 · exact shape21_78
 · exact shape21_79
 · exact shape21_80
 · exact shape21_81
 · exact shape21_82
 · exact shape21_83
 · exact shape21_84
 · exact shape21_85
 · exact shape21_86
 · exact shape21_87
 · exact shape21_88
 · exact shape21_89
 · exact shape21_90
 · exact shape21_91
 · exact shape21_92
 · exact shape21_93
 · exact shape21_94
 · exact shape21_95
 · exact shape21_96
end EP

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace EP
open DZ
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def _GMK:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba300000000000f11a0a2f1b526a91165e99d545850f0f520f22f45bece8bbd33aa8b090ee4337df7cfcbf4e470004
theorem shape22_0:validFrom 11171 0 _GMK=true:=by decide+kernel
def _GML:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba200000000000f11cf818d506e8d0e35e99d545850f0f9d8adc5d901ce68bd33aa8b090ee508fe2f979a70e240004
theorem shape22_1:validFrom 11170 0 _GML=true:=by decide+kernel
def _GMW:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba100000000000f11fe5ee1c60a5d0b05e99d545850f0fe78aeb364d68e45bd33aa8b090ee5de7e675f68ece000004
theorem shape22_2:validFrom 11169 0 _GMW=true:=by decide+kernel
def _GNH:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba000000000000f122d3aeedb2bb907c5e99d545850f103189b69af454e21bd33aa8b090ee6b3fe9f273768ddb0004
theorem shape22_3:validFrom 11168 0 _GNH=true:=by decide+kernel
def _GNS:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9f00000000000f125c15b4ca9fc90475e99d545850f107d01a6194f4cdfcbd33aa8b090ee7897ed6ef05e4db60004
theorem shape22_4:validFrom 11167 0 _GNS=true:=by decide+kernel
def _GOD:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9e00000000000f128aef335999d50125e99d545850f10c87852239454dd8bd33aa8b090ee85eff0eb6d460d910004
theorem shape22_5:validFrom 11166 0 _GOD=true:=by decide+kernel
def _GOO:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9d00000000000f12b9c76ac2e688fdc5e99d545850f11156822478cecdb2bd33aa8b090ee9347f467ea2dcd6c0004
theorem shape22_6:validFrom 11165 0 _GOO=true:=by decide+kernel
def _GOZ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9c00000000000f12e89e5ae91f24fa65e99d545850f1160dc47a25a5cd8dbd33aa8b090eea09ff7e467158d450004
theorem shape22_7:validFrom 11164 0 _GOZ=true:=by decide+kernel
def _GPK:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9b00000000000f13177403aede2cf6e5e99d545850f11af43f84f98c8d66bd33aa8b090eeadf7fb60e3fd4d1f0004
theorem shape22_8:validFrom 11163 0 _GPK=true:=by decide+kernel
def _GPV:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9a00000000000f134648654eef78f365e99d545850f11ed67f5198040d40bd33aa8b090eebb4ffedd60e50cee0004
theorem shape22_9:validFrom 11162 0 _GPV=true:=by decide+kernel
def _GMM:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9900000000000f13751b7f8e87a0efe5e99d545850f122895dfc52818d19bd33aa8b090eec8a80259ddccccba0004
theorem shape22_10:validFrom 11161 0 _GMM=true:=by decide+kernel
def _GMN:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9800000000000f13a3ed52a870a8ec45e99d545850f12653cee8a8090cf1bd33aa8b090eed60005d65ab48c860004
theorem shape22_11:validFrom 11160 0 _GMN=true:=by decide+kernel
def _GMO:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9700000000000f13d2bdde61e26ce8a5e99d545850f12a35d2130dc90cc9bd33aa8b090eee3580952d79c4c530004
theorem shape22_12:validFrom 11159 0 _GMO=true:=by decide+kernel
def _GMP:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9600000000000f14018d22f5a3b0e4f5e99d545850f12e2f677f0e930ca0bd33aa8b090eef0b00ccf54840c200004
theorem shape22_13:validFrom 11158 0 _GMP=true:=by decide+kernel
def _GMQ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9500000000000f14305b2028ee00e135e99d545850f1326fdc13c2678c77bd33aa8b090eefe08104bd16bcbef0004
theorem shape22_14:validFrom 11157 0 _GMQ=true:=by decide+kernel
def _GMR:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9400000000000f145f27d636880cdd75e99d545850f136c7e2e84be1cc4dbd33aa8b090ef0b6013c84e538bbe0004
theorem shape22_15:validFrom 11156 0 _GMR=true:=by decide+kernel
def _GMS:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9300000000000f148df344e3ab7cd995e99d545850f13b66c8e913070c21bd33aa8b090ef18b81744cb3b4b8f0004
theorem shape22_16:validFrom 11155 0 _GMS=true:=by decide+kernel
def _GMT:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9200000000000f14bcbd6c6b1dc8d5b5e99d545850f14034e79d3bee4bdfbd33aa8b090ef26101ac148230b610004
theorem shape22_17:validFrom 11154 0 _GMT=true:=by decide+kernel
def _GMU:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9100000000000f14eb864c921a50d1c5e99d545850f144eb4ba85cedcb9dbd33aa8b090ef33681e3dc50acb320004
theorem shape22_18:validFrom 11153 0 _GMU=true:=by decide+kernel
def _GMV:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae40000000000078a8d26f2c9b21e66e5e99d545850f0454b44126c77cb590003
theorem shape22_19:validFrom 11152 0 _GMV=true:=by decide+kernel
def _GMX:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571e0f15491437343a80c9b0002
theorem shape22_20:validFrom 11151 0 _GMX=true:=by decide+kernel
def _GMY:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571c0f1577d941af5ca4c5a0002
theorem shape22_21:validFrom 11150 0 _GMY=true:=by decide+kernel
def _GMZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571a0f15a69d04ca0b5cc170002
theorem shape22_22:validFrom 11149 0 _GMZ=true:=by decide+kernel
def _GNA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057180f15d55f80bf0668bd30002
theorem shape22_23:validFrom 11148 0 _GNA=true:=by decide+kernel
def _GNB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057160f160420b5538e38b8f0002
theorem shape22_24:validFrom 11147 0 _GNB=true:=by decide+kernel
def _GNC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057140f1632e0a2c260ccb490002
theorem shape22_25:validFrom 11146 0 _GNC=true:=by decide+kernel
def _GND:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057120f16619f48d0c274b030002
theorem shape22_26:validFrom 11145 0 _GND=true:=by decide+kernel
def _GNE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057100f16905ca7b96d40abb0002
theorem shape22_27:validFrom 11144 0 _GNE=true:=by decide+kernel
def _GNF:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570e0f16bf18bf41a740a730002
theorem shape22_28:validFrom 11143 0 _GNF=true:=by decide+kernel
def _GNG:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570c0f16edd38fa42aa0a290002
theorem shape22_29:validFrom 11142 0 _GNG=true:=by decide+kernel
def _GNI:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570a0f171c8d18a63e249de0002
theorem shape22_30:validFrom 11141 0 _GNI=true:=by decide+kernel
def _GNJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057080f174b455a8298f09930002
theorem shape22_31:validFrom 11140 0 _GNJ=true:=by decide+kernel
def _GNK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057060f1779fc54fe86689460002
theorem shape22_32:validFrom 11139 0 _GNK=true:=by decide+kernel
def _GNL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057040f17a8b20854b96c8f70002
theorem shape22_33:validFrom 11138 0 _GNL=true:=by decide+kernel
def _GNM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057020f17d766744a80048a80002
theorem shape22_34:validFrom 11137 0 _GNM=true:=by decide+kernel
def _GNN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057000f180619991a8b448570002
theorem shape22_35:validFrom 11136 0 _GNN=true:=by decide+kernel
def _GNO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fe0f1834cb768a2a148060002
theorem shape22_36:validFrom 11135 0 _GNO=true:=by decide+kernel
def _GNP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fc0f18637c0cd40e747b20002
theorem shape22_37:validFrom 11134 0 _GNP=true:=by decide+kernel
def _GNQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fa0f18922b5bbd866075e0002
theorem shape22_38:validFrom 11133 0 _GNQ=true:=by decide+kernel
def _GNR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f80f18c0d96381420c7080002
theorem shape22_39:validFrom 11132 0 _GNR=true:=by decide+kernel
def _GNT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f60f18ef8623e494046b10002
theorem shape22_40:validFrom 11131 0 _GNT=true:=by decide+kernel
def _GNU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f40f191e319d2227ec6580002
theorem shape22_41:validFrom 11130 0 _GNU=true:=by decide+kernel
def _GNV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f20f194cdbcf1ca8245fe0002
theorem shape22_42:validFrom 11129 0 _GNV=true:=by decide+kernel
def _GNW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f00f197b84b9b6bf245a30002
theorem shape22_43:validFrom 11128 0 _GNW=true:=by decide+kernel
def _GNX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ee0f19aa2c5d2b179c5460002
theorem shape22_44:validFrom 11127 0 _GNX=true:=by decide+kernel
def _GNY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ec0f19d8d2b93f06ac4e70002
theorem shape22_45:validFrom 11126 0 _GNY=true:=by decide+kernel
def _GNZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ea0f1a0777ce2d38684870002
theorem shape22_46:validFrom 11125 0 _GNZ=true:=by decide+kernel
def _GOA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e80f1a361b9bbb00984250002
theorem shape22_47:validFrom 11124 0 _GOA=true:=by decide+kernel
def _GOB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e60f1a64be222309783c10002
theorem shape22_48:validFrom 11123 0 _GOB=true:=by decide+kernel
def _GOC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e40f1a935f612aabdc35c0002
theorem shape22_49:validFrom 11122 0 _GOC=true:=by decide+kernel
def _GOE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e20f1ac1ff590c8cf82f50002
theorem shape22_50:validFrom 11121 0 _GOE=true:=by decide+kernel
def _GOF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e00f1af09e098e087828c0002
theorem shape22_51:validFrom 11120 0 _GOF=true:=by decide+kernel
def _GOG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056de0f1b1f3b72e9c1cc2210002
theorem shape22_52:validFrom 11119 0 _GOG=true:=by decide+kernel
def _GOH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056dc0f1b4dd794e515481b50002
theorem shape22_53:validFrom 11118 0 _GOH=true:=by decide+kernel
def _GOI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056da0f1b7c726fbaa8001460002
theorem shape22_54:validFrom 11117 0 _GOI=true:=by decide+kernel
def _GOJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d80f1bab0c032fd4900d60002
theorem shape22_55:validFrom 11116 0 _GOJ=true:=by decide+kernel
def _GOK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056d60f1bd9a44f7f3e580630002
theorem shape22_56:validFrom 11115 0 _GOK=true:=by decide+kernel
def _GOL:List Piece:=DZ.decode 62 62 0x3782dace9d900000adab3bbd8bfc8746eb20f1c083b546e45380020002
theorem shape22_57:validFrom 11114 0 _GOL=true:=by decide+kernel
def _GOM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ada73bbcd1a59021e320f1c36d1123787380020002
theorem shape22_58:validFrom 11113 0 _GOM=true:=by decide+kernel
def _GON:List Piece:=DZ.decode 62 62 0x3782dace9d900000ada33bbc1753b67e6820f1c656588a065f80020002
theorem shape22_59:validFrom 11112 0 _GON=true:=by decide+kernel
def _GOP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad9f3bbb5d06f971fa30f1c93f8b7e381740020002
theorem shape22_60:validFrom 11111 0 _GOP=true:=by decide+kernel
def _GOQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad9b3bbaa2bf59e71ad0f1cc28a9fc6394c0020002
theorem shape22_61:validFrom 11110 0 _GOQ=true:=by decide+kernel
def _GOR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad973bb9e87cd6f35110f1cf11b40832bbc0020002
theorem shape22_62:validFrom 11109 0 _GOR=true:=by decide+kernel
def _GOS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad933bb92e3f71810800f1d1faa99dfbe000020002
theorem shape22_63:validFrom 11108 0 _GOS=true:=by decide+kernel
def _GOT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8f3bb8740728a5dd70f1d4e38ac1688a40020002
theorem shape22_64:validFrom 11107 0 _GOT=true:=by decide+kernel
def _GOU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8b3bb7b9d3fd4c3550f1d7cc576ecf2ac0020002
theorem shape22_65:validFrom 11106 0 _GOU=true:=by decide+kernel
def _GOV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad873bb6ffa5ee89a460f1dab50fa9d96e80020002
theorem shape22_66:validFrom 11105 0 _GOV=true:=by decide+kernel
def _GOW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad833bb6457cfd4897e0f1dd9db36edda080020002
theorem shape22_67:validFrom 11104 0 _GOW=true:=by decide+kernel
def _GOX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7f3bb58b59289ea5e0f1e08642c1856880020002
theorem shape22_68:validFrom 11103 0 _GOX=true:=by decide+kernel
def _GOY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7b3bb4d31730b64ff0f1e3674aa126c040020002
theorem shape22_69:validFrom 11102 0 _GOY=true:=by decide+kernel
def _GPA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad773bb4242eebfd2780f1e622ebb40b6200020002
theorem shape22_70:validFrom 11101 0 _GPA=true:=by decide+kernel
def _GPB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad733bb3754b6fda5720f1e8de79a496a380020002
theorem shape22_71:validFrom 11100 0 _GPB=true:=by decide+kernel
def _GPC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6f3bb2c66cbb6399c0f1eb99f476719900020002
theorem shape22_72:validFrom 11099 0 _GPC=true:=by decide+kernel
def _GPD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6b3bb21792cf833510f1ee555c25f32bc0020002
theorem shape22_73:validFrom 11098 0 _GPD=true:=by decide+kernel
def _GPE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad673bb168bdab4edce0f1f110b0b6c48c80020002
theorem shape22_74:validFrom 11097 0 _GPE=true:=by decide+kernel
def _GPF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad633bb0b9ed4fb0dfc0f1f3cbf2253c8100020002
theorem shape22_75:validFrom 11096 0 _GPF=true:=by decide+kernel
def _GPG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5f3bb00b21bbbef8b0f1f6872075041d40020002
theorem shape22_76:validFrom 11095 0 _GPG=true:=by decide+kernel
def _GPH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5b3baf5c5af0635d10f1f9423ba2728bc0020002
theorem shape22_77:validFrom 11094 0 _GPH=true:=by decide+kernel
def _GPI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad573baead98ecb3e110f1fbfd43b1307bc0020002
theorem shape22_78:validFrom 11093 0 _GPI=true:=by decide+kernel
def _GPJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad533badfedbb19ab350f1feb8389d9532c0020002
theorem shape22_79:validFrom 11092 0 _GPJ=true:=by decide+kernel
def _GPL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4f3bad50233ea2b210f201731a697537c0020002
theorem shape22_80:validFrom 11091 0 _GPL=true:=by decide+kernel
def _GPM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4b3baca16f9356d5d0f2042de916a4a8c0020002
theorem shape22_81:validFrom 11090 0 _GPM=true:=by decide+kernel
def _GPN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473babf2c0b0a142a0f206e8a4a17af580020002
theorem shape22_82:validFrom 11089 0 _GPN=true:=by decide+kernel
def _GPO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433bab44169597cb00f209a34d0da0d400020002
theorem shape22_83:validFrom 11088 0 _GPO=true:=by decide+kernel
def _GPP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3baa95714324a110f20c5de2576d7bc0020002
theorem shape22_84:validFrom 11087 0 _GPP=true:=by decide+kernel
def _GPQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3ba9e6d0b85d9480f20f18648289ae00020002
theorem shape22_85:validFrom 11086 0 _GPQ=true:=by decide+kernel
def _GPR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373ba93834f62cd070f211d2d38b4cbe40020002
theorem shape22_86:validFrom 11085 0 _GPR=true:=by decide+kernel
def _GPS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333ba8899dfba83590f2148d2f755f29c0020002
theorem shape22_87:validFrom 11084 0 _GPS=true:=by decide+kernel
def _GPT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3ba7db0bc9b9d260f21747783d18b680020002
theorem shape22_88:validFrom 11083 0 _GPT=true:=by decide+kernel
def _GPU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3ba72c7e5f77a2a0f21a01ade6217580020002
theorem shape22_89:validFrom 11082 0 _GPU=true:=by decide+kernel
def _GPW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273ba67df5bdcbadd0f21cbbd06cd148c0020002
theorem shape22_90:validFrom 11081 0 _GPW=true:=by decide+kernel
def _GPX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233ba5cf71e3cbe240f21f75dfd4d07700020002
theorem shape22_91:validFrom 11080 0 _GPX=true:=by decide+kernel
def _GPY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3ba520f2d2625510f2222fdc1a76abc0020002
theorem shape22_92:validFrom 11079 0 _GPY=true:=by decide+kernel
def _GPZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3ba4727888a4fb90f224e9c5416c11c0020002
theorem shape22_93:validFrom 11078 0 _GPZ=true:=by decide+kernel
def _GQA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173ba3c403077dcec0f227a39b4608c500020002
theorem shape22_94:validFrom 11077 0 _GQA=true:=by decide+kernel
def _GQB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133ba315924e02e070f22a5d5e2bf47e40020002
theorem shape22_95:validFrom 11076 0 _GQB=true:=by decide+kernel
def row22 (v:ℕ):List Piece:=match v with
 | 0=>_GMK
 | 1=>_GML
 | 2=>_GMW
 | 3=>_GNH
 | 4=>_GNS
 | 5=>_GOD
 | 6=>_GOO
 | 7=>_GOZ
 | 8=>_GPK
 | 9=>_GPV
 | 10=>_GMM
 | 11=>_GMN
 | 12=>_GMO
 | 13=>_GMP
 | 14=>_GMQ
 | 15=>_GMR
 | 16=>_GMS
 | 17=>_GMT
 | 18=>_GMU
 | 19=>_GMV
 | 20=>_GMX
 | 21=>_GMY
 | 22=>_GMZ
 | 23=>_GNA
 | 24=>_GNB
 | 25=>_GNC
 | 26=>_GND
 | 27=>_GNE
 | 28=>_GNF
 | 29=>_GNG
 | 30=>_GNI
 | 31=>_GNJ
 | 32=>_GNK
 | 33=>_GNL
 | 34=>_GNM
 | 35=>_GNN
 | 36=>_GNO
 | 37=>_GNP
 | 38=>_GNQ
 | 39=>_GNR
 | 40=>_GNT
 | 41=>_GNU
 | 42=>_GNV
 | 43=>_GNW
 | 44=>_GNX
 | 45=>_GNY
 | 46=>_GNZ
 | 47=>_GOA
 | 48=>_GOB
 | 49=>_GOC
 | 50=>_GOE
 | 51=>_GOF
 | 52=>_GOG
 | 53=>_GOH
 | 54=>_GOI
 | 55=>_GOJ
 | 56=>_GOK
 | 57=>_GOL
 | 58=>_GOM
 | 59=>_GON
 | 60=>_GOP
 | 61=>_GOQ
 | 62=>_GOR
 | 63=>_GOS
 | 64=>_GOT
 | 65=>_GOU
 | 66=>_GOV
 | 67=>_GOW
 | 68=>_GOX
 | 69=>_GOY
 | 70=>_GPA
 | 71=>_GPB
 | 72=>_GPC
 | 73=>_GPD
 | 74=>_GPE
 | 75=>_GPF
 | 76=>_GPG
 | 77=>_GPH
 | 78=>_GPI
 | 79=>_GPJ
 | 80=>_GPL
 | 81=>_GPM
 | 82=>_GPN
 | 83=>_GPO
 | 84=>_GPP
 | 85=>_GPQ
 | 86=>_GPR
 | 87=>_GPS
 | 88=>_GPT
 | 89=>_GPU
 | 90=>_GPW
 | 91=>_GPX
 | 92=>_GPY
 | 93=>_GPZ
 | 94=>_GQA
 | 95=>_GQB
 | _=>[]
theorem checked22 (v:ℕ) (hy:22+v≤117):validFrom (11193-22-v) 0 (row22 v)=true:=by
 have hv:v≤95:=by omega
 interval_cases v
 · exact shape22_0
 · exact shape22_1
 · exact shape22_2
 · exact shape22_3
 · exact shape22_4
 · exact shape22_5
 · exact shape22_6
 · exact shape22_7
 · exact shape22_8
 · exact shape22_9
 · exact shape22_10
 · exact shape22_11
 · exact shape22_12
 · exact shape22_13
 · exact shape22_14
 · exact shape22_15
 · exact shape22_16
 · exact shape22_17
 · exact shape22_18
 · exact shape22_19
 · exact shape22_20
 · exact shape22_21
 · exact shape22_22
 · exact shape22_23
 · exact shape22_24
 · exact shape22_25
 · exact shape22_26
 · exact shape22_27
 · exact shape22_28
 · exact shape22_29
 · exact shape22_30
 · exact shape22_31
 · exact shape22_32
 · exact shape22_33
 · exact shape22_34
 · exact shape22_35
 · exact shape22_36
 · exact shape22_37
 · exact shape22_38
 · exact shape22_39
 · exact shape22_40
 · exact shape22_41
 · exact shape22_42
 · exact shape22_43
 · exact shape22_44
 · exact shape22_45
 · exact shape22_46
 · exact shape22_47
 · exact shape22_48
 · exact shape22_49
 · exact shape22_50
 · exact shape22_51
 · exact shape22_52
 · exact shape22_53
 · exact shape22_54
 · exact shape22_55
 · exact shape22_56
 · exact shape22_57
 · exact shape22_58
 · exact shape22_59
 · exact shape22_60
 · exact shape22_61
 · exact shape22_62
 · exact shape22_63
 · exact shape22_64
 · exact shape22_65
 · exact shape22_66
 · exact shape22_67
 · exact shape22_68
 · exact shape22_69
 · exact shape22_70
 · exact shape22_71
 · exact shape22_72
 · exact shape22_73
 · exact shape22_74
 · exact shape22_75
 · exact shape22_76
 · exact shape22_77
 · exact shape22_78
 · exact shape22_79
 · exact shape22_80
 · exact shape22_81
 · exact shape22_82
 · exact shape22_83
 · exact shape22_84
 · exact shape22_85
 · exact shape22_86
 · exact shape22_87
 · exact shape22_88
 · exact shape22_89
 · exact shape22_90
 · exact shape22_91
 · exact shape22_92
 · exact shape22_93
 · exact shape22_94
 · exact shape22_95
def _GQC:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba200000000000f12cce1b1e6ac84f215e99d545850f11d7c61bd49f7cd3dbd33aa8b090eeb92e910cb4684cf20004
theorem shape23_0:validFrom 11170 0 _GQC=true:=by decide+kernel
def _GQD:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba100000000000f12facd58aa2724eea5e99d545850f120aa872f7eef4d17bd33aa8b090eec686948931500cbb0004
theorem shape23_1:validFrom 11169 0 _GQD=true:=by decide+kernel
def _GQO:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002ba000000000000f1328b7bc3240f4eb35e99d545850f12407e59590640cf0bd33aa8b090eed3de9805ae37cc850004
theorem shape23_2:validFrom 11168 0 _GQO=true:=by decide+kernel
def _GQZ:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9f00000000000f1356a0dc464464e7b5e99d545850f127653004db9a8cc9bd33aa8b090eee1369b822b1f8c4f0004
theorem shape23_3:validFrom 11167 0 _GQZ=true:=by decide+kernel
def _GRK:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9e00000000000f138488b91ee5cce425e99d545850f12af1b3664e834ca2bd33aa8b090eeee8e9efea8074c1a0004
theorem shape23_4:validFrom 11166 0 _GRK=true:=by decide+kernel
def _GRV:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9d00000000000f13b26f52837144e095e99d545850f12ead6fbd52b54c6ebd33aa8b090eefbe6a27b24ef0be60004
theorem shape23_5:validFrom 11165 0 _GRV=true:=by decide+kernel
def _GSG:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9c00000000000f13e054a8ac9a38dcf5e99d545850f13269181d90a24c30bd33aa8b090ef093ea5f7a1d6cbb20004
theorem shape23_6:validFrom 11164 0 _GSG=true:=by decide+kernel
def _GSR:List Piece:=DZ.decode 62 40 0xde0b6b3a76400002b9b00000000000f140e38bb61ae18d945e99d545850f13653f971ab0d0bf2bd33aa8b090ef1696a9741ebe8b7f0004
theorem shape23_7:validFrom 11163 0 _GSR=true:=by decide+kernel
def _GTC:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae68000000000078a1e0dc55f83666ac5e99d545850f02f29f7f0f9fb8bb20003
theorem shape23_8:validFrom 11162 0 _GTC=true:=by decide+kernel
def _GTN:List Piece:=DZ.decode 62 39 0x3782dace9d900000ae64000000000078a34fe8b707db468e5e99d545850f037e2812c0f9dcb730003
theorem shape23_9:validFrom 11161 0 _GTN=true:=by decide+kernel
def _GQE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057300f1497dd5f8edc8ccdf0002
theorem shape23_10:validFrom 11160 0 _GQE=true:=by decide+kernel
def _GQF:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000572e0f14c5bc6501583cca10002
theorem shape23_11:validFrom 11159 0 _GQF=true:=by decide+kernel
def _GQG:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000572c0f14f39a26ffc160c630002
theorem shape23_12:validFrom 11158 0 _GQG=true:=by decide+kernel
def _GQH:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000572a0f152176a5c2c510c240002
theorem shape23_13:validFrom 11157 0 _GQH=true:=by decide+kernel
def _GQI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057280f154f51e111b72cbe40002
theorem shape23_14:validFrom 11156 0 _GQI=true:=by decide+kernel
def _GQJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057260f157d2bd908ed90ba30002
theorem shape23_15:validFrom 11155 0 _GQJ=true:=by decide+kernel
def _GQK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057240f15ab048dc4bc68b610002
theorem shape23_16:validFrom 11154 0 _GQK=true:=by decide+kernel
def _GQL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057220f15d8dbff0c7b38b1e0002
theorem shape23_17:validFrom 11153 0 _GQL=true:=by decide+kernel
def _GQM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057200f1606b22d18d1a0adb0002
theorem shape23_18:validFrom 11152 0 _GQM=true:=by decide+kernel
def _GQN:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571e0f16348717b118d8a970002
theorem shape23_19:validFrom 11151 0 _GQN=true:=by decide+kernel
def _GQP:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571c0f16625abf0df780a510002
theorem shape23_20:validFrom 11150 0 _GQP=true:=by decide+kernel
def _GQQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571a0f16902d22f6c724a0b0002
theorem shape23_21:validFrom 11149 0 _GQQ=true:=by decide+kernel
def _GQR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057180f16bdfe4387dac89c40002
theorem shape23_22:validFrom 11148 0 _GQR=true:=by decide+kernel
def _GQS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057160f16ebce20dd84c497c0002
theorem shape23_23:validFrom 11147 0 _GQS=true:=by decide+kernel
def _GQT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057140f17199cbabf20d09330002
theorem shape23_24:validFrom 11146 0 _GQT=true:=by decide+kernel
def _GQU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057120f17476a116552b08e90002
theorem shape23_25:validFrom 11145 0 _GQU=true:=by decide+kernel
def _GQV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057100f1775362497779889e0002
theorem shape23_26:validFrom 11144 0 _GQV=true:=by decide+kernel
def _GQW:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570e0f17a300f48e304c8520002
theorem shape23_27:validFrom 11143 0 _GQW=true:=by decide+kernel
def _GQX:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570c0f17d0ca8110dd9c8050002
theorem shape23_28:validFrom 11142 0 _GQX=true:=by decide+kernel
def _GQY:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570a0f17fe92ca3bcef07b70002
theorem shape23_29:validFrom 11141 0 _GQY=true:=by decide+kernel
def _GRA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057080f182c59d02b53a07670002
theorem shape23_30:validFrom 11140 0 _GRA=true:=by decide+kernel
def _GRB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057060f185a1f92a6ce307170002
theorem shape23_31:validFrom 11139 0 _GRB=true:=by decide+kernel
def _GRC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057040f1887e411e6da746c50002
theorem shape23_32:validFrom 11138 0 _GRC=true:=by decide+kernel
def _GRD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057020f18b5a74db2dc9c6720002
theorem shape23_33:validFrom 11137 0 _GRD=true:=by decide+kernel
def _GRE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057000f18e3694643707861e0002
theorem shape23_34:validFrom 11136 0 _GRE=true:=by decide+kernel
def _GRF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fe0f191129fb5ffb045c90002
theorem shape23_35:validFrom 11135 0 _GRF=true:=by decide+kernel
def _GRG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fc0f193ee96d24ca6c5730002
theorem shape23_36:validFrom 11134 0 _GRG=true:=by decide+kernel
def _GRH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fa0f196ca79bae2a5851b0002
theorem shape23_37:validFrom 11133 0 _GRH=true:=by decide+kernel
def _GRI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f80f199a6486c381c04c20002
theorem shape23_38:validFrom 11132 0 _GRI=true:=by decide+kernel
def _GRJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f60f19c8202e9d68c04670002
theorem shape23_39:validFrom 11131 0 _GRJ=true:=by decide+kernel
def _GRL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f40f19f5da9303489040b0002
theorem shape23_40:validFrom 11130 0 _GRL=true:=by decide+kernel
def _GRM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f20f1a2393b42db7243ae0002
theorem shape23_41:validFrom 11129 0 _GRM=true:=by decide+kernel
def _GRN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f00f1a514b91e4206434f0002
theorem shape23_42:validFrom 11128 0 _GRN=true:=by decide+kernel
def _GRO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ee0f1a7f022c42cd782ef0002
theorem shape23_43:validFrom 11127 0 _GRO=true:=by decide+kernel
def _GRP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ec0f1aacb78366073028e0002
theorem shape23_44:validFrom 11126 0 _GRP=true:=by decide+kernel
def _GRQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ea0f1ada6b97153cac22a0002
theorem shape23_45:validFrom 11125 0 _GRQ=true:=by decide+kernel
def _GRR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e80f1b081e6788fdf81c60002
theorem shape23_46:validFrom 11124 0 _GRR=true:=by decide+kernel
def _GRS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e60f1b35cff488bbe415f0002
theorem shape23_47:validFrom 11123 0 _GRS=true:=by decide+kernel
def _GRT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e40f1b63803e4d05d80f70002
theorem shape23_48:validFrom 11122 0 _GRT=true:=by decide+kernel
def _GRU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e20f1b912f449d4c3008d0002
theorem shape23_49:validFrom 11121 0 _GRU=true:=by decide+kernel
def _GRW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056e00f1bbedd0795d6880220002
theorem shape23_50:validFrom 11120 0 _GRW=true:=by decide+kernel
def _GRX:List Piece:=DZ.decode 62 62 0x3782dace9d900000adbf3bbdfac3bbb45430f1bec898752eaf40020002
theorem shape23_51:validFrom 11119 0 _GRX=true:=by decide+kernel
def _GRY:List Piece:=DZ.decode 62 62 0x3782dace9d900000adbb3bbd4416ca900780f1c1a34c39bfe200020002
theorem shape23_52:validFrom 11118 0 _GRY=true:=by decide+kernel
def _GRZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000adb73bbc8d6ee6599780f1c47debca99a200020002
theorem shape23_53:validFrom 11117 0 _GRZ=true:=by decide+kernel
def _GSA:List Piece:=DZ.decode 62 62 0x3782dace9d900000adb33bbbd6cc0ff32460f1c7587724336e80020002
theorem shape23_54:validFrom 11116 0 _GSA=true:=by decide+kernel
def _GSB:List Piece:=DZ.decode 62 62 0x3782dace9d900000adaf3bbb202e467a9600f1ca32ee4a15a800020002
theorem shape23_55:validFrom 11115 0 _GSB=true:=by decide+kernel
def _GSC:List Piece:=DZ.decode 62 62 0x3782dace9d900000adab3bba69958ad20600f1cd0d5138b7e800020002
theorem shape23_56:validFrom 11114 0 _GSC=true:=by decide+kernel
def _GSD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ada73bb9b301dc886600f1cfe79ff1de6800020002
theorem shape23_57:validFrom 11113 0 _GSD=true:=by decide+kernel
def _GSE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ada33bb8fc733b2ca7b0f1d2c1da774d6140020002
theorem shape23_58:validFrom 11112 0 _GSE=true:=by decide+kernel
def _GSF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad9f3bb845e9a7a0e0f0f1d59c00c57c7c40020002
theorem shape23_59:validFrom 11111 0 _GSF=true:=by decide+kernel
def _GSH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad9b3bb78f6521030440f1d87612dff3ef00020002
theorem shape23_60:validFrom 11110 0 _GSH=true:=by decide+kernel
def _GSI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad973bb6d8e5a83520f0f1db5010c32b7c40020002
theorem shape23_61:validFrom 11109 0 _GSI=true:=by decide+kernel
def _GSJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad933bb6226b3c552600f1de29fa72ab6800020002
theorem shape23_62:validFrom 11108 0 _GSJ=true:=by decide+kernel
def _GSK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8f3bb56bf5de452100f1e103cfeaeb7c00020002
theorem shape23_63:validFrom 11107 0 _GSK=true:=by decide+kernel
def _GSL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8b3bb4b5858d940a50f1e3dd912dafd6c0020002
theorem shape23_64:validFrom 11106 0 _GSL=true:=by decide+kernel
def _GSM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad873bb3ff1a49d0dba0f1e6b73e3cbc9180020002
theorem shape23_65:validFrom 11105 0 _GSM=true:=by decide+kernel
def _GSN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad833bb348b413dda350f1e990d7148972c0020002
theorem shape23_66:validFrom 11104 0 _GSN=true:=by decide+kernel
def _GSO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7f3bb29252ead85bd0f1ec6a5bb89e90c0020002
theorem shape23_67:validFrom 11103 0 _GSO=true:=by decide+kernel
def _GSP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7b3bb1ddc138d859a0f1ef3ca2809e9980020002
theorem shape23_68:validFrom 11102 0 _GSP=true:=by decide+kernel
def _GSQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad773bb1322d4bea7000f1f1eaf234564000020002
theorem shape23_69:validFrom 11101 0 _GSQ=true:=by decide+kernel
def _GSS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad733bb0869e1b256ed0f1f4992ef76a44c0020002
theorem shape23_70:validFrom 11100 0 _GSS=true:=by decide+kernel
def _GST:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6f3bafdb13a5a76f50f1f74758cd6242c0020002
theorem shape23_71:validFrom 11099 0 _GST=true:=by decide+kernel
def _GSU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6b3baf2f8dec525930f1f9f56fb2b69b40020002
theorem shape23_72:validFrom 11098 0 _GSU=true:=by decide+kernel
def _GSV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad673bae840cee4443e0f1fca373aaeef080020002
theorem shape23_73:validFrom 11097 0 _GSV=true:=by decide+kernel
def _GSW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad633badd890ac5f1490f1ff5164b283adc0020002
theorem shape23_74:validFrom 11096 0 _GSW=true:=by decide+kernel
def _GSX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5f3bad2d1925c0e980f201ff42ccfc5a00020002
theorem shape23_75:validFrom 11095 0 _GSX=true:=by decide+kernel
def _GSY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5b3bac81a65b4b9ad0f204ad0df6d194c0020002
theorem shape23_76:validFrom 11094 0 _GSY=true:=by decide+kernel
def _GSZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad573babd6384c1d5a00f2075ac6338a9800020002
theorem shape23_77:validFrom 11093 0 _GSZ=true:=by decide+kernel
def _GTA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad533bab2acef917f840f20a086b7fa01f00020002
theorem shape23_78:validFrom 11092 0 _GTA=true:=by decide+kernel
def _GTB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4f3baa7f6a61ca8910f20cb5fddcd5dbc0020002
theorem shape23_79:validFrom 11091 0 _GTB=true:=by decide+kernel
def _GTD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4b3ba9d40a85c426c0f20f637d4cef6500020002
theorem shape23_80:validFrom 11090 0 _GTD=true:=by decide+kernel
def _GTE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473ba928af65e69e70f21210e9cc658640020002
theorem shape23_81:validFrom 11089 0 _GTE=true:=by decide+kernel
def _GTF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433ba87d5901501fc0f214be435ebf8100020002
theorem shape23_82:validFrom 11088 0 _GTF=true:=by decide+kernel
def _GTG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3ba7d20758e27ff0f2176b8a00760040020002
theorem shape23_83:validFrom 11087 0 _GTG=true:=by decide+kernel
def _GTH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3ba726ba6bbbf1f0f21a18bdb5103840020002
theorem shape23_84:validFrom 11086 0 _GTH=true:=by decide+kernel
def _GTI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373ba67b723abe3750f21cc5de790722c0020002
theorem shape23_85:validFrom 11085 0 _GTI=true:=by decide+kernel
def _GTJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333ba5d02ec5079390f21f72ec4fe1b1c0020002
theorem shape23_86:validFrom 11084 0 _GTJ=true:=by decide+kernel
def _GTK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3ba524f00b79b8e0f2221fe736191c80020002
theorem shape23_87:validFrom 11083 0 _GTK=true:=by decide+kernel
def _GTL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3ba479b60d32ff50f224cccf2f3402c0020002
theorem shape23_88:validFrom 11082 0 _GTL=true:=by decide+kernel
def _GTM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273ba3ce80cb151250f22779a437abb6c0020002
theorem shape23_89:validFrom 11081 0 _GTM=true:=by decide+kernel
def _GTO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233ba32350443e4300f22a26665306f400020002
theorem shape23_90:validFrom 11080 0 _GTO=true:=by decide+kernel
def _GTP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3ba2782479903cd0f22cd3157dbf0cc0020002
theorem shape23_91:validFrom 11079 0 _GTP=true:=by decide+kernel
def _GTQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3ba1ccfd6a2957a0f22f7fb1bb5aa180020002
theorem shape23_92:validFrom 11078 0 _GTQ=true:=by decide+kernel
def _GTR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173ba121db16eb3120f2322c3b08533b80020002
theorem shape23_93:validFrom 11077 0 _GTR=true:=by decide+kernel
def _GTS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133ba076bd7ef43620f234d8b1682f2780020002
theorem shape23_94:validFrom 11076 0 _GTS=true:=by decide+kernel
def row23 (v:ℕ):List Piece:=match v with
 | 0=>_GQC
 | 1=>_GQD
 | 2=>_GQO
 | 3=>_GQZ
 | 4=>_GRK
 | 5=>_GRV
 | 6=>_GSG
 | 7=>_GSR
 | 8=>_GTC
 | 9=>_GTN
 | 10=>_GQE
 | 11=>_GQF
 | 12=>_GQG
 | 13=>_GQH
 | 14=>_GQI
 | 15=>_GQJ
 | 16=>_GQK
 | 17=>_GQL
 | 18=>_GQM
 | 19=>_GQN
 | 20=>_GQP
 | 21=>_GQQ
 | 22=>_GQR
 | 23=>_GQS
 | 24=>_GQT
 | 25=>_GQU
 | 26=>_GQV
 | 27=>_GQW
 | 28=>_GQX
 | 29=>_GQY
 | 30=>_GRA
 | 31=>_GRB
 | 32=>_GRC
 | 33=>_GRD
 | 34=>_GRE
 | 35=>_GRF
 | 36=>_GRG
 | 37=>_GRH
 | 38=>_GRI
 | 39=>_GRJ
 | 40=>_GRL
 | 41=>_GRM
 | 42=>_GRN
 | 43=>_GRO
 | 44=>_GRP
 | 45=>_GRQ
 | 46=>_GRR
 | 47=>_GRS
 | 48=>_GRT
 | 49=>_GRU
 | 50=>_GRW
 | 51=>_GRX
 | 52=>_GRY
 | 53=>_GRZ
 | 54=>_GSA
 | 55=>_GSB
 | 56=>_GSC
 | 57=>_GSD
 | 58=>_GSE
 | 59=>_GSF
 | 60=>_GSH
 | 61=>_GSI
 | 62=>_GSJ
 | 63=>_GSK
 | 64=>_GSL
 | 65=>_GSM
 | 66=>_GSN
 | 67=>_GSO
 | 68=>_GSP
 | 69=>_GSQ
 | 70=>_GSS
 | 71=>_GST
 | 72=>_GSU
 | 73=>_GSV
 | 74=>_GSW
 | 75=>_GSX
 | 76=>_GSY
 | 77=>_GSZ
 | 78=>_GTA
 | 79=>_GTB
 | 80=>_GTD
 | 81=>_GTE
 | 82=>_GTF
 | 83=>_GTG
 | 84=>_GTH
 | 85=>_GTI
 | 86=>_GTJ
 | 87=>_GTK
 | 88=>_GTL
 | 89=>_GTM
 | 90=>_GTO
 | 91=>_GTP
 | 92=>_GTQ
 | 93=>_GTR
 | 94=>_GTS
 | _=>[]
theorem checked23 (v:ℕ) (hy:23+v≤117):validFrom (11193-23-v) 0 (row23 v)=true:=by
 have hv:v≤94:=by omega
 interval_cases v
 · exact shape23_0
 · exact shape23_1
 · exact shape23_2
 · exact shape23_3
 · exact shape23_4
 · exact shape23_5
 · exact shape23_6
 · exact shape23_7
 · exact shape23_8
 · exact shape23_9
 · exact shape23_10
 · exact shape23_11
 · exact shape23_12
 · exact shape23_13
 · exact shape23_14
 · exact shape23_15
 · exact shape23_16
 · exact shape23_17
 · exact shape23_18
 · exact shape23_19
 · exact shape23_20
 · exact shape23_21
 · exact shape23_22
 · exact shape23_23
 · exact shape23_24
 · exact shape23_25
 · exact shape23_26
 · exact shape23_27
 · exact shape23_28
 · exact shape23_29
 · exact shape23_30
 · exact shape23_31
 · exact shape23_32
 · exact shape23_33
 · exact shape23_34
 · exact shape23_35
 · exact shape23_36
 · exact shape23_37
 · exact shape23_38
 · exact shape23_39
 · exact shape23_40
 · exact shape23_41
 · exact shape23_42
 · exact shape23_43
 · exact shape23_44
 · exact shape23_45
 · exact shape23_46
 · exact shape23_47
 · exact shape23_48
 · exact shape23_49
 · exact shape23_50
 · exact shape23_51
 · exact shape23_52
 · exact shape23_53
 · exact shape23_54
 · exact shape23_55
 · exact shape23_56
 · exact shape23_57
 · exact shape23_58
 · exact shape23_59
 · exact shape23_60
 · exact shape23_61
 · exact shape23_62
 · exact shape23_63
 · exact shape23_64
 · exact shape23_65
 · exact shape23_66
 · exact shape23_67
 · exact shape23_68
 · exact shape23_69
 · exact shape23_70
 · exact shape23_71
 · exact shape23_72
 · exact shape23_73
 · exact shape23_74
 · exact shape23_75
 · exact shape23_76
 · exact shape23_77
 · exact shape23_78
 · exact shape23_79
 · exact shape23_80
 · exact shape23_81
 · exact shape23_82
 · exact shape23_83
 · exact shape23_84
 · exact shape23_85
 · exact shape23_86
 · exact shape23_87
 · exact shape23_88
 · exact shape23_89
 · exact shape23_90
 · exact shape23_91
 · exact shape23_92
 · exact shape23_93
 · exact shape23_94
def _GTT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057420f13f73bcfababb8ce10002
theorem shape24_0:validFrom 11169 0 _GTT=true:=by decide+kernel
def _GTU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057400f142434897aa2e0ca60002
theorem shape24_1:validFrom 11168 0 _GTU=true:=by decide+kernel
def _GUF:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000573e0f14512c03dd35b4c6a0002
theorem shape24_2:validFrom 11167 0 _GUF=true:=by decide+kernel
def _GUQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000573c0f147e223ed364a4c2e0002
theorem shape24_3:validFrom 11166 0 _GUQ=true:=by decide+kernel
def _GVB:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000573a0f14ab173a41e290bf10002
theorem shape24_4:validFrom 11165 0 _GVB=true:=by decide+kernel
def _GVM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057380f14d80af65f48e8bb30002
theorem shape24_5:validFrom 11164 0 _GVM=true:=by decide+kernel
def _GVX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057360f1504fd73104af0b750002
theorem shape24_6:validFrom 11163 0 _GVX=true:=by decide+kernel
def _GWI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057340f1531eeb054e8acb360002
theorem shape24_7:validFrom 11162 0 _GWI=true:=by decide+kernel
def _GWT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057320f155edeae2d2280af60002
theorem shape24_8:validFrom 11161 0 _GWT=true:=by decide+kernel
def _GXE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057300f158bcd6c98f7a4ab60002
theorem shape24_9:validFrom 11160 0 _GXE=true:=by decide+kernel
def _GTV:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000572e0f15b8baeb98687ca740002
theorem shape24_10:validFrom 11159 0 _GTV=true:=by decide+kernel
def _GTW:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000572c0f15e5a72b2b7500a320002
theorem shape24_11:validFrom 11158 0 _GTW=true:=by decide+kernel
def _GTX:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000572a0f1612922b36d42c9ef0002
theorem shape24_12:validFrom 11157 0 _GTX=true:=by decide+kernel
def _GTY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057280f163f7bebf118e49ab0002
theorem shape24_13:validFrom 11156 0 _GTY=true:=by decide+kernel
def _GTZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057260f166c646d3ef8f09670002
theorem shape24_14:validFrom 11155 0 _GTZ=true:=by decide+kernel
def _GUA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057240f16994baf2074a49220002
theorem shape24_15:validFrom 11154 0 _GUA=true:=by decide+kernel
def _GUB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057220f16c631b1958c148db0002
theorem shape24_16:validFrom 11153 0 _GUB=true:=by decide+kernel
def _GUC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057200f16f316749e3f348940002
theorem shape24_17:validFrom 11152 0 _GUC=true:=by decide+kernel
def _GUD:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571e0f171ff9f83a8e6c84c0002
theorem shape24_18:validFrom 11151 0 _GUD=true:=by decide+kernel
def _GUE:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571c0f174cdc3c6a78f48030002
theorem shape24_19:validFrom 11150 0 _GUE=true:=by decide+kernel
def _GUG:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571a0f1779bd4112b95c7ba0002
theorem shape24_20:validFrom 11149 0 _GUG=true:=by decide+kernel
def _GUH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057180f17a69d0669dbb076f0002
theorem shape24_21:validFrom 11148 0 _GUH=true:=by decide+kernel
def _GUI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057160f17d37b8c5499b07230002
theorem shape24_22:validFrom 11147 0 _GUI=true:=by decide+kernel
def _GUJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057140f180058d2d2f3d46d70002
theorem shape24_23:validFrom 11146 0 _GUJ=true:=by decide+kernel
def _GUK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057120f182d34d9e4e9406890002
theorem shape24_24:validFrom 11145 0 _GUK=true:=by decide+kernel
def _GUL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057100f185a0fa18a7a5c63b0002
theorem shape24_25:validFrom 11144 0 _GUL=true:=by decide+kernel
def _GUM:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570e0f1886e929c3a72c5eb0002
theorem shape24_26:validFrom 11143 0 _GUM=true:=by decide+kernel
def _GUN:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570c0f18b3c172906fac59a0002
theorem shape24_27:validFrom 11142 0 _GUN=true:=by decide+kernel
def _GUO:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570a0f18e0987bd591bc5480002
theorem shape24_28:validFrom 11141 0 _GUO=true:=by decide+kernel
def _GUP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057080f190d6e45c9920c4f60002
theorem shape24_29:validFrom 11140 0 _GUP=true:=by decide+kernel
def _GUR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057060f193a42d0512e104a20002
theorem shape24_30:validFrom 11139 0 _GUR=true:=by decide+kernel
def _GUS:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057040f1967161b6c65c444d0002
theorem shape24_31:validFrom 11138 0 _GUS=true:=by decide+kernel
def _GUT:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057020f1993e8271b39303f60002
theorem shape24_32:validFrom 11137 0 _GUT=true:=by decide+kernel
def _GUU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057000f19c0b8f35da8b439f0002
theorem shape24_33:validFrom 11136 0 _GUU=true:=by decide+kernel
def _GUV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fe0f19ed888033b3803460002
theorem shape24_34:validFrom 11135 0 _GUV=true:=by decide+kernel
def _GUW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fc0f1a1a56cd9d5a042ec0002
theorem shape24_35:validFrom 11134 0 _GUW=true:=by decide+kernel
def _GUX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fa0f1a4723db7f5ce42910002
theorem shape24_36:validFrom 11133 0 _GUX=true:=by decide+kernel
def _GUY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f80f1a73efaa103b342350002
theorem shape24_37:validFrom 11132 0 _GUY=true:=by decide+kernel
def _GUZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f60f1aa0ba3934b59c1d70002
theorem shape24_38:validFrom 11131 0 _GUZ=true:=by decide+kernel
def _GVA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f40f1acd8388eccb501780002
theorem shape24_39:validFrom 11130 0 _GVA=true:=by decide+kernel
def _GVC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f20f1afa4b99387cb81180002
theorem shape24_40:validFrom 11129 0 _GVC=true:=by decide+kernel
def _GVD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056f00f1b27126a17c9d00b60002
theorem shape24_41:validFrom 11128 0 _GVD=true:=by decide+kernel
def _GVE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056ee0f1b53d7fb8ab2a00530002
theorem shape24_42:validFrom 11127 0 _GVE=true:=by decide+kernel
def _GVF:List Piece:=DZ.decode 62 62 0x3782dace9d900000addb3bbfaa78a2bb21f0f1b809c4d9137840020002
theorem shape24_43:validFrom 11126 0 _GVF=true:=by decide+kernel
def _GVG:List Piece:=DZ.decode 62 62 0x3782dace9d900000add73bbef76c58bf9160f1bad5f60101ba80020002
theorem shape24_44:validFrom 11125 0 _GVG=true:=by decide+kernel
def _GVH:List Piece:=DZ.decode 62 62 0x3782dace9d900000add33bbe44650c08a040f1bda21333dd7f00020002
theorem shape24_45:validFrom 11124 0 _GVH=true:=by decide+kernel
def _GVI:List Piece:=DZ.decode 62 62 0x3782dace9d900000adcf3bbd9162bd034030f1c06e1c6ff2ff40020002
theorem shape24_46:validFrom 11123 0 _GVI=true:=by decide+kernel
def _GVJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000adcb3bbcde656baf7160f1c33a11b5423a80020002
theorem shape24_47:validFrom 11122 0 _GVJ=true:=by decide+kernel
def _GVK:List Piece:=DZ.decode 62 62 0x3782dace9d900000adc73bbc2b6d180d3240f1c605f303cb3700020002
theorem shape24_48:validFrom 11121 0 _GVK=true:=by decide+kernel
def _GVL:List Piece:=DZ.decode 62 62 0x3782dace9d900000adc33bbb7879c21c85e0f1c8d1c05b8de880020002
theorem shape24_49:validFrom 11120 0 _GVL=true:=by decide+kernel
def _GVN:List Piece:=DZ.decode 62 62 0x3782dace9d900000adbf3bbac58b69dd6ac0f1cb9d79bc8a5500020002
theorem shape24_50:validFrom 11119 0 _GVN=true:=by decide+kernel
def _GVO:List Piece:=DZ.decode 62 62 0x3782dace9d900000adbb3bba12a20f4fe0c0f1ce691f26c07d00020002
theorem shape24_51:validFrom 11118 0 _GVO=true:=by decide+kernel
def _GVP:List Piece:=DZ.decode 62 62 0x3782dace9d900000adb73bb95fbdb2e0cb40f1d134b0987cd300020002
theorem shape24_52:validFrom 11117 0 _GVP=true:=by decide+kernel
def _GVQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000adb33bb8acde53b66070f1d4002e15267e40020002
theorem shape24_53:validFrom 11116 0 _GVQ=true:=by decide+kernel
def _GVR:List Piece:=DZ.decode 62 62 0x3782dace9d900000adaf3bb7fa03f23d8880f1d6cb979b09de00020002
theorem shape24_54:validFrom 11115 0 _GVR=true:=by decide+kernel
def _GVS:List Piece:=DZ.decode 62 62 0x3782dace9d900000adab3bb7472e8e7641c0f1d996ed2a26f900020002
theorem shape24_55:validFrom 11114 0 _GVS=true:=by decide+kernel
def _GVT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ada73bb6945e28608c30f1dc622ec27dcf40020002
theorem shape24_56:validFrom 11113 0 _GVT=true:=by decide+kernel
def _GVU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ada33bb5e192bffc67e0f1df2d5c640e6080020002
theorem shape24_57:validFrom 11112 0 _GVU=true:=by decide+kernel
def _GVV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad9f3bb52ecc5549d320f1e1f8760ed8b380020002
theorem shape24_58:validFrom 11111 0 _GVV=true:=by decide+kernel
def _GVW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad9b3bb47c0ae848d140f1e4c37bc2dcbb00020002
theorem shape24_59:validFrom 11110 0 _GVW=true:=by decide+kernel
def _GVY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad973bb3c94e796636c0f1e78e6d7e672500020002
theorem shape24_60:validFrom 11109 0 _GVY=true:=by decide+kernel
def _GVZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad933bb3169707c855a0f1ea594b44dea980020002
theorem shape24_61:validFrom 11108 0 _GVZ=true:=by decide+kernel
def _GWA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8f3bb263e493dc0410f1ed2415148fefc0020002
theorem shape24_62:validFrom 11107 0 _GWA=true:=by decide+kernel
def _GWB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8b3bb1b1371da14550f1efeecaed7aeac0020002
theorem shape24_63:validFrom 11106 0 _GWB=true:=by decide+kernel
def _GWC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad873bb0fe8ea51817d0f1f2b96ccf9fa0c0020002
theorem shape24_64:validFrom 11105 0 _GWC=true:=by decide+kernel
def _GWD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad833bb04beb2a407b80f1f583fabafe1200020002
theorem shape24_65:validFrom 11104 0 _GWD=true:=by decide+kernel
def _GWE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7f3baf994cad1a7070f1f84e74af963e40020002
theorem shape24_66:validFrom 11103 0 _GWE=true:=by decide+kernel
def _GWF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7b3baee86b40fa6340f1fb11fa60167300020002
theorem shape24_67:validFrom 11102 0 _GWF=true:=by decide+kernel
def _GWG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad773bae402babd7b880f1fdb2f8b4a11e00020002
theorem shape24_68:validFrom 11101 0 _GWG=true:=by decide+kernel
def _GWH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad733bad97f0c6708c60f20053e44a3dce80020002
theorem shape24_69:validFrom 11100 0 _GWH=true:=by decide+kernel
def _GWJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6f3bacefba8feb4ad0f202f4bd2452d4c0020002
theorem shape24_70:validFrom 11099 0 _GWJ=true:=by decide+kernel
def _GWK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6b3bac478909218330f20595833f79f340020002
theorem shape24_71:validFrom 11098 0 _GWK=true:=by decide+kernel
def _GWL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad673bab9f5c3139aaf0f20836369f195440020002
theorem shape24_72:validFrom 11097 0 _GWL=true:=by decide+kernel
def _GWM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad633baaf734090d4950f20ad6d73fcadac0020002
theorem shape24_73:validFrom 11096 0 _GWM=true:=by decide+kernel
def _GWN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5f3baa4f108fc2da50f20d776524f496c0020002
theorem shape24_74:validFrom 11095 0 _GWN=true:=by decide+kernel
def _GWO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5b3ba9a6f1c633dec0f21017e04b308500020002
theorem shape24_75:validFrom 11094 0 _GWO=true:=by decide+kernel
def _GWP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad573ba8fed7ab86d910f212b848b5e49bc0020002
theorem shape24_76:validFrom 11093 0 _GWP=true:=by decide+kernel
def _GWQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad533ba856c240954380f215589e61aaf200020002
theorem shape24_77:validFrom 11092 0 _GWQ=true:=by decide+kernel
def _GWR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4f3ba7aeb184f26030f217f8e150367f40020002
theorem shape24_78:validFrom 11091 0 _GWR=true:=by decide+kernel
def _GWS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4b3ba706a5783177a0f21a9911833a2180020002
theorem shape24_79:validFrom 11090 0 _GWS=true:=by decide+kernel
def _GWU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473ba65e9e1b2bfa50f21d392ef75016c0020002
theorem shape24_80:validFrom 11089 0 _GWU=true:=by decide+kernel
def _GWV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433ba5b69b6d087b10f21fd939afde13c0020002
theorem shape24_81:validFrom 11088 0 _GWV=true:=by decide+kernel
def _GWW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3ba50e9d6ea06570f2227931a97e6a40020002
theorem shape24_82:validFrom 11087 0 _GWW=true:=by decide+kernel
def _GWX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3ba466a41f1a4f70f2251916e796c240020002
theorem shape24_83:validFrom 11086 0 _GWX=true:=by decide+kernel
def _GWY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373ba3beaf7f4f9e40f227b8e966c18700020002
theorem shape24_84:validFrom 11085 0 _GWY=true:=by decide+kernel
def _GWZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333ba316bf8e66f190f22a58a92a6439c0020002
theorem shape24_85:validFrom 11084 0 _GWZ=true:=by decide+kernel
def _GXA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3ba26ed44d39a650f22cf8562f1966c0020002
theorem shape24_86:validFrom 11083 0 _GXA=true:=by decide+kernel
def _GXB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3ba1c6edbaee6300f22f97f078467400020002
theorem shape24_87:validFrom 11082 0 _GXB=true:=by decide+kernel
def _GXC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273ba11f0bd85e7dc0f232377802860900020002
theorem shape24_88:validFrom 11081 0 _GXC=true:=by decide+kernel
def _GXD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233ba0772ea4b0a3c0f234d6ecd13d7100020002
theorem shape24_89:validFrom 11080 0 _GXD=true:=by decide+kernel
def _GXF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3b9fcf5620be2490f237764ee1076dc0020002
theorem shape24_90:validFrom 11079 0 _GXF=true:=by decide+kernel
def _GXG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3b9f27824badb3d0f23a159e354930c0020002
theorem shape24_91:validFrom 11078 0 _GXG=true:=by decide+kernel
def _GXH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173b9e7fb326589ab0f23cb4daca9d9540020002
theorem shape24_92:validFrom 11077 0 _GXH=true:=by decide+kernel
def _GXI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133b9dd7e8afe59330f23f5404a469b340020002
theorem shape24_93:validFrom 11076 0 _GXI=true:=by decide+kernel
def row24 (v:ℕ):List Piece:=match v with
 | 0=>_GTT
 | 1=>_GTU
 | 2=>_GUF
 | 3=>_GUQ
 | 4=>_GVB
 | 5=>_GVM
 | 6=>_GVX
 | 7=>_GWI
 | 8=>_GWT
 | 9=>_GXE
 | 10=>_GTV
 | 11=>_GTW
 | 12=>_GTX
 | 13=>_GTY
 | 14=>_GTZ
 | 15=>_GUA
 | 16=>_GUB
 | 17=>_GUC
 | 18=>_GUD
 | 19=>_GUE
 | 20=>_GUG
 | 21=>_GUH
 | 22=>_GUI
 | 23=>_GUJ
 | 24=>_GUK
 | 25=>_GUL
 | 26=>_GUM
 | 27=>_GUN
 | 28=>_GUO
 | 29=>_GUP
 | 30=>_GUR
 | 31=>_GUS
 | 32=>_GUT
 | 33=>_GUU
 | 34=>_GUV
 | 35=>_GUW
 | 36=>_GUX
 | 37=>_GUY
 | 38=>_GUZ
 | 39=>_GVA
 | 40=>_GVC
 | 41=>_GVD
 | 42=>_GVE
 | 43=>_GVF
 | 44=>_GVG
 | 45=>_GVH
 | 46=>_GVI
 | 47=>_GVJ
 | 48=>_GVK
 | 49=>_GVL
 | 50=>_GVN
 | 51=>_GVO
 | 52=>_GVP
 | 53=>_GVQ
 | 54=>_GVR
 | 55=>_GVS
 | 56=>_GVT
 | 57=>_GVU
 | 58=>_GVV
 | 59=>_GVW
 | 60=>_GVY
 | 61=>_GVZ
 | 62=>_GWA
 | 63=>_GWB
 | 64=>_GWC
 | 65=>_GWD
 | 66=>_GWE
 | 67=>_GWF
 | 68=>_GWG
 | 69=>_GWH
 | 70=>_GWJ
 | 71=>_GWK
 | 72=>_GWL
 | 73=>_GWM
 | 74=>_GWN
 | 75=>_GWO
 | 76=>_GWP
 | 77=>_GWQ
 | 78=>_GWR
 | 79=>_GWS
 | 80=>_GWU
 | 81=>_GWV
 | 82=>_GWW
 | 83=>_GWX
 | 84=>_GWY
 | 85=>_GWZ
 | 86=>_GXA
 | 87=>_GXB
 | 88=>_GXC
 | 89=>_GXD
 | 90=>_GXF
 | 91=>_GXG
 | 92=>_GXH
 | 93=>_GXI
 | _=>[]
theorem checked24 (v:ℕ) (hy:24+v≤117):validFrom (11193-24-v) 0 (row24 v)=true:=by
 have hv:v≤93:=by omega
 interval_cases v
 · exact shape24_0
 · exact shape24_1
 · exact shape24_2
 · exact shape24_3
 · exact shape24_4
 · exact shape24_5
 · exact shape24_6
 · exact shape24_7
 · exact shape24_8
 · exact shape24_9
 · exact shape24_10
 · exact shape24_11
 · exact shape24_12
 · exact shape24_13
 · exact shape24_14
 · exact shape24_15
 · exact shape24_16
 · exact shape24_17
 · exact shape24_18
 · exact shape24_19
 · exact shape24_20
 · exact shape24_21
 · exact shape24_22
 · exact shape24_23
 · exact shape24_24
 · exact shape24_25
 · exact shape24_26
 · exact shape24_27
 · exact shape24_28
 · exact shape24_29
 · exact shape24_30
 · exact shape24_31
 · exact shape24_32
 · exact shape24_33
 · exact shape24_34
 · exact shape24_35
 · exact shape24_36
 · exact shape24_37
 · exact shape24_38
 · exact shape24_39
 · exact shape24_40
 · exact shape24_41
 · exact shape24_42
 · exact shape24_43
 · exact shape24_44
 · exact shape24_45
 · exact shape24_46
 · exact shape24_47
 · exact shape24_48
 · exact shape24_49
 · exact shape24_50
 · exact shape24_51
 · exact shape24_52
 · exact shape24_53
 · exact shape24_54
 · exact shape24_55
 · exact shape24_56
 · exact shape24_57
 · exact shape24_58
 · exact shape24_59
 · exact shape24_60
 · exact shape24_61
 · exact shape24_62
 · exact shape24_63
 · exact shape24_64
 · exact shape24_65
 · exact shape24_66
 · exact shape24_67
 · exact shape24_68
 · exact shape24_69
 · exact shape24_70
 · exact shape24_71
 · exact shape24_72
 · exact shape24_73
 · exact shape24_74
 · exact shape24_75
 · exact shape24_76
 · exact shape24_77
 · exact shape24_78
 · exact shape24_79
 · exact shape24_80
 · exact shape24_81
 · exact shape24_82
 · exact shape24_83
 · exact shape24_84
 · exact shape24_85
 · exact shape24_86
 · exact shape24_87
 · exact shape24_88
 · exact shape24_89
 · exact shape24_90
 · exact shape24_91
 · exact shape24_92
 · exact shape24_93
def _GXJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057400f151fb156c304d8a720002
theorem shape25_0:validFrom 11168 0 _GXJ=true:=by decide+kernel
def _GXK:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000573e0f154bb72b603424a330002
theorem shape25_1:validFrom 11167 0 _GXK=true:=by decide+kernel
def _GXV:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000573c0f1577bbc47c56fc9f40002
theorem shape25_2:validFrom 11166 0 _GXV=true:=by decide+kernel
def _GYG:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000573a0f15a3bf22176d6c9b30002
theorem shape25_3:validFrom 11165 0 _GYG=true:=by decide+kernel
def _GYR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057380f15cfc1443176949720002
theorem shape25_4:validFrom 11164 0 _GYR=true:=by decide+kernel
def _GZC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057360f15fbc22aca74249300002
theorem shape25_5:validFrom 11163 0 _GZC=true:=by decide+kernel
def _GZN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057340f1627c1d5e265488ee0002
theorem shape25_6:validFrom 11162 0 _GZN=true:=by decide+kernel
def _GZY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057320f1653c0457949988aa0002
theorem shape25_7:validFrom 11161 0 _GZY=true:=by decide+kernel
def _HAJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057300f167fbd798f21e08660002
theorem shape25_8:validFrom 11160 0 _HAJ=true:=by decide+kernel
def _HAU:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000572e0f16abb97223edbc8220002
theorem shape25_9:validFrom 11159 0 _HAU=true:=by decide+kernel
def _GXL:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000572c0f16d7b42f37ac9c7dc0002
theorem shape25_10:validFrom 11158 0 _GXL=true:=by decide+kernel
def _GXM:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000572a0f1703adb0ca5f347960002
theorem shape25_11:validFrom 11157 0 _GXM=true:=by decide+kernel
def _GXN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057280f172fa5f6dc05c474e0002
theorem shape25_12:validFrom 11156 0 _GXN=true:=by decide+kernel
def _GXO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057260f175b9d016c9fe87060002
theorem shape25_13:validFrom 11155 0 _GXO=true:=by decide+kernel
def _GXP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057240f178792d07c2d346be0002
theorem shape25_14:validFrom 11154 0 _GXP=true:=by decide+kernel
def _GXQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057220f17b387640aae806740002
theorem shape25_15:validFrom 11153 0 _GXQ=true:=by decide+kernel
def _GXR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057200f17df7abc1822b46290002
theorem shape25_16:validFrom 11152 0 _GXR=true:=by decide+kernel
def _GXS:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571e0f180b6cd8a48b1c5de0002
theorem shape25_17:validFrom 11151 0 _GXS=true:=by decide+kernel
def _GXT:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571c0f18375db9afe6b45920002
theorem shape25_18:validFrom 11150 0 _GXT=true:=by decide+kernel
def _GXU:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571a0f18634d5f546f8c5440002
theorem shape25_19:validFrom 11149 0 _GXU=true:=by decide+kernel
def _GXW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057180f188f3bc95db2484f60002
theorem shape25_20:validFrom 11148 0 _GXW=true:=by decide+kernel
def _GXX:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057160f18bb28f7e5e7e04a70002
theorem shape25_21:validFrom 11147 0 _GXX=true:=by decide+kernel
def _GXY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057140f18e714eaed115c4570002
theorem shape25_22:validFrom 11146 0 _GXY=true:=by decide+kernel
def _GXZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057120f1912ffa2732ecc4060002
theorem shape25_23:validFrom 11145 0 _GXZ=true:=by decide+kernel
def _GYA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057100f193ee91e783fd03b40002
theorem shape25_24:validFrom 11144 0 _GYA=true:=by decide+kernel
def _GYB:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570e0f196ad15efc44003610002
theorem shape25_25:validFrom 11143 0 _GYB=true:=by decide+kernel
def _GYC:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570c0f1996b863ff3c2c30d0002
theorem shape25_26:validFrom 11142 0 _GYC=true:=by decide+kernel
def _GYD:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570a0f19c29e2d8127182b70002
theorem shape25_27:validFrom 11141 0 _GYD=true:=by decide+kernel
def _GYE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057080f19ee82bb8206642610002
theorem shape25_28:validFrom 11140 0 _GYE=true:=by decide+kernel
def _GYF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057060f1a1a660e01d8dc20a0002
theorem shape25_29:validFrom 11139 0 _GYF=true:=by decide+kernel
def _GYH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057040f1a464825009f501b10002
theorem shape25_30:validFrom 11138 0 _GYH=true:=by decide+kernel
def _GYI:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057020f1a7229007e59501580002
theorem shape25_31:validFrom 11137 0 _GYI=true:=by decide+kernel
def _GYJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057000f1a9e08a07b06840fd0002
theorem shape25_32:validFrom 11136 0 _GYJ=true:=by decide+kernel
def _GYK:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fe0f1ac9e704f6a6c40a10002
theorem shape25_33:validFrom 11135 0 _GYK=true:=by decide+kernel
def _GYL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000056fc0f1af5c42df13b7c0440002
theorem shape25_34:validFrom 11134 0 _GYL=true:=by decide+kernel
def _GYM:List Piece:=DZ.decode 62 62 0x3782dace9d900000adf73bc126696b54f0f0f1b21a01b6ac3c40020002
theorem shape25_35:validFrom 11133 0 _GYM=true:=by decide+kernel
def _GYN:List Piece:=DZ.decode 62 62 0x3782dace9d900000adf33bc076fea3730300f1b4d7acd633f400020002
theorem shape25_36:validFrom 11132 0 _GYN=true:=by decide+kernel
def _GYO:List Piece:=DZ.decode 62 62 0x3782dace9d900000adef3bbfc798c9954550f1b795443daaeac0020002
theorem shape25_37:validFrom 11131 0 _GYO=true:=by decide+kernel
def _GYP:List Piece:=DZ.decode 62 62 0x3782dace9d900000adeb3bbf1837ddbbb940f1ba52c7ed111b00020002
theorem shape25_38:validFrom 11130 0 _GYP=true:=by decide+kernel
def _GYQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ade73bbe68dbdfe66480f1bd1037e4666e00020002
theorem shape25_39:validFrom 11129 0 _GYQ=true:=by decide+kernel
def _GYS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ade33bbdb984d0153be0f1bfcd9423ab1080020002
theorem shape25_40:validFrom 11128 0 _GYS=true:=by decide+kernel
def _GYT:List Piece:=DZ.decode 62 62 0x3782dace9d900000addf3bbd0a32ae484510f1c28adcaadeebc0020002
theorem shape25_41:validFrom 11127 0 _GYT=true:=by decide+kernel
def _GYU:List Piece:=DZ.decode 62 62 0x3782dace9d900000addb3bbc5ae57a7f7fe0f1c548117a020080020002
theorem shape25_42:validFrom 11126 0 _GYU=true:=by decide+kernel
def _GYV:List Piece:=DZ.decode 62 62 0x3782dace9d900000add73bbbab9d34baee10f1c80532911447c0020002
theorem shape25_43:validFrom 11125 0 _GYV=true:=by decide+kernel
def _GYW:List Piece:=DZ.decode 62 62 0x3782dace9d900000add33bbafc59dcfa8c40f1cac23ff015cf00020002
theorem shape25_44:validFrom 11124 0 _GYW=true:=by decide+kernel
def _GYX:List Piece:=DZ.decode 62 62 0x3782dace9d900000adcf3bba4d1b733e60b0f1cd7f3997067d40020002
theorem shape25_45:validFrom 11123 0 _GYX=true:=by decide+kernel
def _GYY:List Piece:=DZ.decode 62 62 0x3782dace9d900000adcb3bb99de1f71da770f1d03c1f87896240020002
theorem shape25_46:validFrom 11122 0 _GYY=true:=by decide+kernel
def _GYZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000adc73bb8eead6969de10f1d2f8f1be5887c0020002
theorem shape25_47:validFrom 11121 0 _GYZ=true:=by decide+kernel
def _GZA:List Piece:=DZ.decode 62 62 0x3782dace9d900000adc33bb83f7dc9ba44c0f1d5b5b03d16ed00020002
theorem shape25_48:validFrom 11120 0 _GZA=true:=by decide+kernel
def _GZB:List Piece:=DZ.decode 62 62 0x3782dace9d900000adbf3bb79053180edd30f1d8725b03c48b40020002
theorem shape25_49:validFrom 11119 0 _GZB=true:=by decide+kernel
def _GZD:List Piece:=DZ.decode 62 62 0x3782dace9d900000adbb3bb6e12d5467ad90f1db2ef2126149c0020002
theorem shape25_50:validFrom 11118 0 _GZD=true:=by decide+kernel
def _GZE:List Piece:=DZ.decode 62 62 0x3782dace9d900000adb73bb6320c7ec4a980f1ddeb7568ed5a00020002
theorem shape25_51:validFrom 11117 0 _GZE=true:=by decide+kernel
def _GZF:List Piece:=DZ.decode 62 62 0x3782dace9d900000adb33bb582f09725d710f1e0a7e50768a3c0020002
theorem shape25_52:validFrom 11116 0 _GZF=true:=by decide+kernel
def _GZG:List Piece:=DZ.decode 62 62 0x3782dace9d900000adaf3bb4d3d99d8b3660f1e36440edd32680020002
theorem shape25_53:validFrom 11115 0 _GZG=true:=by decide+kernel
def _GZH:List Piece:=DZ.decode 62 62 0x3782dace9d900000adab3bb424c791f4c8f0f1e620891c2cdc40020002
theorem shape25_54:validFrom 11114 0 _GZH=true:=by decide+kernel
def _GZI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ada73bb375ba74628bc0f1e8dcbd9275d100020002
theorem shape25_55:validFrom 11113 0 _GZI=true:=by decide+kernel
def _GZJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ada33bb2c6b244d48530f1eb98de50adeb40020002
theorem shape25_56:validFrom 11112 0 _GZJ=true:=by decide+kernel
def _GZK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad9f3bb217af034aad00f1ee54eb56d54c00020002
theorem shape25_57:validFrom 11111 0 _GZK=true:=by decide+kernel
def _GZL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad9b3bb168b0afc504e0f1f110e4a4ebec80020002
theorem shape25_58:validFrom 11110 0 _GZL=true:=by decide+kernel
def _GZM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad973bb0b9b74a438e80f1f3ccca3af1c600020002
theorem shape25_59:validFrom 11109 0 _GZM=true:=by decide+kernel
def _GZO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad933bb00ac2d2c649d0f1f6889c18e6d8c0020002
theorem shape25_60:validFrom 11108 0 _GZO=true:=by decide+kernel
def _GZP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8f3baf5bd3494d3870f1f9445a3ecb1e40020002
theorem shape25_61:validFrom 11107 0 _GZP=true:=by decide+kernel
def _GZQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8b3baeace8add85ca0f1fc0004ac9e8d80020002
theorem shape25_62:validFrom 11106 0 _GZQ=true:=by decide+kernel
def _GZR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad873badfe030067ad20f1febb9b62614b80020002
theorem shape25_63:validFrom 11105 0 _GZR=true:=by decide+kernel
def _GZS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad833bad4f2240fb2f50f201771e601342c0020002
theorem shape25_64:validFrom 11104 0 _GZS=true:=by decide+kernel
def _GZT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7f3baca0466f92e4e0f204328da5b46c80020002
theorem shape25_65:validFrom 11103 0 _GZT=true:=by decide+kernel
def _GZU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7b3babf315491c6740f206e7523f8e6300020002
theorem shape25_66:validFrom 11102 0 _GZU=true:=by decide+kernel
def _GZV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad773bab4e2a0bc4fb30f2097aff34ec1340020002
theorem shape25_67:validFrom 11101 0 _GZV=true:=by decide+kernel
def _GZW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad733baaa94371bba420f20c0e999d116f80020002
theorem shape25_68:validFrom 11100 0 _GZW=true:=by decide+kernel
def _GZX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6f3baa04617a2f2070f20ea2217b437e40020002
theorem shape25_69:validFrom 11099 0 _GZX=true:=by decide+kernel
def _GZZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6b3ba95f8425f0a740f2113596cc3d6300020002
theorem shape25_70:validFrom 11098 0 _GZZ=true:=by decide+kernel
def _HAA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad673ba8baab742f0bf0f213c8f99343d040020002
theorem shape25_71:validFrom 11097 0 _HAA=true:=by decide+kernel
def _HAB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad633ba815d765bb7800f2165c49cd122000020002
theorem shape25_72:validFrom 11096 0 _HAB=true:=by decide+kernel
def _HAC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5f3ba77107f9c4cb30f218ef877cecd340020002
theorem shape25_73:validFrom 11095 0 _HAC=true:=by decide+kernel
def _HAD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5b3ba6cc3d311c1c80f21b82b29f8f8e00020002
theorem shape25_74:validFrom 11094 0 _HAD=true:=by decide+kernel
def _HAE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad573ba627770af051f0f21e15cb383eb840020002
theorem shape25_75:validFrom 11093 0 _HAE=true:=by decide+kernel
def _HAF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad533ba582b588128880f220a8d143b5de00020002
theorem shape25_76:validFrom 11092 0 _HAF=true:=by decide+kernel
def _HAG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4f3ba4ddf8a81a30d0f2233bc4c3973cc0020002
theorem shape25_77:validFrom 11091 0 _HAG=true:=by decide+kernel
def _HAH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4b3ba439406a9ec210f225cea5b984f7c0020002
theorem shape25_78:validFrom 11090 0 _HAH=true:=by decide+kernel
def _HAI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473ba3948cd0715620f2286174223aa780020002
theorem shape25_79:validFrom 11089 0 _HAI=true:=by decide+kernel
def _HAK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433ba2efddd8c0cfd0f22af43000fcc0c0020002
theorem shape25_80:validFrom 11088 0 _HAK=true:=by decide+kernel
def _HAL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3ba24b33845e4440f22d86d95286ef00020002
theorem shape25_81:validFrom 11087 0 _HAL=true:=by decide+kernel
def _HAM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3ba1a68dd278a640f23019701a1d6700020002
theorem shape25_82:validFrom 11086 0 _HAM=true:=by decide+kernel
def _HAN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373ba101ecc3e0fe50f232abf4547c06c0020002
theorem shape25_83:validFrom 11085 0 _HAN=true:=by decide+kernel
def _HAO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333ba05d5057c648b0f2353e6604e6dd40020002
theorem shape25_84:validFrom 11084 0 _HAO=true:=by decide+kernel
def _HAP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3b9fb8b88ef98ce0f237d0c52819cc80020002
theorem shape25_85:validFrom 11083 0 _HAP=true:=by decide+kernel
def _HAQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3b9f142568a9bfb0f23a6311c1590140020002
theorem shape25_86:validFrom 11082 0 _HAQ=true:=by decide+kernel
def _HAR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273b9e6f96e5a7e240f23cf54bcd607700020002
theorem shape25_87:validFrom 11081 0 _HAR=true:=by decide+kernel
def _HAS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233b9dcb0d0522fd70f23f87734f740a40020002
theorem shape25_88:validFrom 11080 0 _HAS=true:=by decide+kernel
def _HAT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3b9d2687c7ec0540f2421988444feb00020002
theorem shape25_89:validFrom 11079 0 _HAT=true:=by decide+kernel
def _HAV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3b9c82072d3208c0f244ab8aaf37dd00020002
theorem shape25_90:validFrom 11078 0 _HAV=true:=by decide+kernel
def _HAW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173b9bdd8b35c5fd00f2473d7a8ce80c00020002
theorem shape25_91:validFrom 11077 0 _HAW=true:=by decide+kernel
def _HAX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133b9b3913e0d6e8f0f249cf57e0a45c40020002
theorem shape25_92:validFrom 11076 0 _HAX=true:=by decide+kernel
def row25 (v:ℕ):List Piece:=match v with
 | 0=>_GXJ
 | 1=>_GXK
 | 2=>_GXV
 | 3=>_GYG
 | 4=>_GYR
 | 5=>_GZC
 | 6=>_GZN
 | 7=>_GZY
 | 8=>_HAJ
 | 9=>_HAU
 | 10=>_GXL
 | 11=>_GXM
 | 12=>_GXN
 | 13=>_GXO
 | 14=>_GXP
 | 15=>_GXQ
 | 16=>_GXR
 | 17=>_GXS
 | 18=>_GXT
 | 19=>_GXU
 | 20=>_GXW
 | 21=>_GXX
 | 22=>_GXY
 | 23=>_GXZ
 | 24=>_GYA
 | 25=>_GYB
 | 26=>_GYC
 | 27=>_GYD
 | 28=>_GYE
 | 29=>_GYF
 | 30=>_GYH
 | 31=>_GYI
 | 32=>_GYJ
 | 33=>_GYK
 | 34=>_GYL
 | 35=>_GYM
 | 36=>_GYN
 | 37=>_GYO
 | 38=>_GYP
 | 39=>_GYQ
 | 40=>_GYS
 | 41=>_GYT
 | 42=>_GYU
 | 43=>_GYV
 | 44=>_GYW
 | 45=>_GYX
 | 46=>_GYY
 | 47=>_GYZ
 | 48=>_GZA
 | 49=>_GZB
 | 50=>_GZD
 | 51=>_GZE
 | 52=>_GZF
 | 53=>_GZG
 | 54=>_GZH
 | 55=>_GZI
 | 56=>_GZJ
 | 57=>_GZK
 | 58=>_GZL
 | 59=>_GZM
 | 60=>_GZO
 | 61=>_GZP
 | 62=>_GZQ
 | 63=>_GZR
 | 64=>_GZS
 | 65=>_GZT
 | 66=>_GZU
 | 67=>_GZV
 | 68=>_GZW
 | 69=>_GZX
 | 70=>_GZZ
 | 71=>_HAA
 | 72=>_HAB
 | 73=>_HAC
 | 74=>_HAD
 | 75=>_HAE
 | 76=>_HAF
 | 77=>_HAG
 | 78=>_HAH
 | 79=>_HAI
 | 80=>_HAK
 | 81=>_HAL
 | 82=>_HAM
 | 83=>_HAN
 | 84=>_HAO
 | 85=>_HAP
 | 86=>_HAQ
 | 87=>_HAR
 | 88=>_HAS
 | 89=>_HAT
 | 90=>_HAV
 | 91=>_HAW
 | 92=>_HAX
 | _=>[]
theorem checked25 (v:ℕ) (hy:25+v≤117):validFrom (11193-25-v) 0 (row25 v)=true:=by
 have hv:v≤92:=by omega
 interval_cases v
 · exact shape25_0
 · exact shape25_1
 · exact shape25_2
 · exact shape25_3
 · exact shape25_4
 · exact shape25_5
 · exact shape25_6
 · exact shape25_7
 · exact shape25_8
 · exact shape25_9
 · exact shape25_10
 · exact shape25_11
 · exact shape25_12
 · exact shape25_13
 · exact shape25_14
 · exact shape25_15
 · exact shape25_16
 · exact shape25_17
 · exact shape25_18
 · exact shape25_19
 · exact shape25_20
 · exact shape25_21
 · exact shape25_22
 · exact shape25_23
 · exact shape25_24
 · exact shape25_25
 · exact shape25_26
 · exact shape25_27
 · exact shape25_28
 · exact shape25_29
 · exact shape25_30
 · exact shape25_31
 · exact shape25_32
 · exact shape25_33
 · exact shape25_34
 · exact shape25_35
 · exact shape25_36
 · exact shape25_37
 · exact shape25_38
 · exact shape25_39
 · exact shape25_40
 · exact shape25_41
 · exact shape25_42
 · exact shape25_43
 · exact shape25_44
 · exact shape25_45
 · exact shape25_46
 · exact shape25_47
 · exact shape25_48
 · exact shape25_49
 · exact shape25_50
 · exact shape25_51
 · exact shape25_52
 · exact shape25_53
 · exact shape25_54
 · exact shape25_55
 · exact shape25_56
 · exact shape25_57
 · exact shape25_58
 · exact shape25_59
 · exact shape25_60
 · exact shape25_61
 · exact shape25_62
 · exact shape25_63
 · exact shape25_64
 · exact shape25_65
 · exact shape25_66
 · exact shape25_67
 · exact shape25_68
 · exact shape25_69
 · exact shape25_70
 · exact shape25_71
 · exact shape25_72
 · exact shape25_73
 · exact shape25_74
 · exact shape25_75
 · exact shape25_76
 · exact shape25_77
 · exact shape25_78
 · exact shape25_79
 · exact shape25_80
 · exact shape25_81
 · exact shape25_82
 · exact shape25_83
 · exact shape25_84
 · exact shape25_85
 · exact shape25_86
 · exact shape25_87
 · exact shape25_88
 · exact shape25_89
 · exact shape25_90
 · exact shape25_91
 · exact shape25_92
def _HAY:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000573e0f16464252deff4c7b20002
theorem shape26_0:validFrom 11167 0 _HAY=true:=by decide+kernel
def _HAZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000573c0f1671554a232f7476e0002
theorem shape26_1:validFrom 11166 0 _HAZ=true:=by decide+kernel
def _HBK:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000573a0f169c6709d1ab6872a0002
theorem shape26_2:validFrom 11165 0 _HBK=true:=by decide+kernel
def _HBV:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057380f16c7779203a4c06e60002
theorem shape26_3:validFrom 11164 0 _HBV=true:=by decide+kernel
def _HCG:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057360f16f286e286b6a06a00002
theorem shape26_4:validFrom 11163 0 _HCG=true:=by decide+kernel
def _HCR:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057340f171d94fb74145c65a0002
theorem shape26_5:validFrom 11162 0 _HCR=true:=by decide+kernel
def _HDC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057320f1748a1dccbbd746130002
theorem shape26_6:validFrom 11161 0 _HDC=true:=by decide+kernel
def _HDN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057300f1773ad868db1745cc0002
theorem shape26_7:validFrom 11160 0 _HDN=true:=by decide+kernel
def _HDY:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000572e0f179eb7f8b9f14c5830002
theorem shape26_8:validFrom 11159 0 _HDY=true:=by decide+kernel
def _HEJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000572c0f17c9c133507c0453a0002
theorem shape26_9:validFrom 11158 0 _HEJ=true:=by decide+kernel
def _HBA:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000572a0f17f4c9365152a04f00002
theorem shape26_10:validFrom 11157 0 _HBA=true:=by decide+kernel
def _HBB:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057280f181fd001d5a3a44a50002
theorem shape26_11:validFrom 11156 0 _HBB=true:=by decide+kernel
def _HBC:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057260f184ad595ab101045a0002
theorem shape26_12:validFrom 11155 0 _HBC=true:=by decide+kernel
def _HBD:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057240f1875d9f1eac87040d0002
theorem shape26_13:validFrom 11154 0 _HBD=true:=by decide+kernel
def _HBE:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057220f18a0dd1694cc383c00002
theorem shape26_14:validFrom 11153 0 _HBE=true:=by decide+kernel
def _HBF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057200f18cbdf03a91abc3720002
theorem shape26_15:validFrom 11152 0 _HBF=true:=by decide+kernel
def _HBG:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571e0f18f6dfb927b5443230002
theorem shape26_16:validFrom 11151 0 _HBG=true:=by decide+kernel
def _HBH:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571c0f1921df37109b2c2d30002
theorem shape26_17:validFrom 11150 0 _HBH=true:=by decide+kernel
def _HBI:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571a0f194cdd7d63cb6c2820002
theorem shape26_18:validFrom 11149 0 _HBI=true:=by decide+kernel
def _HBJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057180f1977da8c3a74742310002
theorem shape26_19:validFrom 11148 0 _HBJ=true:=by decide+kernel
def _HBL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057160f19a2d663623c241de0002
theorem shape26_20:validFrom 11147 0 _HBL=true:=by decide+kernel
def _HBM:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057140f19cdd102f44e7818a0002
theorem shape26_21:validFrom 11146 0 _HBM=true:=by decide+kernel
def _HBN:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057120f19f8ca6af0acec1360002
theorem shape26_22:validFrom 11145 0 _HBN=true:=by decide+kernel
def _HBO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057100f1a23c29b5756bc0e00002
theorem shape26_23:validFrom 11144 0 _HBO=true:=by decide+kernel
def _HBP:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570e0f1a4eb994284b2808a0002
theorem shape26_24:validFrom 11143 0 _HBP=true:=by decide+kernel
def _HBQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000570c0f1a79af55638bbc0320002
theorem shape26_25:validFrom 11142 0 _HBQ=true:=by decide+kernel
def _HBR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae173bc31a5a5c76fbb0f1aa4a3df2241140020002
theorem shape26_26:validFrom 11141 0 _HBR=true:=by decide+kernel
def _HBS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae133bc26e8d1437a320f1acf97313217380020002
theorem shape26_27:validFrom 11140 0 _HBS=true:=by decide+kernel
def _HBT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae0f3bc1c2c4aa4f19c0f1afa894bac39900020002
theorem shape26_28:validFrom 11139 0 _HBT=true:=by decide+kernel
def _HBU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae0b3bc117011ebd62d0f1b257a2e90a74c0020002
theorem shape26_29:validFrom 11138 0 _HBU=true:=by decide+kernel
def _HBW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae073bc06b42718281e0f1b5069d9df5f880020002
theorem shape26_30:validFrom 11137 0 _HBW=true:=by decide+kernel
def _HBX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae033bbfbf88a29e6fe0f1b7b584d9864080020002
theorem shape26_31:validFrom 11136 0 _HBX=true:=by decide+kernel
def _HBY:List Piece:=DZ.decode 62 62 0x3782dace9d900000adff3bbf13d3b2113410f1ba64589bbb2fc0020002
theorem shape26_32:validFrom 11135 0 _HBY=true:=by decide+kernel
def _HBZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000adfb3bbe68239fdac890f1bd1318e494ddc0020002
theorem shape26_33:validFrom 11134 0 _HBZ=true:=by decide+kernel
def _HCA:List Piece:=DZ.decode 62 62 0x3782dace9d900000adf73bbdbc786b969310f1bfc1c5b5a5b3c0020002
theorem shape26_34:validFrom 11133 0 _HCA=true:=by decide+kernel
def _HCB:List Piece:=DZ.decode 62 62 0x3782dace9d900000adf33bbd10d2160dd050f1c2705f0bc8bec0020002
theorem shape26_35:validFrom 11132 0 _HCB=true:=by decide+kernel
def _HCC:List Piece:=DZ.decode 62 62 0x3782dace9d900000adef3bbc65309edbdc40f1c51ee4e8908f00020002
theorem shape26_36:validFrom 11131 0 _HCC=true:=by decide+kernel
def _HCD:List Piece:=DZ.decode 62 62 0x3782dace9d900000adeb3bbbb9940600bac0f1c7cd574bfd1500020002
theorem shape26_37:validFrom 11130 0 _HCD=true:=by decide+kernel
def _HCE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ade73bbb0dfc4b7c6f90f1ca7bb6360e41c0020002
theorem shape26_38:validFrom 11129 0 _HCE=true:=by decide+kernel
def _HCF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ade33bba62696f4ef300f1cd2a01a6c43400020002
theorem shape26_39:validFrom 11128 0 _HCF=true:=by decide+kernel
def _HCH:List Piece:=DZ.decode 62 62 0x3782dace9d900000addf3bb9b6db717848d0f1cfd8399e1edcc0020002
theorem shape26_40:validFrom 11127 0 _HCH=true:=by decide+kernel
def _HCI:List Piece:=DZ.decode 62 62 0x3782dace9d900000addb3bb90b5251f876d0f1d2865e1c1e24c0020002
theorem shape26_41:validFrom 11126 0 _HCI=true:=by decide+kernel
def _HCJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000add73bb85fce106ae2a0f1d5346f22547580020002
theorem shape26_42:validFrom 11125 0 _HCJ=true:=by decide+kernel
def _HCK:List Piece:=DZ.decode 62 62 0x3782dace9d900000add33bb7b44ead98b170f1d7e26cad9d3a40020002
theorem shape26_43:validFrom 11124 0 _HCK=true:=by decide+kernel
def _HCL:List Piece:=DZ.decode 62 62 0x3782dace9d900000adcf3bb708d4291d5710f1da9056bf8aa3c0020002
theorem shape26_44:validFrom 11123 0 _HCL=true:=by decide+kernel
def _HCM:List Piece:=DZ.decode 62 62 0x3782dace9d900000adcb3bb65d5e82f8cad0f1dd3e2d581cd4c0020002
theorem shape26_45:validFrom 11122 0 _HCM=true:=by decide+kernel
def _HCN:List Piece:=DZ.decode 62 62 0x3782dace9d900000adc73bb5b1edbb2b1110f1dfebf07753bbc0020002
theorem shape26_46:validFrom 11121 0 _HCN=true:=by decide+kernel
def _HCO:List Piece:=DZ.decode 62 62 0x3782dace9d900000adc33bb50681d1b42e50f1e299a01d2f46c0020002
theorem shape26_47:validFrom 11120 0 _HCO=true:=by decide+kernel
def _HCP:List Piece:=DZ.decode 62 62 0x3782dace9d900000adbf3bb45b1ac6941b00f1e5473c49af9400020002
theorem shape26_48:validFrom 11119 0 _HCP=true:=by decide+kernel
def _HCQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000adbb3bb3afb899cad8a0f1e7f4c4fcd49d80020002
theorem shape26_49:validFrom 11118 0 _HCQ=true:=by decide+kernel
def _HCS:List Piece:=DZ.decode 62 62 0x3782dace9d900000adb73bb3045b4af3ea90f1eaa23a383055c0020002
theorem shape26_50:validFrom 11117 0 _HCS=true:=by decide+kernel
def _HCT:List Piece:=DZ.decode 62 62 0x3782dace9d900000adb33bb25902dad84ea0f1ed4f9bf89ec580020002
theorem shape26_51:validFrom 11116 0 _HCT=true:=by decide+kernel
def _HCU:List Piece:=DZ.decode 62 62 0x3782dace9d900000adaf3bb1adaf49138540f1effcea3fb1eb00020002
theorem shape26_52:validFrom 11115 0 _HCU=true:=by decide+kernel
def _HCV:List Piece:=DZ.decode 62 62 0x3782dace9d900000adab3bb1026095a59330f1f2aa250d69b340020002
theorem shape26_53:validFrom 11114 0 _HCV=true:=by decide+kernel
def _HCW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ada73bb05716c08e6ed0f1f5574c61c644c0020002
theorem shape26_54:validFrom 11113 0 _HCW=true:=by decide+kernel
def _HCX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ada33bafabd1c9ce21e0f1f804603cc77880020002
theorem shape26_55:validFrom 11112 0 _HCX=true:=by decide+kernel
def _HCY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad9f3baf0091b164a3f0f1fab1609e6d7040020002
theorem shape26_56:validFrom 11111 0 _HCY=true:=by decide+kernel
def _HCZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad9b3bae555676ed7e70f1fd5e4d884a0640020002
theorem shape26_57:validFrom 11110 0 _HCZ=true:=by decide+kernel
def _HDA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad973badaa201b31aaa0f2000b26f7395580020002
theorem shape26_58:validFrom 11109 0 _HDA=true:=by decide+kernel
def _HDB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad933bacfeee9dcca420f202b7ececcd6f80020002
theorem shape26_59:validFrom 11108 0 _HDB=true:=by decide+kernel
def _HDD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8f3bac53c1febe7010f205649f69063fc0020002
theorem shape26_60:validFrom 11107 0 _HDD=true:=by decide+kernel
def _HDE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8b3baba89a3e0713e0f208113e6be3b080020002
theorem shape26_61:validFrom 11106 0 _HDE=true:=by decide+kernel
def _HDF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad873baafd775ba684c0f20abdc9f565ed00020002
theorem shape26_62:validFrom 11105 0 _HDF=true:=by decide+kernel
def _HDG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad833baa5259579cc9b0f20d6a42058cd940020002
theorem shape26_63:validFrom 11104 0 _HDG=true:=by decide+kernel
def _HDH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7f3ba9a74031e9e510f21016a69c586bc0020002
theorem shape26_64:validFrom 11103 0 _HDH=true:=by decide+kernel
def _HDI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7b3ba8fdbf513e70f0f212bcaa1f063c40020002
theorem shape26_65:validFrom 11102 0 _HDI=true:=by decide+kernel
def _HDJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad773ba85c286bb243c0f2154305b536f100020002
theorem shape26_66:validFrom 11101 0 _HDJ=true:=by decide+kernel
def _HDK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad733ba7ba961d06bbd0f217c94eefe510c0020002
theorem shape26_67:validFrom 11100 0 _HDK=true:=by decide+kernel
def _HDL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6f3ba719086472f620f21a4f85d2342780020002
theorem shape26_68:validFrom 11099 0 _HDL=true:=by decide+kernel
def _HDM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6b3ba6777f42bfcb50f21cd5aa5900d2c0020002
theorem shape26_69:validFrom 11098 0 _HDM=true:=by decide+kernel
def _HDO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad673ba5d5fab7247310f21f5bbc876e33c0020002
theorem shape26_70:validFrom 11097 0 _HDO=true:=by decide+kernel
def _HDP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad633ba5347ac269acc0f221e1bc5a594d00020002
theorem shape26_71:validFrom 11096 0 _HDP=true:=by decide+kernel
def _HDQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5f3ba492ff63c6b5f0f22467a9d4e52840020002
theorem shape26_72:validFrom 11095 0 _HDQ=true:=by decide+kernel
def _HDR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5b3ba3f1889c045a30f226ed84f3ee9740020002
theorem shape26_73:validFrom 11094 0 _HDR=true:=by decide+kernel
def _HDS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad573ba350166a59cae0f229734dba98d480020002
theorem shape26_74:validFrom 11093 0 _HDS=true:=by decide+kernel
def _HDT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad533ba2aea8cf8fd3c0f22bf90425c0b100020002
theorem shape26_75:validFrom 11092 0 _HDT=true:=by decide+kernel
def _HDU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4f3ba20d3fcb4207f0f22e7ea836f7e040020002
theorem shape26_76:validFrom 11091 0 _HDU=true:=by decide+kernel
def _HDV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4b3ba16bdb5d0c12f0f2310439efcfb440020002
theorem shape26_77:validFrom 11090 0 _HDV=true:=by decide+kernel
def _HDW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473ba0ca7b85b6b200f23389b94d253800020002
theorem shape26_78:validFrom 11089 0 _HDW=true:=by decide+kernel
def _HDX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433ba02920447924a0f2360f26521b6d80020002
theorem shape26_79:validFrom 11088 0 _HDX=true:=by decide+kernel
def _HDZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3b9f87c99a1c2310f2389480fb8f73c0020002
theorem shape26_80:validFrom 11087 0 _HDZ=true:=by decide+kernel
def _HEA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3b9ee67785d703c0f23b19c94ca3f100020002
theorem shape26_81:validFrom 11086 0 _HEA=true:=by decide+kernel
def _HEB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373b9e452a08726540f23d9eff42366b00020002
theorem shape26_82:validFrom 11085 0 _HEB=true:=by decide+kernel
def _HEC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333b9da3e12125a6b0f2402422df696540020002
theorem shape26_83:validFrom 11084 0 _HEC=true:=by decide+kernel
def _HED:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3b9d029cd0b97370f242a934211a3240020002
theorem shape26_84:validFrom 11083 0 _HED=true:=by decide+kernel
def _HEE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3b9c615d16651c60f2452e330a6b8e80020002
theorem shape26_85:validFrom 11082 0 _HEE=true:=by decide+kernel
def _HEF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273b9bc021f2f146c0f247b31f983ae500020002
theorem shape26_86:validFrom 11081 0 _HEF=true:=by decide+kernel
def _HEG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233b9b1eeb65955e30f24a37f9cdaa8740020002
theorem shape26_87:validFrom 11080 0 _HEG=true:=by decide+kernel
def _HEH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3b9a7db96f19ed00f24cbcc1a7984c00020002
theorem shape26_88:validFrom 11079 0 _HEH=true:=by decide+kernel
def _HEI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3b99dc8c0eb664d0f24f417729266cc0020002
theorem shape26_89:validFrom 11078 0 _HEI=true:=by decide+kernel
def _HEK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173b993b6345335f60f251c61a4f328280020002
theorem shape26_90:validFrom 11077 0 _HEK=true:=by decide+kernel
def _HEL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133b989a3f11c83ea0f2544aab1cdf0580020002
theorem shape26_91:validFrom 11076 0 _HEL=true:=by decide+kernel
def row26 (v:ℕ):List Piece:=match v with
 | 0=>_HAY
 | 1=>_HAZ
 | 2=>_HBK
 | 3=>_HBV
 | 4=>_HCG
 | 5=>_HCR
 | 6=>_HDC
 | 7=>_HDN
 | 8=>_HDY
 | 9=>_HEJ
 | 10=>_HBA
 | 11=>_HBB
 | 12=>_HBC
 | 13=>_HBD
 | 14=>_HBE
 | 15=>_HBF
 | 16=>_HBG
 | 17=>_HBH
 | 18=>_HBI
 | 19=>_HBJ
 | 20=>_HBL
 | 21=>_HBM
 | 22=>_HBN
 | 23=>_HBO
 | 24=>_HBP
 | 25=>_HBQ
 | 26=>_HBR
 | 27=>_HBS
 | 28=>_HBT
 | 29=>_HBU
 | 30=>_HBW
 | 31=>_HBX
 | 32=>_HBY
 | 33=>_HBZ
 | 34=>_HCA
 | 35=>_HCB
 | 36=>_HCC
 | 37=>_HCD
 | 38=>_HCE
 | 39=>_HCF
 | 40=>_HCH
 | 41=>_HCI
 | 42=>_HCJ
 | 43=>_HCK
 | 44=>_HCL
 | 45=>_HCM
 | 46=>_HCN
 | 47=>_HCO
 | 48=>_HCP
 | 49=>_HCQ
 | 50=>_HCS
 | 51=>_HCT
 | 52=>_HCU
 | 53=>_HCV
 | 54=>_HCW
 | 55=>_HCX
 | 56=>_HCY
 | 57=>_HCZ
 | 58=>_HDA
 | 59=>_HDB
 | 60=>_HDD
 | 61=>_HDE
 | 62=>_HDF
 | 63=>_HDG
 | 64=>_HDH
 | 65=>_HDI
 | 66=>_HDJ
 | 67=>_HDK
 | 68=>_HDL
 | 69=>_HDM
 | 70=>_HDO
 | 71=>_HDP
 | 72=>_HDQ
 | 73=>_HDR
 | 74=>_HDS
 | 75=>_HDT
 | 76=>_HDU
 | 77=>_HDV
 | 78=>_HDW
 | 79=>_HDX
 | 80=>_HDZ
 | 81=>_HEA
 | 82=>_HEB
 | 83=>_HEC
 | 84=>_HED
 | 85=>_HEE
 | 86=>_HEF
 | 87=>_HEG
 | 88=>_HEH
 | 89=>_HEI
 | 90=>_HEK
 | 91=>_HEL
 | _=>[]
theorem checked26 (v:ℕ) (hy:26+v≤117):validFrom (11193-26-v) 0 (row26 v)=true:=by
 have hv:v≤91:=by omega
 interval_cases v
 · exact shape26_0
 · exact shape26_1
 · exact shape26_2
 · exact shape26_3
 · exact shape26_4
 · exact shape26_5
 · exact shape26_6
 · exact shape26_7
 · exact shape26_8
 · exact shape26_9
 · exact shape26_10
 · exact shape26_11
 · exact shape26_12
 · exact shape26_13
 · exact shape26_14
 · exact shape26_15
 · exact shape26_16
 · exact shape26_17
 · exact shape26_18
 · exact shape26_19
 · exact shape26_20
 · exact shape26_21
 · exact shape26_22
 · exact shape26_23
 · exact shape26_24
 · exact shape26_25
 · exact shape26_26
 · exact shape26_27
 · exact shape26_28
 · exact shape26_29
 · exact shape26_30
 · exact shape26_31
 · exact shape26_32
 · exact shape26_33
 · exact shape26_34
 · exact shape26_35
 · exact shape26_36
 · exact shape26_37
 · exact shape26_38
 · exact shape26_39
 · exact shape26_40
 · exact shape26_41
 · exact shape26_42
 · exact shape26_43
 · exact shape26_44
 · exact shape26_45
 · exact shape26_46
 · exact shape26_47
 · exact shape26_48
 · exact shape26_49
 · exact shape26_50
 · exact shape26_51
 · exact shape26_52
 · exact shape26_53
 · exact shape26_54
 · exact shape26_55
 · exact shape26_56
 · exact shape26_57
 · exact shape26_58
 · exact shape26_59
 · exact shape26_60
 · exact shape26_61
 · exact shape26_62
 · exact shape26_63
 · exact shape26_64
 · exact shape26_65
 · exact shape26_66
 · exact shape26_67
 · exact shape26_68
 · exact shape26_69
 · exact shape26_70
 · exact shape26_71
 · exact shape26_72
 · exact shape26_73
 · exact shape26_74
 · exact shape26_75
 · exact shape26_76
 · exact shape26_77
 · exact shape26_78
 · exact shape26_79
 · exact shape26_80
 · exact shape26_81
 · exact shape26_82
 · exact shape26_83
 · exact shape26_84
 · exact shape26_85
 · exact shape26_86
 · exact shape26_87
 · exact shape26_88
 · exact shape26_89
 · exact shape26_90
 · exact shape26_91
def _HEM:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000573c0f176aeecfd37b884d10002
theorem shape27_0:validFrom 11166 0 _HEM=true:=by decide+kernel
def _HEN:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000573a0f17950ef19dc29c4890002
theorem shape27_1:validFrom 11165 0 _HEN=true:=by decide+kernel
def _HEY:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057380f17bf2ddfbdad0c4410002
theorem shape27_2:validFrom 11164 0 _HEY=true:=by decide+kernel
def _HFJ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057360f17e94b9a3339fc3f90002
theorem shape27_3:validFrom 11163 0 _HFJ=true:=by decide+kernel
def _HFU:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057340f18136820fe6aa83af0002
theorem shape27_4:validFrom 11162 0 _HFU=true:=by decide+kernel
def _HGF:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057320f183d83741f3d703650002
theorem shape27_5:validFrom 11161 0 _HGF=true:=by decide+kernel
def _HGQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057300f18679d9395b3a431a0002
theorem shape27_6:validFrom 11160 0 _HGQ=true:=by decide+kernel
def _HHB:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000572e0f1891b67f49a8d02ce0002
theorem shape27_7:validFrom 11159 0 _HHB=true:=by decide+kernel
def _HHM:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000572c0f18bbce376b65442820002
theorem shape27_8:validFrom 11158 0 _HHM=true:=by decide+kernel
def _HHX:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000572a0f18e5e4bbe2c4182340002
theorem shape27_9:validFrom 11157 0 _HHX=true:=by decide+kernel
def _HEO:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057280f190ffa0cafc6701e60002
theorem shape27_10:validFrom 11156 0 _HEO=true:=by decide+kernel
def _HEP:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057260f193a0e29d26b781970002
theorem shape27_11:validFrom 11155 0 _HEP=true:=by decide+kernel
def _HEQ:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057240f196421134ab3101470002
theorem shape27_12:validFrom 11154 0 _HEQ=true:=by decide+kernel
def _HER:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057220f198e32c9189e380f70002
theorem shape27_13:validFrom 11153 0 _HER=true:=by decide+kernel
def _HES:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057200f19b8434b3c2c040a50002
theorem shape27_14:validFrom 11152 0 _HES=true:=by decide+kernel
def _HET:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000571e0f19e25299b55d0c0530002
theorem shape27_15:validFrom 11151 0 _HET=true:=by decide+kernel
def _HEU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae3b3bc57b67074fc0f0f1a0c60b46c0fc40020002
theorem shape27_16:validFrom 11150 0 _HEU=true:=by decide+kernel
def _HEV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae373bc4d3336abde3f0f1a366d9b9087040020002
theorem shape27_17:validFrom 11149 0 _HEV=true:=by decide+kernel
def _HEW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae333bc42b049cd57c70f1a60794f0aa0e40020002
theorem shape27_18:validFrom 11148 0 _HEW=true:=by decide+kernel
def _HEX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae2f3bc382da9d9687e0f1a8a83ceda5e080020002
theorem shape27_19:validFrom 11147 0 _HEX=true:=by decide+kernel
def _HEZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae2b3bc2dab56d010a70f1ab48d1affbd640020002
theorem shape27_20:validFrom 11146 0 _HEZ=true:=by decide+kernel
def _HFA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae273bc232950b14fce0f1ade95337ac0c80020002
theorem shape27_21:validFrom 11145 0 _HFA=true:=by decide+kernel
def _HFB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae233bc18a7977d26820f1b089c184b65f80020002
theorem shape27_22:validFrom 11144 0 _HFB=true:=by decide+kernel
def _HFC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae1f3bc0e262b3394470f1b32a1c971aee40020002
theorem shape27_23:validFrom 11143 0 _HFC=true:=by decide+kernel
def _HFD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae1b3bc03a50bdaa0f10f1b5ca646d57c3c0020002
theorem shape27_24:validFrom 11142 0 _HFD=true:=by decide+kernel
def _HFE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae173bbf92439663d100f1b86a990a70bc00020002
theorem shape27_25:validFrom 11141 0 _HFE=true:=by decide+kernel
def _HFF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae133bbeea3b3dc70bf0f1bb0aba6ce3d040020002
theorem shape27_26:validFrom 11140 0 _HFF=true:=by decide+kernel
def _HFG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae0f3bbe4237b3d3b7e0f1bdaac894b12080020002
theorem shape27_27:validFrom 11139 0 _HFG=true:=by decide+kernel
def _HFH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae0b3bbd9a38f889d9f0f1c04ac381d89840020002
theorem shape27_28:validFrom 11138 0 _HFH=true:=by decide+kernel
def _HFI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae073bbcf23f0be96e50f1c2eaab345a46c0020002
theorem shape27_29:validFrom 11137 0 _HFI=true:=by decide+kernel
def _HFK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae033bbc4a49edf27a70f1c58a7fac361640020002
theorem shape27_30:validFrom 11136 0 _HFK=true:=by decide+kernel
def _HFL:List Piece:=DZ.decode 62 62 0x3782dace9d900000adff3bbba2599ea4f750f1c82a40e96c22c0020002
theorem shape27_31:validFrom 11135 0 _HFL=true:=by decide+kernel
def _HFM:List Piece:=DZ.decode 62 62 0x3782dace9d900000adfb3bbafa6e1e00eaa0f1cac9eeebfc5580020002
theorem shape27_32:validFrom 11134 0 _HFM=true:=by decide+kernel
def _HFN:List Piece:=DZ.decode 62 62 0x3782dace9d900000adf73bba52876c66bd90f1cd6989b26509c0020002
theorem shape27_33:validFrom 11133 0 _HFN=true:=by decide+kernel
def _HFO:List Piece:=DZ.decode 62 62 0x3782dace9d900000adf33bb9aaa5891595c0f1d009113fa9a900020002
theorem shape27_34:validFrom 11132 0 _HFO=true:=by decide+kernel
def _HFP:List Piece:=DZ.decode 62 62 0x3782dace9d900000adef3bb902c8746de480f1d2a88592486e00020002
theorem shape27_35:validFrom 11131 0 _HFP=true:=by decide+kernel
def _HFQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000adeb3bb85af02e6fa520f1d547e6aa416b80020002
theorem shape27_36:validFrom 11130 0 _HFQ=true:=by decide+kernel
def _HFR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ade73bb7b31cb71ade00f1d7e73487948800020002
theorem shape27_37:validFrom 11129 0 _HFR=true:=by decide+kernel
def _HFS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ade33bb70b4e0e6f8710f1da866f2a41e3c0020002
theorem shape27_38:validFrom 11128 0 _HFS=true:=by decide+kernel
def _HFT:List Piece:=DZ.decode 62 62 0x3782dace9d900000addf3bb66384346da720f1dd259692496380020002
theorem shape27_39:validFrom 11127 0 _HFT=true:=by decide+kernel
def _HFV:List Piece:=DZ.decode 62 62 0x3782dace9d900000addb3bb5bbbf291538b0f1dfc4aabfab1d40020002
theorem shape27_40:validFrom 11126 0 _HFV=true:=by decide+kernel
def _HFW:List Piece:=DZ.decode 62 62 0x3782dace9d900000add73bb513feecc6a120f1e263abb0e57b80020002
theorem shape27_41:validFrom 11125 0 _HFW=true:=by decide+kernel
def _HFX:List Piece:=DZ.decode 62 62 0x3782dace9d900000add33bb46c437ec11850f1e5029968fb9ec0020002
theorem shape27_42:validFrom 11124 0 _HFX=true:=by decide+kernel
def _HFY:List Piece:=DZ.decode 62 62 0x3782dace9d900000adcf3bb3c48cdf650980f1e7a173e66bda00020002
theorem shape27_43:validFrom 11123 0 _HFY=true:=by decide+kernel
def _HFZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000adcb3bb31cdb0eb26aa0f1ea403b29365580020002
theorem shape27_44:validFrom 11122 0 _HFZ=true:=by decide+kernel
def _HGA:List Piece:=DZ.decode 62 62 0x3782dace9d900000adc73bb2752e0ca94460f1ecdeef315aee80020002
theorem shape27_45:validFrom 11121 0 _HGA=true:=by decide+kernel
def _HGB:List Piece:=DZ.decode 62 62 0x3782dace9d900000adc33bb1cd85d9498c90f1ef7d8ffed9cdc0020002
theorem shape27_46:validFrom 11120 0 _HGB=true:=by decide+kernel
def _HGC:List Piece:=DZ.decode 62 62 0x3782dace9d900000adbf3bb125e274934f00f1f21c1d91b2c400020002
theorem shape27_47:validFrom 11119 0 _HGC=true:=by decide+kernel
def _HGD:List Piece:=DZ.decode 62 62 0x3782dace9d900000adbb3bb07e43de868100f1f4ba97e9e5fc00020002
theorem shape27_48:validFrom 11118 0 _HGD=true:=by decide+kernel
def _HGE:List Piece:=DZ.decode 62 62 0x3782dace9d900000adb73bafd6aa17837d80f1f758ff05f20a00020002
theorem shape27_49:validFrom 11117 0 _HGE=true:=by decide+kernel
def _HGG:List Piece:=DZ.decode 62 62 0x3782dace9d900000adb33baf2f151ec99690f1f9f752e8d9a5c0020002
theorem shape27_50:validFrom 11116 0 _HGG=true:=by decide+kernel
def _HGH:List Piece:=DZ.decode 62 62 0x3782dace9d900000adaf3bae8784f4b928c0f1fc9593911b5d00020002
theorem shape27_51:validFrom 11115 0 _HGH=true:=by decide+kernel
def _HGI:List Piece:=DZ.decode 62 62 0x3782dace9d900000adab3baddff999522a50f1ff33c0feb756c0020002
theorem shape27_52:validFrom 11114 0 _HGI=true:=by decide+kernel
def _HGJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ada73bad38730c94a3a0f201d1db31ad7180020002
theorem shape27_53:validFrom 11113 0 _HGJ=true:=by decide+kernel
def _HGK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ada33bac90f14e8092c0f2046fe229fdb500020002
theorem shape27_54:validFrom 11112 0 _HGK=true:=by decide+kernel
def _HGL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad9f3babe9745f15f110f2070dd5e7a83bc0020002
theorem shape27_55:validFrom 11111 0 _HGL=true:=by decide+kernel
def _HGM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad9b3bab41fc3e54c760f209abb66aace280020002
theorem shape27_56:validFrom 11110 0 _HGM=true:=by decide+kernel
def _HGN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad973baa9a88ec3d0e30f20c4983b30bc740020002
theorem shape27_57:validFrom 11109 0 _HGN=true:=by decide+kernel
def _HGO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad933ba9f31a692f1460f20ee73dbf43ae80020002
theorem shape27_58:validFrom 11108 0 _HGO=true:=by decide+kernel
def _HGP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8f3ba94bb0b46a4240f21184e49256f700020002
theorem shape27_59:validFrom 11107 0 _HGP=true:=by decide+kernel
def _HGR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8b3ba8a44bce4ee840f21422782ac45f00020002
theorem shape27_60:validFrom 11106 0 _HGR=true:=by decide+kernel
def _HGS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad873ba7fcebb6dcfe90f216bff8888c05c0020002
theorem shape27_61:validFrom 11105 0 _HGS=true:=by decide+kernel
def _HGT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad833ba755906e148eb0f2195d65abadc540020002
theorem shape27_62:validFrom 11104 0 _HGT=true:=by decide+kernel
def _HGU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7f3ba6ae39f3f58c00f21bfabf9429d000020002
theorem shape27_63:validFrom 11103 0 _HGU=true:=by decide+kernel
def _HGV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7b3ba6086959607aa0f21e9201fe7e1580020002
theorem shape27_64:validFrom 11102 0 _HGV=true:=by decide+kernel
def _HGW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad773ba56a26cb9f8c40f2210b0c3581cf00020002
theorem shape27_65:validFrom 11101 0 _HGW=true:=by decide+kernel
def _HGX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad733ba4cbe8c851d390f223840442b8b1c0020002
theorem shape27_66:validFrom 11100 0 _HGX=true:=by decide+kernel
def _HGY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6f3ba42daf4eb6cbc0f225fcea2924d100020002
theorem shape27_67:validFrom 11099 0 _HGY=true:=by decide+kernel
def _HGZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6b3ba38f7a5f8ef550f22875bde5c42ac0020002
theorem shape27_68:validFrom 11098 0 _HGZ=true:=by decide+kernel
def _HHA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad673ba2f149fa19d410f22aee7f7b98afc0020002
theorem shape27_69:validFrom 11097 0 _HHA=true:=by decide+kernel
def _HHC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad633ba2531e1f17e180f22d672ee7a07a00020002
theorem shape27_70:validFrom 11096 0 _HHC=true:=by decide+kernel
def _HHD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5f3ba1b4f6cdc8a6c0f22fdfcc2cdd6500020002
theorem shape27_71:validFrom 11095 0 _HHD=true:=by decide+kernel
def _HHE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5b3ba116d406ec9800f2325857484da000020002
theorem shape27_72:validFrom 11094 0 _HHE=true:=by decide+kernel
def _HHF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad573ba078b5c9c343c0f234d0d03cf2f100020002
theorem shape27_73:validFrom 11093 0 _HHF=true:=by decide+kernel
def _HHG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad533b9fda9c170d18c0f237493707cb9d00020002
theorem shape27_74:validFrom 11092 0 _HHG=true:=by decide+kernel
def _HHH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4f3b9f3c86ee69def0f239c18baa588440020002
theorem shape27_75:validFrom 11091 0 _HHH=true:=by decide+kernel
def _HHI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4b3b9e9e764f7963e0f23c39ce261a7080020002
theorem shape27_76:validFrom 11090 0 _HHI=true:=by decide+kernel
def _HHJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473b9e006a3afc0de0f23eb1fe780fc880020002
theorem shape27_77:validFrom 11089 0 _HHJ=true:=by decide+kernel
def _HHK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433b9d6262b0317950f2412a1ca33a1ac0020002
theorem shape27_78:validFrom 11088 0 _HHK=true:=by decide+kernel
def _HHL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3b9cc45fafda0890f243a228a497ddc0020002
theorem shape27_79:validFrom 11087 0 _HHL=true:=by decide+kernel
def _HHN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3b9c266139355a80f2461a227f2a9600020002
theorem shape27_80:validFrom 11086 0 _HHN=true:=by decide+kernel
def _HHO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373b9b88674d03cc20f248920a2ff0cf80020002
theorem shape27_81:validFrom 11085 0 _HHO=true:=by decide+kernel
def _HHP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333b9aea71ea8504b0f24b09dfb9ebed40020002
theorem shape27_82:validFrom 11084 0 _HHP=true:=by decide+kernel
def _HHQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3b9a4c8112795a00f24d81a31a1a9800020002
theorem shape27_83:validFrom 11083 0 _HHQ=true:=by decide+kernel
def _HHR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3b99ae94c4207920f24ff954537e1b80020002
theorem shape27_84:validFrom 11082 0 _HHR=true:=by decide+kernel
def _HHS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273b9910ad003ab230f25270f363153740020002
theorem shape27_85:validFrom 11081 0 _HHS=true:=by decide+kernel
def _HHT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233b9872c9c607b7e0f254e8804be12080020002
theorem shape27_86:validFrom 11080 0 _HHT=true:=by decide+kernel
def _HHU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3b97d4eb1647d4d0f2575ffb0ae0acc0020002
theorem shape27_87:validFrom 11079 0 _HHU=true:=by decide+kernel
def _HHV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3b973710f03ac0f0f259d763a314fc40020002
theorem shape27_88:validFrom 11078 0 _HHV=true:=by decide+kernel
def _HHW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173b96993b54a0c1b0f25c4eba117cf940020002
theorem shape27_89:validFrom 11077 0 _HHW=true:=by decide+kernel
def _HHY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133b95fb6a42b99450f25ec5fe5919aec0020002
theorem shape27_90:validFrom 11076 0 _HHY=true:=by decide+kernel
def row27 (v:ℕ):List Piece:=match v with
 | 0=>_HEM
 | 1=>_HEN
 | 2=>_HEY
 | 3=>_HFJ
 | 4=>_HFU
 | 5=>_HGF
 | 6=>_HGQ
 | 7=>_HHB
 | 8=>_HHM
 | 9=>_HHX
 | 10=>_HEO
 | 11=>_HEP
 | 12=>_HEQ
 | 13=>_HER
 | 14=>_HES
 | 15=>_HET
 | 16=>_HEU
 | 17=>_HEV
 | 18=>_HEW
 | 19=>_HEX
 | 20=>_HEZ
 | 21=>_HFA
 | 22=>_HFB
 | 23=>_HFC
 | 24=>_HFD
 | 25=>_HFE
 | 26=>_HFF
 | 27=>_HFG
 | 28=>_HFH
 | 29=>_HFI
 | 30=>_HFK
 | 31=>_HFL
 | 32=>_HFM
 | 33=>_HFN
 | 34=>_HFO
 | 35=>_HFP
 | 36=>_HFQ
 | 37=>_HFR
 | 38=>_HFS
 | 39=>_HFT
 | 40=>_HFV
 | 41=>_HFW
 | 42=>_HFX
 | 43=>_HFY
 | 44=>_HFZ
 | 45=>_HGA
 | 46=>_HGB
 | 47=>_HGC
 | 48=>_HGD
 | 49=>_HGE
 | 50=>_HGG
 | 51=>_HGH
 | 52=>_HGI
 | 53=>_HGJ
 | 54=>_HGK
 | 55=>_HGL
 | 56=>_HGM
 | 57=>_HGN
 | 58=>_HGO
 | 59=>_HGP
 | 60=>_HGR
 | 61=>_HGS
 | 62=>_HGT
 | 63=>_HGU
 | 64=>_HGV
 | 65=>_HGW
 | 66=>_HGX
 | 67=>_HGY
 | 68=>_HGZ
 | 69=>_HHA
 | 70=>_HHC
 | 71=>_HHD
 | 72=>_HHE
 | 73=>_HHF
 | 74=>_HHG
 | 75=>_HHH
 | 76=>_HHI
 | 77=>_HHJ
 | 78=>_HHK
 | 79=>_HHL
 | 80=>_HHN
 | 81=>_HHO
 | 82=>_HHP
 | 83=>_HHQ
 | 84=>_HHR
 | 85=>_HHS
 | 86=>_HHT
 | 87=>_HHU
 | 88=>_HHV
 | 89=>_HHW
 | 90=>_HHY
 | _=>[]
theorem checked27 (v:ℕ) (hy:27+v≤117):validFrom (11193-27-v) 0 (row27 v)=true:=by
 have hv:v≤90:=by omega
 interval_cases v
 · exact shape27_0
 · exact shape27_1
 · exact shape27_2
 · exact shape27_3
 · exact shape27_4
 · exact shape27_5
 · exact shape27_6
 · exact shape27_7
 · exact shape27_8
 · exact shape27_9
 · exact shape27_10
 · exact shape27_11
 · exact shape27_12
 · exact shape27_13
 · exact shape27_14
 · exact shape27_15
 · exact shape27_16
 · exact shape27_17
 · exact shape27_18
 · exact shape27_19
 · exact shape27_20
 · exact shape27_21
 · exact shape27_22
 · exact shape27_23
 · exact shape27_24
 · exact shape27_25
 · exact shape27_26
 · exact shape27_27
 · exact shape27_28
 · exact shape27_29
 · exact shape27_30
 · exact shape27_31
 · exact shape27_32
 · exact shape27_33
 · exact shape27_34
 · exact shape27_35
 · exact shape27_36
 · exact shape27_37
 · exact shape27_38
 · exact shape27_39
 · exact shape27_40
 · exact shape27_41
 · exact shape27_42
 · exact shape27_43
 · exact shape27_44
 · exact shape27_45
 · exact shape27_46
 · exact shape27_47
 · exact shape27_48
 · exact shape27_49
 · exact shape27_50
 · exact shape27_51
 · exact shape27_52
 · exact shape27_53
 · exact shape27_54
 · exact shape27_55
 · exact shape27_56
 · exact shape27_57
 · exact shape27_58
 · exact shape27_59
 · exact shape27_60
 · exact shape27_61
 · exact shape27_62
 · exact shape27_63
 · exact shape27_64
 · exact shape27_65
 · exact shape27_66
 · exact shape27_67
 · exact shape27_68
 · exact shape27_69
 · exact shape27_70
 · exact shape27_71
 · exact shape27_72
 · exact shape27_73
 · exact shape27_74
 · exact shape27_75
 · exact shape27_76
 · exact shape27_77
 · exact shape27_78
 · exact shape27_79
 · exact shape27_80
 · exact shape27_81
 · exact shape27_82
 · exact shape27_83
 · exact shape27_84
 · exact shape27_85
 · exact shape27_86
 · exact shape27_87
 · exact shape27_88
 · exact shape27_89
 · exact shape27_90
def _HHZ:List Piece:=DZ.decode 62 1 0x1bc16d674ec80000573a0f188db6d95d40f817e0002
theorem shape28_0:validFrom 11165 0 _HHZ=true:=by decide+kernel
def _HIA:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057380f18b6e42d844e641320002
theorem shape28_1:validFrom 11164 0 _HIA=true:=by decide+kernel
def _HIL:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057360f18e01051ec56a00e60002
theorem shape28_2:validFrom 11163 0 _HIL=true:=by decide+kernel
def _HIW:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057340f19093b467e40e00990002
theorem shape28_3:validFrom 11162 0 _HIW=true:=by decide+kernel
def _HJH:List Piece:=DZ.decode 62 1 0x1bc16d674ec8000057320f1932650b683e9404b0002
theorem shape28_4:validFrom 11161 0 _HJH=true:=by decide+kernel
def _HJS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae633bc83eb356b32590f195b8da093369c0020002
theorem shape28_5:validFrom 11160 0 _HJS=true:=by decide+kernel
def _HKD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae5f3bc79a15c15fb950f1984b505e811ac0020002
theorem shape28_6:validFrom 11159 0 _HKD=true:=by decide+kernel
def _HKO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae5b3bc6f57ceaac0320f19addb3b94ff380020002
theorem shape28_7:validFrom 11158 0 _HKO=true:=by decide+kernel
def _HKZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae573bc650e8d350bd80f19d700416bd0a00020002
theorem shape28_8:validFrom 11157 0 _HKZ=true:=by decide+kernel
def _HLK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae533bc5ac597a953430f1a0024179ab2f40020002
theorem shape28_9:validFrom 11156 0 _HLK=true:=by decide+kernel
def _HIB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae4f3bc507cee0d5bd40f1a2946be0a90b00020002
theorem shape28_10:validFrom 11155 0 _HIB=true:=by decide+kernel
def _HIC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae4b3bc46349066eb5a0f1a526834a452980020002
theorem shape28_11:validFrom 11154 0 _HIC=true:=by decide+kernel
def _HID:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae473bc3bec7eaa76d30f1a7b887b9624b40020002
theorem shape28_12:validFrom 11153 0 _HID=true:=by decide+kernel
def _HIE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae433bc31a4b8e388c50f1aa4a792b1dcec0020002
theorem shape28_13:validFrom 11152 0 _HIE=true:=by decide+kernel
def _HIF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae3f3bc275d3f0696bf0f1acdc57a25a5040020002
theorem shape28_14:validFrom 11151 0 _HIF=true:=by decide+kernel
def _HIG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae3b3bc1d161119662f0f1af6e231da67440020002
theorem shape28_15:validFrom 11150 0 _HIG=true:=by decide+kernel
def _HIH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae373bc12cf2f21bc020f1b1ffdb9b90ff80020002
theorem shape28_16:validFrom 11149 0 _HIH=true:=by decide+kernel
def _HII:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae333bc088899140e060f1b491811efc7e80020002
theorem shape28_17:validFrom 11148 0 _HII=true:=by decide+kernel
def _HIJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae2f3bbfe424efbe6420f1b72313a5066f80020002
theorem shape28_18:validFrom 11147 0 _HIJ=true:=by decide+kernel
def _HIK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae2b3bbf3fc50cdbb200f1b9b49330913800020002
theorem shape28_19:validFrom 11146 0 _HIK=true:=by decide+kernel
def _HIM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae273bbe9b69e8f512e0f1bc45ffc02bb480020002
theorem shape28_20:validFrom 11145 0 _HIM=true:=by decide+kernel
def _HIN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae233bbdf7138466d360f1bed7595264b280020002
theorem shape28_21:validFrom 11144 0 _HIN=true:=by decide+kernel
def _HIO:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae1f3bbd52c1de786210f1c1689fea1e77c0020002
theorem shape28_22:validFrom 11143 0 _HIO=true:=by decide+kernel
def _HIP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae1b3bbcae74f7860560f1c3f9d385e7ea80020002
theorem shape28_23:validFrom 11142 0 _HIP=true:=by decide+kernel
def _HIQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae173bbc0a2ccfec00b0f1c68af4244ffd40020002
theorem shape28_24:validFrom 11141 0 _HIQ=true:=by decide+kernel
def _HIR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae133bbb65e966f1d030f1c91c01c838bf40020002
theorem shape28_25:validFrom 11140 0 _HIR=true:=by decide+kernel
def _HIS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae0f3bbac1aabd4ff550f1cbacfc6ec02ac0020002
theorem shape28_26:validFrom 11139 0 _HIS=true:=by decide+kernel
def _HIT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae0b3bba1d70d24dec20f1ce3de41ac84f80020002
theorem shape28_27:validFrom 11138 0 _HIT=true:=by decide+kernel
def _HIU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae073bb9793ba647fc70f1d0ceb8cae00e40020002
theorem shape28_28:validFrom 11137 0 _HIU=true:=by decide+kernel
def _HIV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ae033bb8d50b399a5e40f1d35f7a7d968700020002
theorem shape28_29:validFrom 11136 0 _HIV=true:=by decide+kernel
def _HIX:List Piece:=DZ.decode 62 62 0x3782dace9d900000adff3bb830df8b8c95b0f1d5f02935cda940020002
theorem shape28_30:validFrom 11135 0 _HIX=true:=by decide+kernel
def _HIY:List Piece:=DZ.decode 62 62 0x3782dace9d900000adfb3bb78cb89cd71f90f1d880c4f0a381c0020002
theorem shape28_31:validFrom 11134 0 _HIY=true:=by decide+kernel
def _HIZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000adf73bb6e8966cc18550f1db114db0f9eac0020002
theorem shape28_32:validFrom 11133 0 _HIZ=true:=by decide+kernel
def _HJA:List Piece:=DZ.decode 62 62 0x3782dace9d900000adf33bb64478fba7fd60f1dda1c375600a80020002
theorem shape28_33:validFrom 11132 0 _HJA=true:=by decide+kernel
def _HJB:List Piece:=DZ.decode 62 62 0x3782dace9d900000adef3bb5a06049e6c3f0f1e032263c64f040020002
theorem shape28_34:validFrom 11131 0 _HJB=true:=by decide+kernel
def _HJC:List Piece:=DZ.decode 62 62 0x3782dace9d900000adeb3bb4fc4c56c56a70f1e2c27608ea5640020002
theorem shape28_35:validFrom 11130 0 _HJC=true:=by decide+kernel
def _HJD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ade73bb4583d22fc5a70f1e552b2d80e9640020002
theorem shape28_36:validFrom 11129 0 _HJD=true:=by decide+kernel
def _HJE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ade33bb3b432add32660f1e7e2dcacb36680020002
theorem shape28_37:validFrom 11128 0 _HJE=true:=by decide+kernel
def _HJF:List Piece:=DZ.decode 62 62 0x3782dace9d900000addf3bb3102cf7a60dc0f1ea72f38567c900020002
theorem shape28_38:validFrom 11127 0 _HJF=true:=by decide+kernel
def _HJG:List Piece:=DZ.decode 62 62 0x3782dace9d900000addb3bb26c2c00d13900f1ed02f760bb1c00020002
theorem shape28_39:validFrom 11126 0 _HJG=true:=by decide+kernel
def _HJI:List Piece:=DZ.decode 62 62 0x3782dace9d900000add73bb1c82fc89c46f0f1ef92e8418ee440020002
theorem shape28_40:validFrom 11125 0 _HJI=true:=by decide+kernel
def _HJJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000add33bb124384f636f20f1f222c626724380020002
theorem shape28_41:validFrom 11124 0 _HJJ=true:=by decide+kernel
def _HJK:List Piece:=DZ.decode 62 62 0x3782dace9d900000adcf3bb080459582d710f1f4b2910df4a3c0020002
theorem shape28_42:validFrom 11123 0 _HJK=true:=by decide+kernel
def _HJL:List Piece:=DZ.decode 62 62 0x3782dace9d900000adcb3bafdc579a422590f1f74248faf769c0020002
theorem shape28_43:validFrom 11122 0 _HJL=true:=by decide+kernel
def _HJM:List Piece:=DZ.decode 62 62 0x3782dace9d900000adc73baf386e5e59b580f1f9d1edea992a00020002
theorem shape28_44:validFrom 11121 0 _HJM=true:=by decide+kernel
def _HJN:List Piece:=DZ.decode 62 62 0x3782dace9d900000adc33bae9489e1113340f1fc617fdfbb3300020002
theorem shape28_45:validFrom 11120 0 _HJN=true:=by decide+kernel
def _HJO:List Piece:=DZ.decode 62 62 0x3782dace9d900000adbf3badf0aa22c4c700f1fef0fed8ece400020002
theorem shape28_46:validFrom 11119 0 _HJO=true:=by decide+kernel
def _HJP:List Piece:=DZ.decode 62 62 0x3782dace9d900000adbb3bad4ccf23d08f00f201806ad4bdc400020002
theorem shape28_47:validFrom 11118 0 _HJP=true:=by decide+kernel
def _HJQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000adb73baca8f8e37c4d90f2040fc3d60ec9c0020002
theorem shape28_48:validFrom 11117 0 _HJQ=true:=by decide+kernel
def _HJR:List Piece:=DZ.decode 62 62 0x3782dace9d900000adb33bac052762804380f2069f09d9fef200020002
theorem shape28_49:validFrom 11116 0 _HJR=true:=by decide+kernel
def _HJT:List Piece:=DZ.decode 62 62 0x3782dace9d900000adaf3bab615aa02426a0f2092e3ce36f6580020002
theorem shape28_50:validFrom 11115 0 _HJT=true:=by decide+kernel
def _HJU:List Piece:=DZ.decode 62 62 0x3782dace9d900000adab3baabd929cc425f0f20bbd5cf0ef6840020002
theorem shape28_51:validFrom 11114 0 _HJU=true:=by decide+kernel
def _HJV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ada73baa19cf58bc5740f20e4c6a010ea300020002
theorem shape28_52:validFrom 11113 0 _HJV=true:=by decide+kernel
def _HJW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ada33ba97610d3547c50f210db6416ae0ec0020002
theorem shape28_53:validFrom 11112 0 _HJW=true:=by decide+kernel
def _HJX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad9f3ba8d2570d44d700f2136a4b2eeca400020002
theorem shape28_54:validFrom 11111 0 _HJX=true:=by decide+kernel
def _HJY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad9b3ba82ea205d52a70f215f91f4cab5640020002
theorem shape28_55:validFrom 11110 0 _HJY=true:=by decide+kernel
def _HJZ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad973ba78af1bd619560f21887e06e79aa80020002
theorem shape28_56:validFrom 11109 0 _HJZ=true:=by decide+kernel
def _HKA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad933ba6e74634462780f21b168e92e76200020002
theorem shape28_57:validFrom 11108 0 _HKA=true:=by decide+kernel
def _HKB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8f3ba6439f69cabbc0f21da529bcd51100020002
theorem shape28_58:validFrom 11107 0 _HKB=true:=by decide+kernel
def _HKC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad8b3ba59ffd5e4b6790f22033b1ead261c0020002
theorem shape28_59:validFrom 11106 0 _HKC=true:=by decide+kernel
def _HKE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad873ba4fc60122434c0f222c2271b6f2d00020002
theorem shape28_60:validFrom 11105 0 _HKE=true:=by decide+kernel
def _HKF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad833ba458c7849d0b30f2255089518bd340020002
theorem shape28_61:validFrom 11104 0 _HKF=true:=by decide+kernel
def _HKG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7f3ba3b533b66e0750f227ded88a47e2c0020002
theorem shape28_62:validFrom 11103 0 _HKG=true:=by decide+kernel
def _HKH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad7b3ba3131361827ea0f22a6759ddf60580020002
theorem shape28_63:validFrom 11102 0 _HKH=true:=by decide+kernel
def _HKI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad773ba278252b8cd4c0f22cd312b5ccad00020002
theorem shape28_64:validFrom 11101 0 _HKI=true:=by decide+kernel
def _HKJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad733ba1dd3b739ceb40f22f3eb9958c5300020002
theorem shape28_65:validFrom 11100 0 _HKJ=true:=by decide+kernel
def _HKK:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6f3ba1425638faa740f231aa4e80156300020002
theorem shape28_66:validFrom 11099 0 _HKK=true:=by decide+kernel
def _HKL:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad6b3ba0a7757c5e1970f23415d172879a40020002
theorem shape28_67:validFrom 11098 0 _HKL=true:=by decide+kernel
def _HKM:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad673ba00c993d0f3b20f23681426fc31380020002
theorem shape28_68:validFrom 11097 0 _HKM=true:=by decide+kernel
def _HKN:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad633b9f71c17bc61640f238eca174e7a700020002
theorem shape28_69:validFrom 11096 0 _HKN=true:=by decide+kernel
def _HKP:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5f3b9ed6ee37ca9790f23b57ee84d5a1c0020002
theorem shape28_70:validFrom 11095 0 _HKP=true:=by decide+kernel
def _HKQ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad5b3b9e3c1f71d4d5b0f23dc3299caca940020002
theorem shape28_71:validFrom 11094 0 _HKQ=true:=by decide+kernel
def _HKR:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad573b9da155292cc2f0f2402e52bf4cf440020002
theorem shape28_72:validFrom 11093 0 _HKR=true:=by decide+kernel
def _HKS:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad533b9d068f5e8a5db0f2429969e9d68940020002
theorem shape28_73:validFrom 11092 0 _HKS=true:=by decide+kernel
def _HKT:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4f3b9c6bce1191afa0f245046f1db94180020002
theorem shape28_74:validFrom 11091 0 _HKT=true:=by decide+kernel
def _HKU:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad4b3b9bd11141e6b4c0f2476f625c652d00020002
theorem shape28_75:validFrom 11090 0 _HKU=true:=by decide+kernel
def _HKV:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad473b9b3658f04169c0f249da43a2fa5900020002
theorem shape28_76:validFrom 11089 0 _HKV=true:=by decide+kernel
def _HKW:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad433b9a9ba51be9ce20f24c4512f458c780020002
theorem shape28_77:validFrom 11088 0 _HKW=true:=by decide+kernel
def _HKX:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3f3b9a00f5c597e760f24eafd04da06280020002
theorem shape28_78:validFrom 11087 0 _HKX=true:=by decide+kernel
def _HKY:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad3b3b99664aec93b800f2511a7bb1b12000020002
theorem shape28_79:validFrom 11086 0 _HKY=true:=by decide+kernel
def _HLA:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad373b98cba491952c40f25385151dab4f00020002
theorem shape28_80:validFrom 11085 0 _HLA=true:=by decide+kernel
def _HLB:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad333b983102b3e462a0f255ef9c946e7580020002
theorem shape28_81:validFrom 11084 0 _HLB=true:=by decide+kernel
def _HLC:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2f3b97966554394090f2585a12131afdc0020002
theorem shape28_82:validFrom 11083 0 _HLC=true:=by decide+kernel
def _HLD:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad2b3b96fbcc71dbd5d0f25ac4759c90a8c0020002
theorem shape28_83:validFrom 11082 0 _HLD=true:=by decide+kernel
def _HLE:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad273b9661380d8416b0f25d2ec72defa540020002
theorem shape28_84:validFrom 11081 0 _HLE=true:=by decide+kernel
def _HLF:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad233b95c6a8267a18a0f25f9906ca179d80020002
theorem shape28_85:validFrom 11080 0 _HLF=true:=by decide+kernel
def _HLG:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1f3b952c1cbd75bc90f26203346e290dc0020002
theorem shape28_86:validFrom 11079 0 _HLG=true:=by decide+kernel
def _HLH:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad1b3b949195d1bf1d10f2646d501d038bc0020002
theorem shape28_87:validFrom 11078 0 _HLH=true:=by decide+kernel
def _HLI:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad173b93f713640e2400f266d759d3c77000020002
theorem shape28_88:validFrom 11077 0 _HLI=true:=by decide+kernel
def _HLJ:List Piece:=DZ.decode 62 62 0x3782dace9d900000ad133b935c9573aaf170f269415195543a40020002
theorem shape28_89:validFrom 11076 0 _HLJ=true:=by decide+kernel
def row28 (v:ℕ):List Piece:=match v with
 | 0=>_HHZ
 | 1=>_HIA
 | 2=>_HIL
 | 3=>_HIW
 | 4=>_HJH
 | 5=>_HJS
 | 6=>_HKD
 | 7=>_HKO
 | 8=>_HKZ
 | 9=>_HLK
 | 10=>_HIB
 | 11=>_HIC
 | 12=>_HID
 | 13=>_HIE
 | 14=>_HIF
 | 15=>_HIG
 | 16=>_HIH
 | 17=>_HII
 | 18=>_HIJ
 | 19=>_HIK
 | 20=>_HIM
 | 21=>_HIN
 | 22=>_HIO
 | 23=>_HIP
 | 24=>_HIQ
 | 25=>_HIR
 | 26=>_HIS
 | 27=>_HIT
 | 28=>_HIU
 | 29=>_HIV
 | 30=>_HIX
 | 31=>_HIY
 | 32=>_HIZ
 | 33=>_HJA
 | 34=>_HJB
 | 35=>_HJC
 | 36=>_HJD
 | 37=>_HJE
 | 38=>_HJF
 | 39=>_HJG
 | 40=>_HJI
 | 41=>_HJJ
 | 42=>_HJK
 | 43=>_HJL
 | 44=>_HJM
 | 45=>_HJN
 | 46=>_HJO
 | 47=>_HJP
 | 48=>_HJQ
 | 49=>_HJR
 | 50=>_HJT
 | 51=>_HJU
 | 52=>_HJV
 | 53=>_HJW
 | 54=>_HJX
 | 55=>_HJY
 | 56=>_HJZ
 | 57=>_HKA
 | 58=>_HKB
 | 59=>_HKC
 | 60=>_HKE
 | 61=>_HKF
 | 62=>_HKG
 | 63=>_HKH
 | 64=>_HKI
 | 65=>_HKJ
 | 66=>_HKK
 | 67=>_HKL
 | 68=>_HKM
 | 69=>_HKN
 | 70=>_HKP
 | 71=>_HKQ
 | 72=>_HKR
 | 73=>_HKS
 | 74=>_HKT
 | 75=>_HKU
 | 76=>_HKV
 | 77=>_HKW
 | 78=>_HKX
 | 79=>_HKY
 | 80=>_HLA
 | 81=>_HLB
 | 82=>_HLC
 | 83=>_HLD
 | 84=>_HLE
 | 85=>_HLF
 | 86=>_HLG
 | 87=>_HLH
 | 88=>_HLI
 | 89=>_HLJ
 | _=>[]
theorem checked28 (v:ℕ) (hy:28+v≤117):validFrom (11193-28-v) 0 (row28 v)=true:=by
 have hv:v≤89:=by omega
 interval_cases v
 · exact shape28_0
 · exact shape28_1
 · exact shape28_2
 · exact shape28_3
 · exact shape28_4
 · exact shape28_5
 · exact shape28_6
 · exact shape28_7
 · exact shape28_8
 · exact shape28_9
 · exact shape28_10
 · exact shape28_11
 · exact shape28_12
 · exact shape28_13
 · exact shape28_14
 · exact shape28_15
 · exact shape28_16
 · exact shape28_17
 · exact shape28_18
 · exact shape28_19
 · exact shape28_20
 · exact shape28_21
 · exact shape28_22
 · exact shape28_23
 · exact shape28_24
 · exact shape28_25
 · exact shape28_26
 · exact shape28_27
 · exact shape28_28
 · exact shape28_29
 · exact shape28_30
 · exact shape28_31
 · exact shape28_32
 · exact shape28_33
 · exact shape28_34
 · exact shape28_35
 · exact shape28_36
 · exact shape28_37
 · exact shape28_38
 · exact shape28_39
 · exact shape28_40
 · exact shape28_41
 · exact shape28_42
 · exact shape28_43
 · exact shape28_44
 · exact shape28_45
 · exact shape28_46
 · exact shape28_47
 · exact shape28_48
 · exact shape28_49
 · exact shape28_50
 · exact shape28_51
 · exact shape28_52
 · exact shape28_53
 · exact shape28_54
 · exact shape28_55
 · exact shape28_56
 · exact shape28_57
 · exact shape28_58
 · exact shape28_59
 · exact shape28_60
 · exact shape28_61
 · exact shape28_62
 · exact shape28_63
 · exact shape28_64
 · exact shape28_65
 · exact shape28_66
 · exact shape28_67
 · exact shape28_68
 · exact shape28_69
 · exact shape28_70
 · exact shape28_71
 · exact shape28_72
 · exact shape28_73
 · exact shape28_74
 · exact shape28_75
 · exact shape28_76
 · exact shape28_77
 · exact shape28_78
 · exact shape28_79
 · exact shape28_80
 · exact shape28_81
 · exact shape28_82
 · exact shape28_83
 · exact shape28_84
 · exact shape28_85
 · exact shape28_86
 · exact shape28_87
 · exact shape28_88
 · exact shape28_89
end EP

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AA
open DZ EP
set_option autoImplicit false
def row (r v:ℕ):List Piece:=match r with
 | 1=>row1 v
 | 2=>row2 v
 | 3=>row3 v
 | 4=>row4 v
 | 5=>row5 v
 | 6=>row6 v
 | 7=>row7 v
 | 8=>row8 v
 | 9=>row9 v
 | 10=>row10 v
 | 11=>row11 v
 | 12=>row12 v
 | 13=>row13 v
 | 14=>row14 v
 | 15=>row15 v
 | 16=>row16 v
 | 17=>row17 v
 | 18=>row18 v
 | 19=>row19 v
 | 20=>row20 v
 | 21=>row21 v
 | 22=>row22 v
 | 23=>row23 v
 | 24=>row24 v
 | 25=>row25 v
 | 26=>row26 v
 | 27=>row27 v
 | 28=>row28 v
 | _=>[]
theorem checked (r v:ℕ) (hr:1≤r) (hR:r≤28) (hy:r+v≤117):validFrom (11193-r-v) 0 (row r v)=true:=by
 interval_cases r
 · exact checked1 v (by omega)
 · exact checked2 v (by omega)
 · exact checked3 v (by omega)
 · exact checked4 v (by omega)
 · exact checked5 v (by omega)
 · exact checked6 v (by omega)
 · exact checked7 v (by omega)
 · exact checked8 v (by omega)
 · exact checked9 v (by omega)
 · exact checked10 v (by omega)
 · exact checked11 v (by omega)
 · exact checked12 v (by omega)
 · exact checked13 v (by omega)
 · exact checked14 v (by omega)
 · exact checked15 v (by omega)
 · exact checked16 v (by omega)
 · exact checked17 v (by omega)
 · exact checked18 v (by omega)
 · exact checked19 v (by omega)
 · exact checked20 v (by omega)
 · exact checked21 v (by omega)
 · exact checked22 v (by omega)
 · exact checked23 v (by omega)
 · exact checked24 v (by omega)
 · exact checked25 v (by omega)
 · exact checked26 v (by omega)
 · exact checked27 v (by omega)
 · exact checked28 v (by omega)
def cap (r v z:ℕ):=eval (row r v) z
end AA
section MergedPart1
namespace AB
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def shifted (a:Nat):List Nat→List Nat→Bool
  | [],_=>true
  | _,[]=>true
  | b::bs,c::cs=>decide (a+b≤c) && shifted a bs cs

def convolution:List Nat→List Nat→List Nat→Bool
  | [],_,_=>true
  | _,_,[]=>true
  | a::xs,ys,c::cs=>shifted a ys (c::cs) && convolution xs ys cs

theorem GUB (a:Nat) (xs ys:List Nat) (h:shifted a xs ys=true)
    (i:Nat) (hi:i<xs.length) (hj:i<ys.length):
    a+(xs[i]?).getD 0≤(ys[i]?).getD 0:=by
  induction xs generalizing ys i with
  | nil=>simp only [List.length_nil] at hi;omega
  | cons x xs ih=>
    cases ys with
    | nil=>simp only [List.length_nil] at hj;omega
    | cons y ys=>
      simp only [shifted,Bool.and_eq_true,decide_eq_true_eq] at h
      cases i with
      | zero=>simpa using h.1
      | succ i=>
        have hh:=ih ys h.2 i (by simpa using hi) (by simpa using hj)
        simpa using hh

theorem ERJ (xs ys zs:List Nat) (h:convolution xs ys zs=true)
    (i j:Nat) (hi:i<xs.length) (hj:j<ys.length) (hk:i+j<zs.length):
    (xs[i]?).getD 0+(ys[j]?).getD 0≤(zs[i+j]?).getD 0:=by
  induction xs generalizing zs i with
  | nil=>simp only [List.length_nil] at hi;omega
  | cons x xs ih=>
    cases zs with
    | nil=>simp only [List.length_nil] at hk;omega
    | cons z zs=>
      simp only [convolution,Bool.and_eq_true] at h
      cases i with
      | zero=>
        simpa using GUB x ys (z::zs) h.1 j hj (by simpa using hk)
      | succ i=>
        have hh:=ih zs h.2 i (by simpa using hi) (by simpa [Nat.succ_add] using hk)
        simpa [Nat.succ_add] using hh

end AB
end MergedPart1
section MergedPart2
namespace AB
set_option maxHeartbeats 8000000

theorem GEQ (a:Nat) (xs ys:List Nat)
    (h: ∀i,i<xs.length→i<ys.length→
      a+(xs[i]?).getD 0≤(ys[i]?).getD 0):shifted a xs ys=true:=by
  induction xs generalizing ys with
  | nil=>rfl
  | cons x xs ih=>
    cases ys with
    | nil=>rfl
    | cons y ys=>
      simp only [shifted,Bool.and_eq_true,decide_eq_true_eq]
      constructor
      · simpa using h 0 (by simp) (by simp)
      · apply ih
        intro i hi hj
        simpa using h (i+1) (by simpa using hi) (by simpa using hj)

theorem FDO (xs ys zs:List Nat)
    (h: ∀i j,i<xs.length→j<ys.length→i+j<zs.length→
      (xs[i]?).getD 0+(ys[j]?).getD 0≤(zs[i+j]?).getD 0):
    convolution xs ys zs=true:=by
  induction xs generalizing zs with
  | nil=>rfl
  | cons x xs ih=>
    cases zs with
    | nil=>rfl
    | cons z zs=>
      simp only [convolution,Bool.and_eq_true]
      constructor
      · apply GEQ
        intro j hj hk
        simpa using h 0 j (by simp) hj (by simpa using hk)
      · apply ih
        intro i j hi hj hk
        simpa [Nat.succ_add] using h (i+1) j (by simpa using hi) hj
          (by simpa [Nat.succ_add] using hk)

abbrev W64:ℕ:=18446744073709551616

def enc (l:List ℕ):ℕ:=List.rec (motive:=fun _=>ℕ) 0 (fun a _ ih=>Nat.add a (Nat.mul W64 ih)) l

@[simp] theorem enc_nil:enc []=0:=rfl
@[simp] theorem enc_cons (a:ℕ) (l:List ℕ):enc (a::l)=a+W64*enc l:=rfl

def allLt (b:ℕ) (l:List ℕ):Bool:=
  List.rec (motive:=fun _=>Bool) true (fun a _ ih=>Bool.rec false ih (Nat.blt a b)) l

theorem allLt_sound (b:ℕ) (l:List ℕ) (h:allLt b l=true): ∀a ∈ l,a<b:=by
  induction l with
  | nil=>simp
  | cons a l ih=>
    change Bool.rec false (allLt b l) (Nat.blt a b)=true at h
    cases hb:Nat.blt a b with
    | false=>rw [hb] at h;exact absurd h Bool.false_ne_true
    | true=>
      rw [hb] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simpa using hb
      · exact ih h x hx

theorem pow_succ64 (m:ℕ):2^(64*(m+1))=W64*2^(64*m):=by
  rw [Nat.mul_succ,Nat.pow_add,Nat.mul_comm]

theorem ETU (m x:ℕ):x*enc (List.replicate m 1)=enc (List.replicate m x):=by
  induction m with
  | zero=>simp
  | succ m ih=>simp only [List.replicate_succ,enc_cons];rw [← ih];ring

theorem enc_ones (m:ℕ):(W64-1)*enc (List.replicate m 1)=2^(64*m)-1:=by
  induction m with
  | zero=>simp
  | succ m ih=>
    rw [pow_succ64]
    simp only [List.replicate_succ,enc_cons,Nat.mul_add,Nat.mul_one]
    have h1:1≤2^(64*m):=Nat.one_le_two_pow
    rw [Nat.mul_left_comm,ih,Nat.mul_sub,Nat.mul_one]
    have:W64≤W64*2^(64*m):=Nat.le_mul_of_pos_right _ h1
    unfold W64 at*
    omega

theorem ones_eq (m:ℕ):(2^(64*m)-1)/(W64-1)=enc (List.replicate m 1):=by
  rw [← enc_ones,Nat.mul_div_cancel_left _ (by decide)]

theorem lane_mod (a x N:ℕ) (ha:a<W64) (hN:0<N):
    (a+W64*x)%(W64*N)=a+W64*(x%N):=by
  obtain ⟨q,r,hr,rfl⟩: ∃q r,r<N∧x=N*q+r:=⟨x/N,x%N,Nat.mod_lt _ hN,(Nat.div_add_mod x N).symm⟩
  have e:a+W64*(N*q+r)=(a+W64*r)+(W64*N)*q:=by ring
  have hm:(N*q+r)%N=r:=by rw [Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]
  rw [e,Nat.add_mul_mod_self_left,hm,Nat.mod_eq_of_lt]
  have:W64*r+W64≤W64*N:=by rw [← Nat.mul_succ];exact Nat.mul_le_mul_left _ hr
  omega

theorem enc_mod (l:List ℕ) (h: ∀a ∈ l,a<W64) (m:ℕ):enc l%2^(64*m)=enc (l.take m):=by
  induction l generalizing m with
  | nil=>simp
  | cons a l ih=>
    cases m with
    | zero=>simp [Nat.mod_one]
    | succ m=>
      have ha:=h a (List.mem_cons_self ..)
      have hl:=ih (fun x hx=>h x (List.mem_cons_of_mem _ hx)) m
      simp only [enc_cons,List.take_succ_cons]
      rw [pow_succ64,lane_mod _ _ _ ha (Nat.two_pow_pos _),hl]

theorem enc_shift (z:ℕ) (l:List ℕ) (hz:z<W64):enc (z::l)>>>64=enc l:=by
  rw [Nat.shiftRight_eq_div_pow,enc_cons]
  change (z+W64*enc l)/W64=enc l
  rw [Nat.add_mul_div_left _ _ (by decide),Nat.div_eq_of_lt hz,Nat.zero_add]

theorem land_lanes (es:List ℕ) (hes: ∀e ∈ es,e<W64)
    (h:enc es &&& enc (List.replicate es.length (2^63))=enc (List.replicate es.length (2^63))):
    ∀e ∈ es,2^63≤e:=by
  induction es with
  | nil=>simp
  | cons e es ih=>
    have he:=hes e (List.mem_cons_self ..)
    have hes' : ∀x ∈ es,x<W64:=fun x hx=>hes x (List.mem_cons_of_mem _ hx)
    simp only [List.length_cons,List.replicate_succ,enc_cons] at h

    have hsplit:(e+W64*enc es) &&& (2^63+W64*enc (List.replicate es.length (2^63)))=
        (e &&& 2^63)+W64*(enc es &&& enc (List.replicate es.length (2^63))):=by
      apply Nat.eq_of_testBit_eq
      intro j
      have hl1:e &&& 2^63<2^64:=Nat.lt_of_le_of_lt Nat.and_le_left he
      have r1: ∀(x b:ℕ),b<2^64→(b+W64*x).testBit j=
          if j<64 then b.testBit j else x.testBit (j-64):=by
        intro x b hb
        rw [Nat.add_comm]
        exact Nat.testBit_two_pow_mul_add x hb j
      rw [Nat.testBit_and,r1 _ _ he,r1 _ _ (by decide),r1 _ _ hl1]
      split<;>simp [Nat.testBit_and]
    rw [hsplit] at h
    have hl1:e &&& 2^63<W64:=Nat.lt_of_le_of_lt Nat.and_le_left he
    have h63:(2:ℕ)^63<W64:=by decide

    have hlow:e &&& 2^63=2^63:=by
      have:=congrArg (· %W64) h
      simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hl1,Nat.mod_eq_of_lt h63] at this
      exact this
    have hhigh:enc es &&& enc (List.replicate es.length (2^63))=enc (List.replicate es.length (2^63)):=by
      rw [hlow] at h
      exact Nat.eq_of_mul_eq_mul_left (by decide) (Nat.add_left_cancel h)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have hb:x.testBit 63=true:=by
        have h2:(2^63:ℕ).testBit 63=true:=Nat.testBit_two_pow_self
        have:=congrArg (fun y=>y.testBit 63) hlow
        simp only [Nat.testBit_and,h2,Bool.and_true] at this
        exact this
      exact Nat.ge_two_pow_of_testBit hb
    · exact ih hes' hhigh x hx

theorem GJK (a:ℕ) (u w:List ℕ) (h:u.length=w.length)
    (hw: ∀y ∈ w,a+y≤2^63):
    enc u+enc (List.replicate u.length (2^63))=
      enc (List.replicate u.length a)+enc w+enc (List.zipWith (fun z y=>z+2^63-(a+y)) u w):=by
  induction u generalizing w with
  | nil=>cases w<;>simp_all
  | cons z u ih=>
    cases w with
    | nil=>simp at h
    | cons y w=>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at h
      have hy:=hw y (List.mem_cons_self ..)
      have e:=ih w h (fun x hx=>hw x (List.mem_cons_of_mem _ hx))
      simp only [List.length_cons,List.replicate_succ,enc_cons,List.zipWith_cons_cons]
      unfold W64 at*
      omega

def laneCheck (a yv ny zv nz:ℕ):Bool:=
  let m:=cond (Nat.ble ny nz) ny nz
  let mm:=Nat.pow 2 (Nat.mul 64 m)
  let oo:=Nat.div (Nat.sub mm 1) (W64-1)
  let hh:=Nat.mul 9223372036854775808 oo
  Nat.beq (Nat.land (Nat.sub (Nat.add (Nat.mod zv mm) hh) (Nat.add (Nat.mul a oo) (Nat.mod yv mm))) hh) hh

theorem GIE (a:ℕ) (ys zs:List ℕ) (ha:a<2^62) (hys: ∀y ∈ ys,y<2^62)
    (hzs: ∀z ∈ zs,z<2^63) (h:laneCheck a (enc ys) ys.length (enc zs) zs.length=true):
    ∀j,j<ys.length→j<zs.length→a+(ys[j]?).getD 0≤(zs[j]?).getD 0:=by
  intro j hjy hjz
  have hmc:cond (Nat.ble ys.length zs.length) ys.length zs.length=min ys.length zs.length:=by
    by_cases hl:ys.length≤zs.length
    · rw [Nat.ble_eq_true_of_le hl,min_eq_left hl];rfl
    · rw [show Nat.ble ys.length zs.length=false from
        Bool.eq_false_iff.mpr (fun hb=>hl (Nat.le_of_ble_eq_true hb)),min_eq_right (by omega)];rfl
  set m:=min ys.length zs.length with hm
  have hyL: ∀y ∈ ys,y<W64:=fun y hy=>(hys y hy).trans (by decide)
  have hzL: ∀z ∈ zs,z<W64:=fun z hz=>(hzs z hz).trans (by decide)
  set u:=zs.take m
  set w:=ys.take m
  have hu:u.length=m:=by simp [u,m]
  have hw:w.length=m:=by simp [w,m]
  have hZ:enc zs%2^(64*m)=enc u:=enc_mod zs hzL m
  have hY:enc ys%2^(64*m)=enc w:=enc_mod ys hyL m
  have hO:(2^(64*m)-1)/(W64-1)=enc (List.replicate m 1):=ones_eq m
  have hwb: ∀y ∈ w,a+y≤2^63:=by
    intro y hy
    have:=hys y (List.mem_of_mem_take hy)
    have:(2:ℕ)^62+2^62=2^63:=by decide
    omega
  have hid:=GJK a u w (by rw [hu,hw]) hwb
  rw [hu] at hid
  set lanes:=List.zipWith (fun z y=>z+2^63-(a+y)) u w
  have hD:enc u+enc (List.replicate m (2^63))-(enc (List.replicate m a)+enc w)=enc lanes:=by
    omega
  have hlanesLen:lanes.length=m:=by simp [lanes,hu,hw]
  have hlanesL: ∀e ∈ lanes,e<W64:=by
    intro e he
    obtain ⟨k,hk,rfl⟩:=List.mem_iff_getElem.mp he
    have hku:k<u.length:=by rw [hu];omega
    have hkw:k<w.length:=by rw [hw];omega
    have hz:=hzs _ (List.mem_of_mem_take (List.getElem_mem hku))
    simp only [lanes,List.getElem_zipWith]
    unfold W64;omega
  dsimp only [laneCheck] at h
  rw [hmc] at h
  have h2:(enc zs%2^(64*m)+9223372036854775808*((2^(64*m)-1)/(W64-1))-
      (a*((2^(64*m)-1)/(W64-1))+enc ys%2^(64*m))) &&& (9223372036854775808*((2^(64*m)-1)/(W64-1)))=
      9223372036854775808*((2^(64*m)-1)/(W64-1)):=Nat.eq_of_beq_eq_true h
  have hH:9223372036854775808*enc (List.replicate m 1)=enc (List.replicate m (2^63)):=
    ETU m _
  have hA:a*enc (List.replicate m 1)=enc (List.replicate m a):=ETU m a
  rw [hO,hZ,hY,hH,hA,hD,← hlanesLen] at h2
  have hall:=land_lanes lanes hlanesL h2
  have hjm:j<m:=by omega
  have hjl:j<lanes.length:=by omega
  have he:=hall (lanes[j]) (List.getElem_mem hjl)
  have hlj:lanes[j]=u[j]'(by omega)+2^63-(a+w[j]'(by omega)):=by
    simp [lanes,List.getElem_zipWith]
  have huj:u[j]'(by omega)=zs[j]:=by simp [u,List.getElem_take]
  have hwj:w[j]'(by omega)=ys[j]:=by simp [w,List.getElem_take]
  rw [List.getElem?_eq_getElem hjy,List.getElem?_eq_getElem hjz,Option.getD_some,Option.getD_some]
  rw [hlj,huj,hwj] at he
  have:=hzs (zs[j]) (List.getElem_mem hjz)
  omega

def rowsCheck (yv ny:ℕ) (xs:List ℕ):ℕ→ℕ→Bool:=
  List.rec (motive:=fun _=>ℕ→ℕ→Bool) (fun _ _=>true)
    (fun a _ ih zv nz=>Bool.rec false (ih (Nat.shiftRight zv 64) (Nat.sub nz 1)) (laneCheck a yv ny zv nz)) xs

theorem GGC (ys:List ℕ) (hys: ∀y ∈ ys,y<2^62) (xs:List ℕ) (hxs: ∀x ∈ xs,x<2^62)
    (zs:List ℕ) (hzs: ∀z ∈ zs,z<2^63)
    (h:rowsCheck (enc ys) ys.length xs (enc zs) zs.length=true):
    ∀i j,i<xs.length→j<ys.length→i+j<zs.length→
      (xs[i]?).getD 0+(ys[j]?).getD 0≤(zs[i+j]?).getD 0:=by
  induction xs generalizing zs with
  | nil=>intro i j hi;simp at hi
  | cons a xs ih=>
    change Bool.rec false (rowsCheck (enc ys) ys.length xs (Nat.shiftRight (enc zs) 64) (Nat.sub zs.length 1))
      (laneCheck a (enc ys) ys.length (enc zs) zs.length)=true at h
    cases hb:laneCheck a (enc ys) ys.length (enc zs) zs.length with
    | false=>rw [hb] at h;exact absurd h Bool.false_ne_true
    | true=>
      rw [hb] at h
      have ha:=hxs a (List.mem_cons_self ..)
      have hrow:=GIE a ys zs ha hys hzs hb
      intro i j hi hj hij
      cases i with
      | zero=>simpa using hrow j hj (by omega)
      | succ i=>
        cases zs with
        | nil=>simp at hij
        | cons z zs=>
          have hz:z<W64:=(hzs z (List.mem_cons_self ..)).trans (by decide)
          have hshift:Nat.shiftRight (enc (z::zs)) 64=enc zs:=enc_shift z zs hz
          rw [hshift,show Nat.sub (z::zs).length 1=zs.length by simp] at h
          have:=ih (fun x hx=>hxs x (List.mem_cons_of_mem _ hx)) zs
            (fun x hx=>hzs x (List.mem_cons_of_mem _ hx)) h i j (by simpa using hi) hj
            (by simp at hij;omega)
          simpa [show i+1+j=(i+j)+1 by omega] using this

def convolutionS (xs ys zs:List ℕ):Bool:=
  Bool.rec false (rowsCheck (enc ys) ys.length xs (enc zs) zs.length)
    (allLt 4611686018427387904 xs && allLt 4611686018427387904 ys && allLt 9223372036854775808 zs)

theorem _Q0 (xs ys zs:List ℕ) (h:convolutionS xs ys zs=true):
    convolution xs ys zs=true:=by
  unfold convolutionS at h
  cases hb:(allLt 4611686018427387904 xs && allLt 4611686018427387904 ys && allLt 9223372036854775808 zs) with
  | false=>rw [hb] at h;exact absurd h Bool.false_ne_true
  | true=>
    rw [hb] at h
    simp only [Bool.and_eq_true] at hb
    exact FDO xs ys zs (GGC ys (allLt_sound _ _ hb.1.2) xs
      (allLt_sound _ _ hb.1.1) zs (allLt_sound _ _ hb.2) h)

end AB
end MergedPart2
section MergedPart3
namespace EQI


end EQI
end MergedPart3

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace NI
open ProximityPrize.Benchmark RCN095 RCN266
open DY MM AFK
noncomputable section
set_option autoImplicit false
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq P4:=Classical.decEq _
def budget:ℕ:=274980718450187492
abbrev finalCap (p:FlagDegree):=AA.cap p.all p.yz p.zOnly
def charge (L U S:ℕ) (p:FlagDegree):=CY.cost L U S p.all (middle p) (total p)

def combined [DecidableEq P4] (H:P4) (V U:Finset (RegularIndex H)):ℕ:=
  let p:=BF H U
  finalCap p+charge 18000 348 78 (BF H (Finset.univ\V))+
    charge 88902 1382 308 (BF H (V\U))+
    p.all*foldUnit (middle p) (total p) p.all+
    (50-p.all)*foldUnit (229-middle p) (17230-total p) (50-p.all)+
    16220000000000+QQ.cap (BF H Finset.univ).all (middle (BF H Finset.univ)) (total (BF H Finset.univ))

def Budget [DecidableEq P4]:Prop:= ∀(H:P4) (V U:Finset (RegularIndex H)),U⊆V→
  (BF H Finset.univ).all≤50→
  middle (BF H Finset.univ)≤229→
  total (BF H Finset.univ)≤11784→
  ¬TG.cheap.Routeable (BF H V)→
  ¬TG.terminal.Routeable (BF H U)→
  (BF H U).all≤28→
  middle (BF H U)≤117→
  total (BF H U)≤8499→combined H V U≤budget

end
end NI

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace CMW
open ProximityPrize.Benchmark
set_option autoImplicit false
open RCN259
open RCN081 RCN095 RCN100 RCN156 RCN234 RCN266
open Lower80899.Selection DY KZ
open MM (BF KH
  IF JM)
noncomputable section
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq _
local instance:GCDMonoid (MvPolynomial (Fin 4) K):=UniqueFactorizationMonoid.toGCDMonoid _

theorem EMI (u0 u1:I→K) (S:SelectedPair u0 u1):
    let H:=gcd12 S.QA S.QB
    let A:Finset (RegularIndex H):=Finset.univ
    let p:=BF H A
    p.all≤50∧middle p≤229∧total p≤11784:=by
  classical
  dsimp only
  let H:=gcd12 S.QA S.QB
  have hH:H≠0:=by simpa only [H,gcd12] using gcd_ne_zero_of_left S.QA_ne
  have hd:=ZQ H (Finset.univ:Finset (RegularIndex H))
  constructor
  · rw [JM]
    exact (IQ BE _ H hd hH).trans S.GGF
  constructor
  · rw [IF]
    exact (IQ BC _ H hd hH).trans S.common_ys_le
  · rw [KH]
    exact (IQ AT _ H hd hH).trans S.GHS
end
end CMW


end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace ECG

/-- Repeated strict exits can be merged without charging any factor twice. -/
theorem prune {α:Type*} [DecidableEq α] (A:Finset α)
    (route:Finset α→Prop) (paid:α→Prop)
    (step: ∀B⊆A,route B→ ∃C,C ⊂ B∧ ∀x∈B\C,paid x):
    ∃C,C⊆A∧ ¬route C∧ ∀x∈A\C,paid x:=by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih=>
    by_cases hr:route A
    · obtain ⟨B,hB,hpaid⟩:=step A (Finset.Subset.refl A) hr
      obtain ⟨C,hC,hstop,hout⟩:=ih B hB (by
        intro D hD
        exact step D (hD.trans hB.1))
      refine ⟨C,hC.trans hB.1,hstop,?_⟩
      intro x hx
      by_cases hb:x∈B
      · exact hout x (Finset.mem_sdiff.mpr ⟨hb,(Finset.mem_sdiff.mp hx).2⟩)
      · exact hpaid x (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,hb⟩)
    · exact ⟨A,Finset.Subset.refl A,hr,by simp⟩

end ECG

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace BMB

open ProximityPrize.Benchmark
open Lower80899
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266
open DY CS KZ Lower80899.AGR Lower80899.FactorSwitch Lower80899.Oracle

open FV (Potential sumFlag sumFlag_all AQT AXF RawBelow AVS)
open MM (BF JM
  IF KH LY
  AAN AML BCO)

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K

local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

private theorem DJI (s:EA) (p:FlagDegree)
    (hr:1≤p.all) (ht:total p≤s.totalCap)
    (hy:middle p≤s.middleCap) (hs:p.all≤s.slopeCap):
    1≤s.fuel p:=by
  have hmiddle:1≤middle p:=hr.trans (ATD p)
  have htotal:1≤total p:=hmiddle.trans (AIS p)
  unfold EA.fuel
  apply le_min
  · exact (Nat.le_div_iff_mul_le htotal).mpr (by simpa using ht)
  · apply le_min
    · exact (Nat.le_div_iff_mul_le hmiddle).mpr (by simpa using hy)
    · exact (Nat.le_div_iff_mul_le hr).mpr (by simpa using hs)

private theorem BHW (s:EA) (p:FlagDegree)
    (hr:1≤p.all):
    s.fuel p*total p≤s.totalCap∧
      s.fuel p*middle p≤s.middleCap∧
      s.fuel p*p.all≤s.slopeCap:=by
  have hmiddle:1≤middle p:=hr.trans (ATD p)
  have htotal:1≤total p:=hmiddle.trans (AIS p)
  unfold EA.fuel
  refine ⟨?_,?_,?_⟩
  · apply (Nat.le_div_iff_mul_le htotal).mp
    exact min_le_left _ _
  · apply (Nat.le_div_iff_mul_le hmiddle).mp
    exact (min_le_right _ _).trans (min_le_left _ _)
  · apply (Nat.le_div_iff_mul_le hr).mp
    exact (min_le_right _ _).trans (min_le_right _ _)

private theorem AIN (a b:ℕ) (hb:0<b):
    a-(a/b)*b<b:=by
  have hm:=Nat.mod_lt a hb
  have heq:=Nat.mod_add_div' a b
  omega

private theorem BKF (s:EA) (p:FlagDegree)
    (hr:1≤p.all):
    s.totalCap-s.fuel p*total p<total p∨
      s.middleCap-s.fuel p*middle p<middle p∨
      s.slopeCap-s.fuel p*p.all<p.all:=by
  have hall:0<p.all:=by omega
  have hmiddle:0<middle p:=hall.trans_le (ATD p)
  have htotal:0<total p:=hmiddle.trans_le (AIS p)
  unfold EA.fuel
  by_cases hT:s.totalCap/total p≤
      min (s.middleCap/middle p) (s.slopeCap/p.all)
  · left
    rw [min_eq_left hT]
    exact AIN s.totalCap (total p) htotal
  · rw [min_eq_right (Nat.le_of_not_ge hT)]
    by_cases hY:s.middleCap/middle p≤s.slopeCap/p.all
    · right;left
      rw [min_eq_left hY]
      exact AIN s.middleCap (middle p) hmiddle
    · right;right
      rw [min_eq_right (Nat.le_of_not_ge hY)]
      exact AIN s.slopeCap p.all hr

theorem EKV
    (source:EA)
    (hGates: ∀(p:FlagDegree) (j:ℕ),
      1≤p.all→p.all≤50→middle p≤229→total p≤11784→j≤source.fuel p→
      LX (source.totalCap-j*total p) (source.middleCap-j*middle p)
        (source.slopeCap-j*p.all) (middle p) p.all (total p))
    (charge:FlagDegree→ℕ)
    (hpay: ∀(p:FlagDegree) (j:ℕ),
      1≤p.all→p.all≤50→middle p≤229→total p≤11784→j≤source.fuel p→
      PowerRoute.stageCost source.totalCap source.middleCap source.slopeCap
        (Oracle.LP p) j≤charge p)
    (D m:ℕ)
    (hweighted:D=m*181235)
    (hshape:D+source.slopeCap≤
      131071*(source.middleCap+1))
    (hslopeM:source.slopeCap≤m)
    (hmChar:m<2130706433)
    (u0 u1:I→K) (H:P4)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma ∈ Gamma,
      (selected gamma).natDegree≤131071)
    (hagreement: ∀gamma ∈ Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (hgap:source.gap≤Module.finrank K
      (IJ (K:=K) D 131071 source.totalCap
        source.slopeCap m IRSProfile.domain u0 u1))
    (A:Finset (RegularIndex H))
    (hroute:source.Routeable (BF H A))
    (hnarrowS:(BF H A).all≤50)
    (hnarrowY:middle (BF H A)≤229)
    (hnarrowT:total (BF H A)≤11784):
    ∃U,U ⊂ A∧ ∀F ∈ A \ U,
      (regularSeeds H selected Gamma F).card≤
        charge (BG H F):=by
  classical
  let p:=BF H A
  have hr:1≤p.all:=hroute.1
  have hA:A.Nonempty:=by
    by_contra hzero
    have hAe:A= ∅ :=Finset.not_nonempty_iff_eq_empty.mp hzero
    subst A
    simp [p,BF,sumFlag] at hr
  have hfuel:1≤source.fuel p:=
    DJI source p hr hroute.2.1 hroute.2.2.1
      hroute.2.2.2.1
  have hfeasibleP:=BHW source p hr
  have hterminalP:=BKF source p hr
  have hfuelSlope:source.fuel p≤source.slopeCap:=by
    calc
      source.fuel p≤source.slopeCap/p.all:=
        (min_le_right _ _).trans (min_le_right _ _)
      _≤source.slopeCap:=Nat.div_le_self _ _
  have hfuelM:source.fuel p≤m:=hfuelSlope.trans hslopeM
  have hfuelChar:source.fuel p<2130706433:=
    hfuelM.trans_lt hmChar
  have hlowpos: ∀j,1≤j→j≤source.fuel p→
      0<D-j*50165:=by
    intro j hj hjfuel
    have hjm:j≤m:=hjfuel.trans hfuelM
    rw [hweighted]
    omega
  have hcapacity: ∀j,1≤j→j≤source.fuel p→
      D-j*50165≤
        (m-j)*181235+j*(131071-1):=by
    intro j _hj hjfuel
    have hjm:j≤m:=hjfuel.trans hfuelM
    rw [hweighted]
    omega
  have hfield:A.card<ENat.card K:=by
    have hcard:A.card≤p.all:=by
      calc
        A.card= ∑ F ∈ A,1:=by simp
        _≤ ∑ F ∈ A,(BG H F).all:=
          Finset.sum_le_sum (fun F _=>Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (JH H F)))
        _=p.all:=by simp only [p,BF,sumFlag_all]
    calc
      (A.card:ENat)≤(50:ℕ):=by
        exact_mod_cast hcard.trans hnarrowS
      _<ENat.card K:=by
        rw [ENat.card_eq_coe_fintype_card,RCN183.BIS]
        norm_num
  have factor_le_aggregate (F:RegularIndex H) (hFA:F ∈ A):
      (BG H F).all≤p.all∧
      middle (BG H F)≤middle p∧
      total (BG H F)≤total p:=by
    have hsub:({F}:Finset (RegularIndex H)) ⊆ A:=
      Finset.singleton_subset_iff.mpr hFA
    simpa [p,BF,sumFlag,middle,total] using
      LY H hsub
  have factorFuel (F:RegularIndex H) (hFA:F ∈ A) (j:ℕ)
      (hj:j≤source.fuel p):
      j≤source.fuel (BG H F):=by
    have hle:=factor_le_aggregate F hFA
    have hFr:1≤(BG H F).all:=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (JH H F))
    have hFm:1≤middle (BG H F):=
      hFr.trans (ATD _)
    have hFt:1≤total (BG H F):=
      hFm.trans (AIS _)
    have hjT:j*total (BG H F)≤
        source.totalCap:=by
      calc
        j*total (BG H F)≤j*total p:=
          Nat.mul_le_mul_left j hle.2.2
        _≤source.fuel p*total p:=
          Nat.mul_le_mul_right (total p) hj
        _≤source.totalCap:=hfeasibleP.1
    have hjY:j*middle (BG H F)≤
        source.middleCap:=by
      calc
        j*middle (BG H F)≤j*middle p:=
          Nat.mul_le_mul_left j hle.2.1
        _≤source.fuel p*middle p:=
          Nat.mul_le_mul_right (middle p) hj
        _≤source.middleCap:=hfeasibleP.2.1
    have hjS:j*(BG H F).all≤
        source.slopeCap:=by
      calc
        j*(BG H F).all≤j*p.all:=
          Nat.mul_le_mul_left j hle.1
        _≤source.fuel p*p.all:=
          Nat.mul_le_mul_right p.all hj
        _≤source.slopeCap:=hfeasibleP.2.2
    unfold EA.fuel
    apply le_min
    · exact (Nat.le_div_iff_mul_le hFt).mpr hjT
    · apply le_min
      · exact (Nat.le_div_iff_mul_le hFm).mpr hjY
      · exact (Nat.le_div_iff_mul_le hFr).mpr hjS
  have hgates: ∀F ∈ A,∀j,j≤source.fuel p→
      LX
        (source.totalCap-j*wt AT F.1)
        (source.middleCap-j*wt BC F.1)
        (source.slopeCap-j*wt BE F.1)
        (wt BC F.1) (wt BE F.1)
        (wt AT F.1):=by
    intro F hFA j hj
    have hc:=GX F.1
    have hle:=factor_le_aggregate F hFA
    have hFr:1≤(BG H F).all:=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (JH H F))
    have hs:=hGates (BG H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR:(BG H F).all=
        wt BE F.1:=hc.1
    have hY:middle (BG H F)=
        wt BC F.1:=hc.2.1
    have hT:total (BG H F)=
        wt AT F.1:=hc.2.2
    simpa only [hR,hY,hT] using hs
  have hcharge: ∀F ∈ A,∀j,j≤source.fuel p→
      Lower80899.PowerRoute.stageCost source.totalCap
        source.middleCap source.slopeCap
        (Lower80899.AGR.LP F) j≤
          charge (BG H F):=by
    intro F hFA j hj
    have hc:=GX F.1
    have hle:=factor_le_aggregate F hFA
    have hFr:1≤(BG H F).all:=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (JH H F))
    have hs:=hpay (BG H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR:(BG H F).all=
        wt BE F.1:=hc.1
    have hY:middle (BG H F)=
        wt BC F.1:=hc.2.1
    have hT:total (BG H F)=
        wt AT F.1:=hc.2.2
    simpa only [Lower80899.AGR.LP,
      Lower80899.Oracle.LP,hR,hY,hT] using hs
  have hmpos:0<m:=by omega
  have hDpos:0<D:=by
    rw [hweighted]
    exact Nat.mul_pos hmpos (by decide)
  have hDa:D≤m*181235:=hweighted.le
  have hP:CK H A ≠ 0:=AHD H A
  have hcP:contactDec p≤wt (BV 131071) (CK H A):=by
    have h:=CS.FAK 131071 (by decide)
      (CK H A) hP
    simpa only [contactDec,p,IF,
      JM] using h
  have hDcap:D-wt (BV 131071) (CK H A)≤
      source.contactCap p:=by
    unfold EA.contactCap
    omega
  have hbandThin:CS.HN 131071
      (D-wt (BV 131071) (CK H A)) 50165
      (wt (BV 131071) (CK H A))
      (wt AT (CK H A))
      (wt BC (CK H A))
      (wt BE (CK H A))
      (source.totalCap-wt AT (CK H A))
      (source.middleCap-wt BC (CK H A))
      (source.slopeCap-wt BE (CK H A))
      (source.fuel p)<source.gap:=by
    rcases hroute.2.2.2.2 with hold | hthin
    · have hold' :LH 50165
          (wt AT (CK H A))
          (wt BC (CK H A))
          (wt BE (CK H A))
          (source.totalCap-wt AT (CK H A))
          (source.middleCap-wt BC (CK H A))
          (source.slopeCap-wt BE (CK H A))
          (source.fuel p)<source.gap:=by
        simpa only [EA.band,p,KH,
          IF,JM] using hold
      exact (CS.CCZ
        _ _ _ _ _ _ _ _ _ _ _).trans_lt hold'
    · have hthin' :CS.HN 131071
          (source.contactCap p) 50165 (contactDec p)
          (wt AT (CK H A))
          (wt BC (CK H A))
          (wt BE (CK H A))
          (source.totalCap-wt AT (CK H A))
          (source.middleCap-wt BC (CK H A))
          (source.slopeCap-wt BE (CK H A))
          (source.fuel p)<source.gap:=by
        simpa only [EA.bandThin,p,KH,
          IF,JM] using hthin
      exact (CS.AZD 131071 50165
        (source.fuel p) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hDcap hcP le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl).trans_lt hthin'
  apply AAA D
    source.totalCap source.slopeCap m source.middleCap
    source.gap 50165 (source.fuel p)
  · exact hDpos
  · exact hDa
  · exact hshape
  · exact hfuel
  · exact hfuelChar
  · exact hlowpos
  · exact hcapacity
  · exact hdegree
  · exact hagreement
  · exact hno
  · exact hA
  · exact hbandThin
  · simpa only [p,KH,
      IF,JM] using hterminalP
  · simpa only [p,KH,
      IF,JM] using hfeasibleP
  · exact hgap
  · exact hfield
  · exact hgates
  · exact hcharge


theorem FTP
    (source:EA)
    (hGates: ∀(p:FlagDegree) (j:ℕ),
      1≤p.all→p.all≤50→middle p≤229→total p≤11784→j≤source.fuel p→
      LX (source.totalCap-j*total p) (source.middleCap-j*middle p)
        (source.slopeCap-j*p.all) (middle p) p.all (total p))
    (charge:FlagDegree→ℕ)
    (hpay: ∀(p:FlagDegree) (j:ℕ),
      1≤p.all→p.all≤50→middle p≤229→total p≤11784→j≤source.fuel p→
      PowerRoute.stageCost source.totalCap source.middleCap source.slopeCap
        (Oracle.LP p) j≤charge p)
    (D m:ℕ)
    (hweighted:D=m*181235)
    (hshape:D+source.slopeCap≤
      131071*(source.middleCap+1))
    (hslopeM:source.slopeCap≤m)
    (hmChar:m<2130706433)
    (u0 u1:I→K) (H:P4)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma ∈ Gamma,
      (selected gamma).natDegree≤131071)
    (hagreement: ∀gamma ∈ Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (hgap:source.gap≤Module.finrank K
      (IJ (K:=K) D 131071 source.totalCap
        source.slopeCap m IRSProfile.domain u0 u1))
    (A:Finset (RegularIndex H))
    (hnarrowS:(BF H A).all≤50)
    (hnarrowY:middle (BF H A)≤229)
    (hnarrowT:total (BF H A)≤11784):
    ∃U,U ⊆ A∧ ¬source.Routeable (BF H U)∧ ∀F ∈ A \ U,
      (regularSeeds H selected Gamma F).card≤charge (BG H F):=by
  apply ECG.prune A (fun B=>source.Routeable (BF H B))
    (fun F=>(regularSeeds H selected Gamma F).card≤charge (BG H F))
  intro B hBA hroute
  have hm:=LY H hBA
  exact EKV source hGates charge hpay D m hweighted hshape hslopeM hmChar
    u0 u1 H selected Gamma hdegree hagreement hno hgap B hroute
    (hm.1.trans hnarrowS) (hm.2.1.trans hnarrowY) (hm.2.2.trans hnarrowT)


theorem prune_exact
    (source:EA)
    (hGates: ∀(p:FlagDegree) (j:ℕ),
      1≤p.all→p.all≤50→middle p≤229→total p≤11784→j≤source.fuel p→
      LX (source.totalCap-j*total p) (source.middleCap-j*middle p)
        (source.slopeCap-j*p.all) (middle p) p.all (total p))
    (D m:ℕ)
    (hweighted:D=m*181235)
    (hshape:D+source.slopeCap≤
      131071*(source.middleCap+1))
    (hslopeM:source.slopeCap≤m)
    (hmChar:m<2130706433)
    (u0 u1:I→K) (H:P4)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree: ∀gamma ∈ Gamma,
      (selected gamma).natDegree≤131071)
    (hagreement: ∀gamma ∈ Gamma,181235≤
      ((Finset.univ:Finset I).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card)
    (hno:BL selected Gamma 131071 80909)
    (hgap:source.gap≤Module.finrank K
      (IJ (K:=K) D 131071 source.totalCap
        source.slopeCap m IRSProfile.domain u0 u1))
    (A:Finset (RegularIndex H))
    (hnarrowS:(BF H A).all≤50)
    (hnarrowY:middle (BF H A)≤229)
    (hnarrowT:total (BF H A)≤11784):
    ∃U,U ⊆ A∧ ¬source.Routeable (BF H U)∧
      (∑ F∈A,(regularSeeds H selected Gamma F).card)≤
        (∑ F∈U,(regularSeeds H selected Gamma F).card)+
        CY.cost source.totalCap source.middleCap source.slopeCap
          (BF H (A \ U)).all
          (middle (BF H (A \ U)))
          (total (BF H (A \ U))):=by
  have hpay (p:FlagDegree) (j:ℕ):
      PowerRoute.stageCost source.totalCap source.middleCap source.slopeCap
        (Oracle.LP p) j≤
      CY.cost source.totalCap source.middleCap source.slopeCap p.all (middle p) (total p):=by
    have hh:=Lower80899.SourceSound.ZB
      source.totalCap source.middleCap source.slopeCap p j
    simpa only [PowerRoute.stageCost,PowerRoute.stagePair,Oracle.LP,
      FactorSwitch.helperPair,CY.cost,PI.pair,
      Nat.zero_mul,Nat.sub_zero] using hh
  obtain ⟨U,hUA,hstop,hpaid⟩:=FTP source hGates
    (fun p=>CY.cost source.totalCap source.middleCap source.slopeCap p.all (middle p) (total p))
    (fun p j _ _ _ _ _=>hpay p j) D m hweighted hshape hslopeM hmChar
    u0 u1 H selected Gamma hdegree hagreement hno hgap A hnarrowS hnarrowY hnarrowT
  refine ⟨U,hUA,hstop,?_⟩
  have hout:=Finset.sum_le_sum (fun F hF=>hpaid F hF)
  have hs:=CY.sum_cost_le (A \ U)
    source.totalCap source.middleCap source.slopeCap
    (fun F=>(BG H F).all)
    (fun F=>middle (BG H F))
    (fun F=>total (BG H F))
  have hbound:=hout.trans hs
  have he:=Finset.sum_sdiff hUA (f:=fun F=>(regularSeeds H selected Gamma F).card)
  have hrest:(∑ F∈A \ U,(regularSeeds H selected Gamma F).card)≤
      CY.cost source.totalCap source.middleCap source.slopeCap
        (BF H (A \ U)).all
        (middle (BF H (A \ U)))
        (total (BF H (A \ U))):=by
    simpa only [BF,sumFlag_all,AQT,AXF] using hbound
  omega


end
end BMB




end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AHU
set_option maxHeartbeats 2000000
theorem cost0 (r y t:ℕ) (hr:1≤r) (hR:r≤28) (hy:y≤117) (ht:t≤11192):CY.cost 3840000 88497 19840 r y t≤3256892485539*t+224424369372269*y+986153322461098*r:=by
 simpa only [CY.cost] using MZ.count_le 3840000 88497 19840 28 117 11192 3256892485539 224424369372269 986153322461098 r y t (by decide+kernel) hr hR hy ht
theorem cost1 (r y t:ℕ) (hr:1≤r) (hR:r≤28) (hy:y≤117) (ht:t≤11192):CY.cost 3200000 44249 9888 r y t≤1625891214897*t+136077046468709*y+595658330646683*r:=by
 simpa only [CY.cost] using MZ.count_le 3200000 44249 9888 28 117 11192 1625891214897 136077046468709 595658330646683 r y t (by decide+kernel) hr hR hy ht
theorem cost2 (r y t:ℕ) (hr:1≤r) (hR:r≤28) (hy:y≤117) (ht:t≤11192):CY.cost 2880000 44249 9888 r y t≤1625891214897*t+130049502859332*y+570013871545208*r:=by
 simpa only [CY.cost] using MZ.count_le 2880000 44249 9888 28 117 11192 1625891214897 130049502859332 570013871545208 r y t (by decide+kernel) hr hR hy ht
theorem cost3 (r y t:ℕ) (hr:1≤r) (hR:r≤28) (hy:y≤117) (ht:t≤11192):CY.cost 1062000 22124 4940 r y t≤812615633673*t+57874051459222*y+254710585448753*r:=by
 simpa only [CY.cost] using MZ.count_le 1062000 22124 4940 28 117 11192 812615633673 57874051459222 254710585448753 r y t (by decide+kernel) hr hR hy ht
theorem cost4 (r y t:ℕ) (hr:1≤r) (hR:r≤28) (hy:y≤117) (ht:t≤11192):CY.cost 531000 11062 2470 r y t≤406307816837*t+28937025729611*y+127355292724377*r:=by
 simpa only [CY.cost] using MZ.count_le 531000 11062 2470 28 117 11192 406307816837 28937025729611 127355292724377 r y t (by decide+kernel) hr hR hy ht
theorem cost5 (r y t:ℕ) (hr:1≤r) (hR:r≤28) (hy:y≤117) (ht:t≤11192):CY.cost 88902 1382 308 r y t≤50714245849*t+4035698934878*y+17718951857007*r:=by
 simpa only [CY.cost] using MZ.count_le 88902 1382 308 28 117 11192 50714245849 4035698934878 17718951857007 r y t (by decide+kernel) hr hR hy ht
theorem cost6 (r y t:ℕ) (hr:1≤r) (hR:r≤28) (hy:y≤117) (ht:t≤11192):CY.cost 3640000 19359 4267 r y t≤706600386625*t+101274217888165*y+440112212494530*r:=by
 simpa only [CY.cost] using MZ.count_le 3640000 19359 4267 28 117 11192 706600386625 101274217888165 440112212494530 r y t (by decide+kernel) hr hR hy ht
end AHU
section MergedPart0
namespace KT
open AB
open DZ
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 100000



def lookup (rows:ℕ→Array ℕ) (r v:ℕ):=((rows r)[v]?).getD 0

theorem BLF (Rcap Ycap:ℕ) (own packed:ℕ→Array ℕ)
    (ho: ∀r,1≤r→ r≤Rcap→(own r).size=Ycap+1-r)
    (hp: ∀r,r≤Rcap→(packed r).size=Ycap+1-r)
    (hc: ∀R r,1≤r→ r≤R→R≤Rcap→
      convolution (own r).toList (packed (R-r)).toList (packed R).toList=true):
    PV.BellmanRows Rcap Ycap (lookup own) (lookup packed):=by
  intro r v R V hr hR hY
  have he:r+R-r=R:=by omega
  have hh:=hc (r+R) r hr (by omega) hR
  rw [he] at hh
  have h:=ERJ (own r).toList (packed R).toList (packed (r+R)).toList hh v V
    (by rw [Array.length_toList,ho r hr (by omega)];omega)
    (by rw [Array.length_toList,hp R (by omega)];omega)
    (by rw [Array.length_toList,hp (r+R) hR];omega)
  simpa only [Array.getElem?_toList,lookup] using h

theorem _Q13 (Rcap Vcap:ℕ) (own packed:ℕ→Array ℕ)
    (ho: ∀r,1≤r→ r≤Rcap→(own r).size=Vcap+1)
    (hp: ∀r,r≤Rcap→(packed r).size=Vcap+1)
    (hc: ∀R r,1≤r→ r≤R→R≤Rcap→
      convolution (own r).toList (packed (R-r)).toList (packed R).toList=true):
    NK.Bellman Rcap Vcap (lookup own) (lookup packed):=by
  intro r v R V hr hR hV
  have he:r+R-r=R:=by omega
  have hh:=hc (r+R) r hr (by omega) hR
  rw [he] at hh
  have h:=ERJ (own r).toList (packed R).toList (packed (r+R)).toList hh v V
    (by rw [Array.length_toList,ho r hr (by omega)];omega)
    (by rw [Array.length_toList,hp R (by omega)];omega)
    (by rw [Array.length_toList,hp (r+R) hR];omega)
  simpa only [Array.getElem?_toList,lookup] using h



def affineCheck (slope base:ℕ) (curve:List Piece):Bool:=
  allCells (fun lo p=>Nat.ble p.base (slope*lo+base) &&
    Nat.ble (value p lo (p.stop-1)) (slope*(p.stop-1)+base)) 0 curve

theorem ETD (slope base finish:ℕ) (curve:List Piece)
    (hv:validFrom finish 0 curve=true) (hc:affineCheck slope base curve=true)
    (z:ℕ) (hz:z<finish):eval curve z≤slope*z+base:=by
  apply DMA (fun z value=>value≤slope*z+base) 0 finish curve hv _ z (Nat.zero_le _) hz
  apply cells_mono _ _ 0 curve (ANC _ 0 curve hc)
  intro lo p h x hlox hx
  simp only [Bool.and_eq_true,Nat.ble_eq] at h
  have hh:=TP.BCJ lo (p.stop-1) x lo 0 p.base base p.slope slope
    le_rfl (Nat.zero_le _) hlox (by omega)
    (by simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero,Nat.sub_zero,Nat.add_comm] using h.1)
    (by simpa only [value,Nat.sub_zero,Nat.add_comm] using h.2)
  simpa only [value,Nat.sub_zero,Nat.add_comm] using hh

end KT
end MergedPart0
section MergedPart1
namespace ARU
open DZ
open FV
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

def affine (p:Potential) (r v z:ℕ):ℕ:=
  p.totalCoeff*(r+v+z)+p.middleCoeff*(r+v)+p.slopeCoeff*r

theorem affine_shift (p:Potential) (r v lo z:ℕ) (h:lo≤z):
    affine p r v z=affine p r v lo+p.totalCoeff*(z-lo):=by
  unfold affine
  rw [show r+v+z=(r+v+lo)+(z-lo) by omega]
  ring

def clippedPiece (slope base lower upper start:ℕ) (p:Piece):Bool:=
  let lo:=max lower start
  let hi:=min upper p.stop
  if lo<hi then Nat.ble (value p start lo) (base+slope*lo) &&
    Nat.ble (value p start (hi-1)) (base+slope*(hi-1)) else true

def clipped (slope base lower upper:ℕ) (curve:List Piece):Bool:=
  allCells (clippedPiece slope base lower upper) 0 curve

theorem FSV (slope base lower upper finish:ℕ) (curve:List Piece)
    (hv:validFrom finish 0 curve=true) (hc:clipped slope base lower upper curve=true)
    (z:ℕ) (hl:lower≤z) (hu:z<upper) (hz:z<finish):
    eval curve z≤base+slope*z:=by
  obtain ⟨lo,p,hlo,hhi,he,hp⟩:=cell_at _ 0 finish curve hv
    (ANC _ 0 curve hc) z (Nat.zero_le _) hz
  have hn:max lower lo<min upper p.stop:=by omega
  simp only [clippedPiece,if_pos hn,Bool.and_eq_true,Nat.ble_eq] at hp
  have hh:=TP.BCJ (max lower lo) (min upper p.stop-1) z lo 0
    p.base base p.slope slope (le_max_right _ _) (Nat.zero_le _) (by omega) (by omega)
    (by simpa only [value,Nat.sub_zero] using hp.1)
    (by simpa only [value,Nat.sub_zero] using hp.2)
  simpa only [eval,he,value,Nat.sub_zero] using hh

def phase (j:ℕ):Potential:=
  if hj:j<7 then (![⟨3256892485539,224424369372269,986153322461098⟩,⟨1625891214897,136077046468709,595658330646683⟩,⟨1625891214897,130049502859332,570013871545208⟩,⟨812615633673,57874051459222,254710585448753⟩,⟨406307816837,28937025729611,127355292724377⟩,⟨50714245849,4035698934878,17718951857007⟩,⟨706600386625,101274217888165,440112212494530⟩]:Fin 7→Potential) ⟨j,hj⟩ else Lower80899.SourceSound.PhaseFinal.potential
def sourceIndex (j:ℕ):=if j<7 then j else 5
def terminal:ℕ→Potential
  | 0=>⟨0,4941578463932,44352901270546⟩
  | 1=>⟨54403376517,3567494416161,16136495626660⟩
  | 2=>⟨51033431681,3361322287002,15331603481093⟩
  | 3=>⟨48610085170,3300429027688,14905350665897⟩
  | _=>⟨47030594766,3239535768375,14722670887955⟩

def floorR:ℕ→ℕ | 0=>0 | 1=>11 | 2=>13 | 3=>14 | _=>15
def floorY:ℕ→ℕ | 0=>0 | 1=>51 | 2=>58 | 3=>65 | _=>68
def floorT:ℕ→ℕ | 0=>0 | 1=>3100 | _=>3500
def CPQ (k r v:ℕ):Prop:=floorR k≤r∧floorY k≤r+v
instance (k r v:ℕ):Decidable (CPQ k r v):=by unfold CPQ;infer_instance
def eligible (k r v z:ℕ):Prop:=CPQ k r v∧floorT k≤r+v+z
instance (k r v z:ℕ):Decidable (eligible k r v z):=by unfold eligible;infer_instance
def classify (r v z:ℕ):ℕ:=
  if eligible 4 r v z then 4 else if eligible 3 r v z then 3 else
    if eligible 2 r v z then 2 else if eligible 1 r v z then 1 else 0
def lower (k r v:ℕ):=floorT k-(r+v)
def upper (k r v:ℕ):=if k<4∧CPQ (k+1) r v then lower (k+1) r v else 11193

theorem FOQ (r v z:ℕ):classify r v z<5:=by unfold classify;split_ifs<;>omega

theorem FKX (r v z:ℕ) (hz:z<11193):
    CPQ (classify r v z) r v∧lower (classify r v z) r v≤z∧
      z<upper (classify r v z) r v:=by
  unfold classify
  split_ifs<;>
    simp_all [eligible,CPQ,floorR,floorY,floorT,lower,upper]<;>
    (try split_ifs)<;>(try simp_all)<;>omega

def phaseCheck (r v cut intercept j:ℕ) (curve:List Piece):Bool:=
  clipped (phase j).totalCoeff (affine (phase j) r v 0+intercept) 0 cut curve

theorem EDJ (r v cut intercept j finish z:ℕ) (curve:List Piece)
    (hv:validFrom finish 0 curve=true) (hc:phaseCheck r v cut intercept j curve=true)
    (hz:z<finish) (hcut:z<cut):
    eval curve z≤affine (phase j) r v z+intercept:=by
  have h:=FSV _ _ 0 cut finish curve hv hc z (Nat.zero_le _) hcut hz
  rw [affine_shift (phase j) r v 0 z (Nat.zero_le _)]
  simpa only [Nat.sub_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def classCheck (r v cut intercept k:ℕ) (present:Bool) (curve:List Piece):Bool:=
  if CPQ k r v then
    clipped (terminal k).totalCoeff (affine (terminal k) r v 0+intercept)
      (lower k r v) (min cut (upper k r v)) curve &&
    (if lower k r v<min cut (min (upper k r v) (11193-r-v)) then present else true)
  else true

theorem FZH (r v cut intercept k z:ℕ) (present:Bool) (curve:List Piece)
    (hv:validFrom (11193-r-v) 0 curve=true)
    (hc:classCheck r v cut intercept k present curve=true)
    (hk:classify r v z=k) (hz:z<11193-r-v) (hcut:z<cut):
    eval curve z≤affine (terminal k) r v z+intercept∧present=true:=by
  have hi:=FKX r v z (by omega)
  rw [hk] at hi
  simp only [classCheck,if_pos hi.1,Bool.and_eq_true] at hc
  have h:=FSV _ _ _ _ _ curve hv hc.1 z hi.2.1 (lt_min hcut hi.2.2) hz
  have hn:lower k r v<min cut (min (upper k r v) (11193-r-v)):=by omega
  simp only [if_pos hn] at hc
  refine ⟨?_,hc.2⟩
  rw [affine_shift (terminal k) r v 0 z (Nat.zero_le _)]
  simpa only [Nat.sub_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem FKG {α:Type*} [Preorder α] (f:ℕ→ℕ→α) (Rcap Ycap:ℕ)
    (hR: ∀r v,r+1≤Rcap→ r+1+v≤Ycap→f r v≤f (r+1) v)
    (hV: ∀r v,r≤Rcap→ r+v+1≤Ycap→f r v≤f r (v+1))
    (r v R V:ℕ) (hr:r≤R) (hv:v≤V) (hcap:R≤Rcap) (hy:R+V≤Ycap):
    f r v≤f R V:=by
  have ha:f r v≤f R v:=by
    induction R,hr using Nat.le_induction with
    | base=>exact le_rfl
    | succ n hn ih=>exact ih (by omega) (by omega) |>.trans (hR n v (by omega) (by omega))
  apply ha.trans
  induction V,hv using Nat.le_induction with
  | base=>exact le_rfl
  | succ n hn ih=>exact ih (by omega) |>.trans (hV R n hcap (by omega))

end ARU
end MergedPart1
section MergedPart2
namespace FM
open ARU CL
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

structure Entry where
  values:Array ℕ
  mask:ℕ
  deriving Inhabited
def zero:Entry:=⟨#[],1⟩
def coeff (d:Entry) (j:ℕ):ℕ:=(d.values[j]?).getD 0
def phaseAt (d:Entry) (j:ℕ):=coeff d j
def terminalAt (d:Entry) (k:ℕ):=coeff d (k+8)
def present (d:Entry) (k:ℕ):Bool:=d.mask.testBit k
def threshold (th:Array ℕ) (j:ℕ):=EK.thresholdAt th j

def check (r v:ℕ) (curve:List DZ.Piece) (th:Array ℕ)
    (d prevR prevV:Entry):Bool:=
  allN (fun j=>phaseCheck r v (threshold th (sourceIndex j)) (phaseAt d j) j curve) 8 &&
  allN (fun k=>classCheck r v (threshold th 5) (terminalAt d k) k (present d k) curve) 5 &&
  allN (fun j=>Nat.ble (coeff prevR j) (coeff d j) && Nat.ble (coeff prevV j) (coeff d j)) 13 &&
  allN (fun k=>(!present prevR k || present d k) && (!present prevV k || present d k)) 5

theorem phase_check (r v:ℕ) (curve:List DZ.Piece) (th:Array ℕ)
    (d prevR prevV:Entry) (h:check r v curve th d prevR prevV=true)
    (j:ℕ) (hj:j<8):
    phaseCheck r v (threshold th (sourceIndex j)) (phaseAt d j) j curve=true:=by
  simp only [check,Bool.and_eq_true] at h
  exact allN_sound _ 8 h.1.1.1 j hj

theorem class_check (r v:ℕ) (curve:List DZ.Piece) (th:Array ℕ)
    (d prevR prevV:Entry) (h:check r v curve th d prevR prevV=true)
    (k:ℕ) (hk:k<5):
    classCheck r v (threshold th 5) (terminalAt d k) k (present d k) curve=true:=by
  simp only [check,Bool.and_eq_true] at h
  exact allN_sound _ 5 h.1.1.2 k hk

theorem coeff_mono (r v:ℕ) (curve:List DZ.Piece) (th:Array ℕ)
    (d prevR prevV:Entry) (h:check r v curve th d prevR prevV=true)
    (j:ℕ) (hj:j<13):coeff prevR j≤coeff d j∧coeff prevV j≤coeff d j:=by
  simp only [check,Bool.and_eq_true] at h
  have hh:=allN_sound _ 13 h.1.2 j hj
  simpa only [Bool.and_eq_true,Nat.ble_eq] using hh

theorem present_mono (r v:ℕ) (curve:List DZ.Piece) (th:Array ℕ)
    (d prevR prevV:Entry) (h:check r v curve th d prevR prevV=true)
    (k:ℕ) (hk:k<5):
    (present prevR k=true→present d k=true)∧(present prevV k=true→present d k=true):=by
  simp only [check,Bool.and_eq_true] at h
  have hh:=allN_sound _ 5 h.2 k hk
  simp only [Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at hh
  constructor
  · intro hp
    rcases hh.1 with hn | hn
    · simp [hp] at hn
    · exact hn
  · intro hp
    rcases hh.2 with hn | hn
    · simp [hp] at hn
    · exact hn

end FM
end MergedPart2

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower

namespace AK

def seriesWAux (m:Nat) (n:Nat):Nat→Nat→Nat→List Nat:=
  Nat.rec (motive:=fun _=>Nat→Nat→Nat→List Nat) (fun _ _ _=>[])
    (fun _ ih prev older code=>
      let z:=Nat.mod code m
      let pred:=Nat.sub (Nat.mul 2 prev) older
      let value:=cond (Nat.beq (Nat.mod z 2) 0) (Nat.add pred (Nat.div z 2)) (Nat.sub pred (Nat.div z 2))
      value::ih value prev (Nat.div code m)) n

def seriesW (n w code:Nat):Array Nat:=(seriesWAux (2^w) n 0 0 code).toArray

end AK

end SubmissionLower
end ProximityPrize
end
