import ProximityPrize.SubmissionLower.AY
import ProximityPrize.SubmissionLower.ZL8vffb
set_option Elab.async false
section
set_option autoImplicit true
namespace qpECY2d
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
private def d0_0:=s! 4189 858 858 40 8 0xad0817ee009f7a89ee008b36fbee00703d6dee004ea67cb41b2bd5593f40114dfbff4002a21ebf40
private def d0_1 :=s! 4189 858 2906 40 8 0x3cac56f61956e240a44f724a19cc828c21ddee00a0224fee00ad6cc1ee00b40133ee00b3dfa5ee00
private def d0_2 :=s! 4189 858 4954 38 4 0x2000f6d7061b5c28804ae507a20256a17462f
private def r0:=j! 4189 858 0x75c8c30a950 [d0_0,d0_1,d0_2]
private def d1_0:=s! 4302 898 898 40 8 0xbb91186a80ab8eeb6a809486be6a807678916a8051b0d1d7ae2d3c493a4011d27afa4002b52cba40
private def d1_1 :=s! 4302 898 2946 40 8 0x4ee327ba916b789571fb886f2ec1eba241f96a80b55dcc6a80c1739f6a80c683726a80c48d456a80
private def d1_2 :=s! 4302 898 4994 38 5 0xb7729e00c302c8800d3c2c2200787e5488034951fc390
private def r1 :=j! 4302 898 0x84f8b82c6d5 [d1_0,d1_1,d1_2]
private def d2_0:=s! 4855 1022 1022 40 8 0xfbf56ae200e02460e200bc5556e20090884ce2005f4c524e483418db1d40145ae3dd4003126c9d40
private def d2_1 :=s! 4855 1022 3070 41 8 0x5defcc0710b7b92c96151f60b4dc4010f289ce2008da6c9710047dd2238802373afdc4010fc874e200
private def d2_2 :=s! 4855 1022 5118 40 7 0x160b036f909ff8758201abb71482032a4733820506cfcbbc6724cfaf95496bd51e856
private def r2 :=j! 4855 1022 0xd911bf0cd46 [d2_0,d2_1,d2_2]
def dataH :Array aqm := #[
  r0,r1,r2
]
end qpECY2d
end
