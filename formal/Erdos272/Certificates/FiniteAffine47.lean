module

public import Erdos272.Certificates.FiniteAffine47.Part00
public import Erdos272.Certificates.FiniteAffine47.Part01
public import Erdos272.Certificates.FiniteAffine47.Part02
public import Erdos272.Certificates.FiniteAffine47.Part03
public import Erdos272.Certificates.FiniteAffine47.Part04
public import Erdos272.Certificates.FiniteAffine47.Part05
public import Erdos272.Certificates.FiniteAffine47.Part06
public import Erdos272.Certificates.FiniteAffine47.Part07

@[expose] public section
namespace JSP233.FiniteAffine47
open AffineWitness47 PrimorialValue47 PrimorialPrefix46 AffineTrace46
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem actual_full_block : BlockEstimate 7858321551080267055879090 8 0 524288 68151 62 := by
  have h0 : BlockEstimate 7858321551080267055879090 8 0 32768 4161 62 := estimate_join block_00 block_01
  have h1 : BlockEstimate 7858321551080267055879090 8 32768 32768 4253 2 := estimate_join block_02 block_03
  have h2 : BlockEstimate 7858321551080267055879090 8 65536 32768 4277 0 := estimate_join block_04 block_05
  have h3 : BlockEstimate 7858321551080267055879090 8 98304 32768 4279 16 := estimate_join block_06 block_07
  have h4 : BlockEstimate 7858321551080267055879090 8 131072 32768 4276 36 := estimate_join block_08 block_09
  have h5 : BlockEstimate 7858321551080267055879090 8 163840 32768 4274 20 := estimate_join block_10 block_11
  have h6 : BlockEstimate 7858321551080267055879090 8 196608 32768 4279 16 := estimate_join block_12 block_13
  have h7 : BlockEstimate 7858321551080267055879090 8 229376 32768 4262 14 := estimate_join block_14 block_15
  have h8 : BlockEstimate 7858321551080267055879090 8 262144 32768 4274 8 := estimate_join block_16 block_17
  have h9 : BlockEstimate 7858321551080267055879090 8 294912 32768 4271 36 := estimate_join block_18 block_19
  have h10 : BlockEstimate 7858321551080267055879090 8 327680 32768 4259 26 := estimate_join block_20 block_21
  have h11 : BlockEstimate 7858321551080267055879090 8 360448 32768 4255 38 := estimate_join block_22 block_23
  have h12 : BlockEstimate 7858321551080267055879090 8 393216 32768 4251 20 := estimate_join block_24 block_25
  have h13 : BlockEstimate 7858321551080267055879090 8 425984 32768 4261 10 := estimate_join block_26 block_27
  have h14 : BlockEstimate 7858321551080267055879090 8 458752 32768 4262 28 := estimate_join block_28 block_29
  have h15 : BlockEstimate 7858321551080267055879090 8 491520 32768 4257 22 := estimate_join block_30 block_31
  have h16 : BlockEstimate 7858321551080267055879090 8 0 65536 8414 62 := estimate_join h0 h1
  have h17 : BlockEstimate 7858321551080267055879090 8 65536 65536 8556 0 := estimate_join h2 h3
  have h18 : BlockEstimate 7858321551080267055879090 8 131072 65536 8550 36 := estimate_join h4 h5
  have h19 : BlockEstimate 7858321551080267055879090 8 196608 65536 8541 16 := estimate_join h6 h7
  have h20 : BlockEstimate 7858321551080267055879090 8 262144 65536 8545 8 := estimate_join h8 h9
  have h21 : BlockEstimate 7858321551080267055879090 8 327680 65536 8514 26 := estimate_join h10 h11
  have h22 : BlockEstimate 7858321551080267055879090 8 393216 65536 8512 20 := estimate_join h12 h13
  have h23 : BlockEstimate 7858321551080267055879090 8 458752 65536 8519 28 := estimate_join h14 h15
  have h24 : BlockEstimate 7858321551080267055879090 8 0 131072 16970 62 := estimate_join h16 h17
  have h25 : BlockEstimate 7858321551080267055879090 8 131072 131072 17091 36 := estimate_join h18 h19
  have h26 : BlockEstimate 7858321551080267055879090 8 262144 131072 17059 8 := estimate_join h20 h21
  have h27 : BlockEstimate 7858321551080267055879090 8 393216 131072 17031 20 := estimate_join h22 h23
  have h28 : BlockEstimate 7858321551080267055879090 8 0 262144 34061 62 := estimate_join h24 h25
  have h29 : BlockEstimate 7858321551080267055879090 8 262144 262144 34090 8 := estimate_join h26 h27
  have h30 : BlockEstimate 7858321551080267055879090 8 0 524288 68151 62 := estimate_join h28 h29
  exact h30
#print axioms actual_full_block
end JSP233.FiniteAffine47
