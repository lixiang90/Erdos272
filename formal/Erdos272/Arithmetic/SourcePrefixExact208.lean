import Erdos272.Arithmetic.SourcePrefix208_13_000
import Erdos272.Arithmetic.SourcePrefix208_B00
import Erdos272.Arithmetic.SourcePrefix208_B01
import Erdos272.Arithmetic.SourcePrefix208_B02
import Erdos272.Arithmetic.SourcePrefix208_B03
import Erdos272.Arithmetic.SourcePrefix208_B04
import Erdos272.Arithmetic.SourcePrefix208_B05
import Erdos272.Arithmetic.SourcePrefix208_B06
import Erdos272.Arithmetic.SourcePrefix208_B07
import Erdos272.Arithmetic.SourcePrefix208_B08
import Erdos272.Arithmetic.SourcePrefix208_B09
import Erdos272.Arithmetic.SourcePrefix208_B10
import Erdos272.Arithmetic.SourcePrefix208_B11
import Erdos272.Arithmetic.SourcePrefix208_B12
import Erdos272.Arithmetic.SourcePrefix208_B13
import Erdos272.Arithmetic.SourcePrefix208_B14
import Erdos272.Arithmetic.SourcePrefix208_B15
import Erdos272.Arithmetic.SourcePrefix208_B16

/-! Disjoint physical checks, joined entirely by proof. -/
namespace JSP233.SourcePrefixExact208
open SourcePrefixSpecs208 BatchSourceBlocks208
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem segment_00 : BatchSource208.checkBlock FastDecode208.phi 242 242
    (rowTargets (⟨0, by decide⟩ : Fin 14)) = true :=
  SourcePrefix208_00_000.checked

theorem segment_01 : BatchSource208.checkBlock FastDecode208.phi 243 337
    (rowTargets (⟨1, by decide⟩ : Fin 14)) = true :=
  SourcePrefix208_01_000.checked

theorem segment_02 : BatchSource208.checkBlock FastDecode208.phi 338 339
    (rowTargets (⟨2, by decide⟩ : Fin 14)) = true :=
  SourcePrefix208_02_000.checked

theorem segment_03 : BatchSource208.checkBlock FastDecode208.phi 340 483
    (rowTargets (⟨3, by decide⟩ : Fin 14)) = true :=
  SourcePrefix208_03_000.checked

theorem segment_04 : BatchSource208.checkBlock FastDecode208.phi 484 485
    (rowTargets (⟨4, by decide⟩ : Fin 14)) = true :=
  SourcePrefix208_04_000.checked

theorem segment_05 : BatchSource208.checkBlock FastDecode208.phi 486 725
    (rowTargets (⟨5, by decide⟩ : Fin 14)) = true :=
  SourcePrefix208_05_000.checked

theorem segment_06 : BatchSource208.checkBlock FastDecode208.phi 726 728
    (rowTargets (⟨6, by decide⟩ : Fin 14)) = true :=
  SourcePrefix208_06_000.checked

theorem segment_07 : BatchSource208.checkBlock FastDecode208.phi 729 1209
    (rowTargets (⟨7, by decide⟩ : Fin 14)) = true :=
  (checkBlock_split (a := FastDecode208.phi) (T := 729) (C := 984) (H := 1209) (targets := rowTargets (⟨7, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_07_000.checked
    SourcePrefix208_07_001.checked)

theorem segment_08 : BatchSource208.checkBlock FastDecode208.phi 1210 1214
    (rowTargets (⟨8, by decide⟩ : Fin 14)) = true :=
  SourcePrefix208_08_000.checked

theorem segment_09 : BatchSource208.checkBlock FastDecode208.phi 1215 2419
    (rowTargets (⟨9, by decide⟩ : Fin 14)) = true :=
  (checkBlock_split (a := FastDecode208.phi) (T := 1215) (C := 1726) (H := 2419) (targets := rowTargets (⟨9, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 1215) (C := 1470) (H := 1726) (targets := rowTargets (⟨9, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_09_000.checked
    SourcePrefix208_09_001.checked)
    (checkBlock_split (a := FastDecode208.phi) (T := 1727) (C := 1982) (H := 2419) (targets := rowTargets (⟨9, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_09_002.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 1983) (C := 2238) (H := 2419) (targets := rowTargets (⟨9, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_09_003.checked
    SourcePrefix208_09_004.checked)))

theorem segment_10 : BatchSource208.checkBlock FastDecode208.phi 2420 2429
    (rowTargets (⟨10, by decide⟩ : Fin 14)) = true :=
  SourcePrefix208_10_000.checked

theorem segment_11 : BatchSource208.checkBlock FastDecode208.phi 2430 7743
    (rowTargets (⟨11, by decide⟩ : Fin 14)) = true :=
  (checkBlock_split (a := FastDecode208.phi) (T := 2430) (C := 4989) (H := 7743) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 2430) (C := 3709) (H := 4989) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 2430) (C := 2941) (H := 3709) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 2430) (C := 2685) (H := 2941) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_11_000.checked
    SourcePrefix208_11_001.checked)
    (checkBlock_split (a := FastDecode208.phi) (T := 2942) (C := 3197) (H := 3709) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_11_002.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 3198) (C := 3453) (H := 3709) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_11_003.checked
    SourcePrefix208_11_004.checked)))
    (checkBlock_split (a := FastDecode208.phi) (T := 3710) (C := 4221) (H := 4989) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 3710) (C := 3965) (H := 4221) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_11_005.checked
    SourcePrefix208_11_006.checked)
    (checkBlock_split (a := FastDecode208.phi) (T := 4222) (C := 4477) (H := 4989) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_11_007.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 4478) (C := 4733) (H := 4989) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_11_008.checked
    SourcePrefix208_11_009.checked))))
    (checkBlock_split (a := FastDecode208.phi) (T := 4990) (C := 6269) (H := 7743) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 4990) (C := 5501) (H := 6269) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 4990) (C := 5245) (H := 5501) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_11_010.checked
    SourcePrefix208_11_011.checked)
    (checkBlock_split (a := FastDecode208.phi) (T := 5502) (C := 5757) (H := 6269) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_11_012.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 5758) (C := 6013) (H := 6269) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_11_013.checked
    SourcePrefix208_11_014.checked)))
    (checkBlock_split (a := FastDecode208.phi) (T := 6270) (C := 7037) (H := 7743) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 6270) (C := 6525) (H := 7037) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_11_015.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 6526) (C := 6781) (H := 7037) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_11_016.checked
    SourcePrefix208_11_017.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 7038) (C := 7293) (H := 7743) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_11_018.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 7294) (C := 7549) (H := 7743) (targets := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_11_019.checked
    SourcePrefix208_11_020.checked)))))

theorem segment_12 : BatchSource208.checkBlock FastDecode208.phi 7744 7775
    (rowTargets (⟨12, by decide⟩ : Fin 14)) = true :=
  SourcePrefix208_12_000.checked

theorem segment_13 : BatchSource208.checkBlock FastDecode208.phi 7776 32753
    (rowTargets (⟨13, by decide⟩ : Fin 14)) = true :=
  (checkBlock_split (a := FastDecode208.phi) (T := 7776) (C := 20319) (H := 32753) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 7776) (C := 13919) (H := 20319) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 7776) (C := 10847) (H := 13919) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 7776) (C := 9311) (H := 10847) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 7776) (C := 8543) (H := 9311) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 7776) (C := 8031) (H := 8543) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_000.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 8032) (C := 8287) (H := 8543) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_001.checked
    SourcePrefix208_13_002.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 8544) (C := 8799) (H := 9311) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_003.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 8800) (C := 9055) (H := 9311) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_004.checked
    SourcePrefix208_13_005.checked)))
    (checkBlock_split (a := FastDecode208.phi) (T := 9312) (C := 10079) (H := 10847) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 9312) (C := 9567) (H := 10079) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_006.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 9568) (C := 9823) (H := 10079) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_007.checked
    SourcePrefix208_13_008.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 10080) (C := 10335) (H := 10847) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_009.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 10336) (C := 10591) (H := 10847) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_010.checked
    SourcePrefix208_13_011.checked))))
    (checkBlock_split (a := FastDecode208.phi) (T := 10848) (C := 12383) (H := 13919) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 10848) (C := 11615) (H := 12383) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 10848) (C := 11103) (H := 11615) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_012.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 11104) (C := 11359) (H := 11615) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_013.checked
    SourcePrefix208_13_014.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 11616) (C := 11871) (H := 12383) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_015.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 11872) (C := 12127) (H := 12383) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_016.checked
    SourcePrefix208_13_017.checked)))
    (checkBlock_split (a := FastDecode208.phi) (T := 12384) (C := 13151) (H := 13919) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 12384) (C := 12639) (H := 13151) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_018.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 12640) (C := 12895) (H := 13151) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_019.checked
    SourcePrefix208_13_020.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 13152) (C := 13407) (H := 13919) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_021.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 13408) (C := 13663) (H := 13919) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_022.checked
    SourcePrefix208_13_023.checked)))))
    (checkBlock_split (a := FastDecode208.phi) (T := 13920) (C := 16991) (H := 20319) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 13920) (C := 15455) (H := 16991) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 13920) (C := 14687) (H := 15455) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 13920) (C := 14175) (H := 14687) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_024.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 14176) (C := 14431) (H := 14687) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_025.checked
    SourcePrefix208_13_026.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 14688) (C := 14943) (H := 15455) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_027.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 14944) (C := 15199) (H := 15455) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_028.checked
    SourcePrefix208_13_029.checked)))
    (checkBlock_split (a := FastDecode208.phi) (T := 15456) (C := 16223) (H := 16991) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 15456) (C := 15711) (H := 16223) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_030.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 15712) (C := 15967) (H := 16223) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_031.checked
    SourcePrefix208_13_032.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 16224) (C := 16479) (H := 16991) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_033.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 16480) (C := 16735) (H := 16991) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_034.checked
    SourcePrefix208_13_035.checked))))
    (checkBlock_split (a := FastDecode208.phi) (T := 16992) (C := 18527) (H := 20319) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 16992) (C := 17759) (H := 18527) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 16992) (C := 17247) (H := 17759) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_036.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 17248) (C := 17503) (H := 17759) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_037.checked
    SourcePrefix208_13_038.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 17760) (C := 18015) (H := 18527) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_039.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 18016) (C := 18271) (H := 18527) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_040.checked
    SourcePrefix208_13_041.checked)))
    (checkBlock_split (a := FastDecode208.phi) (T := 18528) (C := 19295) (H := 20319) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 18528) (C := 18783) (H := 19295) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_042.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 18784) (C := 19039) (H := 19295) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_043.checked
    SourcePrefix208_13_044.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 19296) (C := 19807) (H := 20319) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 19296) (C := 19551) (H := 19807) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_045.checked
    SourcePrefix208_13_046.checked)
    (checkBlock_split (a := FastDecode208.phi) (T := 19808) (C := 20063) (H := 20319) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_047.checked
    SourcePrefix208_13_048.checked))))))
    (checkBlock_split (a := FastDecode208.phi) (T := 20320) (C := 26463) (H := 32753) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 20320) (C := 23391) (H := 26463) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 20320) (C := 21855) (H := 23391) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 20320) (C := 21087) (H := 21855) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 20320) (C := 20575) (H := 21087) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_049.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 20576) (C := 20831) (H := 21087) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_050.checked
    SourcePrefix208_13_051.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 21088) (C := 21343) (H := 21855) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_052.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 21344) (C := 21599) (H := 21855) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_053.checked
    SourcePrefix208_13_054.checked)))
    (checkBlock_split (a := FastDecode208.phi) (T := 21856) (C := 22623) (H := 23391) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 21856) (C := 22111) (H := 22623) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_055.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 22112) (C := 22367) (H := 22623) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_056.checked
    SourcePrefix208_13_057.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 22624) (C := 22879) (H := 23391) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_058.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 22880) (C := 23135) (H := 23391) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_059.checked
    SourcePrefix208_13_060.checked))))
    (checkBlock_split (a := FastDecode208.phi) (T := 23392) (C := 24927) (H := 26463) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 23392) (C := 24159) (H := 24927) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 23392) (C := 23647) (H := 24159) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_061.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 23648) (C := 23903) (H := 24159) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_062.checked
    SourcePrefix208_13_063.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 24160) (C := 24415) (H := 24927) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_064.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 24416) (C := 24671) (H := 24927) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_065.checked
    SourcePrefix208_13_066.checked)))
    (checkBlock_split (a := FastDecode208.phi) (T := 24928) (C := 25695) (H := 26463) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 24928) (C := 25183) (H := 25695) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_067.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 25184) (C := 25439) (H := 25695) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_068.checked
    SourcePrefix208_13_069.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 25696) (C := 25951) (H := 26463) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_070.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 25952) (C := 26207) (H := 26463) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_071.checked
    SourcePrefix208_13_072.checked)))))
    (checkBlock_split (a := FastDecode208.phi) (T := 26464) (C := 29535) (H := 32753) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 26464) (C := 27999) (H := 29535) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 26464) (C := 27231) (H := 27999) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 26464) (C := 26719) (H := 27231) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_073.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 26720) (C := 26975) (H := 27231) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_074.checked
    SourcePrefix208_13_075.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 27232) (C := 27487) (H := 27999) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_076.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 27488) (C := 27743) (H := 27999) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_077.checked
    SourcePrefix208_13_078.checked)))
    (checkBlock_split (a := FastDecode208.phi) (T := 28000) (C := 28767) (H := 29535) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 28000) (C := 28255) (H := 28767) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_079.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 28256) (C := 28511) (H := 28767) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_080.checked
    SourcePrefix208_13_081.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 28768) (C := 29023) (H := 29535) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_082.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 29024) (C := 29279) (H := 29535) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_083.checked
    SourcePrefix208_13_084.checked))))
    (checkBlock_split (a := FastDecode208.phi) (T := 29536) (C := 31071) (H := 32753) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 29536) (C := 30303) (H := 31071) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 29536) (C := 29791) (H := 30303) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_085.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 29792) (C := 30047) (H := 30303) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_086.checked
    SourcePrefix208_13_087.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 30304) (C := 30559) (H := 31071) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_088.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 30560) (C := 30815) (H := 31071) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_089.checked
    SourcePrefix208_13_090.checked)))
    (checkBlock_split (a := FastDecode208.phi) (T := 31072) (C := 31839) (H := 32753) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 31072) (C := 31327) (H := 31839) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_091.checked
    (checkBlock_split (a := FastDecode208.phi) (T := 31328) (C := 31583) (H := 31839) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_092.checked
    SourcePrefix208_13_093.checked))
    (checkBlock_split (a := FastDecode208.phi) (T := 31840) (C := 32351) (H := 32753) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (checkBlock_split (a := FastDecode208.phi) (T := 31840) (C := 32095) (H := 32351) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_094.checked
    SourcePrefix208_13_095.checked)
    (checkBlock_split (a := FastDecode208.phi) (T := 32352) (C := 32607) (H := 32753) (targets := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    SourcePrefix208_13_096.checked
    SourcePrefix208_13_097.checked)))))))

theorem suffix_13 : BatchSource208.checkBlock FastDecode208.phi 7776 32753
    (rowTargets (⟨13, by decide⟩ : Fin 14)) = true := by
  exact segment_13

theorem suffix_12 : BatchSource208.checkBlock FastDecode208.phi 7744 32753
    (rowTargets (⟨12, by decide⟩ : Fin 14)) = true := by
  exact checkBlock_extend_stronger (a := FastDecode208.phi) (T := 7744) (U := 7776) (H := 32753) (lower := rowTargets (⟨12, by decide⟩ : Fin 14)) (upper := rowTargets (⟨13, by decide⟩ : Fin 14)) (by decide) (by decide)
    (SourceTargetOrder208.adjacent_targets (i := 12) (by decide)).2
    segment_12 suffix_13

theorem suffix_11 : BatchSource208.checkBlock FastDecode208.phi 2430 32753
    (rowTargets (⟨11, by decide⟩ : Fin 14)) = true := by
  exact checkBlock_extend_stronger (a := FastDecode208.phi) (T := 2430) (U := 7744) (H := 32753) (lower := rowTargets (⟨11, by decide⟩ : Fin 14)) (upper := rowTargets (⟨12, by decide⟩ : Fin 14)) (by decide) (by decide)
    (SourceTargetOrder208.adjacent_targets (i := 11) (by decide)).2
    segment_11 suffix_12

theorem suffix_10 : BatchSource208.checkBlock FastDecode208.phi 2420 32753
    (rowTargets (⟨10, by decide⟩ : Fin 14)) = true := by
  exact checkBlock_extend_stronger (a := FastDecode208.phi) (T := 2420) (U := 2430) (H := 32753) (lower := rowTargets (⟨10, by decide⟩ : Fin 14)) (upper := rowTargets (⟨11, by decide⟩ : Fin 14)) (by decide) (by decide)
    (SourceTargetOrder208.adjacent_targets (i := 10) (by decide)).2
    segment_10 suffix_11

theorem suffix_09 : BatchSource208.checkBlock FastDecode208.phi 1215 32753
    (rowTargets (⟨9, by decide⟩ : Fin 14)) = true := by
  exact checkBlock_extend_stronger (a := FastDecode208.phi) (T := 1215) (U := 2420) (H := 32753) (lower := rowTargets (⟨9, by decide⟩ : Fin 14)) (upper := rowTargets (⟨10, by decide⟩ : Fin 14)) (by decide) (by decide)
    (SourceTargetOrder208.adjacent_targets (i := 9) (by decide)).2
    segment_09 suffix_10

theorem suffix_08 : BatchSource208.checkBlock FastDecode208.phi 1210 32753
    (rowTargets (⟨8, by decide⟩ : Fin 14)) = true := by
  exact checkBlock_extend_stronger (a := FastDecode208.phi) (T := 1210) (U := 1215) (H := 32753) (lower := rowTargets (⟨8, by decide⟩ : Fin 14)) (upper := rowTargets (⟨9, by decide⟩ : Fin 14)) (by decide) (by decide)
    (SourceTargetOrder208.adjacent_targets (i := 8) (by decide)).2
    segment_08 suffix_09

theorem suffix_07 : BatchSource208.checkBlock FastDecode208.phi 729 32753
    (rowTargets (⟨7, by decide⟩ : Fin 14)) = true := by
  exact checkBlock_extend_stronger (a := FastDecode208.phi) (T := 729) (U := 1210) (H := 32753) (lower := rowTargets (⟨7, by decide⟩ : Fin 14)) (upper := rowTargets (⟨8, by decide⟩ : Fin 14)) (by decide) (by decide)
    (SourceTargetOrder208.adjacent_targets (i := 7) (by decide)).2
    segment_07 suffix_08

theorem suffix_06 : BatchSource208.checkBlock FastDecode208.phi 726 32753
    (rowTargets (⟨6, by decide⟩ : Fin 14)) = true := by
  exact checkBlock_extend_stronger (a := FastDecode208.phi) (T := 726) (U := 729) (H := 32753) (lower := rowTargets (⟨6, by decide⟩ : Fin 14)) (upper := rowTargets (⟨7, by decide⟩ : Fin 14)) (by decide) (by decide)
    (SourceTargetOrder208.adjacent_targets (i := 6) (by decide)).2
    segment_06 suffix_07

theorem suffix_05 : BatchSource208.checkBlock FastDecode208.phi 486 32753
    (rowTargets (⟨5, by decide⟩ : Fin 14)) = true := by
  exact checkBlock_extend_stronger (a := FastDecode208.phi) (T := 486) (U := 726) (H := 32753) (lower := rowTargets (⟨5, by decide⟩ : Fin 14)) (upper := rowTargets (⟨6, by decide⟩ : Fin 14)) (by decide) (by decide)
    (SourceTargetOrder208.adjacent_targets (i := 5) (by decide)).2
    segment_05 suffix_06

theorem suffix_04 : BatchSource208.checkBlock FastDecode208.phi 484 32753
    (rowTargets (⟨4, by decide⟩ : Fin 14)) = true := by
  exact checkBlock_extend_stronger (a := FastDecode208.phi) (T := 484) (U := 486) (H := 32753) (lower := rowTargets (⟨4, by decide⟩ : Fin 14)) (upper := rowTargets (⟨5, by decide⟩ : Fin 14)) (by decide) (by decide)
    (SourceTargetOrder208.adjacent_targets (i := 4) (by decide)).2
    segment_04 suffix_05

theorem suffix_03 : BatchSource208.checkBlock FastDecode208.phi 340 32753
    (rowTargets (⟨3, by decide⟩ : Fin 14)) = true := by
  exact checkBlock_extend_stronger (a := FastDecode208.phi) (T := 340) (U := 484) (H := 32753) (lower := rowTargets (⟨3, by decide⟩ : Fin 14)) (upper := rowTargets (⟨4, by decide⟩ : Fin 14)) (by decide) (by decide)
    (SourceTargetOrder208.adjacent_targets (i := 3) (by decide)).2
    segment_03 suffix_04

theorem suffix_02 : BatchSource208.checkBlock FastDecode208.phi 338 32753
    (rowTargets (⟨2, by decide⟩ : Fin 14)) = true := by
  exact checkBlock_extend_stronger (a := FastDecode208.phi) (T := 338) (U := 340) (H := 32753) (lower := rowTargets (⟨2, by decide⟩ : Fin 14)) (upper := rowTargets (⟨3, by decide⟩ : Fin 14)) (by decide) (by decide)
    (SourceTargetOrder208.adjacent_targets (i := 2) (by decide)).2
    segment_02 suffix_03

theorem suffix_01 : BatchSource208.checkBlock FastDecode208.phi 243 32753
    (rowTargets (⟨1, by decide⟩ : Fin 14)) = true := by
  exact checkBlock_extend_stronger (a := FastDecode208.phi) (T := 243) (U := 338) (H := 32753) (lower := rowTargets (⟨1, by decide⟩ : Fin 14)) (upper := rowTargets (⟨2, by decide⟩ : Fin 14)) (by decide) (by decide)
    (SourceTargetOrder208.adjacent_targets (i := 1) (by decide)).2
    segment_01 suffix_02

theorem suffix_00 : BatchSource208.checkBlock FastDecode208.phi 242 32753
    (rowTargets (⟨0, by decide⟩ : Fin 14)) = true := by
  exact checkBlock_extend_stronger (a := FastDecode208.phi) (T := 242) (U := 243) (H := 32753) (lower := rowTargets (⟨0, by decide⟩ : Fin 14)) (upper := rowTargets (⟨1, by decide⟩ : Fin 14)) (by decide) (by decide)
    (SourceTargetOrder208.adjacent_targets (i := 0) (by decide)).2
    segment_00 suffix_01

theorem checked_suffix (i : Fin 14) :
    BatchSource208.checkBlock FastDecode208.phi (rowStart i) 32753 (rowTargets i) = true := by
  fin_cases i
  · exact suffix_00
  · exact suffix_01
  · exact suffix_02
  · exact suffix_03
  · exact suffix_04
  · exact suffix_05
  · exact suffix_06
  · exact suffix_07
  · exact suffix_08
  · exact suffix_09
  · exact suffix_10
  · exact suffix_11
  · exact suffix_12
  · exact suffix_13

theorem rowStart_le (i : Fin 14) : rowStart i ≤ 32753 := by
  fin_cases i <;> decide +kernel

theorem rowStart_ge (i : Fin 14) : 185 ≤ rowStart i := by
  fin_cases i <;> decide +kernel

theorem finite_floor (i : Fin 14) (e : Nat) (he : e < 185) :
    (rowTargets i)[e]'(by rw [rowTargets_length]; exact he) ≤
      PureSource208.finiteMinimum (rowStart i) 32753 e (rowStart_le i) := by
  exact BatchSource208.checkBlock_sound FastDecode208.phi_correct (rowStart_le i)
    (by rw [rowTargets_length]; exact rowStart_ge i) (checked_suffix i) e
    (by rw [rowTargets_length]; exact he)

theorem physical_floor (i : Fin 14) (e : Nat) (he : e < 185)
    (s : Nat) (hs : rowStart i ≤ s) (hH : s ≤ 32753) :
    (rowTargets i)[e]'(by rw [rowTargets_length]; exact he) ≤ PureSource208.physicalK s e :=
  (finite_floor i e he).trans (PureSource208.finiteMinimum_le (rowStart_le i) hs hH)

#print axioms checked_suffix
#print axioms finite_floor
#print axioms physical_floor
end JSP233.SourcePrefixExact208
