import Erdos272.Certificates.LightCeilFast209
namespace JSP233.LightValues209_010
open LightAnalytic209 ResidualCeil208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
  (1563,1443,6645,120,1443241319),
  (5082,4962,19650,120,401856652),
  (14592,14496,54276,96,135065521),
  (39745,39710,149870,35,49627561),
  (110147,110134,423478,13,18058386),
  (82,41,591,224,88165219288),
  (407,264,1732,143,7768780351),
  (1343,1218,5502,125,1680310787),
  (4159,4034,16274,125,497066056),
  (12115,11990,48710,125,169386500),
  (36678,36636,146796,42,55316870),
  (110146,110132,423476,14,18058751),
  (74,37,587,232,106453356769),
  (402,254,1722,148,8087045907),
  (1340,1212,5496,128,1689422955),
  (4156,4028,16268,128,497886374),
  (12112,11984,48704,128,169481138),
  (36676,36632,146792,44,55323624),
  (110145,110130,423474,15,18059116),
  (245,146,971,99,13482377232),
  (754,683,3435,71,3144847588),
  (2681,2610,12930,71,844086520),
  (10280,10240,44640,40,205412716),
  (34388,34376,137576,12,58942503),
  (103196,103192,343992,4,17990112),
  (240798,240796,593052,2,6562978),
  (195,97,785,149,21221890163),
  (593,498,2562,95,4202617059),
  (1969,1874,8754,95,1134342878),
  (6785,6690,27330,95,303837554),
  (20600,20560,82480,40,98588032),
  (61906,61892,233892,14,31870687),
  (171995,171990,524246,5,10313437),
  (161,80,733,183,29238751309),
  (538,423,2315,115,4925693730),
  (1783,1674,7522,109,1239999397),
  (5739,5630,22142,109,353822283),
  (16443,16374,61094,69,119513480),
  (44694,44668,168508,26,44116166),
  (123830,123820,476076,10,16062232),
  (138,69,722,206,38440514105),
  (525,397,2289,128,5271363414),
  (1773,1654,7502,119,1256588143),
  (5729,5610,22122,119,355220747),
  (16428,16344,61064,84,119756331),
  (44689,44658,168498,31,44127131),
  (123828,123816,476072,12,16062809),
  (118,59,712,226,51056673182),
  (513,373,2265,140,5632687969),
  (1764,1636,7484,128,1271866279),
  (5720,5592,22104,128,356488033),
  (16414,16316,61036,98,119983806),
  (44684,44648,168488,36,44138101),
  (123827,123814,476070,13,16063098),
  (104,52,705,240,64238194763),
  (505,357,2249,148,5900241665),
  (1758,1624,7472,134,1282240632),
  (5714,5580,22092,134,357337494),
  (16404,16296,61016,108,120146772),
  (44680,44640,168480,40,44146881),
  (123825,123810,476066,15,16063675),
  (92,46,665,252,78746272784),
  (459,299,1950,160,6855616123),
  (1512,1373,6189,139,1490060670)
]
def checks : Bool := data.all (fun a=>LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)
private theorem rowCheck_000 :
    LightCeilFast209.checkFast 1563 1443 6645 120 128 1443241319 = true := by decide +kernel

private theorem rowCheck_001 :
    LightCeilFast209.checkFast 5082 4962 19650 120 128 401856652 = true := by decide +kernel

private theorem rowCheck_002 :
    LightCeilFast209.checkFast 14592 14496 54276 96 128 135065521 = true := by decide +kernel

private theorem rowCheck_003 :
    LightCeilFast209.checkFast 39745 39710 149870 35 128 49627561 = true := by decide +kernel

private theorem rowCheck_004 :
    LightCeilFast209.checkFast 110147 110134 423478 13 128 18058386 = true := by decide +kernel

private theorem rowCheck_005 :
    LightCeilFast209.checkFast 82 41 591 224 128 88165219288 = true := by decide +kernel

private theorem rowCheck_006 :
    LightCeilFast209.checkFast 407 264 1732 143 128 7768780351 = true := by decide +kernel

private theorem rowCheck_007 :
    LightCeilFast209.checkFast 1343 1218 5502 125 128 1680310787 = true := by decide +kernel

private theorem rowCheck_008 :
    LightCeilFast209.checkFast 4159 4034 16274 125 128 497066056 = true := by decide +kernel

private theorem rowCheck_009 :
    LightCeilFast209.checkFast 12115 11990 48710 125 128 169386500 = true := by decide +kernel

private theorem rowCheck_010 :
    LightCeilFast209.checkFast 36678 36636 146796 42 128 55316870 = true := by decide +kernel

private theorem rowCheck_011 :
    LightCeilFast209.checkFast 110146 110132 423476 14 128 18058751 = true := by decide +kernel

private theorem rowCheck_012 :
    LightCeilFast209.checkFast 74 37 587 232 128 106453356769 = true := by decide +kernel

private theorem rowCheck_013 :
    LightCeilFast209.checkFast 402 254 1722 148 128 8087045907 = true := by decide +kernel

private theorem rowCheck_014 :
    LightCeilFast209.checkFast 1340 1212 5496 128 128 1689422955 = true := by decide +kernel

private theorem rowCheck_015 :
    LightCeilFast209.checkFast 4156 4028 16268 128 128 497886374 = true := by decide +kernel

private theorem rowCheck_016 :
    LightCeilFast209.checkFast 12112 11984 48704 128 128 169481138 = true := by decide +kernel

private theorem rowCheck_017 :
    LightCeilFast209.checkFast 36676 36632 146792 44 128 55323624 = true := by decide +kernel

private theorem rowCheck_018 :
    LightCeilFast209.checkFast 110145 110130 423474 15 128 18059116 = true := by decide +kernel

private theorem rowCheck_019 :
    LightCeilFast209.checkFast 245 146 971 99 128 13482377232 = true := by decide +kernel

private theorem rowCheck_020 :
    LightCeilFast209.checkFast 754 683 3435 71 128 3144847588 = true := by decide +kernel

private theorem rowCheck_021 :
    LightCeilFast209.checkFast 2681 2610 12930 71 128 844086520 = true := by decide +kernel

private theorem rowCheck_022 :
    LightCeilFast209.checkFast 10280 10240 44640 40 128 205412716 = true := by decide +kernel

private theorem rowCheck_023 :
    LightCeilFast209.checkFast 34388 34376 137576 12 128 58942503 = true := by decide +kernel

private theorem rowCheck_024 :
    LightCeilFast209.checkFast 103196 103192 343992 4 128 17990112 = true := by decide +kernel

private theorem rowCheck_025 :
    LightCeilFast209.checkFast 240798 240796 593052 2 128 6562978 = true := by decide +kernel

private theorem rowCheck_026 :
    LightCeilFast209.checkFast 195 97 785 149 128 21221890163 = true := by decide +kernel

private theorem rowCheck_027 :
    LightCeilFast209.checkFast 593 498 2562 95 128 4202617059 = true := by decide +kernel

private theorem rowCheck_028 :
    LightCeilFast209.checkFast 1969 1874 8754 95 128 1134342878 = true := by decide +kernel

private theorem rowCheck_029 :
    LightCeilFast209.checkFast 6785 6690 27330 95 128 303837554 = true := by decide +kernel

private theorem rowCheck_030 :
    LightCeilFast209.checkFast 20600 20560 82480 40 128 98588032 = true := by decide +kernel

private theorem rowCheck_031 :
    LightCeilFast209.checkFast 61906 61892 233892 14 128 31870687 = true := by decide +kernel

private theorem rowCheck_032 :
    LightCeilFast209.checkFast 171995 171990 524246 5 128 10313437 = true := by decide +kernel

private theorem rowCheck_033 :
    LightCeilFast209.checkFast 161 80 733 183 128 29238751309 = true := by decide +kernel

private theorem rowCheck_034 :
    LightCeilFast209.checkFast 538 423 2315 115 128 4925693730 = true := by decide +kernel

private theorem rowCheck_035 :
    LightCeilFast209.checkFast 1783 1674 7522 109 128 1239999397 = true := by decide +kernel

private theorem rowCheck_036 :
    LightCeilFast209.checkFast 5739 5630 22142 109 128 353822283 = true := by decide +kernel

private theorem rowCheck_037 :
    LightCeilFast209.checkFast 16443 16374 61094 69 128 119513480 = true := by decide +kernel

private theorem rowCheck_038 :
    LightCeilFast209.checkFast 44694 44668 168508 26 128 44116166 = true := by decide +kernel

private theorem rowCheck_039 :
    LightCeilFast209.checkFast 123830 123820 476076 10 128 16062232 = true := by decide +kernel

private theorem rowCheck_040 :
    LightCeilFast209.checkFast 138 69 722 206 128 38440514105 = true := by decide +kernel

private theorem rowCheck_041 :
    LightCeilFast209.checkFast 525 397 2289 128 128 5271363414 = true := by decide +kernel

private theorem rowCheck_042 :
    LightCeilFast209.checkFast 1773 1654 7502 119 128 1256588143 = true := by decide +kernel

private theorem rowCheck_043 :
    LightCeilFast209.checkFast 5729 5610 22122 119 128 355220747 = true := by decide +kernel

private theorem rowCheck_044 :
    LightCeilFast209.checkFast 16428 16344 61064 84 128 119756331 = true := by decide +kernel

private theorem rowCheck_045 :
    LightCeilFast209.checkFast 44689 44658 168498 31 128 44127131 = true := by decide +kernel

private theorem rowCheck_046 :
    LightCeilFast209.checkFast 123828 123816 476072 12 128 16062809 = true := by decide +kernel

private theorem rowCheck_047 :
    LightCeilFast209.checkFast 118 59 712 226 128 51056673182 = true := by decide +kernel

private theorem rowCheck_048 :
    LightCeilFast209.checkFast 513 373 2265 140 128 5632687969 = true := by decide +kernel

private theorem rowCheck_049 :
    LightCeilFast209.checkFast 1764 1636 7484 128 128 1271866279 = true := by decide +kernel

private theorem rowCheck_050 :
    LightCeilFast209.checkFast 5720 5592 22104 128 128 356488033 = true := by decide +kernel

private theorem rowCheck_051 :
    LightCeilFast209.checkFast 16414 16316 61036 98 128 119983806 = true := by decide +kernel

private theorem rowCheck_052 :
    LightCeilFast209.checkFast 44684 44648 168488 36 128 44138101 = true := by decide +kernel

private theorem rowCheck_053 :
    LightCeilFast209.checkFast 123827 123814 476070 13 128 16063098 = true := by decide +kernel

private theorem rowCheck_054 :
    LightCeilFast209.checkFast 104 52 705 240 128 64238194763 = true := by decide +kernel

private theorem rowCheck_055 :
    LightCeilFast209.checkFast 505 357 2249 148 128 5900241665 = true := by decide +kernel

private theorem rowCheck_056 :
    LightCeilFast209.checkFast 1758 1624 7472 134 128 1282240632 = true := by decide +kernel

private theorem rowCheck_057 :
    LightCeilFast209.checkFast 5714 5580 22092 134 128 357337494 = true := by decide +kernel

private theorem rowCheck_058 :
    LightCeilFast209.checkFast 16404 16296 61016 108 128 120146772 = true := by decide +kernel

private theorem rowCheck_059 :
    LightCeilFast209.checkFast 44680 44640 168480 40 128 44146881 = true := by decide +kernel

private theorem rowCheck_060 :
    LightCeilFast209.checkFast 123825 123810 476066 15 128 16063675 = true := by decide +kernel

private theorem rowCheck_061 :
    LightCeilFast209.checkFast 92 46 665 252 128 78746272784 = true := by decide +kernel

private theorem rowCheck_062 :
    LightCeilFast209.checkFast 459 299 1950 160 128 6855616123 = true := by decide +kernel

private theorem rowCheck_063 :
    LightCeilFast209.checkFast 1512 1373 6189 139 128 1490060670 = true := by decide +kernel

private theorem fast_checks_true : LightCeilFast209.checkAllFast data = true := by
  simp only [LightCeilFast209.checkAllFast, data, List.all_cons, List.all_nil,
    rowCheck_000, rowCheck_001, rowCheck_002, rowCheck_003, rowCheck_004, rowCheck_005,
    rowCheck_006, rowCheck_007, rowCheck_008, rowCheck_009, rowCheck_010, rowCheck_011,
    rowCheck_012, rowCheck_013, rowCheck_014, rowCheck_015, rowCheck_016, rowCheck_017,
    rowCheck_018, rowCheck_019, rowCheck_020, rowCheck_021, rowCheck_022, rowCheck_023,
    rowCheck_024, rowCheck_025, rowCheck_026, rowCheck_027, rowCheck_028, rowCheck_029,
    rowCheck_030, rowCheck_031, rowCheck_032, rowCheck_033, rowCheck_034, rowCheck_035,
    rowCheck_036, rowCheck_037, rowCheck_038, rowCheck_039, rowCheck_040, rowCheck_041,
    rowCheck_042, rowCheck_043, rowCheck_044, rowCheck_045, rowCheck_046, rowCheck_047,
    rowCheck_048, rowCheck_049, rowCheck_050, rowCheck_051, rowCheck_052, rowCheck_053,
    rowCheck_054, rowCheck_055, rowCheck_056, rowCheck_057, rowCheck_058, rowCheck_059,
    rowCheck_060, rowCheck_061, rowCheck_062, rowCheck_063,
    Bool.true_and]

theorem checks_true : checks=true :=
  (LightCeilFast209.checkAllFast_eq data).symm.trans fast_checks_true

theorem bound {A B V E u : ℕ} (ha : (A,B,V,E,u)∈data) :
    Alpha A B V E 128≤(u : ℝ)/(Grid : ℝ) :=
  LightCeilFast209.boundOfChecks 128 (data := data)
    (LightCeilFast209.checkAllFast_sound (data := data) fast_checks_true) ha
#print axioms checks_true
#print axioms bound
end
end JSP233.LightValues209_010
