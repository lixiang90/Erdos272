import Erdos272.Certificates.LightCeilFast209
namespace JSP233.LightValues209_006
open LightAnalytic209 ResidualCeil208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
  (1337,1244,5664,93,1671595571),
  (4327,4234,16714,93,470736828),
  (12417,12354,46154,63,158432972),
  (33776,33752,127352,24,58385777),
  (93591,93582,359822,9,21252297),
  (98,49,543,162,56957469966),
  (393,292,1722,101,7177397974),
  (1334,1238,5658,96,1680543728),
  (4324,4228,16708,96,471477121),
  (12412,12344,46144,68,158575035),
  (33775,33750,127350,25,58389617),
  (92,46,540,168,63871745889),
  (390,286,1716,104,7337477016),
  (1332,1234,5654,98,1686557706),
  (4322,4224,16704,98,471971834),
  (12408,12336,46136,72,158688852),
  (33773,33746,127346,27,58397299),
  (93590,93580,359820,10,21252802),
  (85,42,536,175,74425411038),
  (386,278,1708,108,7561537703),
  (1329,1228,5648,101,1695652431),
  (4319,4218,16698,101,472715687),
  (12403,12326,46126,77,158831334),
  (33771,33742,127342,29,58404983),
  (93589,93578,359818,11,21253308),
  (79,39,533,181,85089855575),
  (382,270,1700,112,7798729132),
  (1326,1222,5642,104,1704836822),
  (4316,4212,16692,104,473461686),
  (12399,12318,46118,81,158945488),
  (33770,33740,127340,30,58408826),
  (74,37,505,186,92965624362),
  (349,230,1478,119,8905092809),
  (1142,1036,4676,106,1975013367),
  (3534,3428,13828,106,584929424),
  (10298,10196,41396,102,199171203),
  (31166,31132,124732,34,65095815),
  (93588,93576,359816,12,21253813),
  (70,35,503,190,102933731180),
  (347,226,1474,121,9069390838),
  (1140,1032,4672,108,1983399092),
  (3532,3424,13824,108,585686499),
  (10294,10188,41388,106,199345746),
  (31164,31128,124728,36,65105168),
  (66,33,501,194,114670497203),
  (344,220,1468,124,9326892664),
  (1139,1030,4670,109,1987616357),
  (3531,3422,13822,109,586065709),
  (10291,10182,41382,109,199476835),
  (31163,31126,124726,37,65109846),
  (93587,93574,359814,13,21254319),
  (63,31,499,197,126469070141),
  (343,218,1466,125,9415837830),
  (1137,1026,4666,111,1996100163),
  (3529,3418,13818,111,586825479),
  (10289,10178,41378,111,199564314),
  (31162,31124,124724,38,65114524),
  (214,159,912,55,13009572192),
  (708,663,3084,45,3176583297),
  (2376,2331,10939,45,926143488),
  (8592,8576,36821,16,243817170),
  (28240,28235,112970,5,71759343),
  (84733,84731,275721,2,21647218),
  (192,115,760,77,17112137506)
]
def checks : Bool := data.all (fun a=>LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)
private theorem rowCheck_000 :
    LightCeilFast209.checkFast 1337 1244 5664 93 128 1671595571 = true := by decide +kernel

private theorem rowCheck_001 :
    LightCeilFast209.checkFast 4327 4234 16714 93 128 470736828 = true := by decide +kernel

private theorem rowCheck_002 :
    LightCeilFast209.checkFast 12417 12354 46154 63 128 158432972 = true := by decide +kernel

private theorem rowCheck_003 :
    LightCeilFast209.checkFast 33776 33752 127352 24 128 58385777 = true := by decide +kernel

private theorem rowCheck_004 :
    LightCeilFast209.checkFast 93591 93582 359822 9 128 21252297 = true := by decide +kernel

private theorem rowCheck_005 :
    LightCeilFast209.checkFast 98 49 543 162 128 56957469966 = true := by decide +kernel

private theorem rowCheck_006 :
    LightCeilFast209.checkFast 393 292 1722 101 128 7177397974 = true := by decide +kernel

private theorem rowCheck_007 :
    LightCeilFast209.checkFast 1334 1238 5658 96 128 1680543728 = true := by decide +kernel

private theorem rowCheck_008 :
    LightCeilFast209.checkFast 4324 4228 16708 96 128 471477121 = true := by decide +kernel

private theorem rowCheck_009 :
    LightCeilFast209.checkFast 12412 12344 46144 68 128 158575035 = true := by decide +kernel

private theorem rowCheck_010 :
    LightCeilFast209.checkFast 33775 33750 127350 25 128 58389617 = true := by decide +kernel

private theorem rowCheck_011 :
    LightCeilFast209.checkFast 92 46 540 168 128 63871745889 = true := by decide +kernel

private theorem rowCheck_012 :
    LightCeilFast209.checkFast 390 286 1716 104 128 7337477016 = true := by decide +kernel

private theorem rowCheck_013 :
    LightCeilFast209.checkFast 1332 1234 5654 98 128 1686557706 = true := by decide +kernel

private theorem rowCheck_014 :
    LightCeilFast209.checkFast 4322 4224 16704 98 128 471971834 = true := by decide +kernel

private theorem rowCheck_015 :
    LightCeilFast209.checkFast 12408 12336 46136 72 128 158688852 = true := by decide +kernel

private theorem rowCheck_016 :
    LightCeilFast209.checkFast 33773 33746 127346 27 128 58397299 = true := by decide +kernel

private theorem rowCheck_017 :
    LightCeilFast209.checkFast 93590 93580 359820 10 128 21252802 = true := by decide +kernel

private theorem rowCheck_018 :
    LightCeilFast209.checkFast 85 42 536 175 128 74425411038 = true := by decide +kernel

private theorem rowCheck_019 :
    LightCeilFast209.checkFast 386 278 1708 108 128 7561537703 = true := by decide +kernel

private theorem rowCheck_020 :
    LightCeilFast209.checkFast 1329 1228 5648 101 128 1695652431 = true := by decide +kernel

private theorem rowCheck_021 :
    LightCeilFast209.checkFast 4319 4218 16698 101 128 472715687 = true := by decide +kernel

private theorem rowCheck_022 :
    LightCeilFast209.checkFast 12403 12326 46126 77 128 158831334 = true := by decide +kernel

private theorem rowCheck_023 :
    LightCeilFast209.checkFast 33771 33742 127342 29 128 58404983 = true := by decide +kernel

private theorem rowCheck_024 :
    LightCeilFast209.checkFast 93589 93578 359818 11 128 21253308 = true := by decide +kernel

private theorem rowCheck_025 :
    LightCeilFast209.checkFast 79 39 533 181 128 85089855575 = true := by decide +kernel

private theorem rowCheck_026 :
    LightCeilFast209.checkFast 382 270 1700 112 128 7798729132 = true := by decide +kernel

private theorem rowCheck_027 :
    LightCeilFast209.checkFast 1326 1222 5642 104 128 1704836822 = true := by decide +kernel

private theorem rowCheck_028 :
    LightCeilFast209.checkFast 4316 4212 16692 104 128 473461686 = true := by decide +kernel

private theorem rowCheck_029 :
    LightCeilFast209.checkFast 12399 12318 46118 81 128 158945488 = true := by decide +kernel

private theorem rowCheck_030 :
    LightCeilFast209.checkFast 33770 33740 127340 30 128 58408826 = true := by decide +kernel

private theorem rowCheck_031 :
    LightCeilFast209.checkFast 74 37 505 186 128 92965624362 = true := by decide +kernel

private theorem rowCheck_032 :
    LightCeilFast209.checkFast 349 230 1478 119 128 8905092809 = true := by decide +kernel

private theorem rowCheck_033 :
    LightCeilFast209.checkFast 1142 1036 4676 106 128 1975013367 = true := by decide +kernel

private theorem rowCheck_034 :
    LightCeilFast209.checkFast 3534 3428 13828 106 128 584929424 = true := by decide +kernel

private theorem rowCheck_035 :
    LightCeilFast209.checkFast 10298 10196 41396 102 128 199171203 = true := by decide +kernel

private theorem rowCheck_036 :
    LightCeilFast209.checkFast 31166 31132 124732 34 128 65095815 = true := by decide +kernel

private theorem rowCheck_037 :
    LightCeilFast209.checkFast 93588 93576 359816 12 128 21253813 = true := by decide +kernel

private theorem rowCheck_038 :
    LightCeilFast209.checkFast 70 35 503 190 128 102933731180 = true := by decide +kernel

private theorem rowCheck_039 :
    LightCeilFast209.checkFast 347 226 1474 121 128 9069390838 = true := by decide +kernel

private theorem rowCheck_040 :
    LightCeilFast209.checkFast 1140 1032 4672 108 128 1983399092 = true := by decide +kernel

private theorem rowCheck_041 :
    LightCeilFast209.checkFast 3532 3424 13824 108 128 585686499 = true := by decide +kernel

private theorem rowCheck_042 :
    LightCeilFast209.checkFast 10294 10188 41388 106 128 199345746 = true := by decide +kernel

private theorem rowCheck_043 :
    LightCeilFast209.checkFast 31164 31128 124728 36 128 65105168 = true := by decide +kernel

private theorem rowCheck_044 :
    LightCeilFast209.checkFast 66 33 501 194 128 114670497203 = true := by decide +kernel

private theorem rowCheck_045 :
    LightCeilFast209.checkFast 344 220 1468 124 128 9326892664 = true := by decide +kernel

private theorem rowCheck_046 :
    LightCeilFast209.checkFast 1139 1030 4670 109 128 1987616357 = true := by decide +kernel

private theorem rowCheck_047 :
    LightCeilFast209.checkFast 3531 3422 13822 109 128 586065709 = true := by decide +kernel

private theorem rowCheck_048 :
    LightCeilFast209.checkFast 10291 10182 41382 109 128 199476835 = true := by decide +kernel

private theorem rowCheck_049 :
    LightCeilFast209.checkFast 31163 31126 124726 37 128 65109846 = true := by decide +kernel

private theorem rowCheck_050 :
    LightCeilFast209.checkFast 93587 93574 359814 13 128 21254319 = true := by decide +kernel

private theorem rowCheck_051 :
    LightCeilFast209.checkFast 63 31 499 197 128 126469070141 = true := by decide +kernel

private theorem rowCheck_052 :
    LightCeilFast209.checkFast 343 218 1466 125 128 9415837830 = true := by decide +kernel

private theorem rowCheck_053 :
    LightCeilFast209.checkFast 1137 1026 4666 111 128 1996100163 = true := by decide +kernel

private theorem rowCheck_054 :
    LightCeilFast209.checkFast 3529 3418 13818 111 128 586825479 = true := by decide +kernel

private theorem rowCheck_055 :
    LightCeilFast209.checkFast 10289 10178 41378 111 128 199564314 = true := by decide +kernel

private theorem rowCheck_056 :
    LightCeilFast209.checkFast 31162 31124 124724 38 128 65114524 = true := by decide +kernel

private theorem rowCheck_057 :
    LightCeilFast209.checkFast 214 159 912 55 128 13009572192 = true := by decide +kernel

private theorem rowCheck_058 :
    LightCeilFast209.checkFast 708 663 3084 45 128 3176583297 = true := by decide +kernel

private theorem rowCheck_059 :
    LightCeilFast209.checkFast 2376 2331 10939 45 128 926143488 = true := by decide +kernel

private theorem rowCheck_060 :
    LightCeilFast209.checkFast 8592 8576 36821 16 128 243817170 = true := by decide +kernel

private theorem rowCheck_061 :
    LightCeilFast209.checkFast 28240 28235 112970 5 128 71759343 = true := by decide +kernel

private theorem rowCheck_062 :
    LightCeilFast209.checkFast 84733 84731 275721 2 128 21647218 = true := by decide +kernel

private theorem rowCheck_063 :
    LightCeilFast209.checkFast 192 115 760 77 128 17112137506 = true := by decide +kernel

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
end JSP233.LightValues209_006
