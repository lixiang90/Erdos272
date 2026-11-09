module

public import Erdos272.Certificates.LightCeilFast209

@[expose] public section
namespace JSP233.LightValues209_002
open LightAnalytic209 ResidualCeil208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
  (100,50,525,150,53193587672),
  (381,287,1662,94,7292122010),
  (1285,1195,5445,90,1740313393),
  (4160,4070,16070,90,489720105),
  (11939,11878,44378,61,164783283),
  (32477,32454,122454,23,60720888),
  (89991,89982,345982,9,22102578),
  (96,48,523,154,57272992490),
  (379,283,1658,96,7401918977),
  (1283,1191,5441,92,1746768515),
  (4158,4066,16066,92,490253978),
  (11936,11872,44372,64,164875461),
  (32476,32452,122452,24,60725042),
  (92,46,521,158,61864740805),
  (377,279,1654,98,7514825131),
  (1282,1189,5439,93,1750012430),
  (4157,4064,16064,93,490521313),
  (11933,11866,44366,67,164967733),
  (32475,32450,122450,25,60729196),
  (88,44,519,162,67060254663),
  (374,273,1648,101,7690312976),
  (1280,1185,5435,95,1756533243),
  (4155,4060,16060,95,491056785),
  (11931,11862,44362,69,165029300),
  (32474,32448,122448,26,60733351),
  (89990,89980,345980,10,22103125),
  (83,41,516,167,75281009700),
  (372,269,1644,103,7811603437),
  (1278,1181,5431,97,1763098406),
  (4153,4056,16056,97,491593327),
  (11927,11854,44354,73,165152560),
  (32473,32446,122446,27,60737506),
  (81,40,515,169,78712888040),
  (370,265,1640,105,7936514782),
  (1277,1179,5429,98,1766397759),
  (4152,4054,16054,98,491862000),
  (11926,11852,44352,74,165183401),
  (32472,32444,122444,28,60741662),
  (79,39,514,171,82395581427),
  (369,263,1638,106,8000380067),
  (1276,1177,5427,99,1769708370),
  (4151,4052,16052,99,492130943),
  (11924,11848,44348,76,165245115),
  (89989,89978,345978,11,22103671),
  (77,38,513,173,86354711609),
  (368,261,1636,107,8065214006),
  (1275,1175,5425,100,1773030295),
  (4150,4050,16050,100,492400154),
  (11923,11846,44346,77,165275988),
  (32471,32442,122442,29,60745818),
  (75,37,512,175,90619181489),
  (367,259,1634,108,8131039137),
  (1274,1173,5423,101,1776363592),
  (4149,4048,16048,101,492669635),
  (11921,11842,44342,79,165337766),
  (73,36,511,177,95221186383),
  (366,257,1632,109,8197878712),
  (1273,1171,5421,102,1779708320),
  (4148,4046,16046,102,492939386),
  (11920,11840,44340,80,165368670),
  (32470,32440,122440,30,60749975),
  (71,35,485,179,98142138994),
  (336,222,1422,114,9224489037),
  (1098,996,4496,102,2054361455)
]
def checks : Bool := data.all (fun a=>LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)
private theorem rowCheck_000 :
    LightCeilFast209.checkFast 100 50 525 150 128 53193587672 = true := by decide +kernel

private theorem rowCheck_001 :
    LightCeilFast209.checkFast 381 287 1662 94 128 7292122010 = true := by decide +kernel

private theorem rowCheck_002 :
    LightCeilFast209.checkFast 1285 1195 5445 90 128 1740313393 = true := by decide +kernel

private theorem rowCheck_003 :
    LightCeilFast209.checkFast 4160 4070 16070 90 128 489720105 = true := by decide +kernel

private theorem rowCheck_004 :
    LightCeilFast209.checkFast 11939 11878 44378 61 128 164783283 = true := by decide +kernel

private theorem rowCheck_005 :
    LightCeilFast209.checkFast 32477 32454 122454 23 128 60720888 = true := by decide +kernel

private theorem rowCheck_006 :
    LightCeilFast209.checkFast 89991 89982 345982 9 128 22102578 = true := by decide +kernel

private theorem rowCheck_007 :
    LightCeilFast209.checkFast 96 48 523 154 128 57272992490 = true := by decide +kernel

private theorem rowCheck_008 :
    LightCeilFast209.checkFast 379 283 1658 96 128 7401918977 = true := by decide +kernel

private theorem rowCheck_009 :
    LightCeilFast209.checkFast 1283 1191 5441 92 128 1746768515 = true := by decide +kernel

private theorem rowCheck_010 :
    LightCeilFast209.checkFast 4158 4066 16066 92 128 490253978 = true := by decide +kernel

private theorem rowCheck_011 :
    LightCeilFast209.checkFast 11936 11872 44372 64 128 164875461 = true := by decide +kernel

private theorem rowCheck_012 :
    LightCeilFast209.checkFast 32476 32452 122452 24 128 60725042 = true := by decide +kernel

private theorem rowCheck_013 :
    LightCeilFast209.checkFast 92 46 521 158 128 61864740805 = true := by decide +kernel

private theorem rowCheck_014 :
    LightCeilFast209.checkFast 377 279 1654 98 128 7514825131 = true := by decide +kernel

private theorem rowCheck_015 :
    LightCeilFast209.checkFast 1282 1189 5439 93 128 1750012430 = true := by decide +kernel

private theorem rowCheck_016 :
    LightCeilFast209.checkFast 4157 4064 16064 93 128 490521313 = true := by decide +kernel

private theorem rowCheck_017 :
    LightCeilFast209.checkFast 11933 11866 44366 67 128 164967733 = true := by decide +kernel

private theorem rowCheck_018 :
    LightCeilFast209.checkFast 32475 32450 122450 25 128 60729196 = true := by decide +kernel

private theorem rowCheck_019 :
    LightCeilFast209.checkFast 88 44 519 162 128 67060254663 = true := by decide +kernel

private theorem rowCheck_020 :
    LightCeilFast209.checkFast 374 273 1648 101 128 7690312976 = true := by decide +kernel

private theorem rowCheck_021 :
    LightCeilFast209.checkFast 1280 1185 5435 95 128 1756533243 = true := by decide +kernel

private theorem rowCheck_022 :
    LightCeilFast209.checkFast 4155 4060 16060 95 128 491056785 = true := by decide +kernel

private theorem rowCheck_023 :
    LightCeilFast209.checkFast 11931 11862 44362 69 128 165029300 = true := by decide +kernel

private theorem rowCheck_024 :
    LightCeilFast209.checkFast 32474 32448 122448 26 128 60733351 = true := by decide +kernel

private theorem rowCheck_025 :
    LightCeilFast209.checkFast 89990 89980 345980 10 128 22103125 = true := by decide +kernel

private theorem rowCheck_026 :
    LightCeilFast209.checkFast 83 41 516 167 128 75281009700 = true := by decide +kernel

private theorem rowCheck_027 :
    LightCeilFast209.checkFast 372 269 1644 103 128 7811603437 = true := by decide +kernel

private theorem rowCheck_028 :
    LightCeilFast209.checkFast 1278 1181 5431 97 128 1763098406 = true := by decide +kernel

private theorem rowCheck_029 :
    LightCeilFast209.checkFast 4153 4056 16056 97 128 491593327 = true := by decide +kernel

private theorem rowCheck_030 :
    LightCeilFast209.checkFast 11927 11854 44354 73 128 165152560 = true := by decide +kernel

private theorem rowCheck_031 :
    LightCeilFast209.checkFast 32473 32446 122446 27 128 60737506 = true := by decide +kernel

private theorem rowCheck_032 :
    LightCeilFast209.checkFast 81 40 515 169 128 78712888040 = true := by decide +kernel

private theorem rowCheck_033 :
    LightCeilFast209.checkFast 370 265 1640 105 128 7936514782 = true := by decide +kernel

private theorem rowCheck_034 :
    LightCeilFast209.checkFast 1277 1179 5429 98 128 1766397759 = true := by decide +kernel

private theorem rowCheck_035 :
    LightCeilFast209.checkFast 4152 4054 16054 98 128 491862000 = true := by decide +kernel

private theorem rowCheck_036 :
    LightCeilFast209.checkFast 11926 11852 44352 74 128 165183401 = true := by decide +kernel

private theorem rowCheck_037 :
    LightCeilFast209.checkFast 32472 32444 122444 28 128 60741662 = true := by decide +kernel

private theorem rowCheck_038 :
    LightCeilFast209.checkFast 79 39 514 171 128 82395581427 = true := by decide +kernel

private theorem rowCheck_039 :
    LightCeilFast209.checkFast 369 263 1638 106 128 8000380067 = true := by decide +kernel

private theorem rowCheck_040 :
    LightCeilFast209.checkFast 1276 1177 5427 99 128 1769708370 = true := by decide +kernel

private theorem rowCheck_041 :
    LightCeilFast209.checkFast 4151 4052 16052 99 128 492130943 = true := by decide +kernel

private theorem rowCheck_042 :
    LightCeilFast209.checkFast 11924 11848 44348 76 128 165245115 = true := by decide +kernel

private theorem rowCheck_043 :
    LightCeilFast209.checkFast 89989 89978 345978 11 128 22103671 = true := by decide +kernel

private theorem rowCheck_044 :
    LightCeilFast209.checkFast 77 38 513 173 128 86354711609 = true := by decide +kernel

private theorem rowCheck_045 :
    LightCeilFast209.checkFast 368 261 1636 107 128 8065214006 = true := by decide +kernel

private theorem rowCheck_046 :
    LightCeilFast209.checkFast 1275 1175 5425 100 128 1773030295 = true := by decide +kernel

private theorem rowCheck_047 :
    LightCeilFast209.checkFast 4150 4050 16050 100 128 492400154 = true := by decide +kernel

private theorem rowCheck_048 :
    LightCeilFast209.checkFast 11923 11846 44346 77 128 165275988 = true := by decide +kernel

private theorem rowCheck_049 :
    LightCeilFast209.checkFast 32471 32442 122442 29 128 60745818 = true := by decide +kernel

private theorem rowCheck_050 :
    LightCeilFast209.checkFast 75 37 512 175 128 90619181489 = true := by decide +kernel

private theorem rowCheck_051 :
    LightCeilFast209.checkFast 367 259 1634 108 128 8131039137 = true := by decide +kernel

private theorem rowCheck_052 :
    LightCeilFast209.checkFast 1274 1173 5423 101 128 1776363592 = true := by decide +kernel

private theorem rowCheck_053 :
    LightCeilFast209.checkFast 4149 4048 16048 101 128 492669635 = true := by decide +kernel

private theorem rowCheck_054 :
    LightCeilFast209.checkFast 11921 11842 44342 79 128 165337766 = true := by decide +kernel

private theorem rowCheck_055 :
    LightCeilFast209.checkFast 73 36 511 177 128 95221186383 = true := by decide +kernel

private theorem rowCheck_056 :
    LightCeilFast209.checkFast 366 257 1632 109 128 8197878712 = true := by decide +kernel

private theorem rowCheck_057 :
    LightCeilFast209.checkFast 1273 1171 5421 102 128 1779708320 = true := by decide +kernel

private theorem rowCheck_058 :
    LightCeilFast209.checkFast 4148 4046 16046 102 128 492939386 = true := by decide +kernel

private theorem rowCheck_059 :
    LightCeilFast209.checkFast 11920 11840 44340 80 128 165368670 = true := by decide +kernel

private theorem rowCheck_060 :
    LightCeilFast209.checkFast 32470 32440 122440 30 128 60749975 = true := by decide +kernel

private theorem rowCheck_061 :
    LightCeilFast209.checkFast 71 35 485 179 128 98142138994 = true := by decide +kernel

private theorem rowCheck_062 :
    LightCeilFast209.checkFast 336 222 1422 114 128 9224489037 = true := by decide +kernel

private theorem rowCheck_063 :
    LightCeilFast209.checkFast 1098 996 4496 102 128 2054361455 = true := by decide +kernel

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
end JSP233.LightValues209_002
