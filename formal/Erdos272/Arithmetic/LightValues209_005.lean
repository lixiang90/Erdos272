import Erdos272.Certificates.LightCeilFast209
namespace JSP233.LightValues209_005
open LightAnalytic209 ResidualCeil208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
  (30445,30410,121850,35,66642256),
  (64,32,489,190,118971111658),
  (336,215,1434,121,9544573469),
  (1112,1005,4561,107,2037385448),
  (3449,3342,13502,107,600114748),
  (10053,9946,40426,107,204212499),
  (30444,30408,121848,36,66647157),
  (61,30,487,193,131628704151),
  (334,211,1430,123,9732647360),
  (1110,1001,4557,109,2046298054),
  (3447,3338,13498,109,600911358),
  (10051,9942,40422,109,204304180),
  (30443,30406,121846,37,66652059),
  (91427,91414,351510,13,21756548),
  (207,154,882,53,13431641838),
  (684,640,2980,44,3290982645),
  (2296,2252,10572,44,958686203),
  (8305,8290,35590,15,252225230),
  (27295,27290,109190,5,74244338),
  (81898,81896,266496,2,22396585),
  (185,110,734,75,17901834019),
  (568,512,2592,56,4198012067),
  (2024,1968,9768,56,1119780962),
  (7770,7740,33740,30,271758471),
  (25991,25982,103982,9,77984997),
  (77997,77994,259994,3,23802287),
  (181998,181996,448236,2,8683373),
  (165,82,654,95,24031379128),
  (506,440,2260,66,4834410797),
  (1754,1688,7928,66,1268658957),
  (6183,6126,26926,57,343811498),
  (20783,20766,83166,17,97584138),
  (62394,62388,218388,6,30479288),
  (155997,155994,422234,3,10673897),
  (148,74,594,112,27762437307),
  (446,372,1932,74,5631618100),
  (1486,1412,6612,74,1506028539),
  (5126,5052,20652,74,402390450),
  (15570,15540,62340,30,130435185),
  (46790,46780,176780,10,42166206),
  (129996,129992,396232,4,13645521),
  (135,67,587,125,32903076510),
  (440,360,1920,80,5834964634),
  (1480,1400,6600,80,1520409006),
  (5120,5040,20640,80,403458673),
  (15564,15528,62328,36,130547872),
  (46788,46776,176776,12,42170210),
  (129995,129990,396230,5,13645747),
  (122,61,555,138,38340441558),
  (407,320,1750,87,6508866590),
  (1345,1260,5680,85,1648152183),
  (4335,4250,16730,85,468773068),
  (12428,12376,46176,52,158121251),
  (33781,33762,127362,19,58366582),
  (93593,93586,359826,7,21251286),
  (113,56,550,147,44322865809),
  (402,310,1740,92,6733902560),
  (1341,1252,5672,89,1659798660),
  (4331,4242,16722,89,469753071),
  (12423,12366,46166,57,158262804),
  (33779,33758,127358,21,58374259),
  (93592,93584,359824,8,21251791),
  (104,52,546,156,51147680454),
  (397,300,1730,97,6973801970)
]
def checks : Bool := data.all (fun a=>LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)
private theorem rowCheck_000 :
    LightCeilFast209.checkFast 30445 30410 121850 35 128 66642256 = true := by decide +kernel

private theorem rowCheck_001 :
    LightCeilFast209.checkFast 64 32 489 190 128 118971111658 = true := by decide +kernel

private theorem rowCheck_002 :
    LightCeilFast209.checkFast 336 215 1434 121 128 9544573469 = true := by decide +kernel

private theorem rowCheck_003 :
    LightCeilFast209.checkFast 1112 1005 4561 107 128 2037385448 = true := by decide +kernel

private theorem rowCheck_004 :
    LightCeilFast209.checkFast 3449 3342 13502 107 128 600114748 = true := by decide +kernel

private theorem rowCheck_005 :
    LightCeilFast209.checkFast 10053 9946 40426 107 128 204212499 = true := by decide +kernel

private theorem rowCheck_006 :
    LightCeilFast209.checkFast 30444 30408 121848 36 128 66647157 = true := by decide +kernel

private theorem rowCheck_007 :
    LightCeilFast209.checkFast 61 30 487 193 128 131628704151 = true := by decide +kernel

private theorem rowCheck_008 :
    LightCeilFast209.checkFast 334 211 1430 123 128 9732647360 = true := by decide +kernel

private theorem rowCheck_009 :
    LightCeilFast209.checkFast 1110 1001 4557 109 128 2046298054 = true := by decide +kernel

private theorem rowCheck_010 :
    LightCeilFast209.checkFast 3447 3338 13498 109 128 600911358 = true := by decide +kernel

private theorem rowCheck_011 :
    LightCeilFast209.checkFast 10051 9942 40422 109 128 204304180 = true := by decide +kernel

private theorem rowCheck_012 :
    LightCeilFast209.checkFast 30443 30406 121846 37 128 66652059 = true := by decide +kernel

private theorem rowCheck_013 :
    LightCeilFast209.checkFast 91427 91414 351510 13 128 21756548 = true := by decide +kernel

private theorem rowCheck_014 :
    LightCeilFast209.checkFast 207 154 882 53 128 13431641838 = true := by decide +kernel

private theorem rowCheck_015 :
    LightCeilFast209.checkFast 684 640 2980 44 128 3290982645 = true := by decide +kernel

private theorem rowCheck_016 :
    LightCeilFast209.checkFast 2296 2252 10572 44 128 958686203 = true := by decide +kernel

private theorem rowCheck_017 :
    LightCeilFast209.checkFast 8305 8290 35590 15 128 252225230 = true := by decide +kernel

private theorem rowCheck_018 :
    LightCeilFast209.checkFast 27295 27290 109190 5 128 74244338 = true := by decide +kernel

private theorem rowCheck_019 :
    LightCeilFast209.checkFast 81898 81896 266496 2 128 22396585 = true := by decide +kernel

private theorem rowCheck_020 :
    LightCeilFast209.checkFast 185 110 734 75 128 17901834019 = true := by decide +kernel

private theorem rowCheck_021 :
    LightCeilFast209.checkFast 568 512 2592 56 128 4198012067 = true := by decide +kernel

private theorem rowCheck_022 :
    LightCeilFast209.checkFast 2024 1968 9768 56 128 1119780962 = true := by decide +kernel

private theorem rowCheck_023 :
    LightCeilFast209.checkFast 7770 7740 33740 30 128 271758471 = true := by decide +kernel

private theorem rowCheck_024 :
    LightCeilFast209.checkFast 25991 25982 103982 9 128 77984997 = true := by decide +kernel

private theorem rowCheck_025 :
    LightCeilFast209.checkFast 77997 77994 259994 3 128 23802287 = true := by decide +kernel

private theorem rowCheck_026 :
    LightCeilFast209.checkFast 181998 181996 448236 2 128 8683373 = true := by decide +kernel

private theorem rowCheck_027 :
    LightCeilFast209.checkFast 165 82 654 95 128 24031379128 = true := by decide +kernel

private theorem rowCheck_028 :
    LightCeilFast209.checkFast 506 440 2260 66 128 4834410797 = true := by decide +kernel

private theorem rowCheck_029 :
    LightCeilFast209.checkFast 1754 1688 7928 66 128 1268658957 = true := by decide +kernel

private theorem rowCheck_030 :
    LightCeilFast209.checkFast 6183 6126 26926 57 128 343811498 = true := by decide +kernel

private theorem rowCheck_031 :
    LightCeilFast209.checkFast 20783 20766 83166 17 128 97584138 = true := by decide +kernel

private theorem rowCheck_032 :
    LightCeilFast209.checkFast 62394 62388 218388 6 128 30479288 = true := by decide +kernel

private theorem rowCheck_033 :
    LightCeilFast209.checkFast 155997 155994 422234 3 128 10673897 = true := by decide +kernel

private theorem rowCheck_034 :
    LightCeilFast209.checkFast 148 74 594 112 128 27762437307 = true := by decide +kernel

private theorem rowCheck_035 :
    LightCeilFast209.checkFast 446 372 1932 74 128 5631618100 = true := by decide +kernel

private theorem rowCheck_036 :
    LightCeilFast209.checkFast 1486 1412 6612 74 128 1506028539 = true := by decide +kernel

private theorem rowCheck_037 :
    LightCeilFast209.checkFast 5126 5052 20652 74 128 402390450 = true := by decide +kernel

private theorem rowCheck_038 :
    LightCeilFast209.checkFast 15570 15540 62340 30 128 130435185 = true := by decide +kernel

private theorem rowCheck_039 :
    LightCeilFast209.checkFast 46790 46780 176780 10 128 42166206 = true := by decide +kernel

private theorem rowCheck_040 :
    LightCeilFast209.checkFast 129996 129992 396232 4 128 13645521 = true := by decide +kernel

private theorem rowCheck_041 :
    LightCeilFast209.checkFast 135 67 587 125 128 32903076510 = true := by decide +kernel

private theorem rowCheck_042 :
    LightCeilFast209.checkFast 440 360 1920 80 128 5834964634 = true := by decide +kernel

private theorem rowCheck_043 :
    LightCeilFast209.checkFast 1480 1400 6600 80 128 1520409006 = true := by decide +kernel

private theorem rowCheck_044 :
    LightCeilFast209.checkFast 5120 5040 20640 80 128 403458673 = true := by decide +kernel

private theorem rowCheck_045 :
    LightCeilFast209.checkFast 15564 15528 62328 36 128 130547872 = true := by decide +kernel

private theorem rowCheck_046 :
    LightCeilFast209.checkFast 46788 46776 176776 12 128 42170210 = true := by decide +kernel

private theorem rowCheck_047 :
    LightCeilFast209.checkFast 129995 129990 396230 5 128 13645747 = true := by decide +kernel

private theorem rowCheck_048 :
    LightCeilFast209.checkFast 122 61 555 138 128 38340441558 = true := by decide +kernel

private theorem rowCheck_049 :
    LightCeilFast209.checkFast 407 320 1750 87 128 6508866590 = true := by decide +kernel

private theorem rowCheck_050 :
    LightCeilFast209.checkFast 1345 1260 5680 85 128 1648152183 = true := by decide +kernel

private theorem rowCheck_051 :
    LightCeilFast209.checkFast 4335 4250 16730 85 128 468773068 = true := by decide +kernel

private theorem rowCheck_052 :
    LightCeilFast209.checkFast 12428 12376 46176 52 128 158121251 = true := by decide +kernel

private theorem rowCheck_053 :
    LightCeilFast209.checkFast 33781 33762 127362 19 128 58366582 = true := by decide +kernel

private theorem rowCheck_054 :
    LightCeilFast209.checkFast 93593 93586 359826 7 128 21251286 = true := by decide +kernel

private theorem rowCheck_055 :
    LightCeilFast209.checkFast 113 56 550 147 128 44322865809 = true := by decide +kernel

private theorem rowCheck_056 :
    LightCeilFast209.checkFast 402 310 1740 92 128 6733902560 = true := by decide +kernel

private theorem rowCheck_057 :
    LightCeilFast209.checkFast 1341 1252 5672 89 128 1659798660 = true := by decide +kernel

private theorem rowCheck_058 :
    LightCeilFast209.checkFast 4331 4242 16722 89 128 469753071 = true := by decide +kernel

private theorem rowCheck_059 :
    LightCeilFast209.checkFast 12423 12366 46166 57 128 158262804 = true := by decide +kernel

private theorem rowCheck_060 :
    LightCeilFast209.checkFast 33779 33758 127358 21 128 58374259 = true := by decide +kernel

private theorem rowCheck_061 :
    LightCeilFast209.checkFast 93592 93584 359824 8 128 21251791 = true := by decide +kernel

private theorem rowCheck_062 :
    LightCeilFast209.checkFast 104 52 546 156 128 51147680454 = true := by decide +kernel

private theorem rowCheck_063 :
    LightCeilFast209.checkFast 397 300 1730 97 128 6973801970 = true := by decide +kernel

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
end JSP233.LightValues209_005
