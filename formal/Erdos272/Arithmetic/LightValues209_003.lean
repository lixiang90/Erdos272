import Erdos272.Certificates.LightCeilFast209
namespace JSP233.LightValues209_003
open LightAnalytic209 ResidualCeil208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
  (3398,3296,13296,102,608358060),
  (9902,9804,39804,98,207134423),
  (29967,29934,119934,33,67701204),
  (69,34,484,181,103452597082),
  (335,220,1420,115,9311938568),
  (1097,994,4494,103,2058889441),
  (3397,3294,13294,103,608767292),
  (9900,9800,39800,100,207228778),
  (29966,29932,119932,34,67706262),
  (89988,89976,345976,12,22104218),
  (67,33,483,183,109224549303),
  (333,216,1416,117,9491630048),
  (1096,992,4492,104,2063435667),
  (3396,3292,13292,104,609177028),
  (9898,9796,39796,102,207323209),
  (65,32,482,185,115513185718),
  (332,214,1414,118,9583962042),
  (1095,990,4490,105,2068000245),
  (3395,3290,13290,105,609587269),
  (9896,9792,39792,104,207417719),
  (29965,29930,119930,35,67711321),
  (63,31,481,187,122383098879),
  (331,212,1412,119,9678014459),
  (1094,988,4488,106,2072583285),
  (3394,3288,13288,106,609998016),
  (9894,9788,39788,106,207512306),
  (29964,29928,119928,36,67716380),
  (61,30,480,189,129909809552),
  (330,210,1410,120,9773836786),
  (1093,986,4486,107,2077184899),
  (3393,3286,13286,107,610409271),
  (9893,9786,39786,107,207559629),
  (60,30,480,190,132200335569),
  (329,208,1408,121,9871480457),
  (29963,29926,119926,37,67721440),
  (202,150,861,52,13790816936),
  (668,625,2911,43,3370334086),
  (2243,2200,10328,43,981347770),
  (8113,8098,34768,15,258208099),
  (26665,26660,106670,5,75998877),
  (80008,80006,260346,2,22925667),
  (181,108,717,73,18223310294),
  (554,499,2531,55,4309522218),
  (1977,1922,9542,55,1146625321),
  (7590,7560,32960,30,278235218),
  (25391,25382,101582,9,79828623),
  (76197,76194,253994,3,24364594),
  (177798,177796,437892,2,8888496),
  (161,80,638,93,24637519443),
  (493,428,2206,65,4973903052),
  (1713,1648,7744,65,1299549247),
  (6040,5984,26304,56,351974675),
  (20303,20286,81246,17,99893595),
  (60954,60948,213348,6,31199427),
  (152397,152394,412490,3,10926046),
  (144,72,580,110,28624365995),
  (435,362,1886,73,5789062717),
  (1451,1378,6458,73,1543367821),
  (5007,4934,20174,73,412027477),
  (15210,15180,60900,30,133529946),
  (45710,45700,172700,10,43162742),
  (126996,126992,387088,4,13967878),
  (131,65,573,123,34094423531),
  (429,350,1874,79,6004000103)
]
def checks : Bool := data.all (fun a=>LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)
private theorem rowCheck_000 :
    LightCeilFast209.checkFast 3398 3296 13296 102 128 608358060 = true := by decide +kernel

private theorem rowCheck_001 :
    LightCeilFast209.checkFast 9902 9804 39804 98 128 207134423 = true := by decide +kernel

private theorem rowCheck_002 :
    LightCeilFast209.checkFast 29967 29934 119934 33 128 67701204 = true := by decide +kernel

private theorem rowCheck_003 :
    LightCeilFast209.checkFast 69 34 484 181 128 103452597082 = true := by decide +kernel

private theorem rowCheck_004 :
    LightCeilFast209.checkFast 335 220 1420 115 128 9311938568 = true := by decide +kernel

private theorem rowCheck_005 :
    LightCeilFast209.checkFast 1097 994 4494 103 128 2058889441 = true := by decide +kernel

private theorem rowCheck_006 :
    LightCeilFast209.checkFast 3397 3294 13294 103 128 608767292 = true := by decide +kernel

private theorem rowCheck_007 :
    LightCeilFast209.checkFast 9900 9800 39800 100 128 207228778 = true := by decide +kernel

private theorem rowCheck_008 :
    LightCeilFast209.checkFast 29966 29932 119932 34 128 67706262 = true := by decide +kernel

private theorem rowCheck_009 :
    LightCeilFast209.checkFast 89988 89976 345976 12 128 22104218 = true := by decide +kernel

private theorem rowCheck_010 :
    LightCeilFast209.checkFast 67 33 483 183 128 109224549303 = true := by decide +kernel

private theorem rowCheck_011 :
    LightCeilFast209.checkFast 333 216 1416 117 128 9491630048 = true := by decide +kernel

private theorem rowCheck_012 :
    LightCeilFast209.checkFast 1096 992 4492 104 128 2063435667 = true := by decide +kernel

private theorem rowCheck_013 :
    LightCeilFast209.checkFast 3396 3292 13292 104 128 609177028 = true := by decide +kernel

private theorem rowCheck_014 :
    LightCeilFast209.checkFast 9898 9796 39796 102 128 207323209 = true := by decide +kernel

private theorem rowCheck_015 :
    LightCeilFast209.checkFast 65 32 482 185 128 115513185718 = true := by decide +kernel

private theorem rowCheck_016 :
    LightCeilFast209.checkFast 332 214 1414 118 128 9583962042 = true := by decide +kernel

private theorem rowCheck_017 :
    LightCeilFast209.checkFast 1095 990 4490 105 128 2068000245 = true := by decide +kernel

private theorem rowCheck_018 :
    LightCeilFast209.checkFast 3395 3290 13290 105 128 609587269 = true := by decide +kernel

private theorem rowCheck_019 :
    LightCeilFast209.checkFast 9896 9792 39792 104 128 207417719 = true := by decide +kernel

private theorem rowCheck_020 :
    LightCeilFast209.checkFast 29965 29930 119930 35 128 67711321 = true := by decide +kernel

private theorem rowCheck_021 :
    LightCeilFast209.checkFast 63 31 481 187 128 122383098879 = true := by decide +kernel

private theorem rowCheck_022 :
    LightCeilFast209.checkFast 331 212 1412 119 128 9678014459 = true := by decide +kernel

private theorem rowCheck_023 :
    LightCeilFast209.checkFast 1094 988 4488 106 128 2072583285 = true := by decide +kernel

private theorem rowCheck_024 :
    LightCeilFast209.checkFast 3394 3288 13288 106 128 609998016 = true := by decide +kernel

private theorem rowCheck_025 :
    LightCeilFast209.checkFast 9894 9788 39788 106 128 207512306 = true := by decide +kernel

private theorem rowCheck_026 :
    LightCeilFast209.checkFast 29964 29928 119928 36 128 67716380 = true := by decide +kernel

private theorem rowCheck_027 :
    LightCeilFast209.checkFast 61 30 480 189 128 129909809552 = true := by decide +kernel

private theorem rowCheck_028 :
    LightCeilFast209.checkFast 330 210 1410 120 128 9773836786 = true := by decide +kernel

private theorem rowCheck_029 :
    LightCeilFast209.checkFast 1093 986 4486 107 128 2077184899 = true := by decide +kernel

private theorem rowCheck_030 :
    LightCeilFast209.checkFast 3393 3286 13286 107 128 610409271 = true := by decide +kernel

private theorem rowCheck_031 :
    LightCeilFast209.checkFast 9893 9786 39786 107 128 207559629 = true := by decide +kernel

private theorem rowCheck_032 :
    LightCeilFast209.checkFast 60 30 480 190 128 132200335569 = true := by decide +kernel

private theorem rowCheck_033 :
    LightCeilFast209.checkFast 329 208 1408 121 128 9871480457 = true := by decide +kernel

private theorem rowCheck_034 :
    LightCeilFast209.checkFast 29963 29926 119926 37 128 67721440 = true := by decide +kernel

private theorem rowCheck_035 :
    LightCeilFast209.checkFast 202 150 861 52 128 13790816936 = true := by decide +kernel

private theorem rowCheck_036 :
    LightCeilFast209.checkFast 668 625 2911 43 128 3370334086 = true := by decide +kernel

private theorem rowCheck_037 :
    LightCeilFast209.checkFast 2243 2200 10328 43 128 981347770 = true := by decide +kernel

private theorem rowCheck_038 :
    LightCeilFast209.checkFast 8113 8098 34768 15 128 258208099 = true := by decide +kernel

private theorem rowCheck_039 :
    LightCeilFast209.checkFast 26665 26660 106670 5 128 75998877 = true := by decide +kernel

private theorem rowCheck_040 :
    LightCeilFast209.checkFast 80008 80006 260346 2 128 22925667 = true := by decide +kernel

private theorem rowCheck_041 :
    LightCeilFast209.checkFast 181 108 717 73 128 18223310294 = true := by decide +kernel

private theorem rowCheck_042 :
    LightCeilFast209.checkFast 554 499 2531 55 128 4309522218 = true := by decide +kernel

private theorem rowCheck_043 :
    LightCeilFast209.checkFast 1977 1922 9542 55 128 1146625321 = true := by decide +kernel

private theorem rowCheck_044 :
    LightCeilFast209.checkFast 7590 7560 32960 30 128 278235218 = true := by decide +kernel

private theorem rowCheck_045 :
    LightCeilFast209.checkFast 25391 25382 101582 9 128 79828623 = true := by decide +kernel

private theorem rowCheck_046 :
    LightCeilFast209.checkFast 76197 76194 253994 3 128 24364594 = true := by decide +kernel

private theorem rowCheck_047 :
    LightCeilFast209.checkFast 177798 177796 437892 2 128 8888496 = true := by decide +kernel

private theorem rowCheck_048 :
    LightCeilFast209.checkFast 161 80 638 93 128 24637519443 = true := by decide +kernel

private theorem rowCheck_049 :
    LightCeilFast209.checkFast 493 428 2206 65 128 4973903052 = true := by decide +kernel

private theorem rowCheck_050 :
    LightCeilFast209.checkFast 1713 1648 7744 65 128 1299549247 = true := by decide +kernel

private theorem rowCheck_051 :
    LightCeilFast209.checkFast 6040 5984 26304 56 128 351974675 = true := by decide +kernel

private theorem rowCheck_052 :
    LightCeilFast209.checkFast 20303 20286 81246 17 128 99893595 = true := by decide +kernel

private theorem rowCheck_053 :
    LightCeilFast209.checkFast 60954 60948 213348 6 128 31199427 = true := by decide +kernel

private theorem rowCheck_054 :
    LightCeilFast209.checkFast 152397 152394 412490 3 128 10926046 = true := by decide +kernel

private theorem rowCheck_055 :
    LightCeilFast209.checkFast 144 72 580 110 128 28624365995 = true := by decide +kernel

private theorem rowCheck_056 :
    LightCeilFast209.checkFast 435 362 1886 73 128 5789062717 = true := by decide +kernel

private theorem rowCheck_057 :
    LightCeilFast209.checkFast 1451 1378 6458 73 128 1543367821 = true := by decide +kernel

private theorem rowCheck_058 :
    LightCeilFast209.checkFast 5007 4934 20174 73 128 412027477 = true := by decide +kernel

private theorem rowCheck_059 :
    LightCeilFast209.checkFast 15210 15180 60900 30 128 133529946 = true := by decide +kernel

private theorem rowCheck_060 :
    LightCeilFast209.checkFast 45710 45700 172700 10 128 43162742 = true := by decide +kernel

private theorem rowCheck_061 :
    LightCeilFast209.checkFast 126996 126992 387088 4 128 13967878 = true := by decide +kernel

private theorem rowCheck_062 :
    LightCeilFast209.checkFast 131 65 573 123 128 34094423531 = true := by decide +kernel

private theorem rowCheck_063 :
    LightCeilFast209.checkFast 429 350 1874 79 128 6004000103 = true := by decide +kernel

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
end JSP233.LightValues209_003
