import Erdos272.Certificates.LightCeilFast209
namespace JSP233.LightValues209_012
open LightAnalytic209 ResidualCeil208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
  (16233,16066,65266,167,126411674),
  (49141,49082,196682,59,41290401),
  (147580,147560,567400,20,13478247),
  (380,227,1506,153,8672875679),
  (1176,1073,5337,103,1998585444),
  (4161,4058,20048,103,542655703),
  (15928,15866,69166,62,132574498),
  (53281,53262,213162,19,38042341),
  (159893,159886,532986,7,11611007),
  (373097,373094,1014492,3,4473962),
  (302,151,1217,231,13654840895),
  (921,776,3974,145,2695748329),
  (3058,2918,13578,140,728086305),
  (10520,10380,42360,140,195794662),
  (31918,31856,127796,62,63629153),
  (95919,95898,362398,21,20569119),
  (266492,266484,907882,8,7041885),
  (249,124,1136,284,18903448774),
  (834,656,3587,178,3175532357),
  (2769,2607,11668,162,795825779),
  (8899,8737,34321,162,227959017),
  (25478,25372,94662,106,77128279),
  (69251,69212,261092,39,28471549),
  (191865,191850,833248,15,10964128),
  (214,107,1119,319,24774261619),
  (814,616,3547,198,3396497510),
  (2754,2577,11638,177,806081126),
  (8884,8707,34291,177,228829908),
  (25455,25326,94616,129,77283364),
  (69242,69194,261074,48,28479771),
  (191862,191844,833242,18,10964514),
  (183,91,1103,350,33039888613),
  (796,580,3511,216,3621105998),
  (2740,2549,11610,191,815871531),
  (8870,8679,34263,191,229648245),
  (25433,25282,94572,151,77432239),
  (69234,69178,261058,56,28487082),
  (191860,191840,833238,20,10964771),
  (161,80,1092,372,41730697981),
  (784,556,3487,228,3786811111),
  (2731,2531,11592,200,822280232),
  (8861,8661,34245,200,230177150),
  (25417,25250,94540,167,77540841),
  (69228,69166,261046,62,28492568),
  (191857,191834,833232,23,10965157),
  (143,71,1030,390,50802248805),
  (711,463,3021,248,4427475852),
  (2350,2142,9604,208,954493430),
  (7254,7046,28366,208,284496967),
  (21112,20904,84864,208,97145273),
  (63887,63814,255694,73,31757729),
  (191856,191832,833230,24,10965285),
  (128,64,1023,405,61927128079),
  (702,445,3003,257,4613889147),
  (2344,2130,9592,214,960389153),
  (7248,7034,28354,214,285034816),
  (21106,20892,84852,214,97207547),
  (63883,63806,255686,77,31762181),
  (191854,191828,833226,26,10965543),
  (565,338,2238,227,5823714270),
  (1753,1606,7942,147,1334349593),
  (6189,6042,29802,147,364371806),
  (23668,23576,102776,92,89218874),
  (79172,79144,316744,28,25601559)
]
def checks : Bool := data.all (fun a=>LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)
private theorem rowCheck_000 :
    LightCeilFast209.checkFast 16233 16066 65266 167 128 126411674 = true := by decide +kernel

private theorem rowCheck_001 :
    LightCeilFast209.checkFast 49141 49082 196682 59 128 41290401 = true := by decide +kernel

private theorem rowCheck_002 :
    LightCeilFast209.checkFast 147580 147560 567400 20 128 13478247 = true := by decide +kernel

private theorem rowCheck_003 :
    LightCeilFast209.checkFast 380 227 1506 153 128 8672875679 = true := by decide +kernel

private theorem rowCheck_004 :
    LightCeilFast209.checkFast 1176 1073 5337 103 128 1998585444 = true := by decide +kernel

private theorem rowCheck_005 :
    LightCeilFast209.checkFast 4161 4058 20048 103 128 542655703 = true := by decide +kernel

private theorem rowCheck_006 :
    LightCeilFast209.checkFast 15928 15866 69166 62 128 132574498 = true := by decide +kernel

private theorem rowCheck_007 :
    LightCeilFast209.checkFast 53281 53262 213162 19 128 38042341 = true := by decide +kernel

private theorem rowCheck_008 :
    LightCeilFast209.checkFast 159893 159886 532986 7 128 11611007 = true := by decide +kernel

private theorem rowCheck_009 :
    LightCeilFast209.checkFast 373097 373094 1014492 3 128 4473962 = true := by decide +kernel

private theorem rowCheck_010 :
    LightCeilFast209.checkFast 302 151 1217 231 128 13654840895 = true := by decide +kernel

private theorem rowCheck_011 :
    LightCeilFast209.checkFast 921 776 3974 145 128 2695748329 = true := by decide +kernel

private theorem rowCheck_012 :
    LightCeilFast209.checkFast 3058 2918 13578 140 128 728086305 = true := by decide +kernel

private theorem rowCheck_013 :
    LightCeilFast209.checkFast 10520 10380 42360 140 128 195794662 = true := by decide +kernel

private theorem rowCheck_014 :
    LightCeilFast209.checkFast 31918 31856 127796 62 128 63629153 = true := by decide +kernel

private theorem rowCheck_015 :
    LightCeilFast209.checkFast 95919 95898 362398 21 128 20569119 = true := by decide +kernel

private theorem rowCheck_016 :
    LightCeilFast209.checkFast 266492 266484 907882 8 128 7041885 = true := by decide +kernel

private theorem rowCheck_017 :
    LightCeilFast209.checkFast 249 124 1136 284 128 18903448774 = true := by decide +kernel

private theorem rowCheck_018 :
    LightCeilFast209.checkFast 834 656 3587 178 128 3175532357 = true := by decide +kernel

private theorem rowCheck_019 :
    LightCeilFast209.checkFast 2769 2607 11668 162 128 795825779 = true := by decide +kernel

private theorem rowCheck_020 :
    LightCeilFast209.checkFast 8899 8737 34321 162 128 227959017 = true := by decide +kernel

private theorem rowCheck_021 :
    LightCeilFast209.checkFast 25478 25372 94662 106 128 77128279 = true := by decide +kernel

private theorem rowCheck_022 :
    LightCeilFast209.checkFast 69251 69212 261092 39 128 28471549 = true := by decide +kernel

private theorem rowCheck_023 :
    LightCeilFast209.checkFast 191865 191850 833248 15 128 10964128 = true := by decide +kernel

private theorem rowCheck_024 :
    LightCeilFast209.checkFast 214 107 1119 319 128 24774261619 = true := by decide +kernel

private theorem rowCheck_025 :
    LightCeilFast209.checkFast 814 616 3547 198 128 3396497510 = true := by decide +kernel

private theorem rowCheck_026 :
    LightCeilFast209.checkFast 2754 2577 11638 177 128 806081126 = true := by decide +kernel

private theorem rowCheck_027 :
    LightCeilFast209.checkFast 8884 8707 34291 177 128 228829908 = true := by decide +kernel

private theorem rowCheck_028 :
    LightCeilFast209.checkFast 25455 25326 94616 129 128 77283364 = true := by decide +kernel

private theorem rowCheck_029 :
    LightCeilFast209.checkFast 69242 69194 261074 48 128 28479771 = true := by decide +kernel

private theorem rowCheck_030 :
    LightCeilFast209.checkFast 191862 191844 833242 18 128 10964514 = true := by decide +kernel

private theorem rowCheck_031 :
    LightCeilFast209.checkFast 183 91 1103 350 128 33039888613 = true := by decide +kernel

private theorem rowCheck_032 :
    LightCeilFast209.checkFast 796 580 3511 216 128 3621105998 = true := by decide +kernel

private theorem rowCheck_033 :
    LightCeilFast209.checkFast 2740 2549 11610 191 128 815871531 = true := by decide +kernel

private theorem rowCheck_034 :
    LightCeilFast209.checkFast 8870 8679 34263 191 128 229648245 = true := by decide +kernel

private theorem rowCheck_035 :
    LightCeilFast209.checkFast 25433 25282 94572 151 128 77432239 = true := by decide +kernel

private theorem rowCheck_036 :
    LightCeilFast209.checkFast 69234 69178 261058 56 128 28487082 = true := by decide +kernel

private theorem rowCheck_037 :
    LightCeilFast209.checkFast 191860 191840 833238 20 128 10964771 = true := by decide +kernel

private theorem rowCheck_038 :
    LightCeilFast209.checkFast 161 80 1092 372 128 41730697981 = true := by decide +kernel

private theorem rowCheck_039 :
    LightCeilFast209.checkFast 784 556 3487 228 128 3786811111 = true := by decide +kernel

private theorem rowCheck_040 :
    LightCeilFast209.checkFast 2731 2531 11592 200 128 822280232 = true := by decide +kernel

private theorem rowCheck_041 :
    LightCeilFast209.checkFast 8861 8661 34245 200 128 230177150 = true := by decide +kernel

private theorem rowCheck_042 :
    LightCeilFast209.checkFast 25417 25250 94540 167 128 77540841 = true := by decide +kernel

private theorem rowCheck_043 :
    LightCeilFast209.checkFast 69228 69166 261046 62 128 28492568 = true := by decide +kernel

private theorem rowCheck_044 :
    LightCeilFast209.checkFast 191857 191834 833232 23 128 10965157 = true := by decide +kernel

private theorem rowCheck_045 :
    LightCeilFast209.checkFast 143 71 1030 390 128 50802248805 = true := by decide +kernel

private theorem rowCheck_046 :
    LightCeilFast209.checkFast 711 463 3021 248 128 4427475852 = true := by decide +kernel

private theorem rowCheck_047 :
    LightCeilFast209.checkFast 2350 2142 9604 208 128 954493430 = true := by decide +kernel

private theorem rowCheck_048 :
    LightCeilFast209.checkFast 7254 7046 28366 208 128 284496967 = true := by decide +kernel

private theorem rowCheck_049 :
    LightCeilFast209.checkFast 21112 20904 84864 208 128 97145273 = true := by decide +kernel

private theorem rowCheck_050 :
    LightCeilFast209.checkFast 63887 63814 255694 73 128 31757729 = true := by decide +kernel

private theorem rowCheck_051 :
    LightCeilFast209.checkFast 191856 191832 833230 24 128 10965285 = true := by decide +kernel

private theorem rowCheck_052 :
    LightCeilFast209.checkFast 128 64 1023 405 128 61927128079 = true := by decide +kernel

private theorem rowCheck_053 :
    LightCeilFast209.checkFast 702 445 3003 257 128 4613889147 = true := by decide +kernel

private theorem rowCheck_054 :
    LightCeilFast209.checkFast 2344 2130 9592 214 128 960389153 = true := by decide +kernel

private theorem rowCheck_055 :
    LightCeilFast209.checkFast 7248 7034 28354 214 128 285034816 = true := by decide +kernel

private theorem rowCheck_056 :
    LightCeilFast209.checkFast 21106 20892 84852 214 128 97207547 = true := by decide +kernel

private theorem rowCheck_057 :
    LightCeilFast209.checkFast 63883 63806 255686 77 128 31762181 = true := by decide +kernel

private theorem rowCheck_058 :
    LightCeilFast209.checkFast 191854 191828 833226 26 128 10965543 = true := by decide +kernel

private theorem rowCheck_059 :
    LightCeilFast209.checkFast 565 338 2238 227 128 5823714270 = true := by decide +kernel

private theorem rowCheck_060 :
    LightCeilFast209.checkFast 1753 1606 7942 147 128 1334349593 = true := by decide +kernel

private theorem rowCheck_061 :
    LightCeilFast209.checkFast 6189 6042 29802 147 128 364371806 = true := by decide +kernel

private theorem rowCheck_062 :
    LightCeilFast209.checkFast 23668 23576 102776 92 128 89218874 = true := by decide +kernel

private theorem rowCheck_063 :
    LightCeilFast209.checkFast 79172 79144 316744 28 128 25601559 = true := by decide +kernel

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
end JSP233.LightValues209_012
