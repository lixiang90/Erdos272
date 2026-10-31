import Erdos272.Certificates.LightCeilFast209
namespace JSP233.LightValues209_007
open LightAnalytic209 ResidualCeil208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
  (588,531,2683,57,4047737910),
  (2095,2038,10108,57,1081193087),
  (8039,8008,34908,31,262663345),
  (26890,26880,107580,10,75380151),
  (80696,80692,268992,4,23006486),
  (188298,188296,463752,2,8392844),
  (170,85,676,99,23277230465),
  (523,455,2338,68,4676967081),
  (1815,1747,8203,68,1225766282),
  (6396,6336,27856,60,332429438),
  (21502,21484,86044,18,94323282),
  (64554,64548,225948,6,29459326),
  (161397,161394,436850,3,10316764),
  (153,76,614,116,27004910020),
  (462,386,2000,76,5426045183),
  (1538,1462,6842,76,1454395420),
  (5304,5228,21368,76,388834418),
  (16109,16078,64498,31,126070508),
  (48409,48398,182898,11,40756664),
  (134496,134492,409948,4,13188950),
  (139,69,607,130,32073168821),
  (456,374,1988,82,5614678472),
  (1532,1450,6830,82,1467804901),
  (5298,5216,21356,82,389831847),
  (16103,16066,64486,37,126175777),
  (48407,48394,182894,13,40760404),
  (134495,134490,409946,5,13189162),
  (126,63,574,143,37172670916),
  (421,331,1810,90,6292233476),
  (1391,1303,5876,88,1593976085),
  (4485,4397,17309,88,453102390),
  (12858,12804,47774,54,152836235),
  (34950,34930,131770,20,56415024),
  (96832,96824,372280,8,20540634),
  (117,58,569,152,42767799796),
  (416,321,1800,95,6502322716),
  (1387,1295,5868,92,1604865805),
  (4481,4389,17301,92,454017905),
  (12853,12794,47764,59,152968478),
  (34948,34926,131766,22,56422196),
  (108,54,565,161,49101562365),
  (410,309,1788,101,6772211309),
  (1383,1287,5860,96,1615891488),
  (4477,4381,17293,96,454936807),
  (12847,12782,47752,65,153127447),
  (34946,34922,131762,24,56429369),
  (96831,96822,372278,9,20541106),
  (101,50,561,168,55862049924),
  (406,301,1780,105,6963936644),
  (1380,1281,5854,99,1624251505),
  (4474,4375,17287,99,455628220),
  (12842,12772,47742,70,153260151),
  (34944,34918,131758,26,56436544),
  (96830,96820,372276,10,20541578),
  (95,47,558,174,62456836107),
  (403,295,1774,108,7114470724),
  (1378,1277,5850,101,1629868674),
  (4472,4371,17283,101,456090230),
  (12838,12764,47734,74,153366466),
  (34942,34914,131754,28,56443721),
  (88,44,555,181,71186809567),
  (399,287,1766,112,7324858907),
  (1375,1271,5844,104,1638360991),
  (4469,4365,17277,104,456784854)
]
def checks : Bool := data.all (fun a=>LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)
private theorem rowCheck_000 :
    LightCeilFast209.checkFast 588 531 2683 57 128 4047737910 = true := by decide +kernel

private theorem rowCheck_001 :
    LightCeilFast209.checkFast 2095 2038 10108 57 128 1081193087 = true := by decide +kernel

private theorem rowCheck_002 :
    LightCeilFast209.checkFast 8039 8008 34908 31 128 262663345 = true := by decide +kernel

private theorem rowCheck_003 :
    LightCeilFast209.checkFast 26890 26880 107580 10 128 75380151 = true := by decide +kernel

private theorem rowCheck_004 :
    LightCeilFast209.checkFast 80696 80692 268992 4 128 23006486 = true := by decide +kernel

private theorem rowCheck_005 :
    LightCeilFast209.checkFast 188298 188296 463752 2 128 8392844 = true := by decide +kernel

private theorem rowCheck_006 :
    LightCeilFast209.checkFast 170 85 676 99 128 23277230465 = true := by decide +kernel

private theorem rowCheck_007 :
    LightCeilFast209.checkFast 523 455 2338 68 128 4676967081 = true := by decide +kernel

private theorem rowCheck_008 :
    LightCeilFast209.checkFast 1815 1747 8203 68 128 1225766282 = true := by decide +kernel

private theorem rowCheck_009 :
    LightCeilFast209.checkFast 6396 6336 27856 60 128 332429438 = true := by decide +kernel

private theorem rowCheck_010 :
    LightCeilFast209.checkFast 21502 21484 86044 18 128 94323282 = true := by decide +kernel

private theorem rowCheck_011 :
    LightCeilFast209.checkFast 64554 64548 225948 6 128 29459326 = true := by decide +kernel

private theorem rowCheck_012 :
    LightCeilFast209.checkFast 161397 161394 436850 3 128 10316764 = true := by decide +kernel

private theorem rowCheck_013 :
    LightCeilFast209.checkFast 153 76 614 116 128 27004910020 = true := by decide +kernel

private theorem rowCheck_014 :
    LightCeilFast209.checkFast 462 386 2000 76 128 5426045183 = true := by decide +kernel

private theorem rowCheck_015 :
    LightCeilFast209.checkFast 1538 1462 6842 76 128 1454395420 = true := by decide +kernel

private theorem rowCheck_016 :
    LightCeilFast209.checkFast 5304 5228 21368 76 128 388834418 = true := by decide +kernel

private theorem rowCheck_017 :
    LightCeilFast209.checkFast 16109 16078 64498 31 128 126070508 = true := by decide +kernel

private theorem rowCheck_018 :
    LightCeilFast209.checkFast 48409 48398 182898 11 128 40756664 = true := by decide +kernel

private theorem rowCheck_019 :
    LightCeilFast209.checkFast 134496 134492 409948 4 128 13188950 = true := by decide +kernel

private theorem rowCheck_020 :
    LightCeilFast209.checkFast 139 69 607 130 128 32073168821 = true := by decide +kernel

private theorem rowCheck_021 :
    LightCeilFast209.checkFast 456 374 1988 82 128 5614678472 = true := by decide +kernel

private theorem rowCheck_022 :
    LightCeilFast209.checkFast 1532 1450 6830 82 128 1467804901 = true := by decide +kernel

private theorem rowCheck_023 :
    LightCeilFast209.checkFast 5298 5216 21356 82 128 389831847 = true := by decide +kernel

private theorem rowCheck_024 :
    LightCeilFast209.checkFast 16103 16066 64486 37 128 126175777 = true := by decide +kernel

private theorem rowCheck_025 :
    LightCeilFast209.checkFast 48407 48394 182894 13 128 40760404 = true := by decide +kernel

private theorem rowCheck_026 :
    LightCeilFast209.checkFast 134495 134490 409946 5 128 13189162 = true := by decide +kernel

private theorem rowCheck_027 :
    LightCeilFast209.checkFast 126 63 574 143 128 37172670916 = true := by decide +kernel

private theorem rowCheck_028 :
    LightCeilFast209.checkFast 421 331 1810 90 128 6292233476 = true := by decide +kernel

private theorem rowCheck_029 :
    LightCeilFast209.checkFast 1391 1303 5876 88 128 1593976085 = true := by decide +kernel

private theorem rowCheck_030 :
    LightCeilFast209.checkFast 4485 4397 17309 88 128 453102390 = true := by decide +kernel

private theorem rowCheck_031 :
    LightCeilFast209.checkFast 12858 12804 47774 54 128 152836235 = true := by decide +kernel

private theorem rowCheck_032 :
    LightCeilFast209.checkFast 34950 34930 131770 20 128 56415024 = true := by decide +kernel

private theorem rowCheck_033 :
    LightCeilFast209.checkFast 96832 96824 372280 8 128 20540634 = true := by decide +kernel

private theorem rowCheck_034 :
    LightCeilFast209.checkFast 117 58 569 152 128 42767799796 = true := by decide +kernel

private theorem rowCheck_035 :
    LightCeilFast209.checkFast 416 321 1800 95 128 6502322716 = true := by decide +kernel

private theorem rowCheck_036 :
    LightCeilFast209.checkFast 1387 1295 5868 92 128 1604865805 = true := by decide +kernel

private theorem rowCheck_037 :
    LightCeilFast209.checkFast 4481 4389 17301 92 128 454017905 = true := by decide +kernel

private theorem rowCheck_038 :
    LightCeilFast209.checkFast 12853 12794 47764 59 128 152968478 = true := by decide +kernel

private theorem rowCheck_039 :
    LightCeilFast209.checkFast 34948 34926 131766 22 128 56422196 = true := by decide +kernel

private theorem rowCheck_040 :
    LightCeilFast209.checkFast 108 54 565 161 128 49101562365 = true := by decide +kernel

private theorem rowCheck_041 :
    LightCeilFast209.checkFast 410 309 1788 101 128 6772211309 = true := by decide +kernel

private theorem rowCheck_042 :
    LightCeilFast209.checkFast 1383 1287 5860 96 128 1615891488 = true := by decide +kernel

private theorem rowCheck_043 :
    LightCeilFast209.checkFast 4477 4381 17293 96 128 454936807 = true := by decide +kernel

private theorem rowCheck_044 :
    LightCeilFast209.checkFast 12847 12782 47752 65 128 153127447 = true := by decide +kernel

private theorem rowCheck_045 :
    LightCeilFast209.checkFast 34946 34922 131762 24 128 56429369 = true := by decide +kernel

private theorem rowCheck_046 :
    LightCeilFast209.checkFast 96831 96822 372278 9 128 20541106 = true := by decide +kernel

private theorem rowCheck_047 :
    LightCeilFast209.checkFast 101 50 561 168 128 55862049924 = true := by decide +kernel

private theorem rowCheck_048 :
    LightCeilFast209.checkFast 406 301 1780 105 128 6963936644 = true := by decide +kernel

private theorem rowCheck_049 :
    LightCeilFast209.checkFast 1380 1281 5854 99 128 1624251505 = true := by decide +kernel

private theorem rowCheck_050 :
    LightCeilFast209.checkFast 4474 4375 17287 99 128 455628220 = true := by decide +kernel

private theorem rowCheck_051 :
    LightCeilFast209.checkFast 12842 12772 47742 70 128 153260151 = true := by decide +kernel

private theorem rowCheck_052 :
    LightCeilFast209.checkFast 34944 34918 131758 26 128 56436544 = true := by decide +kernel

private theorem rowCheck_053 :
    LightCeilFast209.checkFast 96830 96820 372276 10 128 20541578 = true := by decide +kernel

private theorem rowCheck_054 :
    LightCeilFast209.checkFast 95 47 558 174 128 62456836107 = true := by decide +kernel

private theorem rowCheck_055 :
    LightCeilFast209.checkFast 403 295 1774 108 128 7114470724 = true := by decide +kernel

private theorem rowCheck_056 :
    LightCeilFast209.checkFast 1378 1277 5850 101 128 1629868674 = true := by decide +kernel

private theorem rowCheck_057 :
    LightCeilFast209.checkFast 4472 4371 17283 101 128 456090230 = true := by decide +kernel

private theorem rowCheck_058 :
    LightCeilFast209.checkFast 12838 12764 47734 74 128 153366466 = true := by decide +kernel

private theorem rowCheck_059 :
    LightCeilFast209.checkFast 34942 34914 131754 28 128 56443721 = true := by decide +kernel

private theorem rowCheck_060 :
    LightCeilFast209.checkFast 88 44 555 181 128 71186809567 = true := by decide +kernel

private theorem rowCheck_061 :
    LightCeilFast209.checkFast 399 287 1766 112 128 7324858907 = true := by decide +kernel

private theorem rowCheck_062 :
    LightCeilFast209.checkFast 1375 1271 5844 104 128 1638360991 = true := by decide +kernel

private theorem rowCheck_063 :
    LightCeilFast209.checkFast 4469 4365 17277 104 128 456784854 = true := by decide +kernel

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
end JSP233.LightValues209_007
