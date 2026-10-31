import Erdos272.Certificates.LightCeilFast209
namespace JSP233.LightValues209_013
open LightAnalytic209 ResidualCeil208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
  (237590,237580,791980,10,7813944),
  (554396,554392,2654631,4,3960389),
  (450,225,1809,342,9143964721),
  (1369,1154,5906,215,1812616470),
  (4551,4350,20190,201,488221986),
  (15639,15438,62958,201,131632020),
  (47429,47338,189898,91,42818854),
  (142529,142498,538498,31,13842558),
  (395989,395978,2496217,11,6207785),
  (371,185,1689,421,12647889569),
  (1240,976,5332,264,2134213850),
  (4122,3888,17352,234,533389522),
  (13230,12996,51012,234,153235897),
  (37859,37702,140662,157,51904224),
  (102902,102844,387964,58,19160798),
  (285099,285078,2385317,21,9581557),
  (319,159,1663,473,16618150762),
  (1211,918,5274,293,2278724925),
  (4099,3842,17306,257,540461080),
  (13207,12950,50966,257,153839485),
  (37825,37634,140594,191,52008048),
  (102889,102818,387938,71,19166176),
  (285094,285068,2385307,26,9581944),
  (273,136,1640,519,22046937414),
  (1185,866,5222,319,2424544541),
  (4079,3802,17266,277,546749968),
  (13187,12910,50926,277,154367887),
  (37793,37570,140530,223,52106111),
  (102878,102796,387916,82,19170729),
  (285090,285060,2385299,30,9582254),
  (240,120,1624,552,27787535322),
  (1166,828,5184,338,2542548374),
  (4066,3776,17240,290,550909499),
  (13174,12884,50900,290,154713132),
  (37768,37520,140480,248,52182958),
  (102869,102778,387898,91,19174456),
  (285087,285054,2385293,33,9582486),
  (213,106,1531,579,33977063230),
  (1058,691,4492,367,2966064390),
  (3499,3197,14285,302,639239965),
  (10786,10484,42164,302,191174438),
  (31378,31076,126116,302,65343592),
  (94933,94826,379946,107,21371568),
  (285084,285048,2385287,36,9582718),
  (191,95,1520,601,41524470636),
  (1044,663,4464,381,3096486034),
  (3490,3179,14267,311,643210028),
  (10777,10466,42146,311,191538833),
  (31369,31058,126098,311,65385860),
  (94926,94812,379932,114,21375096),
  (285082,285044,2385283,38,9582873),
  (1021,610,4046,411,3227323949),
  (3181,2926,14382,255,731753489),
  (11201,10946,53906,255,201076218),
  (42794,42628,185828,166,49343624),
  (143150,143100,572700,50,14159383),
  (429583,429566,1431966,17,4321655),
  (1002392,1002384,6679062,8,2505436),
  (813,406,3270,619,5069025639),
  (2477,2090,10682,387,1000700501),
  (8239,7886,36526,353,269226222),
  (28287,27934,113854,353,72741465),
  (85755,85590,343350,165,23682224),
  (257705,257650,973650,55,7655871)
]
def checks : Bool := data.all (fun a=>LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)
private theorem rowCheck_000 :
    LightCeilFast209.checkFast 237590 237580 791980 10 128 7813944 = true := by decide +kernel

private theorem rowCheck_001 :
    LightCeilFast209.checkFast 554396 554392 2654631 4 128 3960389 = true := by decide +kernel

private theorem rowCheck_002 :
    LightCeilFast209.checkFast 450 225 1809 342 128 9143964721 = true := by decide +kernel

private theorem rowCheck_003 :
    LightCeilFast209.checkFast 1369 1154 5906 215 128 1812616470 = true := by decide +kernel

private theorem rowCheck_004 :
    LightCeilFast209.checkFast 4551 4350 20190 201 128 488221986 = true := by decide +kernel

private theorem rowCheck_005 :
    LightCeilFast209.checkFast 15639 15438 62958 201 128 131632020 = true := by decide +kernel

private theorem rowCheck_006 :
    LightCeilFast209.checkFast 47429 47338 189898 91 128 42818854 = true := by decide +kernel

private theorem rowCheck_007 :
    LightCeilFast209.checkFast 142529 142498 538498 31 128 13842558 = true := by decide +kernel

private theorem rowCheck_008 :
    LightCeilFast209.checkFast 395989 395978 2496217 11 128 6207785 = true := by decide +kernel

private theorem rowCheck_009 :
    LightCeilFast209.checkFast 371 185 1689 421 128 12647889569 = true := by decide +kernel

private theorem rowCheck_010 :
    LightCeilFast209.checkFast 1240 976 5332 264 128 2134213850 = true := by decide +kernel

private theorem rowCheck_011 :
    LightCeilFast209.checkFast 4122 3888 17352 234 128 533389522 = true := by decide +kernel

private theorem rowCheck_012 :
    LightCeilFast209.checkFast 13230 12996 51012 234 128 153235897 = true := by decide +kernel

private theorem rowCheck_013 :
    LightCeilFast209.checkFast 37859 37702 140662 157 128 51904224 = true := by decide +kernel

private theorem rowCheck_014 :
    LightCeilFast209.checkFast 102902 102844 387964 58 128 19160798 = true := by decide +kernel

private theorem rowCheck_015 :
    LightCeilFast209.checkFast 285099 285078 2385317 21 128 9581557 = true := by decide +kernel

private theorem rowCheck_016 :
    LightCeilFast209.checkFast 319 159 1663 473 128 16618150762 = true := by decide +kernel

private theorem rowCheck_017 :
    LightCeilFast209.checkFast 1211 918 5274 293 128 2278724925 = true := by decide +kernel

private theorem rowCheck_018 :
    LightCeilFast209.checkFast 4099 3842 17306 257 128 540461080 = true := by decide +kernel

private theorem rowCheck_019 :
    LightCeilFast209.checkFast 13207 12950 50966 257 128 153839485 = true := by decide +kernel

private theorem rowCheck_020 :
    LightCeilFast209.checkFast 37825 37634 140594 191 128 52008048 = true := by decide +kernel

private theorem rowCheck_021 :
    LightCeilFast209.checkFast 102889 102818 387938 71 128 19166176 = true := by decide +kernel

private theorem rowCheck_022 :
    LightCeilFast209.checkFast 285094 285068 2385307 26 128 9581944 = true := by decide +kernel

private theorem rowCheck_023 :
    LightCeilFast209.checkFast 273 136 1640 519 128 22046937414 = true := by decide +kernel

private theorem rowCheck_024 :
    LightCeilFast209.checkFast 1185 866 5222 319 128 2424544541 = true := by decide +kernel

private theorem rowCheck_025 :
    LightCeilFast209.checkFast 4079 3802 17266 277 128 546749968 = true := by decide +kernel

private theorem rowCheck_026 :
    LightCeilFast209.checkFast 13187 12910 50926 277 128 154367887 = true := by decide +kernel

private theorem rowCheck_027 :
    LightCeilFast209.checkFast 37793 37570 140530 223 128 52106111 = true := by decide +kernel

private theorem rowCheck_028 :
    LightCeilFast209.checkFast 102878 102796 387916 82 128 19170729 = true := by decide +kernel

private theorem rowCheck_029 :
    LightCeilFast209.checkFast 285090 285060 2385299 30 128 9582254 = true := by decide +kernel

private theorem rowCheck_030 :
    LightCeilFast209.checkFast 240 120 1624 552 128 27787535322 = true := by decide +kernel

private theorem rowCheck_031 :
    LightCeilFast209.checkFast 1166 828 5184 338 128 2542548374 = true := by decide +kernel

private theorem rowCheck_032 :
    LightCeilFast209.checkFast 4066 3776 17240 290 128 550909499 = true := by decide +kernel

private theorem rowCheck_033 :
    LightCeilFast209.checkFast 13174 12884 50900 290 128 154713132 = true := by decide +kernel

private theorem rowCheck_034 :
    LightCeilFast209.checkFast 37768 37520 140480 248 128 52182958 = true := by decide +kernel

private theorem rowCheck_035 :
    LightCeilFast209.checkFast 102869 102778 387898 91 128 19174456 = true := by decide +kernel

private theorem rowCheck_036 :
    LightCeilFast209.checkFast 285087 285054 2385293 33 128 9582486 = true := by decide +kernel

private theorem rowCheck_037 :
    LightCeilFast209.checkFast 213 106 1531 579 128 33977063230 = true := by decide +kernel

private theorem rowCheck_038 :
    LightCeilFast209.checkFast 1058 691 4492 367 128 2966064390 = true := by decide +kernel

private theorem rowCheck_039 :
    LightCeilFast209.checkFast 3499 3197 14285 302 128 639239965 = true := by decide +kernel

private theorem rowCheck_040 :
    LightCeilFast209.checkFast 10786 10484 42164 302 128 191174438 = true := by decide +kernel

private theorem rowCheck_041 :
    LightCeilFast209.checkFast 31378 31076 126116 302 128 65343592 = true := by decide +kernel

private theorem rowCheck_042 :
    LightCeilFast209.checkFast 94933 94826 379946 107 128 21371568 = true := by decide +kernel

private theorem rowCheck_043 :
    LightCeilFast209.checkFast 285084 285048 2385287 36 128 9582718 = true := by decide +kernel

private theorem rowCheck_044 :
    LightCeilFast209.checkFast 191 95 1520 601 128 41524470636 = true := by decide +kernel

private theorem rowCheck_045 :
    LightCeilFast209.checkFast 1044 663 4464 381 128 3096486034 = true := by decide +kernel

private theorem rowCheck_046 :
    LightCeilFast209.checkFast 3490 3179 14267 311 128 643210028 = true := by decide +kernel

private theorem rowCheck_047 :
    LightCeilFast209.checkFast 10777 10466 42146 311 128 191538833 = true := by decide +kernel

private theorem rowCheck_048 :
    LightCeilFast209.checkFast 31369 31058 126098 311 128 65385860 = true := by decide +kernel

private theorem rowCheck_049 :
    LightCeilFast209.checkFast 94926 94812 379932 114 128 21375096 = true := by decide +kernel

private theorem rowCheck_050 :
    LightCeilFast209.checkFast 285082 285044 2385283 38 128 9582873 = true := by decide +kernel

private theorem rowCheck_051 :
    LightCeilFast209.checkFast 1021 610 4046 411 128 3227323949 = true := by decide +kernel

private theorem rowCheck_052 :
    LightCeilFast209.checkFast 3181 2926 14382 255 128 731753489 = true := by decide +kernel

private theorem rowCheck_053 :
    LightCeilFast209.checkFast 11201 10946 53906 255 128 201076218 = true := by decide +kernel

private theorem rowCheck_054 :
    LightCeilFast209.checkFast 42794 42628 185828 166 128 49343624 = true := by decide +kernel

private theorem rowCheck_055 :
    LightCeilFast209.checkFast 143150 143100 572700 50 128 14159383 = true := by decide +kernel

private theorem rowCheck_056 :
    LightCeilFast209.checkFast 429583 429566 1431966 17 128 4321655 = true := by decide +kernel

private theorem rowCheck_057 :
    LightCeilFast209.checkFast 1002392 1002384 6679062 8 128 2505436 = true := by decide +kernel

private theorem rowCheck_058 :
    LightCeilFast209.checkFast 813 406 3270 619 128 5069025639 = true := by decide +kernel

private theorem rowCheck_059 :
    LightCeilFast209.checkFast 2477 2090 10682 387 128 1000700501 = true := by decide +kernel

private theorem rowCheck_060 :
    LightCeilFast209.checkFast 8239 7886 36526 353 128 269226222 = true := by decide +kernel

private theorem rowCheck_061 :
    LightCeilFast209.checkFast 28287 27934 113854 353 128 72741465 = true := by decide +kernel

private theorem rowCheck_062 :
    LightCeilFast209.checkFast 85755 85590 343350 165 128 23682224 = true := by decide +kernel

private theorem rowCheck_063 :
    LightCeilFast209.checkFast 257705 257650 973650 55 128 7655871 = true := by decide +kernel

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
end JSP233.LightValues209_013
