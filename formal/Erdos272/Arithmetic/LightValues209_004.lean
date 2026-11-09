module

public import Erdos272.Certificates.LightCeilFast209

@[expose] public section
namespace JSP233.LightValues209_004
open LightAnalytic209 ResidualCeil208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
  (1445,1366,6446,79,1558470225),
  (5001,4922,20162,79,413147474),
  (15205,15170,60890,35,133628347),
  (45708,45696,172696,12,43166938),
  (126995,126990,387086,5,13968115),
  (119,59,541,135,39586200839),
  (396,310,1707,86,6725479101),
  (1313,1229,5547,84,1690004249),
  (4234,4150,16342,84,480092931),
  (12141,12090,45110,51,161862327),
  (33001,32982,124422,19,59747083),
  (91433,91426,351522,7,21753370),
  (110,55,537,144,45329012424),
  (391,300,1697,91,6965636732),
  (1309,1221,5539,88,1702247818),
  (4230,4142,16334,88,481120793),
  (12136,12080,45100,56,162010659),
  (32999,32978,124418,21,59755127),
  (91432,91424,351520,8,21753900),
  (102,51,533,152,51957315012),
  (387,292,1689,95,7169470100),
  (1306,1215,5533,91,1711536753),
  (4227,4136,16328,91,481894334),
  (12130,12068,45088,62,162188985),
  (32997,32974,124414,23,59763173),
  (91431,91422,351518,9,21754429),
  (95,47,529,159,59579914995),
  (383,284,1681,99,7384639807),
  (1303,1209,5527,94,1720918270),
  (4224,4130,16322,94,482670152),
  (12125,12058,45078,67,162337864),
  (32995,32970,124410,25,59771221),
  (89,44,526,165,67104698894),
  (379,276,1673,103,7612130744),
  (1300,1203,5521,97,1730393751),
  (4221,4124,16316,97,483448258),
  (12121,12050,45070,71,162457147),
  (32994,32968,124408,26,59775246),
  (91430,91420,351516,10,21754959),
  (83,41,523,171,76226870561),
  (376,270,1667,106,7791494192),
  (1298,1199,5517,99,1736763637),
  (4219,4120,16312,99,483968272),
  (12117,12042,45062,75,162576590),
  (32992,32964,124404,28,59783297),
  (76,38,520,178,88644232658),
  (372,262,1659,110,8043287628),
  (1295,1193,5511,102,1746398874),
  (4216,4114,16306,102,484750213),
  (12112,12032,45052,80,162726119),
  (32990,32960,124400,30,59791350),
  (91429,91418,351514,11,21755489),
  (72,36,493,182,95854285321),
  (341,225,1444,116,9103300044),
  (1115,1011,4567,104,2024148647),
  (3452,3348,13508,104,598923452),
  (10060,9960,40440,100,203892201),
  (30446,30412,121852,34,66637356),
  (91428,91416,351512,12,21756018),
  (68,34,491,186,106443232564),
  (338,219,1438,119,9363290065),
  (1113,1007,4563,106,2032955671),
  (3450,3344,13504,106,599717167),
  (10056,9952,40432,104,204075118)
]
def checks : Bool := data.all (fun a=>LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)
private theorem rowCheck_000 :
    LightCeilFast209.checkFast 1445 1366 6446 79 128 1558470225 = true := by decide +kernel

private theorem rowCheck_001 :
    LightCeilFast209.checkFast 5001 4922 20162 79 128 413147474 = true := by decide +kernel

private theorem rowCheck_002 :
    LightCeilFast209.checkFast 15205 15170 60890 35 128 133628347 = true := by decide +kernel

private theorem rowCheck_003 :
    LightCeilFast209.checkFast 45708 45696 172696 12 128 43166938 = true := by decide +kernel

private theorem rowCheck_004 :
    LightCeilFast209.checkFast 126995 126990 387086 5 128 13968115 = true := by decide +kernel

private theorem rowCheck_005 :
    LightCeilFast209.checkFast 119 59 541 135 128 39586200839 = true := by decide +kernel

private theorem rowCheck_006 :
    LightCeilFast209.checkFast 396 310 1707 86 128 6725479101 = true := by decide +kernel

private theorem rowCheck_007 :
    LightCeilFast209.checkFast 1313 1229 5547 84 128 1690004249 = true := by decide +kernel

private theorem rowCheck_008 :
    LightCeilFast209.checkFast 4234 4150 16342 84 128 480092931 = true := by decide +kernel

private theorem rowCheck_009 :
    LightCeilFast209.checkFast 12141 12090 45110 51 128 161862327 = true := by decide +kernel

private theorem rowCheck_010 :
    LightCeilFast209.checkFast 33001 32982 124422 19 128 59747083 = true := by decide +kernel

private theorem rowCheck_011 :
    LightCeilFast209.checkFast 91433 91426 351522 7 128 21753370 = true := by decide +kernel

private theorem rowCheck_012 :
    LightCeilFast209.checkFast 110 55 537 144 128 45329012424 = true := by decide +kernel

private theorem rowCheck_013 :
    LightCeilFast209.checkFast 391 300 1697 91 128 6965636732 = true := by decide +kernel

private theorem rowCheck_014 :
    LightCeilFast209.checkFast 1309 1221 5539 88 128 1702247818 = true := by decide +kernel

private theorem rowCheck_015 :
    LightCeilFast209.checkFast 4230 4142 16334 88 128 481120793 = true := by decide +kernel

private theorem rowCheck_016 :
    LightCeilFast209.checkFast 12136 12080 45100 56 128 162010659 = true := by decide +kernel

private theorem rowCheck_017 :
    LightCeilFast209.checkFast 32999 32978 124418 21 128 59755127 = true := by decide +kernel

private theorem rowCheck_018 :
    LightCeilFast209.checkFast 91432 91424 351520 8 128 21753900 = true := by decide +kernel

private theorem rowCheck_019 :
    LightCeilFast209.checkFast 102 51 533 152 128 51957315012 = true := by decide +kernel

private theorem rowCheck_020 :
    LightCeilFast209.checkFast 387 292 1689 95 128 7169470100 = true := by decide +kernel

private theorem rowCheck_021 :
    LightCeilFast209.checkFast 1306 1215 5533 91 128 1711536753 = true := by decide +kernel

private theorem rowCheck_022 :
    LightCeilFast209.checkFast 4227 4136 16328 91 128 481894334 = true := by decide +kernel

private theorem rowCheck_023 :
    LightCeilFast209.checkFast 12130 12068 45088 62 128 162188985 = true := by decide +kernel

private theorem rowCheck_024 :
    LightCeilFast209.checkFast 32997 32974 124414 23 128 59763173 = true := by decide +kernel

private theorem rowCheck_025 :
    LightCeilFast209.checkFast 91431 91422 351518 9 128 21754429 = true := by decide +kernel

private theorem rowCheck_026 :
    LightCeilFast209.checkFast 95 47 529 159 128 59579914995 = true := by decide +kernel

private theorem rowCheck_027 :
    LightCeilFast209.checkFast 383 284 1681 99 128 7384639807 = true := by decide +kernel

private theorem rowCheck_028 :
    LightCeilFast209.checkFast 1303 1209 5527 94 128 1720918270 = true := by decide +kernel

private theorem rowCheck_029 :
    LightCeilFast209.checkFast 4224 4130 16322 94 128 482670152 = true := by decide +kernel

private theorem rowCheck_030 :
    LightCeilFast209.checkFast 12125 12058 45078 67 128 162337864 = true := by decide +kernel

private theorem rowCheck_031 :
    LightCeilFast209.checkFast 32995 32970 124410 25 128 59771221 = true := by decide +kernel

private theorem rowCheck_032 :
    LightCeilFast209.checkFast 89 44 526 165 128 67104698894 = true := by decide +kernel

private theorem rowCheck_033 :
    LightCeilFast209.checkFast 379 276 1673 103 128 7612130744 = true := by decide +kernel

private theorem rowCheck_034 :
    LightCeilFast209.checkFast 1300 1203 5521 97 128 1730393751 = true := by decide +kernel

private theorem rowCheck_035 :
    LightCeilFast209.checkFast 4221 4124 16316 97 128 483448258 = true := by decide +kernel

private theorem rowCheck_036 :
    LightCeilFast209.checkFast 12121 12050 45070 71 128 162457147 = true := by decide +kernel

private theorem rowCheck_037 :
    LightCeilFast209.checkFast 32994 32968 124408 26 128 59775246 = true := by decide +kernel

private theorem rowCheck_038 :
    LightCeilFast209.checkFast 91430 91420 351516 10 128 21754959 = true := by decide +kernel

private theorem rowCheck_039 :
    LightCeilFast209.checkFast 83 41 523 171 128 76226870561 = true := by decide +kernel

private theorem rowCheck_040 :
    LightCeilFast209.checkFast 376 270 1667 106 128 7791494192 = true := by decide +kernel

private theorem rowCheck_041 :
    LightCeilFast209.checkFast 1298 1199 5517 99 128 1736763637 = true := by decide +kernel

private theorem rowCheck_042 :
    LightCeilFast209.checkFast 4219 4120 16312 99 128 483968272 = true := by decide +kernel

private theorem rowCheck_043 :
    LightCeilFast209.checkFast 12117 12042 45062 75 128 162576590 = true := by decide +kernel

private theorem rowCheck_044 :
    LightCeilFast209.checkFast 32992 32964 124404 28 128 59783297 = true := by decide +kernel

private theorem rowCheck_045 :
    LightCeilFast209.checkFast 76 38 520 178 128 88644232658 = true := by decide +kernel

private theorem rowCheck_046 :
    LightCeilFast209.checkFast 372 262 1659 110 128 8043287628 = true := by decide +kernel

private theorem rowCheck_047 :
    LightCeilFast209.checkFast 1295 1193 5511 102 128 1746398874 = true := by decide +kernel

private theorem rowCheck_048 :
    LightCeilFast209.checkFast 4216 4114 16306 102 128 484750213 = true := by decide +kernel

private theorem rowCheck_049 :
    LightCeilFast209.checkFast 12112 12032 45052 80 128 162726119 = true := by decide +kernel

private theorem rowCheck_050 :
    LightCeilFast209.checkFast 32990 32960 124400 30 128 59791350 = true := by decide +kernel

private theorem rowCheck_051 :
    LightCeilFast209.checkFast 91429 91418 351514 11 128 21755489 = true := by decide +kernel

private theorem rowCheck_052 :
    LightCeilFast209.checkFast 72 36 493 182 128 95854285321 = true := by decide +kernel

private theorem rowCheck_053 :
    LightCeilFast209.checkFast 341 225 1444 116 128 9103300044 = true := by decide +kernel

private theorem rowCheck_054 :
    LightCeilFast209.checkFast 1115 1011 4567 104 128 2024148647 = true := by decide +kernel

private theorem rowCheck_055 :
    LightCeilFast209.checkFast 3452 3348 13508 104 128 598923452 = true := by decide +kernel

private theorem rowCheck_056 :
    LightCeilFast209.checkFast 10060 9960 40440 100 128 203892201 = true := by decide +kernel

private theorem rowCheck_057 :
    LightCeilFast209.checkFast 30446 30412 121852 34 128 66637356 = true := by decide +kernel

private theorem rowCheck_058 :
    LightCeilFast209.checkFast 91428 91416 351512 12 128 21756018 = true := by decide +kernel

private theorem rowCheck_059 :
    LightCeilFast209.checkFast 68 34 491 186 128 106443232564 = true := by decide +kernel

private theorem rowCheck_060 :
    LightCeilFast209.checkFast 338 219 1438 119 128 9363290065 = true := by decide +kernel

private theorem rowCheck_061 :
    LightCeilFast209.checkFast 1113 1007 4563 106 128 2032955671 = true := by decide +kernel

private theorem rowCheck_062 :
    LightCeilFast209.checkFast 3450 3344 13504 106 128 599717167 = true := by decide +kernel

private theorem rowCheck_063 :
    LightCeilFast209.checkFast 10056 9952 40432 104 128 204075118 = true := by decide +kernel

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
end JSP233.LightValues209_004
