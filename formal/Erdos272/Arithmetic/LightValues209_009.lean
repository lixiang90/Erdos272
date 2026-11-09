module

public import Erdos272.Certificates.LightCeilFast209

@[expose] public section
namespace JSP233.LightValues209_009
open LightAnalytic209 ResidualCeil208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
  (422,307,1863,115,6843442071),
  (1449,1342,6153,107,1551094075),
  (4704,4597,18181,107,433682835),
  (13504,13424,50214,80,145831080),
  (36760,36730,138610,30,53653212),
  (101869,101858,391650,11,19525592),
  (85,42,579,198,79741665270),
  (415,293,1849,122,7190017233),
  (1444,1332,6143,112,1563945765),
  (4699,4587,18171,112,434730371),
  (13495,13406,50196,89,146047777),
  (36757,36724,138604,33,53662942),
  (101868,101856,391648,12,19526019),
  (76,38,547,207,94979072289),
  (377,245,1603,132,8368863733),
  (1242,1126,5088,116,1817548788),
  (3846,3730,15050,116,537589901),
  (11204,11088,45048,116,183167471),
  (33921,33882,135762,39,59813207),
  (101867,101854,391646,13,19526445),
  (68,34,543,215,116499297043),
  (372,235,1593,137,8739474591),
  (1238,1118,5080,120,1831794439),
  (3842,3722,15042,120,538870072),
  (11200,11080,45040,120,183315053),
  (33919,33878,135758,41,59821103),
  (101866,101852,391644,14,19526872),
  (218,130,864,88,15142569791),
  (670,606,3054,64,3545229499),
  (2384,2320,11500,64,949684907),
  (9144,9108,39708,36,230945339),
  (30589,30578,122378,11,66263738),
  (91796,91792,305992,4,20224391),
  (214198,214196,527540,2,7378004),
  (174,87,699,132,23633658942),
  (527,442,2278,85,4735965075),
  (1751,1666,7786,85,1276051938),
  (6035,5950,24310,85,341632283),
  (18325,18290,73370,35,110823113),
  (55068,55056,208056,12,35827829),
  (152995,152990,466334,5,11594281),
  (143,71,652,163,32981989156),
  (478,375,2058,103,5557135607),
  (1585,1487,6689,98,1396144888),
  (5104,5006,19694,98,397944342),
  (14627,14566,54346,61,134347306),
  (39757,39734,149894,23,49594290),
  (110151,110142,423486,9,18056926),
  (123,61,642,183,43333727284),
  (467,353,2036,114,5928140146),
  (1576,1469,6671,107,1415069186),
  (5095,4988,19676,107,399536378),
  (14614,14540,54320,74,134613256),
  (39752,39724,149884,28,49608148),
  (110150,110140,423484,10,18057291),
  (105,52,633,201,57794488497),
  (457,333,2016,124,6307425784),
  (1568,1453,6655,115,1432286082),
  (5087,4972,19660,115,400961329),
  (14601,14514,54294,87,134880168),
  (39748,39716,149876,32,49619239),
  (110148,110136,423480,12,18058021),
  (93,46,627,213,72137961387),
  (450,319,2002,131,6600887068)
]
def checks : Bool := data.all (fun a=>LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)
private theorem rowCheck_000 :
    LightCeilFast209.checkFast 422 307 1863 115 128 6843442071 = true := by decide +kernel

private theorem rowCheck_001 :
    LightCeilFast209.checkFast 1449 1342 6153 107 128 1551094075 = true := by decide +kernel

private theorem rowCheck_002 :
    LightCeilFast209.checkFast 4704 4597 18181 107 128 433682835 = true := by decide +kernel

private theorem rowCheck_003 :
    LightCeilFast209.checkFast 13504 13424 50214 80 128 145831080 = true := by decide +kernel

private theorem rowCheck_004 :
    LightCeilFast209.checkFast 36760 36730 138610 30 128 53653212 = true := by decide +kernel

private theorem rowCheck_005 :
    LightCeilFast209.checkFast 101869 101858 391650 11 128 19525592 = true := by decide +kernel

private theorem rowCheck_006 :
    LightCeilFast209.checkFast 85 42 579 198 128 79741665270 = true := by decide +kernel

private theorem rowCheck_007 :
    LightCeilFast209.checkFast 415 293 1849 122 128 7190017233 = true := by decide +kernel

private theorem rowCheck_008 :
    LightCeilFast209.checkFast 1444 1332 6143 112 128 1563945765 = true := by decide +kernel

private theorem rowCheck_009 :
    LightCeilFast209.checkFast 4699 4587 18171 112 128 434730371 = true := by decide +kernel

private theorem rowCheck_010 :
    LightCeilFast209.checkFast 13495 13406 50196 89 128 146047777 = true := by decide +kernel

private theorem rowCheck_011 :
    LightCeilFast209.checkFast 36757 36724 138604 33 128 53662942 = true := by decide +kernel

private theorem rowCheck_012 :
    LightCeilFast209.checkFast 101868 101856 391648 12 128 19526019 = true := by decide +kernel

private theorem rowCheck_013 :
    LightCeilFast209.checkFast 76 38 547 207 128 94979072289 = true := by decide +kernel

private theorem rowCheck_014 :
    LightCeilFast209.checkFast 377 245 1603 132 128 8368863733 = true := by decide +kernel

private theorem rowCheck_015 :
    LightCeilFast209.checkFast 1242 1126 5088 116 128 1817548788 = true := by decide +kernel

private theorem rowCheck_016 :
    LightCeilFast209.checkFast 3846 3730 15050 116 128 537589901 = true := by decide +kernel

private theorem rowCheck_017 :
    LightCeilFast209.checkFast 11204 11088 45048 116 128 183167471 = true := by decide +kernel

private theorem rowCheck_018 :
    LightCeilFast209.checkFast 33921 33882 135762 39 128 59813207 = true := by decide +kernel

private theorem rowCheck_019 :
    LightCeilFast209.checkFast 101867 101854 391646 13 128 19526445 = true := by decide +kernel

private theorem rowCheck_020 :
    LightCeilFast209.checkFast 68 34 543 215 128 116499297043 = true := by decide +kernel

private theorem rowCheck_021 :
    LightCeilFast209.checkFast 372 235 1593 137 128 8739474591 = true := by decide +kernel

private theorem rowCheck_022 :
    LightCeilFast209.checkFast 1238 1118 5080 120 128 1831794439 = true := by decide +kernel

private theorem rowCheck_023 :
    LightCeilFast209.checkFast 3842 3722 15042 120 128 538870072 = true := by decide +kernel

private theorem rowCheck_024 :
    LightCeilFast209.checkFast 11200 11080 45040 120 128 183315053 = true := by decide +kernel

private theorem rowCheck_025 :
    LightCeilFast209.checkFast 33919 33878 135758 41 128 59821103 = true := by decide +kernel

private theorem rowCheck_026 :
    LightCeilFast209.checkFast 101866 101852 391644 14 128 19526872 = true := by decide +kernel

private theorem rowCheck_027 :
    LightCeilFast209.checkFast 218 130 864 88 128 15142569791 = true := by decide +kernel

private theorem rowCheck_028 :
    LightCeilFast209.checkFast 670 606 3054 64 128 3545229499 = true := by decide +kernel

private theorem rowCheck_029 :
    LightCeilFast209.checkFast 2384 2320 11500 64 128 949684907 = true := by decide +kernel

private theorem rowCheck_030 :
    LightCeilFast209.checkFast 9144 9108 39708 36 128 230945339 = true := by decide +kernel

private theorem rowCheck_031 :
    LightCeilFast209.checkFast 30589 30578 122378 11 128 66263738 = true := by decide +kernel

private theorem rowCheck_032 :
    LightCeilFast209.checkFast 91796 91792 305992 4 128 20224391 = true := by decide +kernel

private theorem rowCheck_033 :
    LightCeilFast209.checkFast 214198 214196 527540 2 128 7378004 = true := by decide +kernel

private theorem rowCheck_034 :
    LightCeilFast209.checkFast 174 87 699 132 128 23633658942 = true := by decide +kernel

private theorem rowCheck_035 :
    LightCeilFast209.checkFast 527 442 2278 85 128 4735965075 = true := by decide +kernel

private theorem rowCheck_036 :
    LightCeilFast209.checkFast 1751 1666 7786 85 128 1276051938 = true := by decide +kernel

private theorem rowCheck_037 :
    LightCeilFast209.checkFast 6035 5950 24310 85 128 341632283 = true := by decide +kernel

private theorem rowCheck_038 :
    LightCeilFast209.checkFast 18325 18290 73370 35 128 110823113 = true := by decide +kernel

private theorem rowCheck_039 :
    LightCeilFast209.checkFast 55068 55056 208056 12 128 35827829 = true := by decide +kernel

private theorem rowCheck_040 :
    LightCeilFast209.checkFast 152995 152990 466334 5 128 11594281 = true := by decide +kernel

private theorem rowCheck_041 :
    LightCeilFast209.checkFast 143 71 652 163 128 32981989156 = true := by decide +kernel

private theorem rowCheck_042 :
    LightCeilFast209.checkFast 478 375 2058 103 128 5557135607 = true := by decide +kernel

private theorem rowCheck_043 :
    LightCeilFast209.checkFast 1585 1487 6689 98 128 1396144888 = true := by decide +kernel

private theorem rowCheck_044 :
    LightCeilFast209.checkFast 5104 5006 19694 98 128 397944342 = true := by decide +kernel

private theorem rowCheck_045 :
    LightCeilFast209.checkFast 14627 14566 54346 61 128 134347306 = true := by decide +kernel

private theorem rowCheck_046 :
    LightCeilFast209.checkFast 39757 39734 149894 23 128 49594290 = true := by decide +kernel

private theorem rowCheck_047 :
    LightCeilFast209.checkFast 110151 110142 423486 9 128 18056926 = true := by decide +kernel

private theorem rowCheck_048 :
    LightCeilFast209.checkFast 123 61 642 183 128 43333727284 = true := by decide +kernel

private theorem rowCheck_049 :
    LightCeilFast209.checkFast 467 353 2036 114 128 5928140146 = true := by decide +kernel

private theorem rowCheck_050 :
    LightCeilFast209.checkFast 1576 1469 6671 107 128 1415069186 = true := by decide +kernel

private theorem rowCheck_051 :
    LightCeilFast209.checkFast 5095 4988 19676 107 128 399536378 = true := by decide +kernel

private theorem rowCheck_052 :
    LightCeilFast209.checkFast 14614 14540 54320 74 128 134613256 = true := by decide +kernel

private theorem rowCheck_053 :
    LightCeilFast209.checkFast 39752 39724 149884 28 128 49608148 = true := by decide +kernel

private theorem rowCheck_054 :
    LightCeilFast209.checkFast 110150 110140 423484 10 128 18057291 = true := by decide +kernel

private theorem rowCheck_055 :
    LightCeilFast209.checkFast 105 52 633 201 128 57794488497 = true := by decide +kernel

private theorem rowCheck_056 :
    LightCeilFast209.checkFast 457 333 2016 124 128 6307425784 = true := by decide +kernel

private theorem rowCheck_057 :
    LightCeilFast209.checkFast 1568 1453 6655 115 128 1432286082 = true := by decide +kernel

private theorem rowCheck_058 :
    LightCeilFast209.checkFast 5087 4972 19660 115 128 400961329 = true := by decide +kernel

private theorem rowCheck_059 :
    LightCeilFast209.checkFast 14601 14514 54294 87 128 134880168 = true := by decide +kernel

private theorem rowCheck_060 :
    LightCeilFast209.checkFast 39748 39716 149876 32 128 49619239 = true := by decide +kernel

private theorem rowCheck_061 :
    LightCeilFast209.checkFast 110148 110136 423480 12 128 18058021 = true := by decide +kernel

private theorem rowCheck_062 :
    LightCeilFast209.checkFast 93 46 627 213 128 72137961387 = true := by decide +kernel

private theorem rowCheck_063 :
    LightCeilFast209.checkFast 450 319 2002 131 128 6600887068 = true := by decide +kernel

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
end JSP233.LightValues209_009
