module

public import Erdos272.Certificates.LightCeilFast209

@[expose] public section
namespace JSP233.LightValues209_001
open LightAnalytic209 ResidualCeil208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
  (1687,1624,7624,63,1318566597),
  (5947,5894,25894,53,357317740),
  (19984,19968,79968,16,101483569),
  (59994,59988,209988,6,31698727),
  (149997,149994,405994,3,11100871),
  (150,75,625,100,27471282395),
  (482,414,2164,68,5148462373),
  (1682,1614,7614,68,1327704481),
  (5936,5872,25872,64,358820751),
  (19981,19962,79962,19,101517677),
  (59993,59986,209986,7,31699889),
  (142,71,571,108,28984622474),
  (428,356,1856,72,5887040743),
  (1428,1356,6356,72,1568447087),
  (4928,4856,19856,72,418648675),
  (14971,14942,59942,29,135655715),
  (44990,44980,169980,10,43853687),
  (124996,124992,380992,4,14191379),
  (133,66,566,117,32766490758),
  (424,348,1848,76,6033582349),
  (1424,1348,6348,76,1578815070),
  (4924,4848,19848,76,419418911),
  (14967,14934,59934,33,135736954),
  (44989,44978,169978,11,43855852),
  (127,63,563,123,35598292064),
  (422,344,1844,78,6109413634),
  (1422,1344,6344,78,1584045834),
  (4922,4844,19844,78,419804987),
  (14965,14930,59930,35,135777606),
  (44988,44976,169976,12,43858018),
  (124995,124990,380990,5,14191624),
  (121,60,560,129,38835837719),
  (419,338,1838,81,6226532804),
  (1419,1338,6338,81,1591951233),
  (4919,4838,19838,81,420385304),
  (14962,14924,59924,38,135838625),
  (44987,44974,169974,13,43860183),
  (117,58,533,133,40324783705),
  (391,307,1682,84,6785582474),
  (1293,1211,5461,82,1714921103),
  (4168,4086,16086,82,487595208),
  (11950,11900,44400,50,164446101),
  (32481,32462,122462,19,60704279),
  (89993,89986,345986,7,22101484),
  (112,56,556,138,44332666113),
  (415,330,1830,85,6389323197),
  (1415,1330,6330,85,1602603874),
  (4915,4830,19830,85,421161314),
  (14958,14916,59916,42,135920061),
  (44986,44972,169972,14,43862349),
  (124994,124988,380988,6,14191869),
  (108,54,529,142,46285971312),
  (386,297,1672,89,7030409150),
  (1289,1203,5453,86,1727532461),
  (4164,4078,16078,86,488655544),
  (11944,11888,44388,56,164629862),
  (32479,32458,122458,21,60712583),
  (89992,89984,345984,8,22102031),
  (104,52,527,146,49551744734),
  (384,293,1668,91,7132978106),
  (1287,1199,5449,88,1733901518),
  (4162,4074,16074,88,489187295),
  (11942,11884,44384,58,164691199),
  (32478,32456,122456,22,60716735)
]
def checks : Bool := data.all (fun a=>LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)
private theorem rowCheck_000 :
    LightCeilFast209.checkFast 1687 1624 7624 63 128 1318566597 = true := by decide +kernel

private theorem rowCheck_001 :
    LightCeilFast209.checkFast 5947 5894 25894 53 128 357317740 = true := by decide +kernel

private theorem rowCheck_002 :
    LightCeilFast209.checkFast 19984 19968 79968 16 128 101483569 = true := by decide +kernel

private theorem rowCheck_003 :
    LightCeilFast209.checkFast 59994 59988 209988 6 128 31698727 = true := by decide +kernel

private theorem rowCheck_004 :
    LightCeilFast209.checkFast 149997 149994 405994 3 128 11100871 = true := by decide +kernel

private theorem rowCheck_005 :
    LightCeilFast209.checkFast 150 75 625 100 128 27471282395 = true := by decide +kernel

private theorem rowCheck_006 :
    LightCeilFast209.checkFast 482 414 2164 68 128 5148462373 = true := by decide +kernel

private theorem rowCheck_007 :
    LightCeilFast209.checkFast 1682 1614 7614 68 128 1327704481 = true := by decide +kernel

private theorem rowCheck_008 :
    LightCeilFast209.checkFast 5936 5872 25872 64 128 358820751 = true := by decide +kernel

private theorem rowCheck_009 :
    LightCeilFast209.checkFast 19981 19962 79962 19 128 101517677 = true := by decide +kernel

private theorem rowCheck_010 :
    LightCeilFast209.checkFast 59993 59986 209986 7 128 31699889 = true := by decide +kernel

private theorem rowCheck_011 :
    LightCeilFast209.checkFast 142 71 571 108 128 28984622474 = true := by decide +kernel

private theorem rowCheck_012 :
    LightCeilFast209.checkFast 428 356 1856 72 128 5887040743 = true := by decide +kernel

private theorem rowCheck_013 :
    LightCeilFast209.checkFast 1428 1356 6356 72 128 1568447087 = true := by decide +kernel

private theorem rowCheck_014 :
    LightCeilFast209.checkFast 4928 4856 19856 72 128 418648675 = true := by decide +kernel

private theorem rowCheck_015 :
    LightCeilFast209.checkFast 14971 14942 59942 29 128 135655715 = true := by decide +kernel

private theorem rowCheck_016 :
    LightCeilFast209.checkFast 44990 44980 169980 10 128 43853687 = true := by decide +kernel

private theorem rowCheck_017 :
    LightCeilFast209.checkFast 124996 124992 380992 4 128 14191379 = true := by decide +kernel

private theorem rowCheck_018 :
    LightCeilFast209.checkFast 133 66 566 117 128 32766490758 = true := by decide +kernel

private theorem rowCheck_019 :
    LightCeilFast209.checkFast 424 348 1848 76 128 6033582349 = true := by decide +kernel

private theorem rowCheck_020 :
    LightCeilFast209.checkFast 1424 1348 6348 76 128 1578815070 = true := by decide +kernel

private theorem rowCheck_021 :
    LightCeilFast209.checkFast 4924 4848 19848 76 128 419418911 = true := by decide +kernel

private theorem rowCheck_022 :
    LightCeilFast209.checkFast 14967 14934 59934 33 128 135736954 = true := by decide +kernel

private theorem rowCheck_023 :
    LightCeilFast209.checkFast 44989 44978 169978 11 128 43855852 = true := by decide +kernel

private theorem rowCheck_024 :
    LightCeilFast209.checkFast 127 63 563 123 128 35598292064 = true := by decide +kernel

private theorem rowCheck_025 :
    LightCeilFast209.checkFast 422 344 1844 78 128 6109413634 = true := by decide +kernel

private theorem rowCheck_026 :
    LightCeilFast209.checkFast 1422 1344 6344 78 128 1584045834 = true := by decide +kernel

private theorem rowCheck_027 :
    LightCeilFast209.checkFast 4922 4844 19844 78 128 419804987 = true := by decide +kernel

private theorem rowCheck_028 :
    LightCeilFast209.checkFast 14965 14930 59930 35 128 135777606 = true := by decide +kernel

private theorem rowCheck_029 :
    LightCeilFast209.checkFast 44988 44976 169976 12 128 43858018 = true := by decide +kernel

private theorem rowCheck_030 :
    LightCeilFast209.checkFast 124995 124990 380990 5 128 14191624 = true := by decide +kernel

private theorem rowCheck_031 :
    LightCeilFast209.checkFast 121 60 560 129 128 38835837719 = true := by decide +kernel

private theorem rowCheck_032 :
    LightCeilFast209.checkFast 419 338 1838 81 128 6226532804 = true := by decide +kernel

private theorem rowCheck_033 :
    LightCeilFast209.checkFast 1419 1338 6338 81 128 1591951233 = true := by decide +kernel

private theorem rowCheck_034 :
    LightCeilFast209.checkFast 4919 4838 19838 81 128 420385304 = true := by decide +kernel

private theorem rowCheck_035 :
    LightCeilFast209.checkFast 14962 14924 59924 38 128 135838625 = true := by decide +kernel

private theorem rowCheck_036 :
    LightCeilFast209.checkFast 44987 44974 169974 13 128 43860183 = true := by decide +kernel

private theorem rowCheck_037 :
    LightCeilFast209.checkFast 117 58 533 133 128 40324783705 = true := by decide +kernel

private theorem rowCheck_038 :
    LightCeilFast209.checkFast 391 307 1682 84 128 6785582474 = true := by decide +kernel

private theorem rowCheck_039 :
    LightCeilFast209.checkFast 1293 1211 5461 82 128 1714921103 = true := by decide +kernel

private theorem rowCheck_040 :
    LightCeilFast209.checkFast 4168 4086 16086 82 128 487595208 = true := by decide +kernel

private theorem rowCheck_041 :
    LightCeilFast209.checkFast 11950 11900 44400 50 128 164446101 = true := by decide +kernel

private theorem rowCheck_042 :
    LightCeilFast209.checkFast 32481 32462 122462 19 128 60704279 = true := by decide +kernel

private theorem rowCheck_043 :
    LightCeilFast209.checkFast 89993 89986 345986 7 128 22101484 = true := by decide +kernel

private theorem rowCheck_044 :
    LightCeilFast209.checkFast 112 56 556 138 128 44332666113 = true := by decide +kernel

private theorem rowCheck_045 :
    LightCeilFast209.checkFast 415 330 1830 85 128 6389323197 = true := by decide +kernel

private theorem rowCheck_046 :
    LightCeilFast209.checkFast 1415 1330 6330 85 128 1602603874 = true := by decide +kernel

private theorem rowCheck_047 :
    LightCeilFast209.checkFast 4915 4830 19830 85 128 421161314 = true := by decide +kernel

private theorem rowCheck_048 :
    LightCeilFast209.checkFast 14958 14916 59916 42 128 135920061 = true := by decide +kernel

private theorem rowCheck_049 :
    LightCeilFast209.checkFast 44986 44972 169972 14 128 43862349 = true := by decide +kernel

private theorem rowCheck_050 :
    LightCeilFast209.checkFast 124994 124988 380988 6 128 14191869 = true := by decide +kernel

private theorem rowCheck_051 :
    LightCeilFast209.checkFast 108 54 529 142 128 46285971312 = true := by decide +kernel

private theorem rowCheck_052 :
    LightCeilFast209.checkFast 386 297 1672 89 128 7030409150 = true := by decide +kernel

private theorem rowCheck_053 :
    LightCeilFast209.checkFast 1289 1203 5453 86 128 1727532461 = true := by decide +kernel

private theorem rowCheck_054 :
    LightCeilFast209.checkFast 4164 4078 16078 86 128 488655544 = true := by decide +kernel

private theorem rowCheck_055 :
    LightCeilFast209.checkFast 11944 11888 44388 56 128 164629862 = true := by decide +kernel

private theorem rowCheck_056 :
    LightCeilFast209.checkFast 32479 32458 122458 21 128 60712583 = true := by decide +kernel

private theorem rowCheck_057 :
    LightCeilFast209.checkFast 89992 89984 345984 8 128 22102031 = true := by decide +kernel

private theorem rowCheck_058 :
    LightCeilFast209.checkFast 104 52 527 146 128 49551744734 = true := by decide +kernel

private theorem rowCheck_059 :
    LightCeilFast209.checkFast 384 293 1668 91 128 7132978106 = true := by decide +kernel

private theorem rowCheck_060 :
    LightCeilFast209.checkFast 1287 1199 5449 88 128 1733901518 = true := by decide +kernel

private theorem rowCheck_061 :
    LightCeilFast209.checkFast 4162 4074 16074 88 128 489187295 = true := by decide +kernel

private theorem rowCheck_062 :
    LightCeilFast209.checkFast 11942 11884 44384 58 128 164691199 = true := by decide +kernel

private theorem rowCheck_063 :
    LightCeilFast209.checkFast 32478 32456 122456 22 128 60716735 = true := by decide +kernel

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
end JSP233.LightValues209_001
