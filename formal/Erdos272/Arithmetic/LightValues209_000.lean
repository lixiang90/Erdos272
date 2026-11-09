module

public import Erdos272.Certificates.LightCeilFast209

@[expose] public section
namespace JSP233.LightValues209_000
open LightAnalytic209 ResidualCeil208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
  (214,178,978,36,12060135436),
  (767,734,3234,33,2827827367),
  (2475,2450,10950,25,865757138),
  (8493,8486,35986,7,245142629),
  (27497,27494,109994,3,73692168),
  (199,148,848,51,13976615580),
  (658,616,2866,42,3418832366),
  (2208,2166,10166,42,996715065),
  (7985,7970,34220,15,262356897),
  (26245,26240,104990,5,77215377),
  (78748,78746,256246,2,23292497),
  (187,124,824,63,16841492598),
  (651,602,2852,49,3506976320),
  (2201,2152,10152,49,1004008721),
  (7978,7956,34206,22,262875478),
  (26243,26236,104986,7,77228543),
  (78747,78744,256244,3,23293142),
  (178,106,706,72,18576370153),
  (546,492,2492,54,4368947629),
  (1946,1892,9392,54,1164785597),
  (7471,7442,32442,29,282641942),
  (24991,24982,99982,9,81106910),
  (74997,74994,249994,3,24754462),
  (174998,174996,430996,2,9030716),
  (171,92,692,79,21467173159),
  (542,484,2484,58,4448698925),
  (1942,1884,9384,58,1170358883),
  (7466,7432,32432,34,283069329),
  (24989,24978,99978,11,81121435),
  (74996,74992,249992,4,24755183),
  (160,80,630,90,24509225242),
  (487,424,2174,63,5015806388)
]
def checks : Bool := data.all (fun a=>LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)
private theorem rowCheck_000 :
    LightCeilFast209.checkFast 214 178 978 36 128 12060135436 = true := by decide +kernel

private theorem rowCheck_001 :
    LightCeilFast209.checkFast 767 734 3234 33 128 2827827367 = true := by decide +kernel

private theorem rowCheck_002 :
    LightCeilFast209.checkFast 2475 2450 10950 25 128 865757138 = true := by decide +kernel

private theorem rowCheck_003 :
    LightCeilFast209.checkFast 8493 8486 35986 7 128 245142629 = true := by decide +kernel

private theorem rowCheck_004 :
    LightCeilFast209.checkFast 27497 27494 109994 3 128 73692168 = true := by decide +kernel

private theorem rowCheck_005 :
    LightCeilFast209.checkFast 199 148 848 51 128 13976615580 = true := by decide +kernel

private theorem rowCheck_006 :
    LightCeilFast209.checkFast 658 616 2866 42 128 3418832366 = true := by decide +kernel

private theorem rowCheck_007 :
    LightCeilFast209.checkFast 2208 2166 10166 42 128 996715065 = true := by decide +kernel

private theorem rowCheck_008 :
    LightCeilFast209.checkFast 7985 7970 34220 15 128 262356897 = true := by decide +kernel

private theorem rowCheck_009 :
    LightCeilFast209.checkFast 26245 26240 104990 5 128 77215377 = true := by decide +kernel

private theorem rowCheck_010 :
    LightCeilFast209.checkFast 78748 78746 256246 2 128 23292497 = true := by decide +kernel

private theorem rowCheck_011 :
    LightCeilFast209.checkFast 187 124 824 63 128 16841492598 = true := by decide +kernel

private theorem rowCheck_012 :
    LightCeilFast209.checkFast 651 602 2852 49 128 3506976320 = true := by decide +kernel

private theorem rowCheck_013 :
    LightCeilFast209.checkFast 2201 2152 10152 49 128 1004008721 = true := by decide +kernel

private theorem rowCheck_014 :
    LightCeilFast209.checkFast 7978 7956 34206 22 128 262875478 = true := by decide +kernel

private theorem rowCheck_015 :
    LightCeilFast209.checkFast 26243 26236 104986 7 128 77228543 = true := by decide +kernel

private theorem rowCheck_016 :
    LightCeilFast209.checkFast 78747 78744 256244 3 128 23293142 = true := by decide +kernel

private theorem rowCheck_017 :
    LightCeilFast209.checkFast 178 106 706 72 128 18576370153 = true := by decide +kernel

private theorem rowCheck_018 :
    LightCeilFast209.checkFast 546 492 2492 54 128 4368947629 = true := by decide +kernel

private theorem rowCheck_019 :
    LightCeilFast209.checkFast 1946 1892 9392 54 128 1164785597 = true := by decide +kernel

private theorem rowCheck_020 :
    LightCeilFast209.checkFast 7471 7442 32442 29 128 282641942 = true := by decide +kernel

private theorem rowCheck_021 :
    LightCeilFast209.checkFast 24991 24982 99982 9 128 81106910 = true := by decide +kernel

private theorem rowCheck_022 :
    LightCeilFast209.checkFast 74997 74994 249994 3 128 24754462 = true := by decide +kernel

private theorem rowCheck_023 :
    LightCeilFast209.checkFast 174998 174996 430996 2 128 9030716 = true := by decide +kernel

private theorem rowCheck_024 :
    LightCeilFast209.checkFast 171 92 692 79 128 21467173159 = true := by decide +kernel

private theorem rowCheck_025 :
    LightCeilFast209.checkFast 542 484 2484 58 128 4448698925 = true := by decide +kernel

private theorem rowCheck_026 :
    LightCeilFast209.checkFast 1942 1884 9384 58 128 1170358883 = true := by decide +kernel

private theorem rowCheck_027 :
    LightCeilFast209.checkFast 7466 7432 32432 34 128 283069329 = true := by decide +kernel

private theorem rowCheck_028 :
    LightCeilFast209.checkFast 24989 24978 99978 11 128 81121435 = true := by decide +kernel

private theorem rowCheck_029 :
    LightCeilFast209.checkFast 74996 74992 249992 4 128 24755183 = true := by decide +kernel

private theorem rowCheck_030 :
    LightCeilFast209.checkFast 160 80 630 90 128 24509225242 = true := by decide +kernel

private theorem rowCheck_031 :
    LightCeilFast209.checkFast 487 424 2174 63 128 5015806388 = true := by decide +kernel

private theorem fast_checks_true : LightCeilFast209.checkAllFast data = true := by
  simp only [LightCeilFast209.checkAllFast, data, List.all_cons, List.all_nil,
    rowCheck_000, rowCheck_001, rowCheck_002, rowCheck_003, rowCheck_004, rowCheck_005,
    rowCheck_006, rowCheck_007, rowCheck_008, rowCheck_009, rowCheck_010, rowCheck_011,
    rowCheck_012, rowCheck_013, rowCheck_014, rowCheck_015, rowCheck_016, rowCheck_017,
    rowCheck_018, rowCheck_019, rowCheck_020, rowCheck_021, rowCheck_022, rowCheck_023,
    rowCheck_024, rowCheck_025, rowCheck_026, rowCheck_027, rowCheck_028, rowCheck_029,
    rowCheck_030, rowCheck_031,
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
end JSP233.LightValues209_000
