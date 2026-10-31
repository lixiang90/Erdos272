import Erdos272.Certificates.LightCeilFast209
namespace JSP233.LightValues209_014
open LightAnalytic209 ResidualCeil208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
  (715980,715960,6392638,20,3903287),
  (670,335,3055,762,6996650652),
  (2244,1768,9644,476,1177917125),
  (7463,7050,31394,413,294068085),
  (23931,23518,92254,413,84669937),
  (68451,68166,254326,285,28707861),
  (186055,185950,701470,105,10597330),
  (515482,515444,6192122,38,5983483),
  (575,287,3007,857,9233554402),
  (2190,1660,9536,530,1260057126),
  (7422,6968,31312,454,297901147),
  (23890,23436,92172,454,84998472),
  (68390,68044,254204,346,28764842),
  (186032,185904,701424,128,10600240),
  (515474,515428,6192106,46,5983697),
  (492,246,2966,940,12232336143),
  (2143,1566,9442,577,1340660666),
  (7386,6896,31240,490,301342260),
  (23854,23364,92100,490,85288869),
  (68331,67926,254086,405,28820152),
  (186011,185862,701382,149,10602899),
  (515466,515412,6192090,54,5983911),
  (433,216,2936,999,15458511542),
  (2109,1498,9374,611,1405199413),
  (7362,6848,31192,514,303676707),
  (23830,23316,92052,514,85483476),
  (68288,67840,254000,448,28860585),
  (185995,185830,701350,165,10604926),
  (515460,515400,6192078,60,5984071),
  (385,192,2769,1047,18773260886),
  (1914,1251,8124,663,1638175115),
  (6338,5803,25851,535,352031592),
  (19513,18978,76258,535,105597013),
  (56745,56210,228050,535,36123908),
  (171646,171452,686972,194,11820112),
  (515455,515390,6192068,65,5984205),
  (344,172,2749,1088,23038286801),
  (1889,1201,8074,688,1709188950),
  (6321,5769,25817,552,354308120),
  (19496,18944,76224,552,105807076),
  (56728,56176,228016,552,36148311),
  (171633,171426,686946,207,11822116),
  (515451,515382,6192060,69,5984312)
]
def checks : Bool := data.all (fun a=>LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)
private theorem rowCheck_000 :
    LightCeilFast209.checkFast 715980 715960 6392638 20 128 3903287 = true := by decide +kernel

private theorem rowCheck_001 :
    LightCeilFast209.checkFast 670 335 3055 762 128 6996650652 = true := by decide +kernel

private theorem rowCheck_002 :
    LightCeilFast209.checkFast 2244 1768 9644 476 128 1177917125 = true := by decide +kernel

private theorem rowCheck_003 :
    LightCeilFast209.checkFast 7463 7050 31394 413 128 294068085 = true := by decide +kernel

private theorem rowCheck_004 :
    LightCeilFast209.checkFast 23931 23518 92254 413 128 84669937 = true := by decide +kernel

private theorem rowCheck_005 :
    LightCeilFast209.checkFast 68451 68166 254326 285 128 28707861 = true := by decide +kernel

private theorem rowCheck_006 :
    LightCeilFast209.checkFast 186055 185950 701470 105 128 10597330 = true := by decide +kernel

private theorem rowCheck_007 :
    LightCeilFast209.checkFast 515482 515444 6192122 38 128 5983483 = true := by decide +kernel

private theorem rowCheck_008 :
    LightCeilFast209.checkFast 575 287 3007 857 128 9233554402 = true := by decide +kernel

private theorem rowCheck_009 :
    LightCeilFast209.checkFast 2190 1660 9536 530 128 1260057126 = true := by decide +kernel

private theorem rowCheck_010 :
    LightCeilFast209.checkFast 7422 6968 31312 454 128 297901147 = true := by decide +kernel

private theorem rowCheck_011 :
    LightCeilFast209.checkFast 23890 23436 92172 454 128 84998472 = true := by decide +kernel

private theorem rowCheck_012 :
    LightCeilFast209.checkFast 68390 68044 254204 346 128 28764842 = true := by decide +kernel

private theorem rowCheck_013 :
    LightCeilFast209.checkFast 186032 185904 701424 128 128 10600240 = true := by decide +kernel

private theorem rowCheck_014 :
    LightCeilFast209.checkFast 515474 515428 6192106 46 128 5983697 = true := by decide +kernel

private theorem rowCheck_015 :
    LightCeilFast209.checkFast 492 246 2966 940 128 12232336143 = true := by decide +kernel

private theorem rowCheck_016 :
    LightCeilFast209.checkFast 2143 1566 9442 577 128 1340660666 = true := by decide +kernel

private theorem rowCheck_017 :
    LightCeilFast209.checkFast 7386 6896 31240 490 128 301342260 = true := by decide +kernel

private theorem rowCheck_018 :
    LightCeilFast209.checkFast 23854 23364 92100 490 128 85288869 = true := by decide +kernel

private theorem rowCheck_019 :
    LightCeilFast209.checkFast 68331 67926 254086 405 128 28820152 = true := by decide +kernel

private theorem rowCheck_020 :
    LightCeilFast209.checkFast 186011 185862 701382 149 128 10602899 = true := by decide +kernel

private theorem rowCheck_021 :
    LightCeilFast209.checkFast 515466 515412 6192090 54 128 5983911 = true := by decide +kernel

private theorem rowCheck_022 :
    LightCeilFast209.checkFast 433 216 2936 999 128 15458511542 = true := by decide +kernel

private theorem rowCheck_023 :
    LightCeilFast209.checkFast 2109 1498 9374 611 128 1405199413 = true := by decide +kernel

private theorem rowCheck_024 :
    LightCeilFast209.checkFast 7362 6848 31192 514 128 303676707 = true := by decide +kernel

private theorem rowCheck_025 :
    LightCeilFast209.checkFast 23830 23316 92052 514 128 85483476 = true := by decide +kernel

private theorem rowCheck_026 :
    LightCeilFast209.checkFast 68288 67840 254000 448 128 28860585 = true := by decide +kernel

private theorem rowCheck_027 :
    LightCeilFast209.checkFast 185995 185830 701350 165 128 10604926 = true := by decide +kernel

private theorem rowCheck_028 :
    LightCeilFast209.checkFast 515460 515400 6192078 60 128 5984071 = true := by decide +kernel

private theorem rowCheck_029 :
    LightCeilFast209.checkFast 385 192 2769 1047 128 18773260886 = true := by decide +kernel

private theorem rowCheck_030 :
    LightCeilFast209.checkFast 1914 1251 8124 663 128 1638175115 = true := by decide +kernel

private theorem rowCheck_031 :
    LightCeilFast209.checkFast 6338 5803 25851 535 128 352031592 = true := by decide +kernel

private theorem rowCheck_032 :
    LightCeilFast209.checkFast 19513 18978 76258 535 128 105597013 = true := by decide +kernel

private theorem rowCheck_033 :
    LightCeilFast209.checkFast 56745 56210 228050 535 128 36123908 = true := by decide +kernel

private theorem rowCheck_034 :
    LightCeilFast209.checkFast 171646 171452 686972 194 128 11820112 = true := by decide +kernel

private theorem rowCheck_035 :
    LightCeilFast209.checkFast 515455 515390 6192068 65 128 5984205 = true := by decide +kernel

private theorem rowCheck_036 :
    LightCeilFast209.checkFast 344 172 2749 1088 128 23038286801 = true := by decide +kernel

private theorem rowCheck_037 :
    LightCeilFast209.checkFast 1889 1201 8074 688 128 1709188950 = true := by decide +kernel

private theorem rowCheck_038 :
    LightCeilFast209.checkFast 6321 5769 25817 552 128 354308120 = true := by decide +kernel

private theorem rowCheck_039 :
    LightCeilFast209.checkFast 19496 18944 76224 552 128 105807076 = true := by decide +kernel

private theorem rowCheck_040 :
    LightCeilFast209.checkFast 56728 56176 228016 552 128 36148311 = true := by decide +kernel

private theorem rowCheck_041 :
    LightCeilFast209.checkFast 171633 171426 686946 207 128 11822116 = true := by decide +kernel

private theorem rowCheck_042 :
    LightCeilFast209.checkFast 515451 515382 6192060 69 128 5984312 = true := by decide +kernel

private theorem fast_checks_true : LightCeilFast209.checkAllFast data = true := by
  simp only [LightCeilFast209.checkAllFast, data, List.all_cons, List.all_nil,
    rowCheck_000, rowCheck_001, rowCheck_002, rowCheck_003, rowCheck_004, rowCheck_005,
    rowCheck_006, rowCheck_007, rowCheck_008, rowCheck_009, rowCheck_010, rowCheck_011,
    rowCheck_012, rowCheck_013, rowCheck_014, rowCheck_015, rowCheck_016, rowCheck_017,
    rowCheck_018, rowCheck_019, rowCheck_020, rowCheck_021, rowCheck_022, rowCheck_023,
    rowCheck_024, rowCheck_025, rowCheck_026, rowCheck_027, rowCheck_028, rowCheck_029,
    rowCheck_030, rowCheck_031, rowCheck_032, rowCheck_033, rowCheck_034, rowCheck_035,
    rowCheck_036, rowCheck_037, rowCheck_038, rowCheck_039, rowCheck_040, rowCheck_041,
    rowCheck_042,
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
end JSP233.LightValues209_014
