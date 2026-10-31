import Erdos272.Certificates.LightCeilFast209
namespace JSP233.LightValues209_011
open LightAnalytic209 ResidualCeil208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
  (4677,4538,18298,139,441828820),
  (13621,13482,54762,139,150637215),
  (41233,41186,165026,47,49205709),
  (123824,123808,476064,16,16063964),
  (83,41,660,261,96034511643),
  (453,287,1938,166,7153989199),
  (1508,1365,6181,143,1499628864),
  (4673,4530,18290,143,442693344),
  (13617,13474,54754,143,150737025),
  (41230,41180,165020,50,49213726),
  (123823,123806,476062,17,16064253),
  (292,174,1158,118,11316379935),
  (902,820,4100,82,2616935082),
  (3198,3116,15416,82,706865982),
  (12252,12204,53204,48,172356613),
  (40985,40970,163970,15,49456081),
  (122995,122990,409990,5,15094206),
  (286997,286994,706834,3,5506523),
  (233,116,936,177,17714497515),
  (708,596,3056,112,3510360354),
  (2350,2240,10440,110,948686243),
  (8090,7980,32580,110,254697237),
  (24553,24506,98306,47,82712674),
  (73784,73768,278768,16,26739731),
  (204994,204988,624828,6,8653229),
  (192,96,875,218,24401261109),
  (642,505,2760,137,4124204581),
  (2127,1999,8969,128,1038187056),
  (6842,6714,26394,128,296678004),
  (19598,19516,72816,82,100272013),
  (53270,53240,200840,30,37013014),
  (147589,147578,567418,11,13476418),
  (165,82,861,245,32230218419),
  (627,475,2730,152,4403324610),
  (2116,1977,8947,139,1050971114),
  (6831,6692,26372,139,297759363),
  (19581,19482,72782,99,100465738),
  (53263,53226,200826,37,37023820),
  (147586,147572,567412,14,13477027),
  (141,70,849,269,42890697263),
  (613,447,2702,166,4697227661),
  (2105,1955,8925,150,1064044136),
  (6820,6670,26350,150,298847951),
  (19564,19448,72748,116,100660148),
  (53257,53214,200814,43,37033087),
  (147584,147568,567408,16,13477434),
  (124,62,841,286,53879671921),
  (603,427,2682,176,4930473770),
  (2098,1941,8911,157,1072518271),
  (6813,6656,26336,157,299544486),
  (19551,19422,72722,129,100809278),
  (53252,53204,200804,48,37040813),
  (147583,147566,567406,17,13477637),
  (110,55,793,300,65694276973),
  (547,356,2324,191,5757791847),
  (1805,1642,7382,163,1245505886),
  (5577,5414,21814,163,370300264),
  (16237,16074,65274,163,126341465),
  (49144,49088,196688,56,41284758),
  (147581,147562,567402,19,13478044),
  (99,49,787,311,80348026111),
  (541,344,2312,197,5966857309),
  (1801,1634,7374,167,1252189146),
  (5573,5406,21806,167,370907464)
]
def checks : Bool := data.all (fun a=>LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)
private theorem rowCheck_000 :
    LightCeilFast209.checkFast 4677 4538 18298 139 128 441828820 = true := by decide +kernel

private theorem rowCheck_001 :
    LightCeilFast209.checkFast 13621 13482 54762 139 128 150637215 = true := by decide +kernel

private theorem rowCheck_002 :
    LightCeilFast209.checkFast 41233 41186 165026 47 128 49205709 = true := by decide +kernel

private theorem rowCheck_003 :
    LightCeilFast209.checkFast 123824 123808 476064 16 128 16063964 = true := by decide +kernel

private theorem rowCheck_004 :
    LightCeilFast209.checkFast 83 41 660 261 128 96034511643 = true := by decide +kernel

private theorem rowCheck_005 :
    LightCeilFast209.checkFast 453 287 1938 166 128 7153989199 = true := by decide +kernel

private theorem rowCheck_006 :
    LightCeilFast209.checkFast 1508 1365 6181 143 128 1499628864 = true := by decide +kernel

private theorem rowCheck_007 :
    LightCeilFast209.checkFast 4673 4530 18290 143 128 442693344 = true := by decide +kernel

private theorem rowCheck_008 :
    LightCeilFast209.checkFast 13617 13474 54754 143 128 150737025 = true := by decide +kernel

private theorem rowCheck_009 :
    LightCeilFast209.checkFast 41230 41180 165020 50 128 49213726 = true := by decide +kernel

private theorem rowCheck_010 :
    LightCeilFast209.checkFast 123823 123806 476062 17 128 16064253 = true := by decide +kernel

private theorem rowCheck_011 :
    LightCeilFast209.checkFast 292 174 1158 118 128 11316379935 = true := by decide +kernel

private theorem rowCheck_012 :
    LightCeilFast209.checkFast 902 820 4100 82 128 2616935082 = true := by decide +kernel

private theorem rowCheck_013 :
    LightCeilFast209.checkFast 3198 3116 15416 82 128 706865982 = true := by decide +kernel

private theorem rowCheck_014 :
    LightCeilFast209.checkFast 12252 12204 53204 48 128 172356613 = true := by decide +kernel

private theorem rowCheck_015 :
    LightCeilFast209.checkFast 40985 40970 163970 15 128 49456081 = true := by decide +kernel

private theorem rowCheck_016 :
    LightCeilFast209.checkFast 122995 122990 409990 5 128 15094206 = true := by decide +kernel

private theorem rowCheck_017 :
    LightCeilFast209.checkFast 286997 286994 706834 3 128 5506523 = true := by decide +kernel

private theorem rowCheck_018 :
    LightCeilFast209.checkFast 233 116 936 177 128 17714497515 = true := by decide +kernel

private theorem rowCheck_019 :
    LightCeilFast209.checkFast 708 596 3056 112 128 3510360354 = true := by decide +kernel

private theorem rowCheck_020 :
    LightCeilFast209.checkFast 2350 2240 10440 110 128 948686243 = true := by decide +kernel

private theorem rowCheck_021 :
    LightCeilFast209.checkFast 8090 7980 32580 110 128 254697237 = true := by decide +kernel

private theorem rowCheck_022 :
    LightCeilFast209.checkFast 24553 24506 98306 47 128 82712674 = true := by decide +kernel

private theorem rowCheck_023 :
    LightCeilFast209.checkFast 73784 73768 278768 16 128 26739731 = true := by decide +kernel

private theorem rowCheck_024 :
    LightCeilFast209.checkFast 204994 204988 624828 6 128 8653229 = true := by decide +kernel

private theorem rowCheck_025 :
    LightCeilFast209.checkFast 192 96 875 218 128 24401261109 = true := by decide +kernel

private theorem rowCheck_026 :
    LightCeilFast209.checkFast 642 505 2760 137 128 4124204581 = true := by decide +kernel

private theorem rowCheck_027 :
    LightCeilFast209.checkFast 2127 1999 8969 128 128 1038187056 = true := by decide +kernel

private theorem rowCheck_028 :
    LightCeilFast209.checkFast 6842 6714 26394 128 128 296678004 = true := by decide +kernel

private theorem rowCheck_029 :
    LightCeilFast209.checkFast 19598 19516 72816 82 128 100272013 = true := by decide +kernel

private theorem rowCheck_030 :
    LightCeilFast209.checkFast 53270 53240 200840 30 128 37013014 = true := by decide +kernel

private theorem rowCheck_031 :
    LightCeilFast209.checkFast 147589 147578 567418 11 128 13476418 = true := by decide +kernel

private theorem rowCheck_032 :
    LightCeilFast209.checkFast 165 82 861 245 128 32230218419 = true := by decide +kernel

private theorem rowCheck_033 :
    LightCeilFast209.checkFast 627 475 2730 152 128 4403324610 = true := by decide +kernel

private theorem rowCheck_034 :
    LightCeilFast209.checkFast 2116 1977 8947 139 128 1050971114 = true := by decide +kernel

private theorem rowCheck_035 :
    LightCeilFast209.checkFast 6831 6692 26372 139 128 297759363 = true := by decide +kernel

private theorem rowCheck_036 :
    LightCeilFast209.checkFast 19581 19482 72782 99 128 100465738 = true := by decide +kernel

private theorem rowCheck_037 :
    LightCeilFast209.checkFast 53263 53226 200826 37 128 37023820 = true := by decide +kernel

private theorem rowCheck_038 :
    LightCeilFast209.checkFast 147586 147572 567412 14 128 13477027 = true := by decide +kernel

private theorem rowCheck_039 :
    LightCeilFast209.checkFast 141 70 849 269 128 42890697263 = true := by decide +kernel

private theorem rowCheck_040 :
    LightCeilFast209.checkFast 613 447 2702 166 128 4697227661 = true := by decide +kernel

private theorem rowCheck_041 :
    LightCeilFast209.checkFast 2105 1955 8925 150 128 1064044136 = true := by decide +kernel

private theorem rowCheck_042 :
    LightCeilFast209.checkFast 6820 6670 26350 150 128 298847951 = true := by decide +kernel

private theorem rowCheck_043 :
    LightCeilFast209.checkFast 19564 19448 72748 116 128 100660148 = true := by decide +kernel

private theorem rowCheck_044 :
    LightCeilFast209.checkFast 53257 53214 200814 43 128 37033087 = true := by decide +kernel

private theorem rowCheck_045 :
    LightCeilFast209.checkFast 147584 147568 567408 16 128 13477434 = true := by decide +kernel

private theorem rowCheck_046 :
    LightCeilFast209.checkFast 124 62 841 286 128 53879671921 = true := by decide +kernel

private theorem rowCheck_047 :
    LightCeilFast209.checkFast 603 427 2682 176 128 4930473770 = true := by decide +kernel

private theorem rowCheck_048 :
    LightCeilFast209.checkFast 2098 1941 8911 157 128 1072518271 = true := by decide +kernel

private theorem rowCheck_049 :
    LightCeilFast209.checkFast 6813 6656 26336 157 128 299544486 = true := by decide +kernel

private theorem rowCheck_050 :
    LightCeilFast209.checkFast 19551 19422 72722 129 128 100809278 = true := by decide +kernel

private theorem rowCheck_051 :
    LightCeilFast209.checkFast 53252 53204 200804 48 128 37040813 = true := by decide +kernel

private theorem rowCheck_052 :
    LightCeilFast209.checkFast 147583 147566 567406 17 128 13477637 = true := by decide +kernel

private theorem rowCheck_053 :
    LightCeilFast209.checkFast 110 55 793 300 128 65694276973 = true := by decide +kernel

private theorem rowCheck_054 :
    LightCeilFast209.checkFast 547 356 2324 191 128 5757791847 = true := by decide +kernel

private theorem rowCheck_055 :
    LightCeilFast209.checkFast 1805 1642 7382 163 128 1245505886 = true := by decide +kernel

private theorem rowCheck_056 :
    LightCeilFast209.checkFast 5577 5414 21814 163 128 370300264 = true := by decide +kernel

private theorem rowCheck_057 :
    LightCeilFast209.checkFast 16237 16074 65274 163 128 126341465 = true := by decide +kernel

private theorem rowCheck_058 :
    LightCeilFast209.checkFast 49144 49088 196688 56 128 41284758 = true := by decide +kernel

private theorem rowCheck_059 :
    LightCeilFast209.checkFast 147581 147562 567402 19 128 13478044 = true := by decide +kernel

private theorem rowCheck_060 :
    LightCeilFast209.checkFast 99 49 787 311 128 80348026111 = true := by decide +kernel

private theorem rowCheck_061 :
    LightCeilFast209.checkFast 541 344 2312 197 128 5966857309 = true := by decide +kernel

private theorem rowCheck_062 :
    LightCeilFast209.checkFast 1801 1634 7374 167 128 1252189146 = true := by decide +kernel

private theorem rowCheck_063 :
    LightCeilFast209.checkFast 5573 5406 21806 167 128 370907464 = true := by decide +kernel

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
end JSP233.LightValues209_011
