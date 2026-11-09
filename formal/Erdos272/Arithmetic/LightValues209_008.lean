module

public import Erdos272.Certificates.LightCeilFast209

@[expose] public section
namespace JSP233.LightValues209_008
open LightAnalytic209 ResidualCeil208
set_option maxHeartbeats 0
set_option maxRecDepth 65536
noncomputable section
def data : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
  (12833,12754,47724,79,153499549),
  (34940,34910,131750,30,56450899),
  (96829,96818,372274,11,20542051),
  (81,40,551,188,83579585807),
  (395,279,1758,116,7547179532),
  (1372,1265,5838,107,1646934191),
  (4466,4359,17271,107,457481415),
  (12827,12742,47712,85,153659527),
  (34939,34908,131748,31,56454489),
  (96828,96816,372272,12,20542523),
  (77,38,522,192,89811348192),
  (361,238,1529,123,8606460468),
  (1182,1073,4839,109,1906794908),
  (3657,3548,14308,109,565123004),
  (10655,10550,42830,105,192485865),
  (32245,32210,129050,35,62917116),
  (72,36,520,197,100548997911),
  (358,232,1523,126,8838472018),
  (1180,1069,4835,111,1914611769),
  (3655,3544,14304,111,565829698),
  (10650,10540,42820,110,192689681),
  (32243,32206,129046,37,62925853),
  (96827,96814,372270,13,20542995),
  (68,34,518,201,111670129452),
  (356,228,1519,128,8999842060),
  (1178,1065,4831,113,1922487295),
  (3653,3540,14300,113,566538010),
  (10647,10534,42814,113,192812158),
  (32242,32204,129044,38,62930222),
  (65,32,516,204,122797236093),
  (354,224,1515,130,9166905594),
  (1177,1063,4829,114,1926447263),
  (3652,3538,14298,114,566892776),
  (10646,10532,42812,114,192853015),
  (32241,32202,129042,39,62934592),
  (201,119,798,82,16548288792),
  (619,559,2823,60,3844107726),
  (2204,2144,10634,60,1027742646),
  (8457,8424,36724,33,249695153),
  (28290,28280,113180,10,71648148),
  (84896,84892,282992,4,21868239),
  (198098,198096,487888,2,7977642),
  (160,80,646,123,25817571062),
  (486,406,2104,80,5158846887),
  (1618,1538,7198,80,1382535866),
  (5580,5500,22480,80,369605478),
  (16947,16914,67854,33,119839929),
  (50929,50918,192418,11,38739466),
  (141496,141492,431284,4,12536453),
  (132,66,603,151,35585364430),
  (442,347,1903,95,6005729184),
  (1464,1372,6183,92,1513667611),
  (4719,4627,18211,92,430567758),
  (13527,13470,50260,57,145279959),
  (36769,36748,138628,21,53624042),
  (101872,101864,391656,8,19524312),
  (113,56,593,170,47437435239),
  (431,325,1881,106,6441253693),
  (1456,1356,6167,100,1533421440),
  (4711,4611,18195,100,432224020),
  (13515,13446,50236,69,145567025),
  (36764,36738,138618,26,53640244),
  (101870,101860,391652,10,19525165),
  (97,48,585,186,62640707523)
]
def checks : Bool := data.all (fun a=>LightCeil209.Check a.1 a.2.1 a.2.2.1 a.2.2.2.1 128 a.2.2.2.2)
private theorem rowCheck_000 :
    LightCeilFast209.checkFast 12833 12754 47724 79 128 153499549 = true := by decide +kernel

private theorem rowCheck_001 :
    LightCeilFast209.checkFast 34940 34910 131750 30 128 56450899 = true := by decide +kernel

private theorem rowCheck_002 :
    LightCeilFast209.checkFast 96829 96818 372274 11 128 20542051 = true := by decide +kernel

private theorem rowCheck_003 :
    LightCeilFast209.checkFast 81 40 551 188 128 83579585807 = true := by decide +kernel

private theorem rowCheck_004 :
    LightCeilFast209.checkFast 395 279 1758 116 128 7547179532 = true := by decide +kernel

private theorem rowCheck_005 :
    LightCeilFast209.checkFast 1372 1265 5838 107 128 1646934191 = true := by decide +kernel

private theorem rowCheck_006 :
    LightCeilFast209.checkFast 4466 4359 17271 107 128 457481415 = true := by decide +kernel

private theorem rowCheck_007 :
    LightCeilFast209.checkFast 12827 12742 47712 85 128 153659527 = true := by decide +kernel

private theorem rowCheck_008 :
    LightCeilFast209.checkFast 34939 34908 131748 31 128 56454489 = true := by decide +kernel

private theorem rowCheck_009 :
    LightCeilFast209.checkFast 96828 96816 372272 12 128 20542523 = true := by decide +kernel

private theorem rowCheck_010 :
    LightCeilFast209.checkFast 77 38 522 192 128 89811348192 = true := by decide +kernel

private theorem rowCheck_011 :
    LightCeilFast209.checkFast 361 238 1529 123 128 8606460468 = true := by decide +kernel

private theorem rowCheck_012 :
    LightCeilFast209.checkFast 1182 1073 4839 109 128 1906794908 = true := by decide +kernel

private theorem rowCheck_013 :
    LightCeilFast209.checkFast 3657 3548 14308 109 128 565123004 = true := by decide +kernel

private theorem rowCheck_014 :
    LightCeilFast209.checkFast 10655 10550 42830 105 128 192485865 = true := by decide +kernel

private theorem rowCheck_015 :
    LightCeilFast209.checkFast 32245 32210 129050 35 128 62917116 = true := by decide +kernel

private theorem rowCheck_016 :
    LightCeilFast209.checkFast 72 36 520 197 128 100548997911 = true := by decide +kernel

private theorem rowCheck_017 :
    LightCeilFast209.checkFast 358 232 1523 126 128 8838472018 = true := by decide +kernel

private theorem rowCheck_018 :
    LightCeilFast209.checkFast 1180 1069 4835 111 128 1914611769 = true := by decide +kernel

private theorem rowCheck_019 :
    LightCeilFast209.checkFast 3655 3544 14304 111 128 565829698 = true := by decide +kernel

private theorem rowCheck_020 :
    LightCeilFast209.checkFast 10650 10540 42820 110 128 192689681 = true := by decide +kernel

private theorem rowCheck_021 :
    LightCeilFast209.checkFast 32243 32206 129046 37 128 62925853 = true := by decide +kernel

private theorem rowCheck_022 :
    LightCeilFast209.checkFast 96827 96814 372270 13 128 20542995 = true := by decide +kernel

private theorem rowCheck_023 :
    LightCeilFast209.checkFast 68 34 518 201 128 111670129452 = true := by decide +kernel

private theorem rowCheck_024 :
    LightCeilFast209.checkFast 356 228 1519 128 128 8999842060 = true := by decide +kernel

private theorem rowCheck_025 :
    LightCeilFast209.checkFast 1178 1065 4831 113 128 1922487295 = true := by decide +kernel

private theorem rowCheck_026 :
    LightCeilFast209.checkFast 3653 3540 14300 113 128 566538010 = true := by decide +kernel

private theorem rowCheck_027 :
    LightCeilFast209.checkFast 10647 10534 42814 113 128 192812158 = true := by decide +kernel

private theorem rowCheck_028 :
    LightCeilFast209.checkFast 32242 32204 129044 38 128 62930222 = true := by decide +kernel

private theorem rowCheck_029 :
    LightCeilFast209.checkFast 65 32 516 204 128 122797236093 = true := by decide +kernel

private theorem rowCheck_030 :
    LightCeilFast209.checkFast 354 224 1515 130 128 9166905594 = true := by decide +kernel

private theorem rowCheck_031 :
    LightCeilFast209.checkFast 1177 1063 4829 114 128 1926447263 = true := by decide +kernel

private theorem rowCheck_032 :
    LightCeilFast209.checkFast 3652 3538 14298 114 128 566892776 = true := by decide +kernel

private theorem rowCheck_033 :
    LightCeilFast209.checkFast 10646 10532 42812 114 128 192853015 = true := by decide +kernel

private theorem rowCheck_034 :
    LightCeilFast209.checkFast 32241 32202 129042 39 128 62934592 = true := by decide +kernel

private theorem rowCheck_035 :
    LightCeilFast209.checkFast 201 119 798 82 128 16548288792 = true := by decide +kernel

private theorem rowCheck_036 :
    LightCeilFast209.checkFast 619 559 2823 60 128 3844107726 = true := by decide +kernel

private theorem rowCheck_037 :
    LightCeilFast209.checkFast 2204 2144 10634 60 128 1027742646 = true := by decide +kernel

private theorem rowCheck_038 :
    LightCeilFast209.checkFast 8457 8424 36724 33 128 249695153 = true := by decide +kernel

private theorem rowCheck_039 :
    LightCeilFast209.checkFast 28290 28280 113180 10 128 71648148 = true := by decide +kernel

private theorem rowCheck_040 :
    LightCeilFast209.checkFast 84896 84892 282992 4 128 21868239 = true := by decide +kernel

private theorem rowCheck_041 :
    LightCeilFast209.checkFast 198098 198096 487888 2 128 7977642 = true := by decide +kernel

private theorem rowCheck_042 :
    LightCeilFast209.checkFast 160 80 646 123 128 25817571062 = true := by decide +kernel

private theorem rowCheck_043 :
    LightCeilFast209.checkFast 486 406 2104 80 128 5158846887 = true := by decide +kernel

private theorem rowCheck_044 :
    LightCeilFast209.checkFast 1618 1538 7198 80 128 1382535866 = true := by decide +kernel

private theorem rowCheck_045 :
    LightCeilFast209.checkFast 5580 5500 22480 80 128 369605478 = true := by decide +kernel

private theorem rowCheck_046 :
    LightCeilFast209.checkFast 16947 16914 67854 33 128 119839929 = true := by decide +kernel

private theorem rowCheck_047 :
    LightCeilFast209.checkFast 50929 50918 192418 11 128 38739466 = true := by decide +kernel

private theorem rowCheck_048 :
    LightCeilFast209.checkFast 141496 141492 431284 4 128 12536453 = true := by decide +kernel

private theorem rowCheck_049 :
    LightCeilFast209.checkFast 132 66 603 151 128 35585364430 = true := by decide +kernel

private theorem rowCheck_050 :
    LightCeilFast209.checkFast 442 347 1903 95 128 6005729184 = true := by decide +kernel

private theorem rowCheck_051 :
    LightCeilFast209.checkFast 1464 1372 6183 92 128 1513667611 = true := by decide +kernel

private theorem rowCheck_052 :
    LightCeilFast209.checkFast 4719 4627 18211 92 128 430567758 = true := by decide +kernel

private theorem rowCheck_053 :
    LightCeilFast209.checkFast 13527 13470 50260 57 128 145279959 = true := by decide +kernel

private theorem rowCheck_054 :
    LightCeilFast209.checkFast 36769 36748 138628 21 128 53624042 = true := by decide +kernel

private theorem rowCheck_055 :
    LightCeilFast209.checkFast 101872 101864 391656 8 128 19524312 = true := by decide +kernel

private theorem rowCheck_056 :
    LightCeilFast209.checkFast 113 56 593 170 128 47437435239 = true := by decide +kernel

private theorem rowCheck_057 :
    LightCeilFast209.checkFast 431 325 1881 106 128 6441253693 = true := by decide +kernel

private theorem rowCheck_058 :
    LightCeilFast209.checkFast 1456 1356 6167 100 128 1533421440 = true := by decide +kernel

private theorem rowCheck_059 :
    LightCeilFast209.checkFast 4711 4611 18195 100 128 432224020 = true := by decide +kernel

private theorem rowCheck_060 :
    LightCeilFast209.checkFast 13515 13446 50236 69 128 145567025 = true := by decide +kernel

private theorem rowCheck_061 :
    LightCeilFast209.checkFast 36764 36738 138618 26 128 53640244 = true := by decide +kernel

private theorem rowCheck_062 :
    LightCeilFast209.checkFast 101870 101860 391652 10 128 19525165 = true := by decide +kernel

private theorem rowCheck_063 :
    LightCeilFast209.checkFast 97 48 585 186 128 62640707523 = true := by decide +kernel

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
end JSP233.LightValues209_008
