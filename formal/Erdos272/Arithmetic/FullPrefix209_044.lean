import Erdos272.Certificates.ForcedDual209
import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_043
namespace JSP233.FullPrefix209_044
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1441792 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1441792 1024 876504563314927222 631868728327 877127215990508685 632766782975 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1442816 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1442816 1024 877127215990508685 632766782975 877749678732053001 633665201125 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1443840 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1443840 1024 877749678732053001 633665201125 878372115356990902 634564218889 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1444864 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1444864 1024 878372115356990902 634564218889 878994745606306144 635464153903 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1445888 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1445888 1024 878994745606306144 635464153903 879617160434778556 636364414909 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1446912 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1446912 1024 879617160434778556 636364414909 880239645570443282 637265414959 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1447936 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1447936 1024 880239645570443282 637265414959 880862333902002580 638167346823 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1448960 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1448960 1024 880862333902002580 638167346823 881484862063406293 639069684257 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1441792 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1441792 8192 876504563314927222 631868728327 881484862063406293 639069684257 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1441792 876504563314927222 631868728327 877127215990508685 632766782975 7168 881484862063406293 639069684257 checked_small_1441792 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1442816 877127215990508685 632766782975 877749678732053001 633665201125 6144 881484862063406293 639069684257 checked_small_1442816 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1443840 877749678732053001 633665201125 878372115356990902 634564218889 5120 881484862063406293 639069684257 checked_small_1443840 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1444864 878372115356990902 634564218889 878994745606306144 635464153903 4096 881484862063406293 639069684257 checked_small_1444864 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1445888 878994745606306144 635464153903 879617160434778556 636364414909 3072 881484862063406293 639069684257 checked_small_1445888 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1446912 879617160434778556 636364414909 880239645570443282 637265414959 2048 881484862063406293 639069684257 checked_small_1446912 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1447936 880239645570443282 637265414959 880862333902002580 638167346823 1024 881484862063406293 639069684257 checked_small_1447936 checked_small_1448960)))))))
#print axioms checked_part_1441792
private theorem checked_small_1449984 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1449984 1024 881484862063406293 639069684257 882107320928949948 639972558621 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1451008 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1451008 1024 882107320928949948 639972558621 882729968609303065 640876344485 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1452032 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1452032 1024 882729968609303065 640876344485 883352216240847361 641780186785 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1453056 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1453056 1024 883352216240847361 641780186785 883974752926228196 642685086295 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1454080 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1454080 1024 883974752926228196 642685086295 884597423942617962 643590818769 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1455104 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1455104 1024 884597423942617962 643590818769 885219880757775994 644496877107 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1456128 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1456128 1024 885219880757775994 644496877107 885842426732011895 645403702697 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1457152 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1457152 1024 885842426732011895 645403702697 886464985341826259 646311184233 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1449984 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1449984 8192 881484862063406293 639069684257 886464985341826259 646311184233 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1449984 881484862063406293 639069684257 882107320928949948 639972558621 7168 886464985341826259 646311184233 checked_small_1449984 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1451008 882107320928949948 639972558621 882729968609303065 640876344485 6144 886464985341826259 646311184233 checked_small_1451008 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1452032 882729968609303065 640876344485 883352216240847361 641780186785 5120 886464985341826259 646311184233 checked_small_1452032 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1453056 883352216240847361 641780186785 883974752926228196 642685086295 4096 886464985341826259 646311184233 checked_small_1453056 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1454080 883974752926228196 642685086295 884597423942617962 643590818769 3072 886464985341826259 646311184233 checked_small_1454080 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1455104 884597423942617962 643590818769 885219880757775994 644496877107 2048 886464985341826259 646311184233 checked_small_1455104 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1456128 885219880757775994 644496877107 885842426732011895 645403702697 1024 886464985341826259 646311184233 checked_small_1456128 checked_small_1457152)))))))
#print axioms checked_part_1449984
private theorem checked_small_1458176 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1458176 1024 886464985341826259 646311184233 887087293525077418 647218937885 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1459200 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1459200 1024 887087293525077418 647218937885 887709976605772216 648127876005 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1460224 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1460224 1024 887709976605772216 648127876005 888332623317303086 649037398779 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1461248 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1461248 1024 888332623317303086 649037398779 888954893662888118 649947008923 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1462272 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1462272 1024 888954893662888118 649947008923 889577403197064177 650857606021 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1463296 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1463296 1024 889577403197064177 650857606021 890200119675895874 651769143597 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1464320 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1464320 1024 890200119675895874 651769143597 890822579743527642 652680943305 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1465344 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1465344 1024 890822579743527642 652680943305 891444931842879802 653593222031 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1458176 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1458176 8192 886464985341826259 646311184233 891444931842879802 653593222031 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1458176 886464985341826259 646311184233 887087293525077418 647218937885 7168 891444931842879802 653593222031 checked_small_1458176 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1459200 887087293525077418 647218937885 887709976605772216 648127876005 6144 891444931842879802 653593222031 checked_small_1459200 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1460224 887709976605772216 648127876005 888332623317303086 649037398779 5120 891444931842879802 653593222031 checked_small_1460224 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1461248 888332623317303086 649037398779 888954893662888118 649947008923 4096 891444931842879802 653593222031 checked_small_1461248 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1462272 888954893662888118 649947008923 889577403197064177 650857606021 3072 891444931842879802 653593222031 checked_small_1462272 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1463296 889577403197064177 650857606021 890200119675895874 651769143597 2048 891444931842879802 653593222031 checked_small_1463296 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1464320 890200119675895874 651769143597 890822579743527642 652680943305 1024 891444931842879802 653593222031 checked_small_1464320 checked_small_1465344)))))))
#print axioms checked_part_1458176
private theorem checked_small_1466368 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1466368 1024 891444931842879802 653593222031 892067612162646630 654506619507 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1467392 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1467392 1024 892067612162646630 654506619507 892689912308180948 655420096517 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1468416 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1468416 1024 892689912308180948 655420096517 893312469382618476 656334588087 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1469440 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1469440 1024 893312469382618476 656334588087 893935358006609060 657250204723 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1470464 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1470464 1024 893935358006609060 657250204723 894557630553264380 658165553033 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1471488 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1471488 1024 894557630553264380 658165553033 895180197848167959 659081972313 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1472512 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1472512 1024 895180197848167959 659081972313 895802717816842220 659998959419 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1473536 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1473536 1024 895802717816842220 659998959419 896425183295121085 660916503635 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1466368 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1466368 8192 891444931842879802 653593222031 896425183295121085 660916503635 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1466368 891444931842879802 653593222031 892067612162646630 654506619507 7168 896425183295121085 660916503635 checked_small_1466368 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1467392 892067612162646630 654506619507 892689912308180948 655420096517 6144 896425183295121085 660916503635 checked_small_1467392 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1468416 892689912308180948 655420096517 893312469382618476 656334588087 5120 896425183295121085 660916503635 checked_small_1468416 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1469440 893312469382618476 656334588087 893935358006609060 657250204723 4096 896425183295121085 660916503635 checked_small_1469440 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1470464 893935358006609060 657250204723 894557630553264380 658165553033 3072 896425183295121085 660916503635 checked_small_1470464 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1471488 894557630553264380 658165553033 895180197848167959 659081972313 2048 896425183295121085 660916503635 checked_small_1471488 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1472512 895180197848167959 659081972313 895802717816842220 659998959419 1024 896425183295121085 660916503635 checked_small_1472512 checked_small_1473536)))))))
#print axioms checked_part_1466368
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1441792 32768 876504563314927222 631868728327 896425183295121085 660916503635 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1441792 876504563314927222 631868728327 881484862063406293 639069684257 24576 896425183295121085 660916503635 checked_part_1441792 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1449984 881484862063406293 639069684257 886464985341826259 646311184233 16384 896425183295121085 660916503635 checked_part_1449984 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1458176 886464985341826259 646311184233 891444931842879802 653593222031 8192 896425183295121085 660916503635 checked_part_1458176 checked_part_1466368)))
theorem block_sound :
    (896425183295121085 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1474560 ∧
     660916503635 = FrontierCheck209.triangle FactorFullCertificate209.phi 1474560) ∧
    ∀ t, 1441792 < t → t ≤ 1474560 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1441792 876504563314927222 631868728327 896425183295121085 660916503635 FullPrefix209_043.endpoint.1 FullPrefix209_043.endpoint.2 checked
theorem endpoint :
    896425183295121085 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1474560 ∧
    660916503635 = FrontierCheck209.triangle FactorFullCertificate209.phi 1474560 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1474560) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1441792
  · exact FullPrefix209_043.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_044
