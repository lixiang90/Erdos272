module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_036

@[expose] public section
namespace JSP233.FullPrefix209_037
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1212416 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1212416 1024 737060773908577479 446812276329 737683181242882830 447567211787 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1213440 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1213440 1024 737683181242882830 447567211787 738305828394825272 448323075729 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1214464 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1214464 1024 738305828394825272 448323075729 738928288770810731 449079350371 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1215488 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1215488 1024 738928288770810731 449079350371 739550792628944783 449836315251 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1216512 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1216512 1024 739550792628944783 449836315251 740173279307114390 450593896641 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1217536 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1217536 1024 740173279307114390 450593896641 740795938872830544 451352326101 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1218560 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1218560 1024 740795938872830544 451352326101 741418406418178213 452111159127 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1219584 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1219584 1024 741418406418178213 452111159127 742040917822427064 452870683041 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1212416 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1212416 8192 737060773908577479 446812276329 742040917822427064 452870683041 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1212416 737060773908577479 446812276329 737683181242882830 447567211787 7168 742040917822427064 452870683041 checked_small_1212416 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1213440 737683181242882830 447567211787 738305828394825272 448323075729 6144 742040917822427064 452870683041 checked_small_1213440 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1214464 738305828394825272 448323075729 738928288770810731 449079350371 5120 742040917822427064 452870683041 checked_small_1214464 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1215488 738928288770810731 449079350371 739550792628944783 449836315251 4096 742040917822427064 452870683041 checked_small_1215488 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1216512 739550792628944783 449836315251 740173279307114390 450593896641 3072 742040917822427064 452870683041 checked_small_1216512 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1217536 740173279307114390 450593896641 740795938872830544 451352326101 2048 742040917822427064 452870683041 checked_small_1217536 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1218560 740795938872830544 451352326101 741418406418178213 452111159127 1024 742040917822427064 452870683041 checked_small_1218560 checked_small_1219584)))))))
#print axioms checked_part_1212416
private theorem checked_small_1220608 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1220608 1024 742040917822427064 452870683041 742663580417355394 453631029103 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1221632 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1221632 1024 742663580417355394 453631029103 743285885127778315 454391575349 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1222656 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1222656 1024 743285885127778315 454391575349 743908256675571034 455152840405 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1223680 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1223680 1024 743908256675571034 455152840405 744531137532490036 455915366371 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1224704 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1224704 1024 744531137532490036 455915366371 745153449605425547 456677833367 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1225728 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1225728 1024 745153449605425547 456677833367 745775990778982013 457441218455 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1226752 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1226752 1024 745775990778982013 457441218455 746398557367453106 458205272249 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1227776 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1227776 1024 746398557367453106 458205272249 747020960383707563 458969762605 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1220608 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1220608 8192 742040917822427064 452870683041 747020960383707563 458969762605 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1220608 742040917822427064 452870683041 742663580417355394 453631029103 7168 747020960383707563 458969762605 checked_small_1220608 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1221632 742663580417355394 453631029103 743285885127778315 454391575349 6144 747020960383707563 458969762605 checked_small_1221632 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1222656 743285885127778315 454391575349 743908256675571034 455152840405 5120 747020960383707563 458969762605 checked_small_1222656 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1223680 743908256675571034 455152840405 744531137532490036 455915366371 4096 747020960383707563 458969762605 checked_small_1223680 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1224704 744531137532490036 455915366371 745153449605425547 456677833367 3072 747020960383707563 458969762605 checked_small_1224704 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1225728 745153449605425547 456677833367 745775990778982013 457441218455 2048 747020960383707563 458969762605 checked_small_1225728 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1226752 745775990778982013 457441218455 746398557367453106 458205272249 1024 747020960383707563 458969762605 checked_small_1226752 checked_small_1227776)))))))
#print axioms checked_part_1220608
private theorem checked_small_1228800 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1228800 1024 747020960383707563 458969762605 747643573727888920 459735148847 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1229824 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1229824 1024 747643573727888920 459735148847 748266155310450063 460501133655 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1230848 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1230848 1024 748266155310450063 460501133655 748888499165576699 461267463197 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1231872 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1231872 1024 748888499165576699 461267463197 749510959159631391 462034573033 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1232896 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1232896 1024 749510959159631391 462034573033 750133685262811019 462802648565 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1233920 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1233920 1024 750133685262811019 462802648565 750756162519291239 463571054677 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1234944 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1234944 1024 750756162519291239 463571054677 751378659744345678 464340122837 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1235968 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1235968 1024 751378659744345678 464340122837 752001246990092461 465109939777 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1228800 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1228800 8192 747020960383707563 458969762605 752001246990092461 465109939777 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1228800 747020960383707563 458969762605 747643573727888920 459735148847 7168 752001246990092461 465109939777 checked_small_1228800 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1229824 747643573727888920 459735148847 748266155310450063 460501133655 6144 752001246990092461 465109939777 checked_small_1229824 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1230848 748266155310450063 460501133655 748888499165576699 461267463197 5120 752001246990092461 465109939777 checked_small_1230848 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1231872 748888499165576699 461267463197 749510959159631391 462034573033 4096 752001246990092461 465109939777 checked_small_1231872 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1232896 749510959159631391 462034573033 750133685262811019 462802648565 3072 752001246990092461 465109939777 checked_small_1232896 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1233920 750133685262811019 462802648565 750756162519291239 463571054677 2048 752001246990092461 465109939777 checked_small_1233920 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1234944 750756162519291239 463571054677 751378659744345678 464340122837 1024 752001246990092461 465109939777 checked_small_1234944 checked_small_1235968)))))))
#print axioms checked_part_1228800
private theorem checked_small_1236992 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1236992 1024 752001246990092461 465109939777 752623628521346181 465880139635 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1238016 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1238016 1024 752623628521346181 465880139635 753246074413461305 466651056415 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1239040 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1239040 1024 753246074413461305 466651056415 753868808795462014 467422968257 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1240064 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1240064 1024 753868808795462014 467422968257 754491202142964547 468195094745 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1241088 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1241088 1024 754491202142964547 468195094745 755113729647631802 468968025077 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1242112 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1242112 1024 755113729647631802 468968025077 755736344786782720 469741701829 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1243136 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1243136 1024 755736344786782720 469741701829 756358677701774463 470515665111 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1244160 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1244160 1024 756358677701774463 470515665111 756981283659662639 471290605451 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1236992 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1236992 8192 752001246990092461 465109939777 756981283659662639 471290605451 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1236992 752001246990092461 465109939777 752623628521346181 465880139635 7168 756981283659662639 471290605451 checked_small_1236992 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1238016 752623628521346181 465880139635 753246074413461305 466651056415 6144 756981283659662639 471290605451 checked_small_1238016 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1239040 753246074413461305 466651056415 753868808795462014 467422968257 5120 756981283659662639 471290605451 checked_small_1239040 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1240064 753868808795462014 467422968257 754491202142964547 468195094745 4096 756981283659662639 471290605451 checked_small_1240064 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1241088 754491202142964547 468195094745 755113729647631802 468968025077 3072 756981283659662639 471290605451 checked_small_1241088 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1242112 755113729647631802 468968025077 755736344786782720 469741701829 2048 756981283659662639 471290605451 checked_small_1242112 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1243136 755736344786782720 469741701829 756358677701774463 470515665111 1024 756981283659662639 471290605451 checked_small_1243136 checked_small_1244160)))))))
#print axioms checked_part_1236992
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1212416 32768 737060773908577479 446812276329 756981283659662639 471290605451 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1212416 737060773908577479 446812276329 742040917822427064 452870683041 24576 756981283659662639 471290605451 checked_part_1212416 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1220608 742040917822427064 452870683041 747020960383707563 458969762605 16384 756981283659662639 471290605451 checked_part_1220608 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1228800 747020960383707563 458969762605 752001246990092461 465109939777 8192 756981283659662639 471290605451 checked_part_1228800 checked_part_1236992)))
theorem block_sound :
    (756981283659662639 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1245184 ∧
     471290605451 = FrontierCheck209.triangle FactorFullCertificate209.phi 1245184) ∧
    ∀ t, 1212416 < t → t ≤ 1245184 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1212416 737060773908577479 446812276329 756981283659662639 471290605451 FullPrefix209_036.endpoint.1 FullPrefix209_036.endpoint.2 checked
theorem endpoint :
    756981283659662639 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1245184 ∧
    471290605451 = FrontierCheck209.triangle FactorFullCertificate209.phi 1245184 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1245184) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1212416
  · exact FullPrefix209_036.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_037
