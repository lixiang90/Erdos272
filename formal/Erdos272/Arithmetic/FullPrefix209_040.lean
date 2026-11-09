module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_039

@[expose] public section
namespace JSP233.FullPrefix209_040
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1310720 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1310720 1024 796822517763135821 522205806305 797444869517086274 523021854069 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1311744 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1311744 1024 797444869517086274 523021854069 798067329074302163 523838680471 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1312768 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1312768 1024 798067329074302163 523838680471 798690139167925808 524656604745 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1313792 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1313792 1024 798690139167925808 524656604745 799312432372285709 525474487461 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1314816 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1314816 1024 799312432372285709 525474487461 799934872097473513 526293199977 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1315840 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1315840 1024 799934872097473513 526293199977 800557637949826961 527112979261 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1316864 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1316864 1024 800557637949826961 527112979261 801179985060154080 527932844655 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1317888 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1317888 1024 801179985060154080 527932844655 801802481267420958 528753543803 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1310720 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1310720 8192 796822517763135821 522205806305 801802481267420958 528753543803 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1310720 796822517763135821 522205806305 797444869517086274 523021854069 7168 801802481267420958 528753543803 checked_small_1310720 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1311744 797444869517086274 523021854069 798067329074302163 523838680471 6144 801802481267420958 528753543803 checked_small_1311744 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1312768 798067329074302163 523838680471 798690139167925808 524656604745 5120 801802481267420958 528753543803 checked_small_1312768 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1313792 798690139167925808 524656604745 799312432372285709 525474487461 4096 801802481267420958 528753543803 checked_small_1313792 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1314816 799312432372285709 525474487461 799934872097473513 526293199977 3072 801802481267420958 528753543803 checked_small_1314816 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1315840 799934872097473513 526293199977 800557637949826961 527112979261 2048 801802481267420958 528753543803 checked_small_1315840 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1316864 800557637949826961 527112979261 801179985060154080 527932844655 1024 801802481267420958 528753543803 checked_small_1316864 checked_small_1317888)))))))
#print axioms checked_part_1310720
private theorem checked_small_1318912 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1318912 1024 801802481267420958 528753543803 802425114735678983 529575061537 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1319936 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1319936 1024 802425114735678983 529575061537 803047451075722867 530396824473 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1320960 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1320960 1024 803047451075722867 530396824473 803670156853409611 531219712889 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1321984 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1321984 1024 803670156853409611 531219712889 804292663933583528 532042976267 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1323008 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1323008 1024 804292663933583528 532042976267 804915133035260081 532866826797 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1324032 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1324032 1024 804915133035260081 532866826797 805537542518158503 533691235687 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1325056 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1325056 1024 805537542518158503 533691235687 806160260120596511 534516690409 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1326080 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1326080 1024 806160260120596511 534516690409 806782802685565768 535342550703 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1318912 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1318912 8192 801802481267420958 528753543803 806782802685565768 535342550703 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1318912 801802481267420958 528753543803 802425114735678983 529575061537 7168 806782802685565768 535342550703 checked_small_1318912 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1319936 802425114735678983 529575061537 803047451075722867 530396824473 6144 806782802685565768 535342550703 checked_small_1319936 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1320960 803047451075722867 530396824473 803670156853409611 531219712889 5120 806782802685565768 535342550703 checked_small_1320960 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1321984 803670156853409611 531219712889 804292663933583528 532042976267 4096 806782802685565768 535342550703 checked_small_1321984 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1323008 804292663933583528 532042976267 804915133035260081 532866826797 3072 806782802685565768 535342550703 checked_small_1323008 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1324032 804915133035260081 532866826797 805537542518158503 533691235687 2048 806782802685565768 535342550703 checked_small_1324032 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1325056 805537542518158503 533691235687 806160260120596511 534516690409 1024 806782802685565768 535342550703 checked_small_1325056 checked_small_1326080)))))))
#print axioms checked_part_1318912
private theorem checked_small_1327104 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1327104 1024 806782802685565768 535342550703 807405184629875239 536168835183 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1328128 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1328128 1024 807405184629875239 536168835183 808027883322015162 536996177851 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1329152 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1329152 1024 808027883322015162 536996177851 808650009345704170 537823396595 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1330176 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1330176 1024 808650009345704170 537823396595 809272611283230713 538651885533 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1331200 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1331200 1024 809272611283230713 538651885533 809895464211247820 539481346475 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1332224 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1332224 1024 809895464211247820 539481346475 810517745944890341 540310684019 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1333248 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1333248 1024 810517745944890341 540310684019 811140273229788888 541140986175 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1334272 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1334272 1024 811140273229788888 541140986175 811762947246893470 541972121735 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1327104 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1327104 8192 806782802685565768 535342550703 811762947246893470 541972121735 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1327104 806782802685565768 535342550703 807405184629875239 536168835183 7168 811762947246893470 541972121735 checked_small_1327104 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1328128 807405184629875239 536168835183 808027883322015162 536996177851 6144 811762947246893470 541972121735 checked_small_1328128 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1329152 808027883322015162 536996177851 808650009345704170 537823396595 5120 811762947246893470 541972121735 checked_small_1329152 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1330176 808650009345704170 537823396595 809272611283230713 538651885533 4096 811762947246893470 541972121735 checked_small_1330176 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1331200 809272611283230713 538651885533 809895464211247820 539481346475 3072 811762947246893470 541972121735 checked_small_1331200 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1332224 809895464211247820 539481346475 810517745944890341 540310684019 2048 811762947246893470 541972121735 checked_small_1332224 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1333248 810517745944890341 540310684019 811140273229788888 541140986175 1024 811762947246893470 541972121735 checked_small_1333248 checked_small_1334272)))))))
#print axioms checked_part_1327104
private theorem checked_small_1335296 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1335296 1024 811762947246893470 541972121735 812385321150757827 542803494033 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1336320 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1336320 1024 812385321150757827 542803494033 813007859862651229 543635723895 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1337344 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1337344 1024 813007859862651229 543635723895 813630474592915818 544468693001 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1338368 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1338368 1024 813630474592915818 544468693001 814252880853617938 545302020539 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1339392 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1339392 1024 814252880853617938 545302020539 814875306237057072 546136010941 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1340416 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1340416 1024 814875306237057072 546136010941 815497953038186062 546970935631 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1341440 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1341440 1024 815497953038186062 546970935631 816120474428527796 547806329685 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1342464 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1342464 1024 816120474428527796 547806329685 816742972594356337 548642329997 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1335296 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1335296 8192 811762947246893470 541972121735 816742972594356337 548642329997 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1335296 811762947246893470 541972121735 812385321150757827 542803494033 7168 816742972594356337 548642329997 checked_small_1335296 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1336320 812385321150757827 542803494033 813007859862651229 543635723895 6144 816742972594356337 548642329997 checked_small_1336320 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1337344 813007859862651229 543635723895 813630474592915818 544468693001 5120 816742972594356337 548642329997 checked_small_1337344 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1338368 813630474592915818 544468693001 814252880853617938 545302020539 4096 816742972594356337 548642329997 checked_small_1338368 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1339392 814252880853617938 545302020539 814875306237057072 546136010941 3072 816742972594356337 548642329997 checked_small_1339392 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1340416 814875306237057072 546136010941 815497953038186062 546970935631 2048 816742972594356337 548642329997 checked_small_1340416 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1341440 815497953038186062 546970935631 816120474428527796 547806329685 1024 816742972594356337 548642329997 checked_small_1341440 checked_small_1342464)))))))
#print axioms checked_part_1335296
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1310720 32768 796822517763135821 522205806305 816742972594356337 548642329997 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1310720 796822517763135821 522205806305 801802481267420958 528753543803 24576 816742972594356337 548642329997 checked_part_1310720 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1318912 801802481267420958 528753543803 806782802685565768 535342550703 16384 816742972594356337 548642329997 checked_part_1318912 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1327104 806782802685565768 535342550703 811762947246893470 541972121735 8192 816742972594356337 548642329997 checked_part_1327104 checked_part_1335296)))
theorem block_sound :
    (816742972594356337 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1343488 ∧
     548642329997 = FrontierCheck209.triangle FactorFullCertificate209.phi 1343488) ∧
    ∀ t, 1310720 < t → t ≤ 1343488 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1310720 796822517763135821 522205806305 816742972594356337 548642329997 FullPrefix209_039.endpoint.1 FullPrefix209_039.endpoint.2 checked
theorem endpoint :
    816742972594356337 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1343488 ∧
    548642329997 = FrontierCheck209.triangle FactorFullCertificate209.phi 1343488 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1343488) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1310720
  · exact FullPrefix209_039.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_040
