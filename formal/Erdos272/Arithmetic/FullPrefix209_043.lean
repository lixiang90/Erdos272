module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_042

@[expose] public section
namespace JSP233.FullPrefix209_043
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1409024 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1409024 1024 856584120161432895 603473963141 857206511137909376 604351245815 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1410048 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1410048 1024 857206511137909376 604351245815 857829095583009168 605229438683 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1411072 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1411072 1024 857829095583009168 605229438683 858451662142938350 606108243897 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1412096 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1412096 1024 858451662142938350 606108243897 859074049085938410 606987432839 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1413120 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1413120 1024 859074049085938410 606987432839 859696784580280356 607867751871 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1414144 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1414144 1024 859696784580280356 607867751871 860319297174135852 608748393373 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1415168 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1415168 1024 860319297174135852 608748393373 860941608627842068 609629387471 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1416192 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1416192 1024 860941608627842068 609629387471 861564108384483206 610511285471 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1409024 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1409024 8192 856584120161432895 603473963141 861564108384483206 610511285471 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1409024 856584120161432895 603473963141 857206511137909376 604351245815 7168 861564108384483206 610511285471 checked_small_1409024 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1410048 857206511137909376 604351245815 857829095583009168 605229438683 6144 861564108384483206 610511285471 checked_small_1410048 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1411072 857829095583009168 605229438683 858451662142938350 606108243897 5120 861564108384483206 610511285471 checked_small_1411072 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1412096 858451662142938350 606108243897 859074049085938410 606987432839 4096 861564108384483206 610511285471 checked_small_1412096 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1413120 859074049085938410 606987432839 859696784580280356 607867751871 3072 861564108384483206 610511285471 checked_small_1413120 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1414144 859696784580280356 607867751871 860319297174135852 608748393373 2048 861564108384483206 610511285471 checked_small_1414144 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1415168 860319297174135852 608748393373 860941608627842068 609629387471 1024 861564108384483206 610511285471 checked_small_1415168 checked_small_1416192)))))))
#print axioms checked_part_1409024
private theorem checked_small_1417216 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1417216 1024 861564108384483206 610511285471 862186875162508524 611394199593 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1418240 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1418240 1024 862186875162508524 611394199593 862809200446556398 612277125091 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1419264 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1419264 1024 862809200446556398 612277125091 863431686369036847 613160915805 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1420288 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1420288 1024 863431686369036847 613160915805 864054468752849247 614045765277 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1421312 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1421312 1024 864054468752849247 614045765277 864676779247391971 614930581563 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1422336 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1422336 1024 864676779247391971 614930581563 865299140392706831 615816106979 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1423360 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1423360 1024 865299140392706831 615816106979 865921931156443723 616702881469 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1424384 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1424384 1024 865921931156443723 616702881469 866544360621228171 617589778985 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1417216 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1417216 8192 861564108384483206 610511285471 866544360621228171 617589778985 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1417216 861564108384483206 610511285471 862186875162508524 611394199593 7168 866544360621228171 617589778985 checked_small_1417216 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1418240 862186875162508524 611394199593 862809200446556398 612277125091 6144 866544360621228171 617589778985 checked_small_1418240 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1419264 862809200446556398 612277125091 863431686369036847 613160915805 5120 866544360621228171 617589778985 checked_small_1419264 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1420288 863431686369036847 613160915805 864054468752849247 614045765277 4096 866544360621228171 617589778985 checked_small_1420288 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1421312 864054468752849247 614045765277 864676779247391971 614930581563 3072 866544360621228171 617589778985 checked_small_1421312 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1422336 864676779247391971 614930581563 865299140392706831 615816106979 2048 866544360621228171 617589778985 checked_small_1422336 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1423360 865299140392706831 615816106979 865921931156443723 616702881469 1024 866544360621228171 617589778985 checked_small_1423360 checked_small_1424384)))))))
#print axioms checked_part_1417216
private theorem checked_small_1425408 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1425408 1024 866544360621228171 617589778985 867166865202228101 618477420921 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1426432 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1426432 1024 867166865202228101 618477420921 867789442533156082 619365804137 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1427456 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1427456 1024 867789442533156082 619365804137 868411824319251547 620254545601 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1428480 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1428480 1024 868411824319251547 620254545601 869034529111869005 621144385987 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1429504 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1429504 1024 869034529111869005 621144385987 869657064474592690 622034621837 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1430528 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1430528 1024 869657064474592690 622034621837 870279392626400677 622925198551 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1431552 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1431552 1024 870279392626400677 622925198551 870901880446373460 623816641073 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1432576 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1432576 1024 870901880446373460 623816641073 871524531362902325 624708954807 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1425408 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1425408 8192 866544360621228171 617589778985 871524531362902325 624708954807 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1425408 866544360621228171 617589778985 867166865202228101 618477420921 7168 871524531362902325 624708954807 checked_small_1425408 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1426432 867166865202228101 618477420921 867789442533156082 619365804137 6144 871524531362902325 624708954807 checked_small_1426432 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1427456 867789442533156082 619365804137 868411824319251547 620254545601 5120 871524531362902325 624708954807 checked_small_1427456 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1428480 868411824319251547 620254545601 869034529111869005 621144385987 4096 871524531362902325 624708954807 checked_small_1428480 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1429504 869034529111869005 621144385987 869657064474592690 622034621837 3072 871524531362902325 624708954807 checked_small_1429504 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1430528 869657064474592690 622034621837 870279392626400677 622925198551 2048 871524531362902325 624708954807 checked_small_1430528 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1431552 870279392626400677 622925198551 870901880446373460 623816641073 1024 871524531362902325 624708954807 checked_small_1431552 checked_small_1432576)))))))
#print axioms checked_part_1425408
private theorem checked_small_1433600 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1433600 1024 871524531362902325 624708954807 872147090002407302 625601773889 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1434624 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1434624 1024 872147090002407302 625601773889 872769487976107551 626494999853 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1435648 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1435648 1024 872769487976107551 626494999853 873392236215637685 627389366243 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1436672 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1436672 1024 873392236215637685 627389366243 874014396544633293 628283525329 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1437696 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1437696 1024 874014396544633293 628283525329 874636962053276066 629178904081 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1438720 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1438720 1024 874636962053276066 629178904081 875259810057353830 630075327111 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1439744 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1439744 1024 875259810057353830 630075327111 875882042584050077 630971501517 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1440768 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1440768 1024 875882042584050077 630971501517 876504563314927222 631868728327 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1433600 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1433600 8192 871524531362902325 624708954807 876504563314927222 631868728327 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1433600 871524531362902325 624708954807 872147090002407302 625601773889 7168 876504563314927222 631868728327 checked_small_1433600 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1434624 872147090002407302 625601773889 872769487976107551 626494999853 6144 876504563314927222 631868728327 checked_small_1434624 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1435648 872769487976107551 626494999853 873392236215637685 627389366243 5120 876504563314927222 631868728327 checked_small_1435648 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1436672 873392236215637685 627389366243 874014396544633293 628283525329 4096 876504563314927222 631868728327 checked_small_1436672 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1437696 874014396544633293 628283525329 874636962053276066 629178904081 3072 876504563314927222 631868728327 checked_small_1437696 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1438720 874636962053276066 629178904081 875259810057353830 630075327111 2048 876504563314927222 631868728327 checked_small_1438720 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1439744 875259810057353830 630075327111 875882042584050077 630971501517 1024 876504563314927222 631868728327 checked_small_1439744 checked_small_1440768)))))))
#print axioms checked_part_1433600
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1409024 32768 856584120161432895 603473963141 876504563314927222 631868728327 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1409024 856584120161432895 603473963141 861564108384483206 610511285471 24576 876504563314927222 631868728327 checked_part_1409024 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1417216 861564108384483206 610511285471 866544360621228171 617589778985 16384 876504563314927222 631868728327 checked_part_1417216 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1425408 866544360621228171 617589778985 871524531362902325 624708954807 8192 876504563314927222 631868728327 checked_part_1425408 checked_part_1433600)))
theorem block_sound :
    (876504563314927222 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1441792 ∧
     631868728327 = FrontierCheck209.triangle FactorFullCertificate209.phi 1441792) ∧
    ∀ t, 1409024 < t → t ≤ 1441792 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1409024 856584120161432895 603473963141 876504563314927222 631868728327 FullPrefix209_042.endpoint.1 FullPrefix209_042.endpoint.2 checked
theorem endpoint :
    876504563314927222 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1441792 ∧
    631868728327 = FrontierCheck209.triangle FactorFullCertificate209.phi 1441792 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1441792) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1409024
  · exact FullPrefix209_042.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_043
