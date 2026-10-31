import Erdos272.Certificates.ForcedDual209
import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_045
namespace JSP233.FullPrefix209_046
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1507328 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1507328 1024 916345865591926884 690617133889 916968280851338074 691555636791 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1508352 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1508352 1024 916968280851338074 691555636791 917590675868841975 692494746389 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1509376 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1509376 1024 917590675868841975 692494746389 918213328603672426 693434882453 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1510400 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1510400 1024 918213328603672426 693434882453 918835783281729777 694375356901 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1511424 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1511424 1024 918835783281729777 694375356901 919458243324731308 695316476789 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1512448 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1512448 1024 919458243324731308 695316476789 920080999556883196 696258682297 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1513472 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1513472 1024 920080999556883196 696258682297 920703272835582807 697200794319 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1514496 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1514496 1024 920703272835582807 697200794319 921325837553641488 698143984975 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1507328 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1507328 8192 916345865591926884 690617133889 921325837553641488 698143984975 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1507328 916345865591926884 690617133889 916968280851338074 691555636791 7168 921325837553641488 698143984975 checked_small_1507328 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1508352 916968280851338074 691555636791 917590675868841975 692494746389 6144 921325837553641488 698143984975 checked_small_1508352 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1509376 917590675868841975 692494746389 918213328603672426 693434882453 5120 921325837553641488 698143984975 checked_small_1509376 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1510400 918213328603672426 693434882453 918835783281729777 694375356901 4096 921325837553641488 698143984975 checked_small_1510400 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1511424 918835783281729777 694375356901 919458243324731308 695316476789 3072 921325837553641488 698143984975 checked_small_1511424 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1512448 919458243324731308 695316476789 920080999556883196 696258682297 2048 921325837553641488 698143984975 checked_small_1512448 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1513472 920080999556883196 696258682297 920703272835582807 697200794319 1024 921325837553641488 698143984975 checked_small_1513472 checked_small_1514496)))))))
#print axioms checked_part_1507328
private theorem checked_small_1515520 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1515520 1024 921325837553641488 698143984975 921948524685459113 699087998843 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1516544 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1516544 1024 921948524685459113 699087998843 922570886846293265 700032157345 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1517568 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1517568 1024 922570886846293265 700032157345 923193512068545341 700977352467 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1518592 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1518592 1024 923193512068545341 700977352467 923815973627906896 701922936569 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1519616 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1519616 1024 923815973627906896 701922936569 924438394889972828 702869096733 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1520640 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1520640 1024 924438394889972828 702869096733 925060990551042789 703816159537 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1521664 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1521664 1024 925060990551042789 703816159537 925683671307894287 704763989535 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1522688 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1522688 1024 925683671307894287 704763989535 926305881742724268 705711740695 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1515520 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1515520 8192 921325837553641488 698143984975 926305881742724268 705711740695 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1515520 921325837553641488 698143984975 921948524685459113 699087998843 7168 926305881742724268 705711740695 checked_small_1515520 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1516544 921948524685459113 699087998843 922570886846293265 700032157345 6144 926305881742724268 705711740695 checked_small_1516544 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1517568 922570886846293265 700032157345 923193512068545341 700977352467 5120 926305881742724268 705711740695 checked_small_1517568 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1518592 923193512068545341 700977352467 923815973627906896 701922936569 4096 926305881742724268 705711740695 checked_small_1518592 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1519616 923815973627906896 701922936569 924438394889972828 702869096733 3072 926305881742724268 705711740695 checked_small_1519616 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1520640 924438394889972828 702869096733 925060990551042789 703816159537 2048 926305881742724268 705711740695 checked_small_1520640 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1521664 925060990551042789 703816159537 925683671307894287 704763989535 1024 926305881742724268 705711740695 checked_small_1521664 checked_small_1522688)))))))
#print axioms checked_part_1515520
private theorem checked_small_1523712 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1523712 1024 926305881742724268 705711740695 926928400700338689 706660599087 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1524736 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1524736 1024 926928400700338689 706660599087 927551183101680953 707610496899 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1525760 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1525760 1024 927551183101680953 707610496899 928173636901139429 708560531005 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1526784 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1526784 1024 928173636901139429 708560531005 928796028906222089 709511108031 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1527808 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1527808 1024 928796028906222089 709511108031 929418835226971527 710462955677 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1528832 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1528832 1024 929418835226971527 710462955677 930041067617360683 711414563343 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1529856 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1529856 1024 930041067617360683 711414563343 930663581798461027 712367239267 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1530880 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1530880 1024 930663581798461027 712367239267 931286310507538142 713320881285 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1523712 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1523712 8192 926305881742724268 705711740695 931286310507538142 713320881285 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1523712 926305881742724268 705711740695 926928400700338689 706660599087 7168 931286310507538142 713320881285 checked_small_1523712 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1524736 926928400700338689 706660599087 927551183101680953 707610496899 6144 931286310507538142 713320881285 checked_small_1524736 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1525760 927551183101680953 707610496899 928173636901139429 708560531005 5120 931286310507538142 713320881285 checked_small_1525760 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1526784 928173636901139429 708560531005 928796028906222089 709511108031 4096 931286310507538142 713320881285 checked_small_1526784 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1527808 928796028906222089 709511108031 929418835226971527 710462955677 3072 931286310507538142 713320881285 checked_small_1527808 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1528832 929418835226971527 710462955677 930041067617360683 711414563343 2048 931286310507538142 713320881285 checked_small_1528832 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1529856 930041067617360683 711414563343 930663581798461027 712367239267 1024 931286310507538142 713320881285 checked_small_1529856 checked_small_1530880)))))))
#print axioms checked_part_1523712
private theorem checked_small_1531904 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1531904 1024 931286310507538142 713320881285 931908548506879419 714274408969 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1532928 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1532928 1024 931908548506879419 714274408969 932531194831638208 715229199891 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1533952 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1533952 1024 932531194831638208 715229199891 933153714035151761 716184433403 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1534976 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1534976 1024 933153714035151761 716184433403 933776192848006698 717140242339 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1536000 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1536000 1024 933776192848006698 717140242339 934398748889638020 718096807355 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1537024 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1537024 1024 934398748889638020 718096807355 935021337404916879 719054059857 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1538048 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1538048 1024 935021337404916879 719054059857 935643704385290990 720011609001 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1539072 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1539072 1024 935643704385290990 720011609001 936266290889349601 720970133385 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1531904 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1531904 8192 931286310507538142 713320881285 936266290889349601 720970133385 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1531904 931286310507538142 713320881285 931908548506879419 714274408969 7168 936266290889349601 720970133385 checked_small_1531904 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1532928 931908548506879419 714274408969 932531194831638208 715229199891 6144 936266290889349601 720970133385 checked_small_1532928 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1533952 932531194831638208 715229199891 933153714035151761 716184433403 5120 936266290889349601 720970133385 checked_small_1533952 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1534976 933153714035151761 716184433403 933776192848006698 717140242339 4096 936266290889349601 720970133385 checked_small_1534976 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1536000 933776192848006698 717140242339 934398748889638020 718096807355 3072 936266290889349601 720970133385 checked_small_1536000 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1537024 934398748889638020 718096807355 935021337404916879 719054059857 2048 936266290889349601 720970133385 checked_small_1537024 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1538048 935021337404916879 719054059857 935643704385290990 720011609001 1024 936266290889349601 720970133385 checked_small_1538048 checked_small_1539072)))))))
#print axioms checked_part_1531904
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1507328 32768 916345865591926884 690617133889 936266290889349601 720970133385 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1507328 916345865591926884 690617133889 921325837553641488 698143984975 24576 936266290889349601 720970133385 checked_part_1507328 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1515520 921325837553641488 698143984975 926305881742724268 705711740695 16384 936266290889349601 720970133385 checked_part_1515520 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1523712 926305881742724268 705711740695 931286310507538142 713320881285 8192 936266290889349601 720970133385 checked_part_1523712 checked_part_1531904)))
theorem block_sound :
    (936266290889349601 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1540096 ∧
     720970133385 = FrontierCheck209.triangle FactorFullCertificate209.phi 1540096) ∧
    ∀ t, 1507328 < t → t ≤ 1540096 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1507328 916345865591926884 690617133889 936266290889349601 720970133385 FullPrefix209_045.endpoint.1 FullPrefix209_045.endpoint.2 checked
theorem endpoint :
    936266290889349601 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1540096 ∧
    720970133385 = FrontierCheck209.triangle FactorFullCertificate209.phi 1540096 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1540096) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1507328
  · exact FullPrefix209_045.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_046
