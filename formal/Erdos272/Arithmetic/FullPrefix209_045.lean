import Erdos272.Certificates.ForcedDual209
import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_044
namespace JSP233.FullPrefix209_045
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1474560 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1474560 1024 896425183295121085 660916503635 897047715406652155 661834783531 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1475584 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1475584 1024 897047715406652155 661834783531 897670190153828131 662753616213 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1476608 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1476608 1024 897670190153828131 662753616213 898292716058871083 663673161861 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1477632 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1477632 1024 898292716058871083 663673161861 898915190532848560 664593268925 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1478656 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1478656 1024 898915190532848560 664593268925 899537854925775504 665514294383 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1479680 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1479680 1024 899537854925775504 665514294383 900160283216556109 666435607999 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1480704 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1480704 1024 900160283216556109 666435607999 900782737313097248 667357597129 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1481728 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1481728 1024 900782737313097248 667357597129 901405540393297638 668280741045 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1474560 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1474560 8192 896425183295121085 660916503635 901405540393297638 668280741045 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1474560 896425183295121085 660916503635 897047715406652155 661834783531 7168 901405540393297638 668280741045 checked_small_1474560 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1475584 897047715406652155 661834783531 897670190153828131 662753616213 6144 901405540393297638 668280741045 checked_small_1475584 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1476608 897670190153828131 662753616213 898292716058871083 663673161861 5120 901405540393297638 668280741045 checked_small_1476608 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1477632 898292716058871083 663673161861 898915190532848560 664593268925 4096 901405540393297638 668280741045 checked_small_1477632 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1478656 898915190532848560 664593268925 899537854925775504 665514294383 3072 901405540393297638 668280741045 checked_small_1478656 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1479680 899537854925775504 665514294383 900160283216556109 666435607999 2048 901405540393297638 668280741045 checked_small_1479680 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1480704 900160283216556109 666435607999 900782737313097248 667357597129 1024 901405540393297638 668280741045 checked_small_1480704 checked_small_1481728)))))))
#print axioms checked_part_1474560
private theorem checked_small_1482752 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1482752 1024 901405540393297638 668280741045 902027795330148794 669203709679 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1483776 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1483776 1024 902027795330148794 669203709679 902650210884082165 670127553717 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1484800 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1484800 1024 902650210884082165 670127553717 903273025297263343 671052627643 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1485824 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1485824 1024 903273025297263343 671052627643 903895478417390925 671977802449 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1486848 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1486848 1024 903895478417390925 671977802449 904517821582928231 672903450981 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1487872 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1487872 1024 904517821582928231 672903450981 905140464978492353 673830183627 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1488896 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1488896 1024 905140464978492353 673830183627 905762883891512370 674757219527 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1489920 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1489920 1024 905762883891512370 674757219527 906385493436336504 675685176903 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1482752 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1482752 8192 901405540393297638 668280741045 906385493436336504 675685176903 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1482752 901405540393297638 668280741045 902027795330148794 669203709679 7168 906385493436336504 675685176903 checked_small_1482752 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1483776 902027795330148794 669203709679 902650210884082165 670127553717 6144 906385493436336504 675685176903 checked_small_1483776 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1484800 902650210884082165 670127553717 903273025297263343 671052627643 5120 906385493436336504 675685176903 checked_small_1484800 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1485824 903273025297263343 671052627643 903895478417390925 671977802449 4096 906385493436336504 675685176903 checked_small_1485824 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1486848 903895478417390925 671977802449 904517821582928231 672903450981 3072 906385493436336504 675685176903 checked_small_1486848 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1487872 904517821582928231 672903450981 905140464978492353 673830183627 2048 906385493436336504 675685176903 checked_small_1487872 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1488896 905140464978492353 673830183627 905762883891512370 674757219527 1024 906385493436336504 675685176903 checked_small_1488896 checked_small_1489920)))))))
#print axioms checked_part_1482752
private theorem checked_small_1490944 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1490944 1024 906385493436336504 675685176903 907008107600419838 676613778819 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1491968 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1491968 1024 907008107600419838 676613778819 907630434532891830 677542589551 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1492992 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1492992 1024 907630434532891830 677542589551 908252984287825562 678472370253 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1494016 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1494016 1024 908252984287825562 678472370253 908875565000883305 679402834761 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1495040 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1495040 1024 908875565000883305 679402834761 909498062037601930 680333811675 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1496064 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1496064 1024 909498062037601930 680333811675 910120512802049812 681265356735 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1497088 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1497088 1024 910120512802049812 681265356735 910743108303815716 682197755943 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1498112 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1498112 1024 910743108303815716 682197755943 911365426495895235 683130377047 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1490944 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1490944 8192 906385493436336504 675685176903 911365426495895235 683130377047 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1490944 906385493436336504 675685176903 907008107600419838 676613778819 7168 911365426495895235 683130377047 checked_small_1490944 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1491968 907008107600419838 676613778819 907630434532891830 677542589551 6144 911365426495895235 683130377047 checked_small_1491968 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1492992 907630434532891830 677542589551 908252984287825562 678472370253 5120 911365426495895235 683130377047 checked_small_1492992 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1494016 908252984287825562 678472370253 908875565000883305 679402834761 4096 911365426495895235 683130377047 checked_small_1494016 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1495040 908875565000883305 679402834761 909498062037601930 680333811675 3072 911365426495895235 683130377047 checked_small_1495040 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1496064 909498062037601930 680333811675 910120512802049812 681265356735 2048 911365426495895235 683130377047 checked_small_1496064 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1497088 910120512802049812 681265356735 910743108303815716 682197755943 1024 911365426495895235 683130377047 checked_small_1497088 checked_small_1498112)))))))
#print axioms checked_part_1490944
private theorem checked_small_1499136 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1499136 1024 911365426495895235 683130377047 911988094747246189 684064160347 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1500160 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1500160 1024 911988094747246189 684064160347 912610795889197446 684998630787 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1501184 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1501184 1024 912610795889197446 684998630787 913233029870508792 685933037293 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1502208 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1502208 1024 913233029870508792 685933037293 913855585248660725 686868563811 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1503232 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1503232 1024 913855585248660725 686868563811 914478259181546817 687804906199 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1504256 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1504256 1024 914478259181546817 687804906199 915100632396723840 688741433697 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1505280 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1505280 1024 915100632396723840 688741433697 915723252903662497 689678970851 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1506304 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1506304 1024 915723252903662497 689678970851 916345865591926884 690617133889 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1499136 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1499136 8192 911365426495895235 683130377047 916345865591926884 690617133889 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1499136 911365426495895235 683130377047 911988094747246189 684064160347 7168 916345865591926884 690617133889 checked_small_1499136 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1500160 911988094747246189 684064160347 912610795889197446 684998630787 6144 916345865591926884 690617133889 checked_small_1500160 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1501184 912610795889197446 684998630787 913233029870508792 685933037293 5120 916345865591926884 690617133889 checked_small_1501184 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1502208 913233029870508792 685933037293 913855585248660725 686868563811 4096 916345865591926884 690617133889 checked_small_1502208 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1503232 913855585248660725 686868563811 914478259181546817 687804906199 3072 916345865591926884 690617133889 checked_small_1503232 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1504256 914478259181546817 687804906199 915100632396723840 688741433697 2048 916345865591926884 690617133889 checked_small_1504256 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1505280 915100632396723840 688741433697 915723252903662497 689678970851 1024 916345865591926884 690617133889 checked_small_1505280 checked_small_1506304)))))))
#print axioms checked_part_1499136
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1474560 32768 896425183295121085 660916503635 916345865591926884 690617133889 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1474560 896425183295121085 660916503635 901405540393297638 668280741045 24576 916345865591926884 690617133889 checked_part_1474560 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1482752 901405540393297638 668280741045 906385493436336504 675685176903 16384 916345865591926884 690617133889 checked_part_1482752 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1490944 906385493436336504 675685176903 911365426495895235 683130377047 8192 916345865591926884 690617133889 checked_part_1490944 checked_part_1499136)))
theorem block_sound :
    (916345865591926884 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1507328 ∧
     690617133889 = FrontierCheck209.triangle FactorFullCertificate209.phi 1507328) ∧
    ∀ t, 1474560 < t → t ≤ 1507328 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1474560 896425183295121085 660916503635 916345865591926884 690617133889 FullPrefix209_044.endpoint.1 FullPrefix209_044.endpoint.2 checked
theorem endpoint :
    916345865591926884 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1507328 ∧
    690617133889 = FrontierCheck209.triangle FactorFullCertificate209.phi 1507328 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1507328) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1474560
  · exact FullPrefix209_044.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_045
