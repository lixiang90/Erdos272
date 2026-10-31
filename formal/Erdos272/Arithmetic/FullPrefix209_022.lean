import Erdos272.Certificates.ForcedDual209
import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_021
namespace JSP233.FullPrefix209_022
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_720896 : DualFrontier209.checkFrom FactorFullCertificate209.phi 720896 1024 438252410682460218 157967275095 438874845571871228 158416304759 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_721920 : DualFrontier209.checkFrom FactorFullCertificate209.phi 721920 1024 438874845571871228 158416304759 439497453442119675 158866096769 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_722944 : DualFrontier209.checkFrom FactorFullCertificate209.phi 722944 1024 439497453442119675 158866096769 440120076744227640 159316537595 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_723968 : DualFrontier209.checkFrom FactorFullCertificate209.phi 723968 1024 440120076744227640 159316537595 440742486786418029 159767461483 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_724992 : DualFrontier209.checkFrom FactorFullCertificate209.phi 724992 1024 440742486786418029 159767461483 441364935153271336 160219050435 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_726016 : DualFrontier209.checkFrom FactorFullCertificate209.phi 726016 1024 441364935153271336 160219050435 441987654458704492 160671473687 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_727040 : DualFrontier209.checkFrom FactorFullCertificate209.phi 727040 1024 441987654458704492 160671473687 442610045943457952 161124296133 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_728064 : DualFrontier209.checkFrom FactorFullCertificate209.phi 728064 1024 442610045943457952 161124296133 443232514494023228 161577811969 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_720896 : DualFrontier209.checkFrom FactorFullCertificate209.phi 720896 8192 438252410682460218 157967275095 443232514494023228 161577811969 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 720896 438252410682460218 157967275095 438874845571871228 158416304759 7168 443232514494023228 161577811969 checked_small_720896 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 721920 438874845571871228 158416304759 439497453442119675 158866096769 6144 443232514494023228 161577811969 checked_small_721920 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 722944 439497453442119675 158866096769 440120076744227640 159316537595 5120 443232514494023228 161577811969 checked_small_722944 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 723968 440120076744227640 159316537595 440742486786418029 159767461483 4096 443232514494023228 161577811969 checked_small_723968 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 724992 440742486786418029 159767461483 441364935153271336 160219050435 3072 443232514494023228 161577811969 checked_small_724992 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 726016 441364935153271336 160219050435 441987654458704492 160671473687 2048 443232514494023228 161577811969 checked_small_726016 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 727040 441987654458704492 160671473687 442610045943457952 161124296133 1024 443232514494023228 161577811969 checked_small_727040 checked_small_728064)))))))
#print axioms checked_part_720896
private theorem checked_small_729088 : DualFrontier209.checkFrom FactorFullCertificate209.phi 729088 1024 443232514494023228 161577811969 443855225914620370 162032142481 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_730112 : DualFrontier209.checkFrom FactorFullCertificate209.phi 730112 1024 443855225914620370 162032142481 444477490590115033 162486784219 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_731136 : DualFrontier209.checkFrom FactorFullCertificate209.phi 731136 1024 444477490590115033 162486784219 445099915552575019 162942180255 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_732160 : DualFrontier209.checkFrom FactorFullCertificate209.phi 732160 1024 445099915552575019 162942180255 445722818386707695 163398563927 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_733184 : DualFrontier209.checkFrom FactorFullCertificate209.phi 733184 1024 445722818386707695 163398563927 446345169525747193 163855180789 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_734208 : DualFrontier209.checkFrom FactorFullCertificate209.phi 734208 1024 446345169525747193 163855180789 446967586762971486 164312483363 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_735232 : DualFrontier209.checkFrom FactorFullCertificate209.phi 735232 1024 446967586762971486 164312483363 447590115398104601 164770505207 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_736256 : DualFrontier209.checkFrom FactorFullCertificate209.phi 736256 1024 447590115398104601 164770505207 448212606268015017 165229136689 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_729088 : DualFrontier209.checkFrom FactorFullCertificate209.phi 729088 8192 443232514494023228 161577811969 448212606268015017 165229136689 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 729088 443232514494023228 161577811969 443855225914620370 162032142481 7168 448212606268015017 165229136689 checked_small_729088 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 730112 443855225914620370 162032142481 444477490590115033 162486784219 6144 448212606268015017 165229136689 checked_small_730112 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 731136 444477490590115033 162486784219 445099915552575019 162942180255 5120 448212606268015017 165229136689 checked_small_731136 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 732160 445099915552575019 162942180255 445722818386707695 163398563927 4096 448212606268015017 165229136689 checked_small_732160 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 733184 445722818386707695 163398563927 446345169525747193 163855180789 3072 448212606268015017 165229136689 checked_small_733184 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 734208 446345169525747193 163855180789 446967586762971486 164312483363 2048 448212606268015017 165229136689 checked_small_734208 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 735232 446967586762971486 164312483363 447590115398104601 164770505207 1024 448212606268015017 165229136689 checked_small_735232 checked_small_736256)))))))
#print axioms checked_part_729088
private theorem checked_small_737280 : DualFrontier209.checkFrom FactorFullCertificate209.phi 737280 1024 448212606268015017 165229136689 448835205017016285 165688485219 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_738304 : DualFrontier209.checkFrom FactorFullCertificate209.phi 738304 1024 448835205017016285 165688485219 449457815289943606 166148479899 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_739328 : DualFrontier209.checkFrom FactorFullCertificate209.phi 739328 1024 449457815289943606 166148479899 450080182694257402 166608932411 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_740352 : DualFrontier209.checkFrom FactorFullCertificate209.phi 740352 1024 450080182694257402 166608932411 450702779763695294 167070192343 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_741376 : DualFrontier209.checkFrom FactorFullCertificate209.phi 741376 1024 450702779763695294 167070192343 451325358293430865 167532076137 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_742400 : DualFrontier209.checkFrom FactorFullCertificate209.phi 742400 1024 451325358293430865 167532076137 451947870533294261 167994548227 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_743424 : DualFrontier209.checkFrom FactorFullCertificate209.phi 743424 1024 451947870533294261 167994548227 452570166583793710 168457496831 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_744448 : DualFrontier209.checkFrom FactorFullCertificate209.phi 744448 1024 452570166583793710 168457496831 453192878189860225 168921392221 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_737280 : DualFrontier209.checkFrom FactorFullCertificate209.phi 737280 8192 448212606268015017 165229136689 453192878189860225 168921392221 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 737280 448212606268015017 165229136689 448835205017016285 165688485219 7168 453192878189860225 168921392221 checked_small_737280 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 738304 448835205017016285 165688485219 449457815289943606 166148479899 6144 453192878189860225 168921392221 checked_small_738304 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 739328 449457815289943606 166148479899 450080182694257402 166608932411 5120 453192878189860225 168921392221 checked_small_739328 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 740352 450080182694257402 166608932411 450702779763695294 167070192343 4096 453192878189860225 168921392221 checked_small_740352 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 741376 450702779763695294 167070192343 451325358293430865 167532076137 3072 453192878189860225 168921392221 checked_small_741376 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 742400 451325358293430865 167532076137 451947870533294261 167994548227 2048 453192878189860225 168921392221 checked_small_742400 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 743424 451947870533294261 167994548227 452570166583793710 168457496831 1024 453192878189860225 168921392221 checked_small_743424 checked_small_744448)))))))
#print axioms checked_part_737280
private theorem checked_small_745472 : DualFrontier209.checkFrom FactorFullCertificate209.phi 745472 1024 453192878189860225 168921392221 453815214482422831 169385645301 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_746496 : DualFrontier209.checkFrom FactorFullCertificate209.phi 746496 1024 453815214482422831 169385645301 454437787710924376 169850712583 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_747520 : DualFrontier209.checkFrom FactorFullCertificate209.phi 747520 1024 454437787710924376 169850712583 455060537911621209 170316549903 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_748544 : DualFrontier209.checkFrom FactorFullCertificate209.phi 748544 1024 455060537911621209 170316549903 455682823456352853 170782676865 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_749568 : DualFrontier209.checkFrom FactorFullCertificate209.phi 749568 1024 455682823456352853 170782676865 456305418817728259 171249673361 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_750592 : DualFrontier209.checkFrom FactorFullCertificate209.phi 750592 1024 456305418817728259 171249673361 456928078844874009 171717356077 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_751616 : DualFrontier209.checkFrom FactorFullCertificate209.phi 751616 1024 456928078844874009 171717356077 457550376575649760 172185403861 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_752640 : DualFrontier209.checkFrom FactorFullCertificate209.phi 752640 1024 457550376575649760 172185403861 458172948572179690 172654295365 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_745472 : DualFrontier209.checkFrom FactorFullCertificate209.phi 745472 8192 453192878189860225 168921392221 458172948572179690 172654295365 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 745472 453192878189860225 168921392221 453815214482422831 169385645301 7168 458172948572179690 172654295365 checked_small_745472 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 746496 453815214482422831 169385645301 454437787710924376 169850712583 6144 458172948572179690 172654295365 checked_small_746496 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 747520 454437787710924376 169850712583 455060537911621209 170316549903 5120 458172948572179690 172654295365 checked_small_747520 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 748544 455060537911621209 170316549903 455682823456352853 170782676865 4096 458172948572179690 172654295365 checked_small_748544 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 749568 455682823456352853 170782676865 456305418817728259 171249673361 3072 458172948572179690 172654295365 checked_small_749568 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 750592 456305418817728259 171249673361 456928078844874009 171717356077 2048 458172948572179690 172654295365 checked_small_750592 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 751616 456928078844874009 171717356077 457550376575649760 172185403861 1024 458172948572179690 172654295365 checked_small_751616 checked_small_752640)))))))
#print axioms checked_part_745472
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 720896 32768 438252410682460218 157967275095 458172948572179690 172654295365 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 720896 438252410682460218 157967275095 443232514494023228 161577811969 24576 458172948572179690 172654295365 checked_part_720896 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 729088 443232514494023228 161577811969 448212606268015017 165229136689 16384 458172948572179690 172654295365 checked_part_729088 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 737280 448212606268015017 165229136689 453192878189860225 168921392221 8192 458172948572179690 172654295365 checked_part_737280 checked_part_745472)))
theorem block_sound :
    (458172948572179690 = FrontierCheck209.massFloor FactorFullCertificate209.phi 753664 ∧
     172654295365 = FrontierCheck209.triangle FactorFullCertificate209.phi 753664) ∧
    ∀ t, 720896 < t → t ≤ 753664 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 720896 438252410682460218 157967275095 458172948572179690 172654295365 FullPrefix209_021.endpoint.1 FullPrefix209_021.endpoint.2 checked
theorem endpoint :
    458172948572179690 = FrontierCheck209.massFloor FactorFullCertificate209.phi 753664 ∧
    172654295365 = FrontierCheck209.triangle FactorFullCertificate209.phi 753664 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 753664) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 720896
  · exact FullPrefix209_021.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_022
