import Erdos272.Certificates.ForcedDual209
import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_017
namespace JSP233.FullPrefix209_018
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_589824 : DualFrontier209.checkFrom FactorFullCertificate209.phi 589824 1024 358570226846222941 105746731133 359192707622242102 106114204163 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_590848 : DualFrontier209.checkFrom FactorFullCertificate209.phi 590848 1024 359192707622242102 106114204163 359815329586279728 106482398139 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_591872 : DualFrontier209.checkFrom FactorFullCertificate209.phi 591872 1024 359815329586279728 106482398139 360437562698148360 106850999245 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_592896 : DualFrontier209.checkFrom FactorFullCertificate209.phi 592896 1024 360437562698148360 106850999245 361060230104295442 107220495157 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_593920 : DualFrontier209.checkFrom FactorFullCertificate209.phi 593920 1024 361060230104295442 107220495157 361682965100214008 107590669047 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_594944 : DualFrontier209.checkFrom FactorFullCertificate209.phi 594944 1024 361682965100214008 107590669047 362305398043835317 107961300829 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_595968 : DualFrontier209.checkFrom FactorFullCertificate209.phi 595968 1024 362305398043835317 107961300829 362927847062575292 108332579487 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_596992 : DualFrontier209.checkFrom FactorFullCertificate209.phi 596992 1024 362927847062575292 108332579487 363550379486528585 108704545343 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_589824 : DualFrontier209.checkFrom FactorFullCertificate209.phi 589824 8192 358570226846222941 105746731133 363550379486528585 108704545343 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 589824 358570226846222941 105746731133 359192707622242102 106114204163 7168 363550379486528585 108704545343 checked_small_589824 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 590848 359192707622242102 106114204163 359815329586279728 106482398139 6144 363550379486528585 108704545343 checked_small_590848 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 591872 359815329586279728 106482398139 360437562698148360 106850999245 5120 363550379486528585 108704545343 checked_small_591872 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 592896 360437562698148360 106850999245 361060230104295442 107220495157 4096 363550379486528585 108704545343 checked_small_592896 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 593920 361060230104295442 107220495157 361682965100214008 107590669047 3072 363550379486528585 108704545343 checked_small_593920 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 594944 361682965100214008 107590669047 362305398043835317 107961300829 2048 363550379486528585 108704545343 checked_small_594944 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 595968 362305398043835317 107961300829 362927847062575292 108332579487 1024 363550379486528585 108704545343 checked_small_595968 checked_small_596992)))))))
#print axioms checked_part_589824
private theorem checked_small_598016 : DualFrontier209.checkFrom FactorFullCertificate209.phi 598016 1024 363550379486528585 108704545343 364172716792455090 109077031809 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_599040 : DualFrontier209.checkFrom FactorFullCertificate209.phi 599040 1024 364172716792455090 109077031809 364795411373758032 109450369749 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_600064 : DualFrontier209.checkFrom FactorFullCertificate209.phi 600064 1024 364795411373758032 109450369749 365417999982468482 109824281813 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_601088 : DualFrontier209.checkFrom FactorFullCertificate209.phi 601088 1024 365417999982468482 109824281813 366040350316513194 110198688011 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_602112 : DualFrontier209.checkFrom FactorFullCertificate209.phi 602112 1024 366040350316513194 110198688011 366662834515041779 110573812059 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_603136 : DualFrontier209.checkFrom FactorFullCertificate209.phi 603136 1024 366662834515041779 110573812059 367285541123902791 110949707875 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_604160 : DualFrontier209.checkFrom FactorFullCertificate209.phi 604160 1024 367285541123902791 110949707875 367908049576616500 111326121613 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_605184 : DualFrontier209.checkFrom FactorFullCertificate209.phi 605184 1024 367908049576616500 111326121613 368530359488356854 111703052429 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_598016 : DualFrontier209.checkFrom FactorFullCertificate209.phi 598016 8192 363550379486528585 108704545343 368530359488356854 111703052429 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 598016 363550379486528585 108704545343 364172716792455090 109077031809 7168 368530359488356854 111703052429 checked_small_598016 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 599040 364172716792455090 109077031809 364795411373758032 109450369749 6144 368530359488356854 111703052429 checked_small_599040 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 600064 364795411373758032 109450369749 365417999982468482 109824281813 5120 368530359488356854 111703052429 checked_small_600064 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 601088 365417999982468482 109824281813 366040350316513194 110198688011 4096 368530359488356854 111703052429 checked_small_601088 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 602112 366040350316513194 110198688011 366662834515041779 110573812059 3072 368530359488356854 111703052429 checked_small_602112 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 603136 366662834515041779 110573812059 367285541123902791 110949707875 2048 368530359488356854 111703052429 checked_small_603136 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 604160 367285541123902791 110949707875 367908049576616500 111326121613 1024 368530359488356854 111703052429 checked_small_604160 checked_small_605184)))))))
#print axioms checked_part_598016
private theorem checked_small_606208 : DualFrontier209.checkFrom FactorFullCertificate209.phi 606208 1024 368530359488356854 111703052429 369153079434824187 112080869269 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_607232 : DualFrontier209.checkFrom FactorFullCertificate209.phi 607232 1024 369153079434824187 112080869269 369775419145871458 112459092697 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_608256 : DualFrontier209.checkFrom FactorFullCertificate209.phi 608256 1024 369775419145871458 112459092697 370397875986290319 112838024589 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_609280 : DualFrontier209.checkFrom FactorFullCertificate209.phi 609280 1024 370397875986290319 112838024589 371020701223330231 113217818643 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_610304 : DualFrontier209.checkFrom FactorFullCertificate209.phi 610304 1024 371020701223330231 113217818643 371643034824520811 113597950237 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_611328 : DualFrontier209.checkFrom FactorFullCertificate209.phi 611328 1024 371643034824520811 113597950237 372265594983583388 113978857649 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_612352 : DualFrontier209.checkFrom FactorFullCertificate209.phi 612352 1024 372265594983583388 113978857649 372888162409542774 114360407057 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_613376 : DualFrontier209.checkFrom FactorFullCertificate209.phi 613376 1024 372888162409542774 114360407057 373510496499458876 114742450665 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_606208 : DualFrontier209.checkFrom FactorFullCertificate209.phi 606208 8192 368530359488356854 111703052429 373510496499458876 114742450665 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 606208 368530359488356854 111703052429 369153079434824187 112080869269 7168 373510496499458876 114742450665 checked_small_606208 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 607232 369153079434824187 112080869269 369775419145871458 112459092697 6144 373510496499458876 114742450665 checked_small_607232 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 608256 369775419145871458 112459092697 370397875986290319 112838024589 5120 373510496499458876 114742450665 checked_small_608256 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 609280 370397875986290319 112838024589 371020701223330231 113217818643 4096 373510496499458876 114742450665 checked_small_609280 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 610304 371020701223330231 113217818643 371643034824520811 113597950237 3072 373510496499458876 114742450665 checked_small_610304 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 611328 371643034824520811 113597950237 372265594983583388 113978857649 2048 373510496499458876 114742450665 checked_small_611328 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 612352 372265594983583388 113978857649 372888162409542774 114360407057 1024 373510496499458876 114742450665 checked_small_612352 checked_small_613376)))))))
#print axioms checked_part_606208
private theorem checked_small_614400 : DualFrontier209.checkFrom FactorFullCertificate209.phi 614400 1024 373510496499458876 114742450665 374133183102125609 115125348307 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_615424 : DualFrontier209.checkFrom FactorFullCertificate209.phi 615424 1024 374133183102125609 115125348307 374755689414927338 115508772611 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_616448 : DualFrontier209.checkFrom FactorFullCertificate209.phi 616448 1024 374755689414927338 115508772611 375378185046839537 115892827749 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_617472 : DualFrontier209.checkFrom FactorFullCertificate209.phi 617472 1024 375378185046839537 115892827749 376000639519296880 116277494841 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_618496 : DualFrontier209.checkFrom FactorFullCertificate209.phi 618496 1024 376000639519296880 116277494841 376623298348216494 116662925873 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_619520 : DualFrontier209.checkFrom FactorFullCertificate209.phi 619520 1024 376623298348216494 116662925873 377245632150788153 117048792957 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_620544 : DualFrontier209.checkFrom FactorFullCertificate209.phi 620544 1024 377245632150788153 117048792957 377868197571434969 117435441089 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_621568 : DualFrontier209.checkFrom FactorFullCertificate209.phi 621568 1024 377868197571434969 117435441089 378490858220726241 117822786067 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_614400 : DualFrontier209.checkFrom FactorFullCertificate209.phi 614400 8192 373510496499458876 114742450665 378490858220726241 117822786067 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 614400 373510496499458876 114742450665 374133183102125609 115125348307 7168 378490858220726241 117822786067 checked_small_614400 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 615424 374133183102125609 115125348307 374755689414927338 115508772611 6144 378490858220726241 117822786067 checked_small_615424 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 616448 374755689414927338 115508772611 375378185046839537 115892827749 5120 378490858220726241 117822786067 checked_small_616448 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 617472 375378185046839537 115892827749 376000639519296880 116277494841 4096 378490858220726241 117822786067 checked_small_617472 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 618496 376000639519296880 116277494841 376623298348216494 116662925873 3072 378490858220726241 117822786067 checked_small_618496 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 619520 376623298348216494 116662925873 377245632150788153 117048792957 2048 378490858220726241 117822786067 checked_small_619520 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 620544 377245632150788153 117048792957 377868197571434969 117435441089 1024 378490858220726241 117822786067 checked_small_620544 checked_small_621568)))))))
#print axioms checked_part_614400
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 589824 32768 358570226846222941 105746731133 378490858220726241 117822786067 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 589824 358570226846222941 105746731133 363550379486528585 108704545343 24576 378490858220726241 117822786067 checked_part_589824 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 598016 363550379486528585 108704545343 368530359488356854 111703052429 16384 378490858220726241 117822786067 checked_part_598016 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 606208 368530359488356854 111703052429 373510496499458876 114742450665 8192 378490858220726241 117822786067 checked_part_606208 checked_part_614400)))
theorem block_sound :
    (378490858220726241 = FrontierCheck209.massFloor FactorFullCertificate209.phi 622592 ∧
     117822786067 = FrontierCheck209.triangle FactorFullCertificate209.phi 622592) ∧
    ∀ t, 589824 < t → t ≤ 622592 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 589824 358570226846222941 105746731133 378490858220726241 117822786067 FullPrefix209_017.endpoint.1 FullPrefix209_017.endpoint.2 checked
theorem endpoint :
    378490858220726241 = FrontierCheck209.massFloor FactorFullCertificate209.phi 622592 ∧
    117822786067 = FrontierCheck209.triangle FactorFullCertificate209.phi 622592 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 622592) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 589824
  · exact FullPrefix209_017.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_018
