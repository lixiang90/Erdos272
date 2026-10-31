import Erdos272.Certificates.ForcedDual209
import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_030
namespace JSP233.FullPrefix209_031
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1015808 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1015808 1024 617537433467868508 313649844337 618159818379327518 314282386725 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1016832 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1016832 1024 618159818379327518 314282386725 618782362025027860 314915727873 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1017856 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1017856 1024 618782362025027860 314915727873 619405011787563773 315549814653 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1018880 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1018880 1024 619405011787563773 315549814653 620027530365292009 316184405363 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1019904 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1019904 1024 620027530365292009 316184405363 620650025006970402 316819609103 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1020928 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1020928 1024 620650025006970402 316819609103 621272632205741049 317455565269 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1021952 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1021952 1024 621272632205741049 317455565269 621894898326569870 318091810167 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1022976 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1022976 1024 621894898326569870 318091810167 622517489825293685 318729025197 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1015808 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1015808 8192 617537433467868508 313649844337 622517489825293685 318729025197 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1015808 617537433467868508 313649844337 618159818379327518 314282386725 7168 622517489825293685 318729025197 checked_small_1015808 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1016832 618159818379327518 314282386725 618782362025027860 314915727873 6144 622517489825293685 318729025197 checked_small_1016832 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1017856 618782362025027860 314915727873 619405011787563773 315549814653 5120 622517489825293685 318729025197 checked_small_1017856 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1018880 619405011787563773 315549814653 620027530365292009 316184405363 4096 622517489825293685 318729025197 checked_small_1018880 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1019904 620027530365292009 316184405363 620650025006970402 316819609103 3072 622517489825293685 318729025197 checked_small_1019904 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1020928 620650025006970402 316819609103 621272632205741049 317455565269 2048 622517489825293685 318729025197 checked_small_1020928 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1021952 621272632205741049 317455565269 621894898326569870 318091810167 1024 622517489825293685 318729025197 checked_small_1021952 checked_small_1022976)))))))
#print axioms checked_part_1015808
private theorem checked_small_1024000 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1024000 1024 622517489825293685 318729025197 623140131471252212 319366929241 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1025024 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1025024 1024 623140131471252212 319366929241 623762572091748201 320005264735 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1026048 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1026048 1024 623762572091748201 320005264735 624385079284157366 320644305899 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1027072 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1027072 1024 624385079284157366 320644305899 625007672074743790 321284072505 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1028096 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1028096 1024 625007672074743790 321284072505 625629957767176267 321924160679 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1029120 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1029120 1024 625629957767176267 321924160679 626252658090483864 322565312973 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1030144 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1030144 1024 626252658090483864 322565312973 626875316492397050 323207059869 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1031168 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1031168 1024 626875316492397050 323207059869 627497606363240555 323849064121 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1024000 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1024000 8192 622517489825293685 318729025197 627497606363240555 323849064121 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1024000 622517489825293685 318729025197 623140131471252212 319366929241 7168 627497606363240555 323849064121 checked_small_1024000 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1025024 623140131471252212 319366929241 623762572091748201 320005264735 6144 627497606363240555 323849064121 checked_small_1025024 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1026048 623762572091748201 320005264735 624385079284157366 320644305899 5120 627497606363240555 323849064121 checked_small_1026048 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1027072 624385079284157366 320644305899 625007672074743790 321284072505 4096 627497606363240555 323849064121 checked_small_1027072 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1028096 625007672074743790 321284072505 625629957767176267 321924160679 3072 627497606363240555 323849064121 checked_small_1028096 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1029120 625629957767176267 321924160679 626252658090483864 322565312973 2048 627497606363240555 323849064121 checked_small_1029120 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1030144 626252658090483864 322565312973 626875316492397050 323207059869 1024 627497606363240555 323849064121 checked_small_1030144 checked_small_1031168)))))))
#print axioms checked_part_1024000
private theorem checked_small_1032192 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1032192 1024 627497606363240555 323849064121 628120106773910108 324491922899 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1033216 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1033216 1024 628120106773910108 324491922899 628742905177713325 325135727289 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1034240 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1034240 1024 628742905177713325 325135727289 629365375444626170 325779830007 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1035264 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1035264 1024 629365375444626170 325779830007 629987626914713394 326424343349 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1036288 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1036288 1024 629987626914713394 326424343349 630610341316023811 327069973807 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1037312 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1037312 1024 630610341316023811 327069973807 631232625438318673 327715795355 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1038336 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1038336 1024 631232625438318673 327715795355 631855233114775879 328362590165 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1039360 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1039360 1024 631855233114775879 328362590165 632477939905823934 329010125745 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1032192 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1032192 8192 627497606363240555 323849064121 632477939905823934 329010125745 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1032192 627497606363240555 323849064121 628120106773910108 324491922899 7168 632477939905823934 329010125745 checked_small_1032192 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1033216 628120106773910108 324491922899 628742905177713325 325135727289 6144 632477939905823934 329010125745 checked_small_1033216 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1034240 628742905177713325 325135727289 629365375444626170 325779830007 5120 632477939905823934 329010125745 checked_small_1034240 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1035264 629365375444626170 325779830007 629987626914713394 326424343349 4096 632477939905823934 329010125745 checked_small_1035264 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1036288 629987626914713394 326424343349 630610341316023811 327069973807 3072 632477939905823934 329010125745 checked_small_1036288 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1037312 630610341316023811 327069973807 631232625438318673 327715795355 2048 632477939905823934 329010125745 checked_small_1037312 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1038336 631232625438318673 327715795355 631855233114775879 328362590165 1024 632477939905823934 329010125745 checked_small_1038336 checked_small_1039360)))))))
#print axioms checked_part_1032192
private theorem checked_small_1040384 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1040384 1024 632477939905823934 329010125745 633100303395941104 329657941655 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1041408 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1041408 1024 633100303395941104 329657941655 633722889354994104 330306626613 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1042432 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1042432 1024 633722889354994104 330306626613 634345388830974659 330955858927 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1043456 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1043456 1024 634345388830974659 330955858927 634967866360775552 331605705741 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1044480 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1044480 1024 634967866360775552 331605705741 635590480190805223 332256332431 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1045504 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1045504 1024 635590480190805223 332256332431 636213040142917439 332907540391 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1046528 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1046528 1024 636213040142917439 332907540391 636835445850941658 333559224321 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1047552 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1047552 1024 636835445850941658 333559224321 637457902838043309 334211599245 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1040384 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1040384 8192 632477939905823934 329010125745 637457902838043309 334211599245 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1040384 632477939905823934 329010125745 633100303395941104 329657941655 7168 637457902838043309 334211599245 checked_small_1040384 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1041408 633100303395941104 329657941655 633722889354994104 330306626613 6144 637457902838043309 334211599245 checked_small_1041408 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1042432 633722889354994104 330306626613 634345388830974659 330955858927 5120 637457902838043309 334211599245 checked_small_1042432 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1043456 634345388830974659 330955858927 634967866360775552 331605705741 4096 637457902838043309 334211599245 checked_small_1043456 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1044480 634967866360775552 331605705741 635590480190805223 332256332431 3072 637457902838043309 334211599245 checked_small_1044480 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1045504 635590480190805223 332256332431 636213040142917439 332907540391 2048 637457902838043309 334211599245 checked_small_1045504 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1046528 636213040142917439 332907540391 636835445850941658 333559224321 1024 637457902838043309 334211599245 checked_small_1046528 checked_small_1047552)))))))
#print axioms checked_part_1040384
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1015808 32768 617537433467868508 313649844337 637457902838043309 334211599245 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1015808 617537433467868508 313649844337 622517489825293685 318729025197 24576 637457902838043309 334211599245 checked_part_1015808 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1024000 622517489825293685 318729025197 627497606363240555 323849064121 16384 637457902838043309 334211599245 checked_part_1024000 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1032192 627497606363240555 323849064121 632477939905823934 329010125745 8192 637457902838043309 334211599245 checked_part_1032192 checked_part_1040384)))
theorem block_sound :
    (637457902838043309 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1048576 ∧
     334211599245 = FrontierCheck209.triangle FactorFullCertificate209.phi 1048576) ∧
    ∀ t, 1015808 < t → t ≤ 1048576 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1015808 617537433467868508 313649844337 637457902838043309 334211599245 FullPrefix209_030.endpoint.1 FullPrefix209_030.endpoint.2 checked
theorem endpoint :
    637457902838043309 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1048576 ∧
    334211599245 = FrontierCheck209.triangle FactorFullCertificate209.phi 1048576 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1048576) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1015808
  · exact FullPrefix209_030.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_031
