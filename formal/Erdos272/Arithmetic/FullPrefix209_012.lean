module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_011

@[expose] public section
namespace JSP233.FullPrefix209_012
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_393216 : DualFrontier209.checkFrom FactorFullCertificate209.phi 393216 1024 239046777456261722 46998531267 239669260893078827 47243620519 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_394240 : DualFrontier209.checkFrom FactorFullCertificate209.phi 394240 1024 239669260893078827 47243620519 240292089761728545 47489483699 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_395264 : DualFrontier209.checkFrom FactorFullCertificate209.phi 395264 1024 240292089761728545 47489483699 240914360914189104 47735763961 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_396288 : DualFrontier209.checkFrom FactorFullCertificate209.phi 396288 1024 240914360914189104 47735763961 241536926952990008 47982798339 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_397312 : DualFrontier209.checkFrom FactorFullCertificate209.phi 397312 1024 241536926952990008 47982798339 242159421846458460 48230441937 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_398336 : DualFrontier209.checkFrom FactorFullCertificate209.phi 398336 1024 242159421846458460 48230441937 242781852103840533 48478697127 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_399360 : DualFrontier209.checkFrom FactorFullCertificate209.phi 399360 1024 242781852103840533 48478697127 243404533281814442 48727690061 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_400384 : DualFrontier209.checkFrom FactorFullCertificate209.phi 400384 1024 243404533281814442 48727690061 244027086230900196 48977269321 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_393216 : DualFrontier209.checkFrom FactorFullCertificate209.phi 393216 8192 239046777456261722 46998531267 244027086230900196 48977269321 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 393216 239046777456261722 46998531267 239669260893078827 47243620519 7168 244027086230900196 48977269321 checked_small_393216 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 394240 239669260893078827 47243620519 240292089761728545 47489483699 6144 244027086230900196 48977269321 checked_small_394240 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 395264 240292089761728545 47489483699 240914360914189104 47735763961 5120 244027086230900196 48977269321 checked_small_395264 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 396288 240914360914189104 47735763961 241536926952990008 47982798339 4096 244027086230900196 48977269321 checked_small_396288 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 397312 241536926952990008 47982798339 242159421846458460 48230441937 3072 244027086230900196 48977269321 checked_small_397312 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 398336 242159421846458460 48230441937 242781852103840533 48478697127 2048 244027086230900196 48977269321 checked_small_398336 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 399360 242781852103840533 48478697127 243404533281814442 48727690061 1024 244027086230900196 48977269321 checked_small_399360 checked_small_400384)))))))
#print axioms checked_part_393216
private theorem checked_small_401408 : DualFrontier209.checkFrom FactorFullCertificate209.phi 401408 1024 244027086230900196 48977269321 244649513380489442 49227435487 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_402432 : DualFrontier209.checkFrom FactorFullCertificate209.phi 402432 1024 244649513380489442 49227435487 245272011303077913 49478267479 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_403456 : DualFrontier209.checkFrom FactorFullCertificate209.phi 403456 1024 245272011303077913 49478267479 245894758811141323 49729837841 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_404480 : DualFrontier209.checkFrom FactorFullCertificate209.phi 404480 1024 245894758811141323 49729837841 246517064076234931 49981866805 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_405504 : DualFrontier209.checkFrom FactorFullCertificate209.phi 405504 1024 246517064076234931 49981866805 247139449114397021 50234565221 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_406528 : DualFrontier209.checkFrom FactorFullCertificate209.phi 406528 1024 247139449114397021 50234565221 247762278154642570 50488081779 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_407552 : DualFrontier209.checkFrom FactorFullCertificate209.phi 407552 1024 247762278154642570 50488081779 248384521765283088 50741997239 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_408576 : DualFrontier209.checkFrom FactorFullCertificate209.phi 408576 1024 248384521765283088 50741997239 249007085445505041 50996680695 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_401408 : DualFrontier209.checkFrom FactorFullCertificate209.phi 401408 8192 244027086230900196 48977269321 249007085445505041 50996680695 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 401408 244027086230900196 48977269321 244649513380489442 49227435487 7168 249007085445505041 50996680695 checked_small_401408 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 402432 244649513380489442 49227435487 245272011303077913 49478267479 6144 249007085445505041 50996680695 checked_small_402432 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 403456 245272011303077913 49478267479 245894758811141323 49729837841 5120 249007085445505041 50996680695 checked_small_403456 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 404480 245894758811141323 49729837841 246517064076234931 49981866805 4096 249007085445505041 50996680695 checked_small_404480 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 405504 246517064076234931 49981866805 247139449114397021 50234565221 3072 249007085445505041 50996680695 checked_small_405504 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 406528 247139449114397021 50234565221 247762278154642570 50488081779 2048 249007085445505041 50996680695 checked_small_406528 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 407552 247762278154642570 50488081779 248384521765283088 50741997239 1024 249007085445505041 50996680695 checked_small_407552 checked_small_408576)))))))
#print axioms checked_part_401408
private theorem checked_small_409600 : DualFrontier209.checkFrom FactorFullCertificate209.phi 409600 1024 249007085445505041 50996680695 249629851458992352 51252084789 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_410624 : DualFrontier209.checkFrom FactorFullCertificate209.phi 410624 1024 249629851458992352 51252084789 250252257601882339 51507978703 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_411648 : DualFrontier209.checkFrom FactorFullCertificate209.phi 411648 1024 250252257601882339 51507978703 250874623089192319 51764493071 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_412672 : DualFrontier209.checkFrom FactorFullCertificate209.phi 412672 1024 250874623089192319 51764493071 251497266490084897 52021759561 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_413696 : DualFrontier209.checkFrom FactorFullCertificate209.phi 413696 1024 251497266490084897 52021759561 252119654245527008 52279557751 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_414720 : DualFrontier209.checkFrom FactorFullCertificate209.phi 414720 1024 252119654245527008 52279557751 252742266310146211 52538086381 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_415744 : DualFrontier209.checkFrom FactorFullCertificate209.phi 415744 1024 252742266310146211 52538086381 253364772485907175 52797208531 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_416768 : DualFrontier209.checkFrom FactorFullCertificate209.phi 416768 1024 253364772485907175 52797208531 253987141499526408 53056910817 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_409600 : DualFrontier209.checkFrom FactorFullCertificate209.phi 409600 8192 249007085445505041 50996680695 253987141499526408 53056910817 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 409600 249007085445505041 50996680695 249629851458992352 51252084789 7168 253987141499526408 53056910817 checked_small_409600 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 410624 249629851458992352 51252084789 250252257601882339 51507978703 6144 253987141499526408 53056910817 checked_small_410624 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 411648 250252257601882339 51507978703 250874623089192319 51764493071 5120 253987141499526408 53056910817 checked_small_411648 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 412672 250874623089192319 51764493071 251497266490084897 52021759561 4096 253987141499526408 53056910817 checked_small_412672 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 413696 251497266490084897 52021759561 252119654245527008 52279557751 3072 253987141499526408 53056910817 checked_small_413696 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 414720 252119654245527008 52279557751 252742266310146211 52538086381 2048 253987141499526408 53056910817 checked_small_414720 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 415744 252742266310146211 52538086381 253364772485907175 52797208531 1024 253987141499526408 53056910817 checked_small_415744 checked_small_416768)))))))
#print axioms checked_part_409600
private theorem checked_small_417792 : DualFrontier209.checkFrom FactorFullCertificate209.phi 417792 1024 253987141499526408 53056910817 254609825699422484 53317382259 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_418816 : DualFrontier209.checkFrom FactorFullCertificate209.phi 418816 1024 254609825699422484 53317382259 255232336831569140 53578418835 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_419840 : DualFrontier209.checkFrom FactorFullCertificate209.phi 419840 1024 255232336831569140 53578418835 255854927978058501 53840126535 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_420864 : DualFrontier209.checkFrom FactorFullCertificate209.phi 420864 1024 255854927978058501 53840126535 256477362749553949 54102405869 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_421888 : DualFrontier209.checkFrom FactorFullCertificate209.phi 421888 1024 256477362749553949 54102405869 257099981871759239 54365400457 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_422912 : DualFrontier209.checkFrom FactorFullCertificate209.phi 422912 1024 257099981871759239 54365400457 257722268964014797 54628891951 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_423936 : DualFrontier209.checkFrom FactorFullCertificate209.phi 423936 1024 257722268964014797 54628891951 258344841803309088 54893141865 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_424960 : DualFrontier209.checkFrom FactorFullCertificate209.phi 424960 1024 258344841803309088 54893141865 258967554114284513 55158088759 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_417792 : DualFrontier209.checkFrom FactorFullCertificate209.phi 417792 8192 253987141499526408 53056910817 258967554114284513 55158088759 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 417792 253987141499526408 53056910817 254609825699422484 53317382259 7168 258967554114284513 55158088759 checked_small_417792 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 418816 254609825699422484 53317382259 255232336831569140 53578418835 6144 258967554114284513 55158088759 checked_small_418816 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 419840 255232336831569140 53578418835 255854927978058501 53840126535 5120 258967554114284513 55158088759 checked_small_419840 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 420864 255854927978058501 53840126535 256477362749553949 54102405869 4096 258967554114284513 55158088759 checked_small_420864 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 421888 256477362749553949 54102405869 257099981871759239 54365400457 3072 258967554114284513 55158088759 checked_small_421888 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 422912 257099981871759239 54365400457 257722268964014797 54628891951 2048 258967554114284513 55158088759 checked_small_422912 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 423936 257722268964014797 54628891951 258344841803309088 54893141865 1024 258967554114284513 55158088759 checked_small_423936 checked_small_424960)))))))
#print axioms checked_part_417792
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 393216 32768 239046777456261722 46998531267 258967554114284513 55158088759 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 393216 239046777456261722 46998531267 244027086230900196 48977269321 24576 258967554114284513 55158088759 checked_part_393216 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 401408 244027086230900196 48977269321 249007085445505041 50996680695 16384 258967554114284513 55158088759 checked_part_401408 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 409600 249007085445505041 50996680695 253987141499526408 53056910817 8192 258967554114284513 55158088759 checked_part_409600 checked_part_417792)))
theorem block_sound :
    (258967554114284513 = FrontierCheck209.massFloor FactorFullCertificate209.phi 425984 ∧
     55158088759 = FrontierCheck209.triangle FactorFullCertificate209.phi 425984) ∧
    ∀ t, 393216 < t → t ≤ 425984 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 393216 239046777456261722 46998531267 258967554114284513 55158088759 FullPrefix209_011.endpoint.1 FullPrefix209_011.endpoint.2 checked
theorem endpoint :
    258967554114284513 = FrontierCheck209.massFloor FactorFullCertificate209.phi 425984 ∧
    55158088759 = FrontierCheck209.triangle FactorFullCertificate209.phi 425984 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 425984) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 393216
  · exact FullPrefix209_011.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_012
