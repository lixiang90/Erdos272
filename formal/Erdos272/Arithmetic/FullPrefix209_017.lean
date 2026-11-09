module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_016

@[expose] public section
namespace JSP233.FullPrefix209_017
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_557056 : DualFrontier209.checkFrom FactorFullCertificate209.phi 557056 1024 338649543359949609 94323408891 339272252544580712 94670611807 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_558080 : DualFrontier209.checkFrom FactorFullCertificate209.phi 558080 1024 339272252544580712 94670611807 339894690543317326 95018300957 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_559104 : DualFrontier209.checkFrom FactorFullCertificate209.phi 559104 1024 339894690543317326 95018300957 340517205144653610 95366670313 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_560128 : DualFrontier209.checkFrom FactorFullCertificate209.phi 560128 1024 340517205144653610 95366670313 341139867727167433 95715760153 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_561152 : DualFrontier209.checkFrom FactorFullCertificate209.phi 561152 1024 341139867727167433 95715760153 341762157863655782 96065278369 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_562176 : DualFrontier209.checkFrom FactorFullCertificate209.phi 562176 1024 341762157863655782 96065278369 342384602530918800 96415520613 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_563200 : DualFrontier209.checkFrom FactorFullCertificate209.phi 563200 1024 342384602530918800 96415520613 343007335844124891 96766563025 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_564224 : DualFrontier209.checkFrom FactorFullCertificate209.phi 564224 1024 343007335844124891 96766563025 343629752929015556 97118064595 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_557056 : DualFrontier209.checkFrom FactorFullCertificate209.phi 557056 8192 338649543359949609 94323408891 343629752929015556 97118064595 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 557056 338649543359949609 94323408891 339272252544580712 94670611807 7168 343629752929015556 97118064595 checked_small_557056 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 558080 339272252544580712 94670611807 339894690543317326 95018300957 6144 343629752929015556 97118064595 checked_small_558080 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 559104 339894690543317326 95018300957 340517205144653610 95366670313 5120 343629752929015556 97118064595 checked_small_559104 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 560128 340517205144653610 95366670313 341139867727167433 95715760153 4096 343629752929015556 97118064595 checked_small_560128 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 561152 341139867727167433 95715760153 341762157863655782 96065278369 3072 343629752929015556 97118064595 checked_small_561152 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 562176 341762157863655782 96065278369 342384602530918800 96415520613 2048 343629752929015556 97118064595 checked_small_562176 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 563200 342384602530918800 96415520613 343007335844124891 96766563025 1024 343629752929015556 97118064595 checked_small_563200 checked_small_564224)))))))
#print axioms checked_part_557056
private theorem checked_small_565248 : DualFrontier209.checkFrom FactorFullCertificate209.phi 565248 1024 343629752929015556 97118064595 344252221378264135 97470232495 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_566272 : DualFrontier209.checkFrom FactorFullCertificate209.phi 566272 1024 344252221378264135 97470232495 344874874602684190 97823142579 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_567296 : DualFrontier209.checkFrom FactorFullCertificate209.phi 567296 1024 344874874602684190 97823142579 345497308960092243 98176566017 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_568320 : DualFrontier209.checkFrom FactorFullCertificate209.phi 568320 1024 345497308960092243 98176566017 346119965126611838 98530753027 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_569344 : DualFrontier209.checkFrom FactorFullCertificate209.phi 569344 1024 346119965126611838 98530753027 346742365122699784 98885431667 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_570368 : DualFrontier209.checkFrom FactorFullCertificate209.phi 570368 1024 346742365122699784 98885431667 347364751141901881 99240739535 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_571392 : DualFrontier209.checkFrom FactorFullCertificate209.phi 571392 1024 347364751141901881 99240739535 347987252212977302 99596750449 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_572416 : DualFrontier209.checkFrom FactorFullCertificate209.phi 572416 1024 347987252212977302 99596750449 348610004164211512 99953542651 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_565248 : DualFrontier209.checkFrom FactorFullCertificate209.phi 565248 8192 343629752929015556 97118064595 348610004164211512 99953542651 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 565248 343629752929015556 97118064595 344252221378264135 97470232495 7168 348610004164211512 99953542651 checked_small_565248 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 566272 344252221378264135 97470232495 344874874602684190 97823142579 6144 348610004164211512 99953542651 checked_small_566272 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 567296 344874874602684190 97823142579 345497308960092243 98176566017 5120 348610004164211512 99953542651 checked_small_567296 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 568320 345497308960092243 98176566017 346119965126611838 98530753027 4096 348610004164211512 99953542651 checked_small_568320 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 569344 346119965126611838 98530753027 346742365122699784 98885431667 3072 348610004164211512 99953542651 checked_small_569344 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 570368 346742365122699784 98885431667 347364751141901881 99240739535 2048 348610004164211512 99953542651 checked_small_570368 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 571392 347364751141901881 99240739535 347987252212977302 99596750449 1024 348610004164211512 99953542651 checked_small_571392 checked_small_572416)))))))
#print axioms checked_part_565248
private theorem checked_small_573440 : DualFrontier209.checkFrom FactorFullCertificate209.phi 573440 1024 348610004164211512 99953542651 349232450860654935 100310797435 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_574464 : DualFrontier209.checkFrom FactorFullCertificate209.phi 574464 1024 349232450860654935 100310797435 349854870327988291 100668673859 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_575488 : DualFrontier209.checkFrom FactorFullCertificate209.phi 575488 1024 349854870327988291 100668673859 350477601360716383 101027367167 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_576512 : DualFrontier209.checkFrom FactorFullCertificate209.phi 576512 1024 350477601360716383 101027367167 351099866025338382 101386429021 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_577536 : DualFrontier209.checkFrom FactorFullCertificate209.phi 577536 1024 351099866025338382 101386429021 351722428516082563 101746300129 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_578560 : DualFrontier209.checkFrom FactorFullCertificate209.phi 578560 1024 351722428516082563 101746300129 352345167788544853 102106911249 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_579584 : DualFrontier209.checkFrom FactorFullCertificate209.phi 579584 1024 352345167788544853 102106911249 352967462617833038 102467902229 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_580608 : DualFrontier209.checkFrom FactorFullCertificate209.phi 580608 1024 352967462617833038 102467902229 353590052669643912 102829701923 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_573440 : DualFrontier209.checkFrom FactorFullCertificate209.phi 573440 8192 348610004164211512 99953542651 353590052669643912 102829701923 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 573440 348610004164211512 99953542651 349232450860654935 100310797435 7168 353590052669643912 102829701923 checked_small_573440 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 574464 349232450860654935 100310797435 349854870327988291 100668673859 6144 353590052669643912 102829701923 checked_small_574464 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 575488 349854870327988291 100668673859 350477601360716383 101027367167 5120 353590052669643912 102829701923 checked_small_575488 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 576512 350477601360716383 101027367167 351099866025338382 101386429021 4096 353590052669643912 102829701923 checked_small_576512 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 577536 351099866025338382 101386429021 351722428516082563 101746300129 3072 353590052669643912 102829701923 checked_small_577536 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 578560 351722428516082563 101746300129 352345167788544853 102106911249 2048 353590052669643912 102829701923 checked_small_578560 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 579584 352345167788544853 102106911249 352967462617833038 102467902229 1024 353590052669643912 102829701923 checked_small_579584 checked_small_580608)))))))
#print axioms checked_part_573440
private theorem checked_small_581632 : DualFrontier209.checkFrom FactorFullCertificate209.phi 581632 1024 353590052669643912 102829701923 354212697855035371 103192171349 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_582656 : DualFrontier209.checkFrom FactorFullCertificate209.phi 582656 1024 354212697855035371 103192171349 354835121616944790 103555149251 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_583680 : DualFrontier209.checkFrom FactorFullCertificate209.phi 583680 1024 354835121616944790 103555149251 355457593450352621 103918792535 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_584704 : DualFrontier209.checkFrom FactorFullCertificate209.phi 584704 1024 355457593450352621 103918792535 356080163411200605 104283130657 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_585728 : DualFrontier209.checkFrom FactorFullCertificate209.phi 585728 1024 356080163411200605 104283130657 356702581531251968 104648017247 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_586752 : DualFrontier209.checkFrom FactorFullCertificate209.phi 586752 1024 356702581531251968 104648017247 357325053191294465 105013572563 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_587776 : DualFrontier209.checkFrom FactorFullCertificate209.phi 587776 1024 357325053191294465 105013572563 357947724494060518 105379882785 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_588800 : DualFrontier209.checkFrom FactorFullCertificate209.phi 588800 1024 357947724494060518 105379882785 358570226846222941 105746731133 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_581632 : DualFrontier209.checkFrom FactorFullCertificate209.phi 581632 8192 353590052669643912 102829701923 358570226846222941 105746731133 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 581632 353590052669643912 102829701923 354212697855035371 103192171349 7168 358570226846222941 105746731133 checked_small_581632 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 582656 354212697855035371 103192171349 354835121616944790 103555149251 6144 358570226846222941 105746731133 checked_small_582656 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 583680 354835121616944790 103555149251 355457593450352621 103918792535 5120 358570226846222941 105746731133 checked_small_583680 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 584704 355457593450352621 103918792535 356080163411200605 104283130657 4096 358570226846222941 105746731133 checked_small_584704 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 585728 356080163411200605 104283130657 356702581531251968 104648017247 3072 358570226846222941 105746731133 checked_small_585728 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 586752 356702581531251968 104648017247 357325053191294465 105013572563 2048 358570226846222941 105746731133 checked_small_586752 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 587776 357325053191294465 105013572563 357947724494060518 105379882785 1024 358570226846222941 105746731133 checked_small_587776 checked_small_588800)))))))
#print axioms checked_part_581632
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 557056 32768 338649543359949609 94323408891 358570226846222941 105746731133 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 557056 338649543359949609 94323408891 343629752929015556 97118064595 24576 358570226846222941 105746731133 checked_part_557056 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 565248 343629752929015556 97118064595 348610004164211512 99953542651 16384 358570226846222941 105746731133 checked_part_565248 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 573440 348610004164211512 99953542651 353590052669643912 102829701923 8192 358570226846222941 105746731133 checked_part_573440 checked_part_581632)))
theorem block_sound :
    (358570226846222941 = FrontierCheck209.massFloor FactorFullCertificate209.phi 589824 ∧
     105746731133 = FrontierCheck209.triangle FactorFullCertificate209.phi 589824) ∧
    ∀ t, 557056 < t → t ≤ 589824 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 557056 338649543359949609 94323408891 358570226846222941 105746731133 FullPrefix209_016.endpoint.1 FullPrefix209_016.endpoint.2 checked
theorem endpoint :
    358570226846222941 = FrontierCheck209.massFloor FactorFullCertificate209.phi 589824 ∧
    105746731133 = FrontierCheck209.triangle FactorFullCertificate209.phi 589824 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 589824) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 557056
  · exact FullPrefix209_016.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_017
