module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_015

@[expose] public section
namespace JSP233.FullPrefix209_016
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_524288 : DualFrontier209.checkFrom FactorFullCertificate209.phi 524288 1024 318729258473855633 83553060809 319351575014627589 83879652813 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_525312 : DualFrontier209.checkFrom FactorFullCertificate209.phi 525312 1024 319351575014627589 83879652813 319974159251839347 84207022757 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_526336 : DualFrontier209.checkFrom FactorFullCertificate209.phi 526336 1024 319974159251839347 84207022757 320596689798401149 84535001981 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_527360 : DualFrontier209.checkFrom FactorFullCertificate209.phi 527360 1024 320596689798401149 84535001981 321219185493349911 84863600273 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_528384 : DualFrontier209.checkFrom FactorFullCertificate209.phi 528384 1024 321219185493349911 84863600273 321841565285031674 85192774621 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_529408 : DualFrontier209.checkFrom FactorFullCertificate209.phi 529408 1024 321841565285031674 85192774621 322464274678233088 85522760981 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_530432 : DualFrontier209.checkFrom FactorFullCertificate209.phi 530432 1024 322464274678233088 85522760981 323086526772918706 85853142145 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_531456 : DualFrontier209.checkFrom FactorFullCertificate209.phi 531456 1024 323086526772918706 85853142145 323709083535737243 86184322465 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_524288 : DualFrontier209.checkFrom FactorFullCertificate209.phi 524288 8192 318729258473855633 83553060809 323709083535737243 86184322465 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 524288 318729258473855633 83553060809 319351575014627589 83879652813 7168 323709083535737243 86184322465 checked_small_524288 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 525312 319351575014627589 83879652813 319974159251839347 84207022757 6144 323709083535737243 86184322465 checked_small_525312 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 526336 319974159251839347 84207022757 320596689798401149 84535001981 5120 323709083535737243 86184322465 checked_small_526336 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 527360 320596689798401149 84535001981 321219185493349911 84863600273 4096 323709083535737243 86184322465 checked_small_527360 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 528384 321219185493349911 84863600273 321841565285031674 85192774621 3072 323709083535737243 86184322465 checked_small_528384 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 529408 321841565285031674 85192774621 322464274678233088 85522760981 2048 323709083535737243 86184322465 checked_small_529408 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 530432 322464274678233088 85522760981 323086526772918706 85853142145 1024 323709083535737243 86184322465 checked_small_530432 checked_small_531456)))))))
#print axioms checked_part_524288
private theorem checked_small_532480 : DualFrontier209.checkFrom FactorFullCertificate209.phi 532480 1024 323709083535737243 86184322465 324331916803893987 86516287835 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_533504 : DualFrontier209.checkFrom FactorFullCertificate209.phi 533504 1024 324331916803893987 86516287835 324954153268550132 86848572301 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_534528 : DualFrontier209.checkFrom FactorFullCertificate209.phi 534528 1024 324954153268550132 86848572301 325576762986272034 87181693549 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_535552 : DualFrontier209.checkFrom FactorFullCertificate209.phi 535552 1024 325576762986272034 87181693549 326199347431102990 87515438887 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_536576 : DualFrontier209.checkFrom FactorFullCertificate209.phi 536576 1024 326199347431102990 87515438887 326821746043463470 87849721909 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_537600 : DualFrontier209.checkFrom FactorFullCertificate209.phi 537600 1024 326821746043463470 87849721909 327444391710261395 88184775219 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_538624 : DualFrontier209.checkFrom FactorFullCertificate209.phi 538624 1024 327444391710261395 88184775219 328066989752679795 88520440545 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_539648 : DualFrontier209.checkFrom FactorFullCertificate209.phi 539648 1024 328066989752679795 88520440545 328689311561377347 88856594149 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_532480 : DualFrontier209.checkFrom FactorFullCertificate209.phi 532480 8192 323709083535737243 86184322465 328689311561377347 88856594149 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 532480 323709083535737243 86184322465 324331916803893987 86516287835 7168 328689311561377347 88856594149 checked_small_532480 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 533504 324331916803893987 86516287835 324954153268550132 86848572301 6144 328689311561377347 88856594149 checked_small_533504 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 534528 324954153268550132 86848572301 325576762986272034 87181693549 5120 328689311561377347 88856594149 checked_small_534528 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 535552 325576762986272034 87181693549 326199347431102990 87515438887 4096 328689311561377347 88856594149 checked_small_535552 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 536576 326199347431102990 87515438887 326821746043463470 87849721909 3072 328689311561377347 88856594149 checked_small_536576 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 537600 326821746043463470 87849721909 327444391710261395 88184775219 2048 328689311561377347 88856594149 checked_small_537600 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 538624 327444391710261395 88184775219 328066989752679795 88520440545 1024 328689311561377347 88856594149 checked_small_538624 checked_small_539648)))))))
#print axioms checked_part_532480
private theorem checked_small_540672 : DualFrontier209.checkFrom FactorFullCertificate209.phi 540672 1024 328689311561377347 88856594149 329311762888782177 89193454969 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_541696 : DualFrontier209.checkFrom FactorFullCertificate209.phi 541696 1024 329311762888782177 89193454969 329934432542104191 89531071599 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_542720 : DualFrontier209.checkFrom FactorFullCertificate209.phi 542720 1024 329934432542104191 89531071599 330556924525203881 89869229393 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_543744 : DualFrontier209.checkFrom FactorFullCertificate209.phi 543744 1024 330556924525203881 89869229393 331179274797830553 90207947391 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_544768 : DualFrontier209.checkFrom FactorFullCertificate209.phi 544768 1024 331179274797830553 90207947391 331802100629089182 90547562063 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_545792 : DualFrontier209.checkFrom FactorFullCertificate209.phi 545792 1024 331802100629089182 90547562063 332424434341269524 90887545723 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_546816 : DualFrontier209.checkFrom FactorFullCertificate209.phi 546816 1024 332424434341269524 90887545723 333046954027436714 91228268355 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_547840 : DualFrontier209.checkFrom FactorFullCertificate209.phi 547840 1024 333046954027436714 91228268355 333669663419401106 91569732569 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_540672 : DualFrontier209.checkFrom FactorFullCertificate209.phi 540672 8192 328689311561377347 88856594149 333669663419401106 91569732569 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 540672 328689311561377347 88856594149 329311762888782177 89193454969 7168 333669663419401106 91569732569 checked_small_540672 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 541696 329311762888782177 89193454969 329934432542104191 89531071599 6144 333669663419401106 91569732569 checked_small_541696 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 542720 329934432542104191 89531071599 330556924525203881 89869229393 5120 333669663419401106 91569732569 checked_small_542720 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 543744 330556924525203881 89869229393 331179274797830553 90207947391 4096 333669663419401106 91569732569 checked_small_543744 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 544768 331179274797830553 90207947391 331802100629089182 90547562063 3072 333669663419401106 91569732569 checked_small_544768 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 545792 331802100629089182 90547562063 332424434341269524 90887545723 2048 333669663419401106 91569732569 checked_small_545792 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 546816 332424434341269524 90887545723 333046954027436714 91228268355 1024 333669663419401106 91569732569 checked_small_546816 checked_small_547840)))))))
#print axioms checked_part_540672
private theorem checked_small_548864 : DualFrontier209.checkFrom FactorFullCertificate209.phi 548864 1024 333669663419401106 91569732569 334291985053697582 91911621411 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_549888 : DualFrontier209.checkFrom FactorFullCertificate209.phi 549888 1024 334291985053697582 91911621411 334914609319242883 92254314031 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_550912 : DualFrontier209.checkFrom FactorFullCertificate209.phi 550912 1024 334914609319242883 92254314031 335537087047781471 92597563451 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_551936 : DualFrontier209.checkFrom FactorFullCertificate209.phi 551936 1024 335537087047781471 92597563451 336159378742869981 92941347377 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_552960 : DualFrontier209.checkFrom FactorFullCertificate209.phi 552960 1024 336159378742869981 92941347377 336782120539366376 93286017647 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_553984 : DualFrontier209.checkFrom FactorFullCertificate209.phi 553984 1024 336782120539366376 93286017647 337404799282541441 93631290839 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_555008 : DualFrontier209.checkFrom FactorFullCertificate209.phi 555008 1024 337404799282541441 93631290839 338027028596449272 93976951921 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_556032 : DualFrontier209.checkFrom FactorFullCertificate209.phi 556032 1024 338027028596449272 93976951921 338649543359949609 94323408891 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_548864 : DualFrontier209.checkFrom FactorFullCertificate209.phi 548864 8192 333669663419401106 91569732569 338649543359949609 94323408891 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 548864 333669663419401106 91569732569 334291985053697582 91911621411 7168 338649543359949609 94323408891 checked_small_548864 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 549888 334291985053697582 91911621411 334914609319242883 92254314031 6144 338649543359949609 94323408891 checked_small_549888 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 550912 334914609319242883 92254314031 335537087047781471 92597563451 5120 338649543359949609 94323408891 checked_small_550912 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 551936 335537087047781471 92597563451 336159378742869981 92941347377 4096 338649543359949609 94323408891 checked_small_551936 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 552960 336159378742869981 92941347377 336782120539366376 93286017647 3072 338649543359949609 94323408891 checked_small_552960 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 553984 336782120539366376 93286017647 337404799282541441 93631290839 2048 338649543359949609 94323408891 checked_small_553984 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 555008 337404799282541441 93631290839 338027028596449272 93976951921 1024 338649543359949609 94323408891 checked_small_555008 checked_small_556032)))))))
#print axioms checked_part_548864
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 524288 32768 318729258473855633 83553060809 338649543359949609 94323408891 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 524288 318729258473855633 83553060809 323709083535737243 86184322465 24576 338649543359949609 94323408891 checked_part_524288 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 532480 323709083535737243 86184322465 328689311561377347 88856594149 16384 338649543359949609 94323408891 checked_part_532480 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 540672 328689311561377347 88856594149 333669663419401106 91569732569 8192 338649543359949609 94323408891 checked_part_540672 checked_part_548864)))
theorem block_sound :
    (338649543359949609 = FrontierCheck209.massFloor FactorFullCertificate209.phi 557056 ∧
     94323408891 = FrontierCheck209.triangle FactorFullCertificate209.phi 557056) ∧
    ∀ t, 524288 < t → t ≤ 557056 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 524288 318729258473855633 83553060809 338649543359949609 94323408891 FullPrefix209_015.endpoint.1 FullPrefix209_015.endpoint.2 checked
theorem endpoint :
    338649543359949609 = FrontierCheck209.massFloor FactorFullCertificate209.phi 557056 ∧
    94323408891 = FrontierCheck209.triangle FactorFullCertificate209.phi 557056 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 557056) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 524288
  · exact FullPrefix209_015.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_016
