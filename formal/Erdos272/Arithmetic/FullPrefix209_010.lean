module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_009

@[expose] public section
namespace JSP233.FullPrefix209_010
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_327680 : DualFrontier209.checkFrom FactorFullCertificate209.phi 327680 1024 199205802047310123 32637919475 199828315021504033 32842223501 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_328704 : DualFrontier209.checkFrom FactorFullCertificate209.phi 328704 1024 199828315021504033 32842223501 200450673118463670 33047113915 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_329728 : DualFrontier209.checkFrom FactorFullCertificate209.phi 329728 1024 200450673118463670 33047113915 201073418635924734 33252769595 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_330752 : DualFrontier209.checkFrom FactorFullCertificate209.phi 330752 1024 201073418635924734 33252769595 201695713228012510 33458913599 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_331776 : DualFrontier209.checkFrom FactorFullCertificate209.phi 331776 1024 201695713228012510 33458913599 202318293924959399 33665789815 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_332800 : DualFrontier209.checkFrom FactorFullCertificate209.phi 332800 1024 202318293924959399 33665789815 202941015105042498 33873350515 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_333824 : DualFrontier209.checkFrom FactorFullCertificate209.phi 333824 1024 202941015105042498 33873350515 203563356810378927 34081422031 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_334848 : DualFrontier209.checkFrom FactorFullCertificate209.phi 334848 1024 203563356810378927 34081422031 204185844623348741 34290179713 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_327680 : DualFrontier209.checkFrom FactorFullCertificate209.phi 327680 8192 199205802047310123 32637919475 204185844623348741 34290179713 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 327680 199205802047310123 32637919475 199828315021504033 32842223501 7168 204185844623348741 34290179713 checked_small_327680 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 328704 199828315021504033 32842223501 200450673118463670 33047113915 6144 204185844623348741 34290179713 checked_small_328704 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 329728 200450673118463670 33047113915 201073418635924734 33252769595 5120 204185844623348741 34290179713 checked_small_329728 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 330752 201073418635924734 33252769595 201695713228012510 33458913599 4096 204185844623348741 34290179713 checked_small_330752 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 331776 201695713228012510 33458913599 202318293924959399 33665789815 3072 204185844623348741 34290179713 checked_small_331776 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 332800 202318293924959399 33665789815 202941015105042498 33873350515 2048 204185844623348741 34290179713 checked_small_332800 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 333824 202941015105042498 33873350515 203563356810378927 34081422031 1024 204185844623348741 34290179713 checked_small_333824 checked_small_334848)))))))
#print axioms checked_part_327680
private theorem checked_small_335872 : DualFrontier209.checkFrom FactorFullCertificate209.phi 335872 1024 204185844623348741 34290179713 204808399201941984 34499597291 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_336896 : DualFrontier209.checkFrom FactorFullCertificate209.phi 336896 1024 204808399201941984 34499597291 205430882239601039 34709628223 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_337920 : DualFrontier209.checkFrom FactorFullCertificate209.phi 337920 1024 205430882239601039 34709628223 206053510009694800 34920345597 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_338944 : DualFrontier209.checkFrom FactorFullCertificate209.phi 338944 1024 206053510009694800 34920345597 206676047772789777 35131670057 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_339968 : DualFrontier209.checkFrom FactorFullCertificate209.phi 339968 1024 206676047772789777 35131670057 207298380188558967 35343561999 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_340992 : DualFrontier209.checkFrom FactorFullCertificate209.phi 340992 1024 207298380188558967 35343561999 207920985547978205 35556184369 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_342016 : DualFrontier209.checkFrom FactorFullCertificate209.phi 342016 1024 207920985547978205 35556184369 208543686634704004 35769477217 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_343040 : DualFrontier209.checkFrom FactorFullCertificate209.phi 343040 1024 208543686634704004 35769477217 209166039682358681 35983288149 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_335872 : DualFrontier209.checkFrom FactorFullCertificate209.phi 335872 8192 204185844623348741 34290179713 209166039682358681 35983288149 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 335872 204185844623348741 34290179713 204808399201941984 34499597291 7168 209166039682358681 35983288149 checked_small_335872 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 336896 204808399201941984 34499597291 205430882239601039 34709628223 6144 209166039682358681 35983288149 checked_small_336896 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 337920 205430882239601039 34709628223 206053510009694800 34920345597 5120 209166039682358681 35983288149 checked_small_337920 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 338944 206053510009694800 34920345597 206676047772789777 35131670057 4096 209166039682358681 35983288149 checked_small_338944 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 339968 206676047772789777 35131670057 207298380188558967 35343561999 3072 209166039682358681 35983288149 checked_small_339968 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 340992 207298380188558967 35343561999 207920985547978205 35556184369 2048 209166039682358681 35983288149 checked_small_340992 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 342016 207920985547978205 35556184369 208543686634704004 35769477217 1024 209166039682358681 35983288149 checked_small_342016 checked_small_343040)))))))
#print axioms checked_part_335872
private theorem checked_small_344064 : DualFrontier209.checkFrom FactorFullCertificate209.phi 344064 1024 209166039682358681 35983288149 209788466698996548 36197761727 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_345088 : DualFrontier209.checkFrom FactorFullCertificate209.phi 345088 1024 209788466698996548 36197761727 210411225801854300 36412987521 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_346112 : DualFrontier209.checkFrom FactorFullCertificate209.phi 346112 1024 210411225801854300 36412987521 211033599953336662 36628717635 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_347136 : DualFrontier209.checkFrom FactorFullCertificate209.phi 347136 1024 211033599953336662 36628717635 211655963647132098 36845081271 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_348160 : DualFrontier209.checkFrom FactorFullCertificate209.phi 348160 1024 211655963647132098 36845081271 212278709828483360 37062215611 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_349184 : DualFrontier209.checkFrom FactorFullCertificate209.phi 349184 1024 212278709828483360 37062215611 212901004878417208 37279829885 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_350208 : DualFrontier209.checkFrom FactorFullCertificate209.phi 350208 1024 212901004878417208 37279829885 213523653476381542 37498205343 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_351232 : DualFrontier209.checkFrom FactorFullCertificate209.phi 351232 1024 213523653476381542 37498205343 214146225554222245 37717191571 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_344064 : DualFrontier209.checkFrom FactorFullCertificate209.phi 344064 8192 209166039682358681 35983288149 214146225554222245 37717191571 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 344064 209166039682358681 35983288149 209788466698996548 36197761727 7168 214146225554222245 37717191571 checked_small_344064 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 345088 209788466698996548 36197761727 210411225801854300 36412987521 6144 214146225554222245 37717191571 checked_small_345088 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 346112 210411225801854300 36412987521 211033599953336662 36628717635 5120 214146225554222245 37717191571 checked_small_346112 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 347136 211033599953336662 36628717635 211655963647132098 36845081271 4096 214146225554222245 37717191571 checked_small_347136 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 348160 211655963647132098 36845081271 212278709828483360 37062215611 3072 214146225554222245 37717191571 checked_small_348160 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 349184 212278709828483360 37062215611 212901004878417208 37279829885 2048 214146225554222245 37717191571 checked_small_349184 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 350208 212901004878417208 37279829885 213523653476381542 37498205343 1024 214146225554222245 37717191571 checked_small_350208 checked_small_351232)))))))
#print axioms checked_part_344064
private theorem checked_small_352256 : DualFrontier209.checkFrom FactorFullCertificate209.phi 352256 1024 214146225554222245 37717191571 214768591041013193 37936742379 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_353280 : DualFrontier209.checkFrom FactorFullCertificate209.phi 353280 1024 214768591041013193 37936742379 215391217090143660 38157022657 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_354304 : DualFrontier209.checkFrom FactorFullCertificate209.phi 354304 1024 215391217090143660 38157022657 216013753954812206 38377908919 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_355328 : DualFrontier209.checkFrom FactorFullCertificate209.phi 355328 1024 216013753954812206 38377908919 216636203278037358 38599401487 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_356352 : DualFrontier209.checkFrom FactorFullCertificate209.phi 356352 1024 216636203278037358 38599401487 217258697008293332 38821547247 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_357376 : DualFrontier209.checkFrom FactorFullCertificate209.phi 357376 1024 217258697008293332 38821547247 217881294185036065 39044367489 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_358400 : DualFrontier209.checkFrom FactorFullCertificate209.phi 358400 1024 217881294185036065 39044367489 218503857609958388 39267813223 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_359424 : DualFrontier209.checkFrom FactorFullCertificate209.phi 359424 1024 218503857609958388 39267813223 219126322227156836 39491860885 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_352256 : DualFrontier209.checkFrom FactorFullCertificate209.phi 352256 8192 214146225554222245 37717191571 219126322227156836 39491860885 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 352256 214146225554222245 37717191571 214768591041013193 37936742379 7168 219126322227156836 39491860885 checked_small_352256 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 353280 214768591041013193 37936742379 215391217090143660 38157022657 6144 219126322227156836 39491860885 checked_small_353280 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 354304 215391217090143660 38157022657 216013753954812206 38377908919 5120 219126322227156836 39491860885 checked_small_354304 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 355328 216013753954812206 38377908919 216636203278037358 38599401487 4096 219126322227156836 39491860885 checked_small_355328 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 356352 216636203278037358 38599401487 217258697008293332 38821547247 3072 219126322227156836 39491860885 checked_small_356352 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 357376 217258697008293332 38821547247 217881294185036065 39044367489 2048 219126322227156836 39491860885 checked_small_357376 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 358400 217881294185036065 39044367489 218503857609958388 39267813223 1024 219126322227156836 39491860885 checked_small_358400 checked_small_359424)))))))
#print axioms checked_part_352256
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 327680 32768 199205802047310123 32637919475 219126322227156836 39491860885 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 327680 199205802047310123 32637919475 204185844623348741 34290179713 24576 219126322227156836 39491860885 checked_part_327680 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 335872 204185844623348741 34290179713 209166039682358681 35983288149 16384 219126322227156836 39491860885 checked_part_335872 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 344064 209166039682358681 35983288149 214146225554222245 37717191571 8192 219126322227156836 39491860885 checked_part_344064 checked_part_352256)))
theorem block_sound :
    (219126322227156836 = FrontierCheck209.massFloor FactorFullCertificate209.phi 360448 ∧
     39491860885 = FrontierCheck209.triangle FactorFullCertificate209.phi 360448) ∧
    ∀ t, 327680 < t → t ≤ 360448 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 327680 199205802047310123 32637919475 219126322227156836 39491860885 FullPrefix209_009.endpoint.1 FullPrefix209_009.endpoint.2 checked
theorem endpoint :
    219126322227156836 = FrontierCheck209.massFloor FactorFullCertificate209.phi 360448 ∧
    39491860885 = FrontierCheck209.triangle FactorFullCertificate209.phi 360448 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 360448) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 327680
  · exact FullPrefix209_009.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_010
