module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_013

@[expose] public section
namespace JSP233.FullPrefix209_014
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_458752 : DualFrontier209.checkFrom FactorFullCertificate209.phi 458752 1024 278887983028847432 63970257971 279510567552309288 64256188877 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_459776 : DualFrontier209.checkFrom FactorFullCertificate209.phi 459776 1024 279510567552309288 64256188877 280133011356239191 64542692539 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_460800 : DualFrontier209.checkFrom FactorFullCertificate209.phi 460800 1024 280133011356239191 64542692539 280755614035438679 64829906875 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_461824 : DualFrontier209.checkFrom FactorFullCertificate209.phi 461824 1024 280755614035438679 64829906875 281378086326908778 65117698505 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_462848 : DualFrontier209.checkFrom FactorFullCertificate209.phi 462848 1024 281378086326908778 65117698505 282000492258785561 65406096715 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_463872 : DualFrontier209.checkFrom FactorFullCertificate209.phi 463872 1024 282000492258785561 65406096715 282622992061043447 65695175791 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_464896 : DualFrontier209.checkFrom FactorFullCertificate209.phi 464896 1024 282622992061043447 65695175791 283245582099074536 65984934327 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_465920 : DualFrontier209.checkFrom FactorFullCertificate209.phi 465920 1024 283245582099074536 65984934327 283868151621624329 66275320895 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_458752 : DualFrontier209.checkFrom FactorFullCertificate209.phi 458752 8192 278887983028847432 63970257971 283868151621624329 66275320895 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 458752 278887983028847432 63970257971 279510567552309288 64256188877 7168 283868151621624329 66275320895 checked_small_458752 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 459776 279510567552309288 64256188877 280133011356239191 64542692539 6144 283868151621624329 66275320895 checked_small_459776 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 460800 280133011356239191 64542692539 280755614035438679 64829906875 5120 283868151621624329 66275320895 checked_small_460800 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 461824 280755614035438679 64829906875 281378086326908778 65117698505 4096 283868151621624329 66275320895 checked_small_461824 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 462848 281378086326908778 65117698505 282000492258785561 65406096715 3072 283868151621624329 66275320895 checked_small_462848 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 463872 282000492258785561 65406096715 282622992061043447 65695175791 2048 283868151621624329 66275320895 checked_small_463872 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 464896 282622992061043447 65695175791 283245582099074536 65984934327 1024 283868151621624329 66275320895 checked_small_464896 checked_small_465920)))))))
#print axioms checked_part_458752
private theorem checked_small_466944 : DualFrontier209.checkFrom FactorFullCertificate209.phi 466944 1024 283868151621624329 66275320895 284490628699710999 66566301773 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_467968 : DualFrontier209.checkFrom FactorFullCertificate209.phi 467968 1024 284490628699710999 66566301773 285113367696964862 66858042853 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_468992 : DualFrontier209.checkFrom FactorFullCertificate209.phi 468992 1024 285113367696964862 66858042853 285735492088397074 67150132975 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_470016 : DualFrontier209.checkFrom FactorFullCertificate209.phi 470016 1024 285735492088397074 67150132975 286358064857505355 67443070951 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_471040 : DualFrontier209.checkFrom FactorFullCertificate209.phi 471040 1024 286358064857505355 67443070951 286980945975906649 67736792061 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_472064 : DualFrontier209.checkFrom FactorFullCertificate209.phi 472064 1024 286980945975906649 67736792061 287603091294561290 68030803269 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_473088 : DualFrontier209.checkFrom FactorFullCertificate209.phi 473088 1024 287603091294561290 68030803269 288225677943799777 68325660421 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_474112 : DualFrontier209.checkFrom FactorFullCertificate209.phi 474112 1024 288225677943799777 68325660421 288848306180435358 68621174929 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_466944 : DualFrontier209.checkFrom FactorFullCertificate209.phi 466944 8192 283868151621624329 66275320895 288848306180435358 68621174929 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 466944 283868151621624329 66275320895 284490628699710999 66566301773 7168 288848306180435358 68621174929 checked_small_466944 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 467968 284490628699710999 66566301773 285113367696964862 66858042853 6144 288848306180435358 68621174929 checked_small_467968 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 468992 285113367696964862 66858042853 285735492088397074 67150132975 5120 288848306180435358 68621174929 checked_small_468992 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 470016 285735492088397074 67150132975 286358064857505355 67443070951 4096 288848306180435358 68621174929 checked_small_470016 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 471040 286358064857505355 67443070951 286980945975906649 67736792061 3072 288848306180435358 68621174929 checked_small_471040 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 472064 286980945975906649 67736792061 287603091294561290 68030803269 2048 288848306180435358 68621174929 checked_small_472064 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 473088 287603091294561290 68030803269 288225677943799777 68325660421 1024 288848306180435358 68621174929 checked_small_473088 checked_small_474112)))))))
#print axioms checked_part_466944
private theorem checked_small_475136 : DualFrontier209.checkFrom FactorFullCertificate209.phi 475136 1024 288848306180435358 68621174929 289470723511811551 68917226697 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_476160 : DualFrontier209.checkFrom FactorFullCertificate209.phi 476160 1024 289470723511811551 68917226697 290093338627248823 69214010091 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_477184 : DualFrontier209.checkFrom FactorFullCertificate209.phi 477184 1024 290093338627248823 69214010091 290715886323901442 69511398913 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_478208 : DualFrontier209.checkFrom FactorFullCertificate209.phi 478208 1024 290715886323901442 69511398913 291338270406336459 69809346843 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_479232 : DualFrontier209.checkFrom FactorFullCertificate209.phi 479232 1024 291338270406336459 69809346843 291960764845558158 70107984955 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_480256 : DualFrontier209.checkFrom FactorFullCertificate209.phi 480256 1024 291960764845558158 70107984955 292583468712694907 70407361271 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_481280 : DualFrontier209.checkFrom FactorFullCertificate209.phi 481280 1024 292583468712694907 70407361271 293205934187343030 70707260449 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_482304 : DualFrontier209.checkFrom FactorFullCertificate209.phi 482304 1024 293205934187343030 70707260449 293828382122047441 71007788503 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_475136 : DualFrontier209.checkFrom FactorFullCertificate209.phi 475136 8192 288848306180435358 68621174929 293828382122047441 71007788503 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 475136 288848306180435358 68621174929 289470723511811551 68917226697 7168 293828382122047441 71007788503 checked_small_475136 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 476160 289470723511811551 68917226697 290093338627248823 69214010091 6144 293828382122047441 71007788503 checked_small_476160 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 477184 290093338627248823 69214010091 290715886323901442 69511398913 5120 293828382122047441 71007788503 checked_small_477184 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 478208 290715886323901442 69511398913 291338270406336459 69809346843 4096 293828382122047441 71007788503 checked_small_478208 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 479232 291338270406336459 69809346843 291960764845558158 70107984955 3072 293828382122047441 71007788503 checked_small_479232 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 480256 291960764845558158 70107984955 292583468712694907 70407361271 2048 293828382122047441 71007788503 checked_small_480256 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 481280 292583468712694907 70407361271 293205934187343030 70707260449 1024 293828382122047441 71007788503 checked_small_481280 checked_small_482304)))))))
#print axioms checked_part_475136
private theorem checked_small_483328 : DualFrontier209.checkFrom FactorFullCertificate209.phi 483328 1024 293828382122047441 71007788503 294451003654449260 71309037951 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_484352 : DualFrontier209.checkFrom FactorFullCertificate209.phi 484352 1024 294451003654449260 71309037951 295073273425236488 71610754335 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_485376 : DualFrontier209.checkFrom FactorFullCertificate209.phi 485376 1024 295073273425236488 71610754335 295695852667099159 71913258207 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_486400 : DualFrontier209.checkFrom FactorFullCertificate209.phi 486400 1024 295695852667099159 71913258207 296318542587423090 72216453605 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_487424 : DualFrontier209.checkFrom FactorFullCertificate209.phi 487424 1024 296318542587423090 72216453605 296941001464035440 72520173963 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_488448 : DualFrontier209.checkFrom FactorFullCertificate209.phi 488448 1024 296941001464035440 72520173963 297563473868820474 72824538277 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_489472 : DualFrontier209.checkFrom FactorFullCertificate209.phi 489472 1024 297563473868820474 72824538277 298186152487550267 73129641103 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_490496 : DualFrontier209.checkFrom FactorFullCertificate209.phi 490496 1024 298186152487550267 73129641103 298808435651494805 73435187345 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_483328 : DualFrontier209.checkFrom FactorFullCertificate209.phi 483328 8192 293828382122047441 71007788503 298808435651494805 73435187345 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 483328 293828382122047441 71007788503 294451003654449260 71309037951 7168 298808435651494805 73435187345 checked_small_483328 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 484352 294451003654449260 71309037951 295073273425236488 71610754335 6144 298808435651494805 73435187345 checked_small_484352 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 485376 295073273425236488 71610754335 295695852667099159 71913258207 5120 298808435651494805 73435187345 checked_small_485376 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 486400 295695852667099159 71913258207 296318542587423090 72216453605 4096 298808435651494805 73435187345 checked_small_486400 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 487424 296318542587423090 72216453605 296941001464035440 72520173963 3072 298808435651494805 73435187345 checked_small_487424 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 488448 296941001464035440 72520173963 297563473868820474 72824538277 2048 298808435651494805 73435187345 checked_small_488448 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 489472 297563473868820474 72824538277 298186152487550267 73129641103 1024 298808435651494805 73435187345 checked_small_489472 checked_small_490496)))))))
#print axioms checked_part_483328
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 458752 32768 278887983028847432 63970257971 298808435651494805 73435187345 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 458752 278887983028847432 63970257971 283868151621624329 66275320895 24576 298808435651494805 73435187345 checked_part_458752 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 466944 283868151621624329 66275320895 288848306180435358 68621174929 16384 298808435651494805 73435187345 checked_part_466944 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 475136 288848306180435358 68621174929 293828382122047441 71007788503 8192 298808435651494805 73435187345 checked_part_475136 checked_part_483328)))
theorem block_sound :
    (298808435651494805 = FrontierCheck209.massFloor FactorFullCertificate209.phi 491520 ∧
     73435187345 = FrontierCheck209.triangle FactorFullCertificate209.phi 491520) ∧
    ∀ t, 458752 < t → t ≤ 491520 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 458752 278887983028847432 63970257971 298808435651494805 73435187345 FullPrefix209_013.endpoint.1 FullPrefix209_013.endpoint.2 checked
theorem endpoint :
    298808435651494805 = FrontierCheck209.massFloor FactorFullCertificate209.phi 491520 ∧
    73435187345 = FrontierCheck209.triangle FactorFullCertificate209.phi 491520 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 491520) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 458752
  · exact FullPrefix209_013.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_014
