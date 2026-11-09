module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_012

@[expose] public section
namespace JSP233.FullPrefix209_013
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_425984 : DualFrontier209.checkFrom FactorFullCertificate209.phi 425984 1024 258967554114284513 55158088759 259589905422794012 55423519363 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_427008 : DualFrontier209.checkFrom FactorFullCertificate209.phi 427008 1024 259589905422794012 55423519363 260212363765975537 55689632899 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_428032 : DualFrontier209.checkFrom FactorFullCertificate209.phi 428032 1024 260212363765975537 55689632899 260834983893278755 55956453183 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_429056 : DualFrontier209.checkFrom FactorFullCertificate209.phi 429056 1024 260834983893278755 55956453183 261457356603234985 56223804735 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_430080 : DualFrontier209.checkFrom FactorFullCertificate209.phi 430080 1024 261457356603234985 56223804735 262079984954714400 56491903651 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_431104 : DualFrontier209.checkFrom FactorFullCertificate209.phi 431104 1024 262079984954714400 56491903651 262702635630584869 56760649899 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_432128 : DualFrontier209.checkFrom FactorFullCertificate209.phi 432128 1024 262702635630584869 56760649899 263325058137270165 57029935043 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_433152 : DualFrontier209.checkFrom FactorFullCertificate209.phi 433152 1024 263325058137270165 57029935043 263947396858088117 57299821073 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_425984 : DualFrontier209.checkFrom FactorFullCertificate209.phi 425984 8192 258967554114284513 55158088759 263947396858088117 57299821073 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 425984 258967554114284513 55158088759 259589905422794012 55423519363 7168 263947396858088117 57299821073 checked_small_425984 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 427008 259589905422794012 55423519363 260212363765975537 55689632899 6144 263947396858088117 57299821073 checked_small_427008 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 428032 260212363765975537 55689632899 260834983893278755 55956453183 5120 263947396858088117 57299821073 checked_small_428032 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 429056 260834983893278755 55956453183 261457356603234985 56223804735 4096 263947396858088117 57299821073 checked_small_429056 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 430080 261457356603234985 56223804735 262079984954714400 56491903651 3072 263947396858088117 57299821073 checked_small_430080 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 431104 262079984954714400 56491903651 262702635630584869 56760649899 2048 263947396858088117 57299821073 checked_small_431104 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 432128 262702635630584869 56760649899 263325058137270165 57029935043 1024 263947396858088117 57299821073 checked_small_432128 checked_small_433152)))))))
#print axioms checked_part_425984
private theorem checked_small_434176 : DualFrontier209.checkFrom FactorFullCertificate209.phi 434176 1024 263947396858088117 57299821073 264570213546680742 57570552207 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_435200 : DualFrontier209.checkFrom FactorFullCertificate209.phi 435200 1024 264570213546680742 57570552207 265192645570584816 57841753609 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_436224 : DualFrontier209.checkFrom FactorFullCertificate209.phi 436224 1024 265192645570584816 57841753609 265815032172655133 58113572433 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_437248 : DualFrontier209.checkFrom FactorFullCertificate209.phi 437248 1024 265815032172655133 58113572433 266437809458417185 58386199675 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_438272 : DualFrontier209.checkFrom FactorFullCertificate209.phi 438272 1024 266437809458417185 58386199675 267060100765223954 58659251417 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_439296 : DualFrontier209.checkFrom FactorFullCertificate209.phi 439296 1024 267060100765223954 58659251417 267682577968077616 58933022015 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_440320 : DualFrontier209.checkFrom FactorFullCertificate209.phi 440320 1024 267682577968077616 58933022015 268305289323106151 59207533323 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_441344 : DualFrontier209.checkFrom FactorFullCertificate209.phi 441344 1024 268305289323106151 59207533323 268927669558635084 59482536017 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_434176 : DualFrontier209.checkFrom FactorFullCertificate209.phi 434176 8192 263947396858088117 57299821073 268927669558635084 59482536017 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 434176 263947396858088117 57299821073 264570213546680742 57570552207 7168 268927669558635084 59482536017 checked_small_434176 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 435200 264570213546680742 57570552207 265192645570584816 57841753609 6144 268927669558635084 59482536017 checked_small_435200 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 436224 265192645570584816 57841753609 265815032172655133 58113572433 5120 268927669558635084 59482536017 checked_small_436224 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 437248 265815032172655133 58113572433 266437809458417185 58386199675 4096 268927669558635084 59482536017 checked_small_437248 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 438272 266437809458417185 58386199675 267060100765223954 58659251417 3072 268927669558635084 59482536017 checked_small_438272 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 439296 267060100765223954 58659251417 267682577968077616 58933022015 2048 268927669558635084 59482536017 checked_small_439296 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 440320 267682577968077616 58933022015 268305289323106151 59207533323 1024 268927669558635084 59482536017 checked_small_440320 checked_small_441344)))))))
#print axioms checked_part_434176
private theorem checked_small_442368 : DualFrontier209.checkFrom FactorFullCertificate209.phi 442368 1024 268927669558635084 59482536017 269550198644781080 59758241883 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_443392 : DualFrontier209.checkFrom FactorFullCertificate209.phi 443392 1024 269550198644781080 59758241883 270172736376171378 60034589069 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_444416 : DualFrontier209.checkFrom FactorFullCertificate209.phi 444416 1024 270172736376171378 60034589069 270795211585255381 60311545899 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_445440 : DualFrontier209.checkFrom FactorFullCertificate209.phi 445440 1024 270795211585255381 60311545899 271417806385657401 60589193501 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_446464 : DualFrontier209.checkFrom FactorFullCertificate209.phi 446464 1024 271417806385657401 60589193501 272040460000400965 60867505039 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_447488 : DualFrontier209.checkFrom FactorFullCertificate209.phi 447488 1024 272040460000400965 60867505039 272662736415483835 61146285137 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_448512 : DualFrontier209.checkFrom FactorFullCertificate209.phi 448512 1024 272662736415483835 61146285137 273285149785371126 61425763765 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_449536 : DualFrontier209.checkFrom FactorFullCertificate209.phi 449536 1024 273285149785371126 61425763765 273907928904401720 61706044429 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_442368 : DualFrontier209.checkFrom FactorFullCertificate209.phi 442368 8192 268927669558635084 59482536017 273907928904401720 61706044429 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 442368 268927669558635084 59482536017 269550198644781080 59758241883 7168 273907928904401720 61706044429 checked_small_442368 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 443392 269550198644781080 59758241883 270172736376171378 60034589069 6144 273907928904401720 61706044429 checked_small_443392 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 444416 270172736376171378 60034589069 270795211585255381 60311545899 5120 273907928904401720 61706044429 checked_small_444416 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 445440 270795211585255381 60311545899 271417806385657401 60589193501 4096 273907928904401720 61706044429 checked_small_445440 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 446464 271417806385657401 60589193501 272040460000400965 60867505039 3072 273907928904401720 61706044429 checked_small_446464 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 447488 272040460000400965 60867505039 272662736415483835 61146285137 2048 273907928904401720 61706044429 checked_small_447488 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 448512 272662736415483835 61146285137 273285149785371126 61425763765 1024 273907928904401720 61706044429 checked_small_448512 checked_small_449536)))))))
#print axioms checked_part_442368
private theorem checked_small_450560 : DualFrontier209.checkFrom FactorFullCertificate209.phi 450560 1024 273907928904401720 61706044429 274530294584624947 61986776377 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_451584 : DualFrontier209.checkFrom FactorFullCertificate209.phi 451584 1024 274530294584624947 61986776377 275152740742837097 62268181901 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_452608 : DualFrontier209.checkFrom FactorFullCertificate209.phi 452608 1024 275152740742837097 62268181901 275775480643280992 62550357993 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_453632 : DualFrontier209.checkFrom FactorFullCertificate209.phi 453632 1024 275775480643280992 62550357993 276397796762739145 62832979321 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_454656 : DualFrontier209.checkFrom FactorFullCertificate209.phi 454656 1024 276397796762739145 62832979321 277020205370313286 63116279847 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_455680 : DualFrontier209.checkFrom FactorFullCertificate209.phi 455680 1024 277020205370313286 63116279847 277643041089102669 63400412669 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_456704 : DualFrontier209.checkFrom FactorFullCertificate209.phi 456704 1024 277643041089102669 63400412669 278265409178255098 63684969547 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_457728 : DualFrontier209.checkFrom FactorFullCertificate209.phi 457728 1024 278265409178255098 63684969547 278887983028847432 63970257971 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_450560 : DualFrontier209.checkFrom FactorFullCertificate209.phi 450560 8192 273907928904401720 61706044429 278887983028847432 63970257971 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 450560 273907928904401720 61706044429 274530294584624947 61986776377 7168 278887983028847432 63970257971 checked_small_450560 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 451584 274530294584624947 61986776377 275152740742837097 62268181901 6144 278887983028847432 63970257971 checked_small_451584 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 452608 275152740742837097 62268181901 275775480643280992 62550357993 5120 278887983028847432 63970257971 checked_small_452608 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 453632 275775480643280992 62550357993 276397796762739145 62832979321 4096 278887983028847432 63970257971 checked_small_453632 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 454656 276397796762739145 62832979321 277020205370313286 63116279847 3072 278887983028847432 63970257971 checked_small_454656 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 455680 277020205370313286 63116279847 277643041089102669 63400412669 2048 278887983028847432 63970257971 checked_small_455680 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 456704 277643041089102669 63400412669 278265409178255098 63684969547 1024 278887983028847432 63970257971 checked_small_456704 checked_small_457728)))))))
#print axioms checked_part_450560
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 425984 32768 258967554114284513 55158088759 278887983028847432 63970257971 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 425984 258967554114284513 55158088759 263947396858088117 57299821073 24576 278887983028847432 63970257971 checked_part_425984 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 434176 263947396858088117 57299821073 268927669558635084 59482536017 16384 278887983028847432 63970257971 checked_part_434176 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 442368 268927669558635084 59482536017 273907928904401720 61706044429 8192 278887983028847432 63970257971 checked_part_442368 checked_part_450560)))
theorem block_sound :
    (278887983028847432 = FrontierCheck209.massFloor FactorFullCertificate209.phi 458752 ∧
     63970257971 = FrontierCheck209.triangle FactorFullCertificate209.phi 458752) ∧
    ∀ t, 425984 < t → t ≤ 458752 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 425984 258967554114284513 55158088759 278887983028847432 63970257971 FullPrefix209_012.endpoint.1 FullPrefix209_012.endpoint.2 checked
theorem endpoint :
    278887983028847432 = FrontierCheck209.massFloor FactorFullCertificate209.phi 458752 ∧
    63970257971 = FrontierCheck209.triangle FactorFullCertificate209.phi 458752 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 458752) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 425984
  · exact FullPrefix209_012.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_013
