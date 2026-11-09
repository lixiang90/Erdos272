module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_010

@[expose] public section
namespace JSP233.FullPrefix209_011
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_360448 : DualFrontier209.checkFrom FactorFullCertificate209.phi 360448 1024 219126322227156836 39491860885 219748963282224715 39716609687 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_361472 : DualFrontier209.checkFrom FactorFullCertificate209.phi 361472 1024 219748963282224715 39716609687 220371164627899873 39941836805 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_362496 : DualFrontier209.checkFrom FactorFullCertificate209.phi 362496 1024 220371164627899873 39941836805 220993658188764196 40167806961 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_363520 : DualFrontier209.checkFrom FactorFullCertificate209.phi 363520 1024 220993658188764196 40167806961 221616614688339138 40394583281 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_364544 : DualFrontier209.checkFrom FactorFullCertificate209.phi 364544 1024 221616614688339138 40394583281 222238854636166991 40621736013 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_365568 : DualFrontier209.checkFrom FactorFullCertificate209.phi 365568 1024 222238854636166991 40621736013 222861331881625767 40849612625 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_366592 : DualFrontier209.checkFrom FactorFullCertificate209.phi 366592 1024 222861331881625767 40849612625 223484000985681092 41078197141 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_367616 : DualFrontier209.checkFrom FactorFullCertificate209.phi 367616 1024 223484000985681092 41078197141 224106447489690673 41307337363 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_360448 : DualFrontier209.checkFrom FactorFullCertificate209.phi 360448 8192 219126322227156836 39491860885 224106447489690673 41307337363 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 360448 219126322227156836 39491860885 219748963282224715 39716609687 7168 224106447489690673 41307337363 checked_small_360448 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 361472 219748963282224715 39716609687 220371164627899873 39941836805 6144 224106447489690673 41307337363 checked_small_361472 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 362496 220371164627899873 39941836805 220993658188764196 40167806961 5120 224106447489690673 41307337363 checked_small_362496 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 363520 220993658188764196 40167806961 221616614688339138 40394583281 4096 224106447489690673 41307337363 checked_small_363520 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 364544 221616614688339138 40394583281 222238854636166991 40621736013 3072 224106447489690673 41307337363 checked_small_364544 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 365568 222238854636166991 40621736013 222861331881625767 40849612625 2048 224106447489690673 41307337363 checked_small_365568 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 366592 222861331881625767 40849612625 223484000985681092 41078197141 1024 224106447489690673 41307337363 checked_small_366592 checked_small_367616)))))))
#print axioms checked_part_360448
private theorem checked_small_368640 : DualFrontier209.checkFrom FactorFullCertificate209.phi 368640 1024 224106447489690673 41307337363 224729006888514042 41537156635 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_369664 : DualFrontier209.checkFrom FactorFullCertificate209.phi 369664 1024 224729006888514042 41537156635 225351676531405609 41767654323 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_370688 : DualFrontier209.checkFrom FactorFullCertificate209.phi 370688 1024 225351676531405609 41767654323 225973921213305071 41998631819 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_371712 : DualFrontier209.checkFrom FactorFullCertificate209.phi 371712 1024 225973921213305071 41998631819 226596402955307683 42230334573 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_372736 : DualFrontier209.checkFrom FactorFullCertificate209.phi 372736 1024 226596402955307683 42230334573 227219143660894355 42462771497 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_373760 : DualFrontier209.checkFrom FactorFullCertificate209.phi 373760 1024 227219143660894355 42462771497 227841553167802568 42695722217 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_374784 : DualFrontier209.checkFrom FactorFullCertificate209.phi 374784 1024 227841553167802568 42695722217 228464113620644212 42929366889 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_375808 : DualFrontier209.checkFrom FactorFullCertificate209.phi 375808 1024 228464113620644212 42929366889 229086634003897665 43163634015 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_368640 : DualFrontier209.checkFrom FactorFullCertificate209.phi 368640 8192 224106447489690673 41307337363 229086634003897665 43163634015 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 368640 224106447489690673 41307337363 224729006888514042 41537156635 7168 229086634003897665 43163634015 checked_small_368640 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 369664 224729006888514042 41537156635 225351676531405609 41767654323 6144 229086634003897665 43163634015 checked_small_369664 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 370688 225351676531405609 41767654323 225973921213305071 41998631819 5120 229086634003897665 43163634015 checked_small_370688 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 371712 225973921213305071 41998631819 226596402955307683 42230334573 4096 229086634003897665 43163634015 checked_small_371712 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 372736 226596402955307683 42230334573 227219143660894355 42462771497 3072 229086634003897665 43163634015 checked_small_372736 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 373760 227219143660894355 42462771497 227841553167802568 42695722217 2048 229086634003897665 43163634015 checked_small_373760 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 374784 227841553167802568 42695722217 228464113620644212 42929366889 1024 229086634003897665 43163634015 checked_small_374784 checked_small_375808)))))))
#print axioms checked_part_368640
private theorem checked_small_376832 : DualFrontier209.checkFrom FactorFullCertificate209.phi 376832 1024 229086634003897665 43163634015 229709042810369989 43398496439 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_377856 : DualFrontier209.checkFrom FactorFullCertificate209.phi 377856 1024 229709042810369989 43398496439 230331486738515411 43634009411 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_378880 : DualFrontier209.checkFrom FactorFullCertificate209.phi 378880 1024 230331486738515411 43634009411 230954266785820573 43870287381 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_379904 : DualFrontier209.checkFrom FactorFullCertificate209.phi 379904 1024 230954266785820573 43870287381 231576645345311971 44107050407 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_380928 : DualFrontier209.checkFrom FactorFullCertificate209.phi 380928 1024 231576645345311971 44107050407 232199280631144345 44344548665 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_381952 : DualFrontier209.checkFrom FactorFullCertificate209.phi 381952 1024 232199280631144345 44344548665 232821723847825904 44582611067 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_382976 : DualFrontier209.checkFrom FactorFullCertificate209.phi 382976 1024 232821723847825904 44582611067 233444056065421597 44821268151 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_384000 : DualFrontier209.checkFrom FactorFullCertificate209.phi 384000 1024 233444056065421597 44821268151 234066707119221398 45060685071 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_376832 : DualFrontier209.checkFrom FactorFullCertificate209.phi 376832 8192 229086634003897665 43163634015 234066707119221398 45060685071 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 376832 229086634003897665 43163634015 229709042810369989 43398496439 7168 234066707119221398 45060685071 checked_small_376832 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 377856 229709042810369989 43398496439 230331486738515411 43634009411 6144 234066707119221398 45060685071 checked_small_377856 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 378880 230331486738515411 43634009411 230954266785820573 43870287381 5120 234066707119221398 45060685071 checked_small_378880 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 379904 230954266785820573 43870287381 231576645345311971 44107050407 4096 234066707119221398 45060685071 checked_small_379904 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 380928 231576645345311971 44107050407 232199280631144345 44344548665 3072 234066707119221398 45060685071 checked_small_380928 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 381952 232199280631144345 44344548665 232821723847825904 44582611067 2048 234066707119221398 45060685071 checked_small_381952 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 382976 232821723847825904 44582611067 233444056065421597 44821268151 1024 234066707119221398 45060685071 checked_small_382976 checked_small_384000)))))))
#print axioms checked_part_376832
private theorem checked_small_385024 : DualFrontier209.checkFrom FactorFullCertificate209.phi 385024 1024 234066707119221398 45060685071 234689333067233226 45300730033 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_386048 : DualFrontier209.checkFrom FactorFullCertificate209.phi 386048 1024 234689333067233226 45300730033 235311687371784942 45541307525 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_387072 : DualFrontier209.checkFrom FactorFullCertificate209.phi 387072 1024 235311687371784942 45541307525 235934106487295548 45782547297 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_388096 : DualFrontier209.checkFrom FactorFullCertificate209.phi 388096 1024 235934106487295548 45782547297 236556894144430619 46024567737 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_389120 : DualFrontier209.checkFrom FactorFullCertificate209.phi 389120 1024 236556894144430619 46024567737 237179358970184636 46267100237 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_390144 : DualFrontier209.checkFrom FactorFullCertificate209.phi 390144 1024 237179358970184636 46267100237 237801814648172794 46510266505 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_391168 : DualFrontier209.checkFrom FactorFullCertificate209.phi 391168 1024 237801814648172794 46510266505 238424478831093804 46754151879 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_392192 : DualFrontier209.checkFrom FactorFullCertificate209.phi 392192 1024 238424478831093804 46754151879 239046777456261722 46998531267 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_385024 : DualFrontier209.checkFrom FactorFullCertificate209.phi 385024 8192 234066707119221398 45060685071 239046777456261722 46998531267 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 385024 234066707119221398 45060685071 234689333067233226 45300730033 7168 239046777456261722 46998531267 checked_small_385024 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 386048 234689333067233226 45300730033 235311687371784942 45541307525 6144 239046777456261722 46998531267 checked_small_386048 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 387072 235311687371784942 45541307525 235934106487295548 45782547297 5120 239046777456261722 46998531267 checked_small_387072 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 388096 235934106487295548 45782547297 236556894144430619 46024567737 4096 239046777456261722 46998531267 checked_small_388096 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 389120 236556894144430619 46024567737 237179358970184636 46267100237 3072 239046777456261722 46998531267 checked_small_389120 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 390144 237179358970184636 46267100237 237801814648172794 46510266505 2048 239046777456261722 46998531267 checked_small_390144 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 391168 237801814648172794 46510266505 238424478831093804 46754151879 1024 239046777456261722 46998531267 checked_small_391168 checked_small_392192)))))))
#print axioms checked_part_385024
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 360448 32768 219126322227156836 39491860885 239046777456261722 46998531267 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 360448 219126322227156836 39491860885 224106447489690673 41307337363 24576 239046777456261722 46998531267 checked_part_360448 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 368640 224106447489690673 41307337363 229086634003897665 43163634015 16384 239046777456261722 46998531267 checked_part_368640 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 376832 229086634003897665 43163634015 234066707119221398 45060685071 8192 239046777456261722 46998531267 checked_part_376832 checked_part_385024)))
theorem block_sound :
    (239046777456261722 = FrontierCheck209.massFloor FactorFullCertificate209.phi 393216 ∧
     46998531267 = FrontierCheck209.triangle FactorFullCertificate209.phi 393216) ∧
    ∀ t, 360448 < t → t ≤ 393216 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 360448 219126322227156836 39491860885 239046777456261722 46998531267 FullPrefix209_010.endpoint.1 FullPrefix209_010.endpoint.2 checked
theorem endpoint :
    239046777456261722 = FrontierCheck209.massFloor FactorFullCertificate209.phi 393216 ∧
    46998531267 = FrontierCheck209.triangle FactorFullCertificate209.phi 393216 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 393216) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 360448
  · exact FullPrefix209_010.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_011
