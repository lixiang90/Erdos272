import Erdos272.Certificates.ForcedDual209
import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_028
namespace JSP233.FullPrefix209_029
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_950272 : DualFrontier209.checkFrom FactorFullCertificate209.phi 950272 1024 577696225005780916 274484331541 578318892125769086 275076353675 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_951296 : DualFrontier209.checkFrom FactorFullCertificate209.phi 951296 1024 578318892125769086 275076353675 578941298553038488 275668765313 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_952320 : DualFrontier209.checkFrom FactorFullCertificate209.phi 952320 1024 578941298553038488 275668765313 579563825156897247 276261928747 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_953344 : DualFrontier209.checkFrom FactorFullCertificate209.phi 953344 1024 579563825156897247 276261928747 580186516564397793 276855886947 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_954368 : DualFrontier209.checkFrom FactorFullCertificate209.phi 954368 1024 580186516564397793 276855886947 580808867042538072 277450157241 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_955392 : DualFrontier209.checkFrom FactorFullCertificate209.phi 955392 1024 580808867042538072 277450157241 581431471819959918 278045307861 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_956416 : DualFrontier209.checkFrom FactorFullCertificate209.phi 956416 1024 581431471819959918 278045307861 582053940894279636 278640966197 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_957440 : DualFrontier209.checkFrom FactorFullCertificate209.phi 957440 1024 582053940894279636 278640966197 582676385339434581 279237238285 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_950272 : DualFrontier209.checkFrom FactorFullCertificate209.phi 950272 8192 577696225005780916 274484331541 582676385339434581 279237238285 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 950272 577696225005780916 274484331541 578318892125769086 275076353675 7168 582676385339434581 279237238285 checked_small_950272 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 951296 578318892125769086 275076353675 578941298553038488 275668765313 6144 582676385339434581 279237238285 checked_small_951296 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 952320 578941298553038488 275668765313 579563825156897247 276261928747 5120 582676385339434581 279237238285 checked_small_952320 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 953344 579563825156897247 276261928747 580186516564397793 276855886947 4096 582676385339434581 279237238285 checked_small_953344 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 954368 580186516564397793 276855886947 580808867042538072 277450157241 3072 582676385339434581 279237238285 checked_small_954368 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 955392 580808867042538072 277450157241 581431471819959918 278045307861 2048 582676385339434581 279237238285 checked_small_955392 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 956416 581431471819959918 278045307861 582053940894279636 278640966197 1024 582676385339434581 279237238285 checked_small_956416 checked_small_957440)))))))
#print axioms checked_part_950272
private theorem checked_small_958464 : DualFrontier209.checkFrom FactorFullCertificate209.phi 958464 1024 582676385339434581 279237238285 583298925142988688 279834239175 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_959488 : DualFrontier209.checkFrom FactorFullCertificate209.phi 959488 1024 583298925142988688 279834239175 583921522065666754 280431932433 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_960512 : DualFrontier209.checkFrom FactorFullCertificate209.phi 960512 1024 583921522065666754 280431932433 584543896613089597 281030049491 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_961536 : DualFrontier209.checkFrom FactorFullCertificate209.phi 961536 1024 584543896613089597 281030049491 585166338817023635 281628868833 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_962560 : DualFrontier209.checkFrom FactorFullCertificate209.phi 962560 1024 585166338817023635 281628868833 585789245063045267 282228772623 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_963584 : DualFrontier209.checkFrom FactorFullCertificate209.phi 963584 1024 585789245063045267 282228772623 586411464163211871 282828651845 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_964608 : DualFrontier209.checkFrom FactorFullCertificate209.phi 964608 1024 586411464163211871 282828651845 587034023514684711 283429496469 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_965632 : DualFrontier209.checkFrom FactorFullCertificate209.phi 965632 1024 587034023514684711 283429496469 587656705615767594 284031097291 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_958464 : DualFrontier209.checkFrom FactorFullCertificate209.phi 958464 8192 582676385339434581 279237238285 587656705615767594 284031097291 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 958464 582676385339434581 279237238285 583298925142988688 279834239175 7168 587656705615767594 284031097291 checked_small_958464 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 959488 583298925142988688 279834239175 583921522065666754 280431932433 6144 587656705615767594 284031097291 checked_small_959488 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 960512 583921522065666754 280431932433 584543896613089597 281030049491 5120 587656705615767594 284031097291 checked_small_960512 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 961536 584543896613089597 281030049491 585166338817023635 281628868833 4096 587656705615767594 284031097291 checked_small_961536 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 962560 585166338817023635 281628868833 585789245063045267 282228772623 3072 587656705615767594 284031097291 checked_small_962560 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 963584 585789245063045267 282228772623 586411464163211871 282828651845 2048 587656705615767594 284031097291 checked_small_963584 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 964608 586411464163211871 282828651845 587034023514684711 283429496469 1024 587656705615767594 284031097291 checked_small_964608 checked_small_965632)))))))
#print axioms checked_part_958464
private theorem checked_small_966656 : DualFrontier209.checkFrom FactorFullCertificate209.phi 966656 1024 587656705615767594 284031097291 588279072888038273 284633031259 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_967680 : DualFrontier209.checkFrom FactorFullCertificate209.phi 967680 1024 588279072888038273 284633031259 588901618900544855 285235775519 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_968704 : DualFrontier209.checkFrom FactorFullCertificate209.phi 968704 1024 588901618900544855 285235775519 589524259258163754 285839248785 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_969728 : DualFrontier209.checkFrom FactorFullCertificate209.phi 969728 1024 589524259258163754 285839248785 590146596548515256 286443065563 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_970752 : DualFrontier209.checkFrom FactorFullCertificate209.phi 970752 1024 590146596548515256 286443065563 590768983145977435 287047567339 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_971776 : DualFrontier209.checkFrom FactorFullCertificate209.phi 971776 1024 590768983145977435 287047567339 591391795565655751 287653120547 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_972800 : DualFrontier209.checkFrom FactorFullCertificate209.phi 972800 1024 591391795565655751 287653120547 592014207249632895 288258921575 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_973824 : DualFrontier209.checkFrom FactorFullCertificate209.phi 973824 1024 592014207249632895 288258921575 592636637225482738 288865377677 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_966656 : DualFrontier209.checkFrom FactorFullCertificate209.phi 966656 8192 587656705615767594 284031097291 592636637225482738 288865377677 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 966656 587656705615767594 284031097291 588279072888038273 284633031259 7168 592636637225482738 288865377677 checked_small_966656 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 967680 588279072888038273 284633031259 588901618900544855 285235775519 6144 592636637225482738 288865377677 checked_small_967680 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 968704 588901618900544855 285235775519 589524259258163754 285839248785 5120 592636637225482738 288865377677 checked_small_968704 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 969728 589524259258163754 285839248785 590146596548515256 286443065563 4096 592636637225482738 288865377677 checked_small_969728 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 970752 590146596548515256 286443065563 590768983145977435 287047567339 3072 592636637225482738 288865377677 checked_small_970752 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 971776 590768983145977435 287047567339 591391795565655751 287653120547 2048 592636637225482738 288865377677 checked_small_971776 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 972800 591391795565655751 287653120547 592014207249632895 288258921575 1024 592636637225482738 288865377677 checked_small_972800 checked_small_973824)))))))
#print axioms checked_part_966656
private theorem checked_small_974848 : DualFrontier209.checkFrom FactorFullCertificate209.phi 974848 1024 592636637225482738 288865377677 593259389399720796 289472785473 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_975872 : DualFrontier209.checkFrom FactorFullCertificate209.phi 975872 1024 593259389399720796 289472785473 593881684396487050 290080384595 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_976896 : DualFrontier209.checkFrom FactorFullCertificate209.phi 976896 1024 593881684396487050 290080384595 594504201456444689 290688837885 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_977920 : DualFrontier209.checkFrom FactorFullCertificate209.phi 977920 1024 594504201456444689 290688837885 595126929806992777 291298135471 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_978944 : DualFrontier209.checkFrom FactorFullCertificate209.phi 978944 1024 595126929806992777 291298135471 595749229675790326 291907651049 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_979968 : DualFrontier209.checkFrom FactorFullCertificate209.phi 979968 1024 595749229675790326 291907651049 596371801131531448 292518070065 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_980992 : DualFrontier209.checkFrom FactorFullCertificate209.phi 980992 1024 596371801131531448 292518070065 596994376291934890 293129130291 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_982016 : DualFrontier209.checkFrom FactorFullCertificate209.phi 982016 1024 596994376291934890 293129130291 597616831487308745 293740710159 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_974848 : DualFrontier209.checkFrom FactorFullCertificate209.phi 974848 8192 592636637225482738 288865377677 597616831487308745 293740710159 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 974848 592636637225482738 288865377677 593259389399720796 289472785473 7168 597616831487308745 293740710159 checked_small_974848 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 975872 593259389399720796 289472785473 593881684396487050 290080384595 6144 597616831487308745 293740710159 checked_small_975872 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 976896 593881684396487050 290080384595 594504201456444689 290688837885 5120 597616831487308745 293740710159 checked_small_976896 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 977920 594504201456444689 290688837885 595126929806992777 291298135471 4096 597616831487308745 293740710159 checked_small_977920 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 978944 595126929806992777 291298135471 595749229675790326 291907651049 3072 597616831487308745 293740710159 checked_small_978944 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 979968 595749229675790326 291907651049 596371801131531448 292518070065 2048 597616831487308745 293740710159 checked_small_979968 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 980992 596371801131531448 292518070065 596994376291934890 293129130291 1024 597616831487308745 293740710159 checked_small_980992 checked_small_982016)))))))
#print axioms checked_part_974848
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 950272 32768 577696225005780916 274484331541 597616831487308745 293740710159 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 950272 577696225005780916 274484331541 582676385339434581 279237238285 24576 597616831487308745 293740710159 checked_part_950272 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 958464 582676385339434581 279237238285 587656705615767594 284031097291 16384 597616831487308745 293740710159 checked_part_958464 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 966656 587656705615767594 284031097291 592636637225482738 288865377677 8192 597616831487308745 293740710159 checked_part_966656 checked_part_974848)))
theorem block_sound :
    (597616831487308745 = FrontierCheck209.massFloor FactorFullCertificate209.phi 983040 ∧
     293740710159 = FrontierCheck209.triangle FactorFullCertificate209.phi 983040) ∧
    ∀ t, 950272 < t → t ≤ 983040 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 950272 577696225005780916 274484331541 597616831487308745 293740710159 FullPrefix209_028.endpoint.1 FullPrefix209_028.endpoint.2 checked
theorem endpoint :
    597616831487308745 = FrontierCheck209.massFloor FactorFullCertificate209.phi 983040 ∧
    293740710159 = FrontierCheck209.triangle FactorFullCertificate209.phi 983040 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 983040) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 950272
  · exact FullPrefix209_028.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_029
