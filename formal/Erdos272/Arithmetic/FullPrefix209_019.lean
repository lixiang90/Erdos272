module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_018

@[expose] public section
namespace JSP233.FullPrefix209_019
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_622592 : DualFrontier209.checkFrom FactorFullCertificate209.phi 622592 1024 378490858220726241 117822786067 379113107039478411 118210511971 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_623616 : DualFrontier209.checkFrom FactorFullCertificate209.phi 623616 1024 379113107039478411 118210511971 379735613059774407 118599035441 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_624640 : DualFrontier209.checkFrom FactorFullCertificate209.phi 624640 1024 379735613059774407 118599035441 380358545660577388 118988463243 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_625664 : DualFrontier209.checkFrom FactorFullCertificate209.phi 625664 1024 380358545660577388 118988463243 380980853140659697 119378137599 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_626688 : DualFrontier209.checkFrom FactorFullCertificate209.phi 626688 1024 380980853140659697 119378137599 381603329211102139 119768554805 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_627712 : DualFrontier209.checkFrom FactorFullCertificate209.phi 627712 1024 381603329211102139 119768554805 382225887198363627 120159660891 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_628736 : DualFrontier209.checkFrom FactorFullCertificate209.phi 628736 1024 382225887198363627 120159660891 382848331440591301 120551332889 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_629760 : DualFrontier209.checkFrom FactorFullCertificate209.phi 629760 1024 382848331440591301 120551332889 383470872428028892 120943703215 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_622592 : DualFrontier209.checkFrom FactorFullCertificate209.phi 622592 8192 378490858220726241 117822786067 383470872428028892 120943703215 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 622592 378490858220726241 117822786067 379113107039478411 118210511971 7168 383470872428028892 120943703215 checked_small_622592 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 623616 379113107039478411 118210511971 379735613059774407 118599035441 6144 383470872428028892 120943703215 checked_small_623616 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 624640 379735613059774407 118599035441 380358545660577388 118988463243 5120 383470872428028892 120943703215 checked_small_624640 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 625664 380358545660577388 118988463243 380980853140659697 119378137599 4096 383470872428028892 120943703215 checked_small_625664 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 626688 380980853140659697 119378137599 381603329211102139 119768554805 3072 383470872428028892 120943703215 checked_small_626688 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 627712 381603329211102139 119768554805 382225887198363627 120159660891 2048 383470872428028892 120943703215 checked_small_627712 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 628736 382225887198363627 120159660891 382848331440591301 120551332889 1024 383470872428028892 120943703215 checked_small_628736 checked_small_629760)))))))
#print axioms checked_part_622592
private theorem checked_small_630784 : DualFrontier209.checkFrom FactorFullCertificate209.phi 630784 1024 383470872428028892 120943703215 384093501077338743 121336766439 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_631808 : DualFrontier209.checkFrom FactorFullCertificate209.phi 631808 1024 384093501077338743 121336766439 384715871831804603 121730304141 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_632832 : DualFrontier209.checkFrom FactorFullCertificate209.phi 632832 1024 384715871831804603 121730304141 385338433179074689 122124599811 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_633856 : DualFrontier209.checkFrom FactorFullCertificate209.phi 633856 1024 385338433179074689 122124599811 385961087588462547 122519592111 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_634880 : DualFrontier209.checkFrom FactorFullCertificate209.phi 634880 1024 385961087588462547 122519592111 386583456134317581 122915040363 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_635904 : DualFrontier209.checkFrom FactorFullCertificate209.phi 635904 1024 386583456134317581 122915040363 387205936797998069 123311197183 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_636928 : DualFrontier209.checkFrom FactorFullCertificate209.phi 636928 1024 387205936797998069 123311197183 387828581470900389 123708096011 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_637952 : DualFrontier209.checkFrom FactorFullCertificate209.phi 637952 1024 387828581470900389 123708096011 388450901365260307 124105425039 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_630784 : DualFrontier209.checkFrom FactorFullCertificate209.phi 630784 8192 383470872428028892 120943703215 388450901365260307 124105425039 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 630784 383470872428028892 120943703215 384093501077338743 121336766439 7168 388450901365260307 124105425039 checked_small_630784 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 631808 384093501077338743 121336766439 384715871831804603 121730304141 6144 388450901365260307 124105425039 checked_small_631808 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 632832 384715871831804603 121730304141 385338433179074689 122124599811 5120 388450901365260307 124105425039 checked_small_632832 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 633856 385338433179074689 122124599811 385961087588462547 122519592111 4096 388450901365260307 124105425039 checked_small_633856 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 634880 385961087588462547 122519592111 386583456134317581 122915040363 3072 388450901365260307 124105425039 checked_small_634880 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 635904 386583456134317581 122915040363 387205936797998069 123311197183 2048 388450901365260307 124105425039 checked_small_635904 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 636928 387205936797998069 123311197183 387828581470900389 123708096011 1024 388450901365260307 124105425039 checked_small_636928 checked_small_637952)))))))
#print axioms checked_part_630784
private theorem checked_small_638976 : DualFrontier209.checkFrom FactorFullCertificate209.phi 638976 1024 388450901365260307 124105425039 389073466923919668 124503548345 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_640000 : DualFrontier209.checkFrom FactorFullCertificate209.phi 640000 1024 389073466923919668 124503548345 389696280309500071 124902468067 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_641024 : DualFrontier209.checkFrom FactorFullCertificate209.phi 641024 1024 389696280309500071 124902468067 390318454806475575 125301615661 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_642048 : DualFrontier209.checkFrom FactorFullCertificate209.phi 642048 1024 390318454806475575 125301615661 390941024331053397 125701654039 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_643072 : DualFrontier209.checkFrom FactorFullCertificate209.phi 643072 1024 390941024331053397 125701654039 391563621625006451 126102347871 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_644096 : DualFrontier209.checkFrom FactorFullCertificate209.phi 644096 1024 391563621625006451 126102347871 392186063711801166 126503579197 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_645120 : DualFrontier209.checkFrom FactorFullCertificate209.phi 645120 1024 392186063711801166 126503579197 392808627458310365 126905526433 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_646144 : DualFrontier209.checkFrom FactorFullCertificate209.phi 646144 1024 392808627458310365 126905526433 393431252215599799 127308150707 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_638976 : DualFrontier209.checkFrom FactorFullCertificate209.phi 638976 8192 388450901365260307 124105425039 393431252215599799 127308150707 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 638976 388450901365260307 124105425039 389073466923919668 124503548345 7168 393431252215599799 127308150707 checked_small_638976 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 640000 389073466923919668 124503548345 389696280309500071 124902468067 6144 393431252215599799 127308150707 checked_small_640000 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 641024 389696280309500071 124902468067 390318454806475575 125301615661 5120 393431252215599799 127308150707 checked_small_641024 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 642048 390318454806475575 125301615661 390941024331053397 125701654039 4096 393431252215599799 127308150707 checked_small_642048 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 643072 390941024331053397 125701654039 391563621625006451 126102347871 3072 393431252215599799 127308150707 checked_small_643072 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 644096 391563621625006451 126102347871 392186063711801166 126503579197 2048 393431252215599799 127308150707 checked_small_644096 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 645120 392186063711801166 126503579197 392808627458310365 126905526433 1024 393431252215599799 127308150707 checked_small_645120 checked_small_646144)))))))
#print axioms checked_part_638976
private theorem checked_small_647168 : DualFrontier209.checkFrom FactorFullCertificate209.phi 647168 1024 393431252215599799 127308150707 394053739524061533 127711323569 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_648192 : DualFrontier209.checkFrom FactorFullCertificate209.phi 648192 1024 394053739524061533 127711323569 394676080755298051 128115038985 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_649216 : DualFrontier209.checkFrom FactorFullCertificate209.phi 649216 1024 394676080755298051 128115038985 395298744138262434 128519600973 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_650240 : DualFrontier209.checkFrom FactorFullCertificate209.phi 650240 1024 395298744138262434 128519600973 395921252807754149 128924699965 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_651264 : DualFrontier209.checkFrom FactorFullCertificate209.phi 651264 1024 395921252807754149 128924699965 396543718536565623 129330408385 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_652288 : DualFrontier209.checkFrom FactorFullCertificate209.phi 652288 1024 396543718536565623 129330408385 397166438977683144 129736920561 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_653312 : DualFrontier209.checkFrom FactorFullCertificate209.phi 653312 1024 397166438977683144 129736920561 397788646794274644 130143735187 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_654336 : DualFrontier209.checkFrom FactorFullCertificate209.phi 654336 1024 397788646794274644 130143735187 398411321728698376 130551492759 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_647168 : DualFrontier209.checkFrom FactorFullCertificate209.phi 647168 8192 393431252215599799 127308150707 398411321728698376 130551492759 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 647168 393431252215599799 127308150707 394053739524061533 127711323569 7168 398411321728698376 130551492759 checked_small_647168 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 648192 394053739524061533 127711323569 394676080755298051 128115038985 6144 398411321728698376 130551492759 checked_small_648192 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 649216 394676080755298051 128115038985 395298744138262434 128519600973 5120 398411321728698376 130551492759 checked_small_649216 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 650240 395298744138262434 128519600973 395921252807754149 128924699965 4096 398411321728698376 130551492759 checked_small_650240 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 651264 395921252807754149 128924699965 396543718536565623 129330408385 3072 398411321728698376 130551492759 checked_small_651264 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 652288 396543718536565623 129330408385 397166438977683144 129736920561 2048 398411321728698376 130551492759 checked_small_652288 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 653312 397166438977683144 129736920561 397788646794274644 130143735187 1024 398411321728698376 130551492759 checked_small_653312 checked_small_654336)))))))
#print axioms checked_part_647168
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 622592 32768 378490858220726241 117822786067 398411321728698376 130551492759 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 622592 378490858220726241 117822786067 383470872428028892 120943703215 24576 398411321728698376 130551492759 checked_part_622592 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 630784 383470872428028892 120943703215 388450901365260307 124105425039 16384 398411321728698376 130551492759 checked_part_630784 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 638976 388450901365260307 124105425039 393431252215599799 127308150707 8192 398411321728698376 130551492759 checked_part_638976 checked_part_647168)))
theorem block_sound :
    (398411321728698376 = FrontierCheck209.massFloor FactorFullCertificate209.phi 655360 ∧
     130551492759 = FrontierCheck209.triangle FactorFullCertificate209.phi 655360) ∧
    ∀ t, 622592 < t → t ≤ 655360 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 622592 378490858220726241 117822786067 398411321728698376 130551492759 FullPrefix209_018.endpoint.1 FullPrefix209_018.endpoint.2 checked
theorem endpoint :
    398411321728698376 = FrontierCheck209.massFloor FactorFullCertificate209.phi 655360 ∧
    130551492759 = FrontierCheck209.triangle FactorFullCertificate209.phi 655360 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 655360) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 622592
  · exact FullPrefix209_018.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_019
