import Erdos272.Certificates.ForcedDual209
import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_032
namespace JSP233.FullPrefix209_033
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1081344 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1081344 1024 657378556047990272 355426304111 658000880029067265 356099569183 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1082368 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1082368 1024 658000880029067265 356099569183 658623763563609485 356774077533 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1083392 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1083392 1024 658623763563609485 356774077533 659245963313020871 357448482579 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1084416 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1084416 1024 659245963313020871 357448482579 659868528523212181 358123921119 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1085440 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1085440 1024 659868528523212181 358123921119 660491186635584880 358800098155 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1086464 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1086464 1024 660491186635584880 358800098155 661113650064107248 359476701221 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1087488 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1087488 1024 661113650064107248 359476701221 661736085319055023 360153910965 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1088512 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1088512 1024 661736085319055023 360153910965 662358687841605437 360831940239 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1081344 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1081344 8192 657378556047990272 355426304111 662358687841605437 360831940239 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1081344 657378556047990272 355426304111 658000880029067265 356099569183 7168 662358687841605437 360831940239 checked_small_1081344 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1082368 658000880029067265 356099569183 658623763563609485 356774077533 6144 662358687841605437 360831940239 checked_small_1082368 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1083392 658623763563609485 356774077533 659245963313020871 357448482579 5120 662358687841605437 360831940239 checked_small_1083392 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1084416 659245963313020871 357448482579 659868528523212181 358123921119 4096 662358687841605437 360831940239 checked_small_1084416 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1085440 659868528523212181 358123921119 660491186635584880 358800098155 3072 662358687841605437 360831940239 checked_small_1085440 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1086464 660491186635584880 358800098155 661113650064107248 359476701221 2048 662358687841605437 360831940239 checked_small_1086464 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1087488 661113650064107248 359476701221 661736085319055023 360153910965 1024 662358687841605437 360831940239 checked_small_1087488 checked_small_1088512)))))))
#print axioms checked_part_1081344
private theorem checked_small_1089536 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1089536 1024 662358687841605437 360831940239 662981095216251693 361510394335 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1090560 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1090560 1024 662981095216251693 361510394335 663603824874522412 362189837457 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1091584 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1091584 1024 663603824874522412 362189837457 664226360099118427 362869706031 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1092608 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1092608 1024 664226360099118427 362869706031 664848508859563971 363549789455 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1093632 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1093632 1024 664848508859563971 363549789455 665471091813225045 364230984869 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1094656 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1094656 1024 665471091813225045 364230984869 666093835294870195 364912993757 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1095680 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1095680 1024 666093835294870195 364912993757 666716312622697172 365595348677 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1096704 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1096704 1024 666716312622697172 365595348677 667338726959728407 366278271831 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1089536 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1089536 8192 662358687841605437 360831940239 667338726959728407 366278271831 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1089536 662358687841605437 360831940239 662981095216251693 361510394335 7168 667338726959728407 366278271831 checked_small_1089536 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1090560 662981095216251693 361510394335 663603824874522412 362189837457 6144 667338726959728407 366278271831 checked_small_1090560 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1091584 663603824874522412 362189837457 664226360099118427 362869706031 5120 667338726959728407 366278271831 checked_small_1091584 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1092608 664226360099118427 362869706031 664848508859563971 363549789455 4096 667338726959728407 366278271831 checked_small_1092608 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1093632 664848508859563971 363549789455 665471091813225045 364230984869 3072 667338726959728407 366278271831 checked_small_1093632 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1094656 665471091813225045 364230984869 666093835294870195 364912993757 2048 667338726959728407 366278271831 checked_small_1094656 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1095680 666093835294870195 364912993757 666716312622697172 365595348677 1024 667338726959728407 366278271831 checked_small_1095680 checked_small_1096704)))))))
#print axioms checked_part_1089536
private theorem checked_small_1097728 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1097728 1024 667338726959728407 366278271831 667961478670708064 366962202915 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1098752 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1098752 1024 667961478670708064 366962202915 668583789337554171 367646286897 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1099776 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1099776 1024 668583789337554171 367646286897 669206325615147820 368331256257 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1100800 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1100800 1024 669206325615147820 368331256257 669829004255338826 369017019975 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1101824 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1101824 1024 669829004255338826 369017019975 670451402849935397 369703112631 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1102848 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1102848 1024 670451402849935397 369703112631 671073819416794353 370389862341 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1103872 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1103872 1024 671073819416794353 370389862341 671696445646108570 371077480963 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1104896 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1104896 1024 671696445646108570 371077480963 672318871262385291 371765515401 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1097728 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1097728 8192 667338726959728407 366278271831 672318871262385291 371765515401 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1097728 667338726959728407 366278271831 667961478670708064 366962202915 7168 672318871262385291 371765515401 checked_small_1097728 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1098752 667961478670708064 366962202915 668583789337554171 367646286897 6144 672318871262385291 371765515401 checked_small_1098752 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1099776 668583789337554171 367646286897 669206325615147820 368331256257 5120 672318871262385291 371765515401 checked_small_1099776 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1100800 669206325615147820 368331256257 669829004255338826 369017019975 4096 672318871262385291 371765515401 checked_small_1100800 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1101824 669829004255338826 369017019975 670451402849935397 369703112631 3072 672318871262385291 371765515401 checked_small_1101824 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1102848 670451402849935397 369703112631 671073819416794353 370389862341 2048 672318871262385291 371765515401 checked_small_1102848 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1103872 671073819416794353 370389862341 671696445646108570 371077480963 1024 672318871262385291 371765515401 checked_small_1103872 checked_small_1104896)))))))
#print axioms checked_part_1097728
private theorem checked_small_1105920 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1105920 1024 672318871262385291 371765515401 672941513301309669 372454426675 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1106944 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1106944 1024 672941513301309669 372454426675 673564019436795313 373143825085 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1107968 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1107968 1024 673564019436795313 373143825085 674186384542708490 373833704531 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1108992 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1108992 1024 674186384542708490 373833704531 674808942970372502 374524435711 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1110016 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1110016 1024 674808942970372502 374524435711 675431575362469093 375215886613 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1111040 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1111040 1024 675431575362469093 375215886613 676054063165765731 375907814411 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1112064 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1112064 1024 676054063165765731 375907814411 676676526623312107 376600352507 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1113088 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1113088 1024 676676526623312107 376600352507 677299234994878149 377293800811 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1105920 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1105920 8192 672318871262385291 371765515401 677299234994878149 377293800811 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1105920 672318871262385291 371765515401 672941513301309669 372454426675 7168 677299234994878149 377293800811 checked_small_1105920 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1106944 672941513301309669 372454426675 673564019436795313 373143825085 6144 677299234994878149 377293800811 checked_small_1106944 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1107968 673564019436795313 373143825085 674186384542708490 373833704531 5120 677299234994878149 377293800811 checked_small_1107968 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1108992 674186384542708490 373833704531 674808942970372502 374524435711 4096 677299234994878149 377293800811 checked_small_1108992 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1110016 674808942970372502 374524435711 675431575362469093 375215886613 3072 677299234994878149 377293800811 checked_small_1110016 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1111040 675431575362469093 375215886613 676054063165765731 375907814411 2048 677299234994878149 377293800811 checked_small_1111040 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1112064 676054063165765731 375907814411 676676526623312107 376600352507 1024 677299234994878149 377293800811 checked_small_1112064 checked_small_1113088)))))))
#print axioms checked_part_1105920
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1081344 32768 657378556047990272 355426304111 677299234994878149 377293800811 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1081344 657378556047990272 355426304111 662358687841605437 360831940239 24576 677299234994878149 377293800811 checked_part_1081344 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1089536 662358687841605437 360831940239 667338726959728407 366278271831 16384 677299234994878149 377293800811 checked_part_1089536 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1097728 667338726959728407 366278271831 672318871262385291 371765515401 8192 677299234994878149 377293800811 checked_part_1097728 checked_part_1105920)))
theorem block_sound :
    (677299234994878149 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1114112 ∧
     377293800811 = FrontierCheck209.triangle FactorFullCertificate209.phi 1114112) ∧
    ∀ t, 1081344 < t → t ≤ 1114112 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1081344 657378556047990272 355426304111 677299234994878149 377293800811 FullPrefix209_032.endpoint.1 FullPrefix209_032.endpoint.2 checked
theorem endpoint :
    677299234994878149 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1114112 ∧
    377293800811 = FrontierCheck209.triangle FactorFullCertificate209.phi 1114112 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1114112) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1081344
  · exact FullPrefix209_032.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_033
