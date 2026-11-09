module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_014

@[expose] public section
namespace JSP233.FullPrefix209_015
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_491520 : DualFrontier209.checkFrom FactorFullCertificate209.phi 491520 1024 298808435651494805 73435187345 299431034145306250 73741525875 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_492544 : DualFrontier209.checkFrom FactorFullCertificate209.phi 492544 1024 299431034145306250 73741525875 300053703628073544 74048537073 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_493568 : DualFrontier209.checkFrom FactorFullCertificate209.phi 493568 1024 300053703628073544 74048537073 300676026868191084 74356014791 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_494592 : DualFrontier209.checkFrom FactorFullCertificate209.phi 494592 1024 300676026868191084 74356014791 301298445342005078 74664176765 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_495616 : DualFrontier209.checkFrom FactorFullCertificate209.phi 495616 1024 301298445342005078 74664176765 301921166838586813 74973126483 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_496640 : DualFrontier209.checkFrom FactorFullCertificate209.phi 496640 1024 301921166838586813 74973126483 302543728814496991 75282634695 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_497664 : DualFrontier209.checkFrom FactorFullCertificate209.phi 497664 1024 302543728814496991 75282634695 303166036352022987 75592653569 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_498688 : DualFrontier209.checkFrom FactorFullCertificate209.phi 498688 1024 303166036352022987 75592653569 303788811688118638 75903543237 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_491520 : DualFrontier209.checkFrom FactorFullCertificate209.phi 491520 8192 298808435651494805 73435187345 303788811688118638 75903543237 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 491520 298808435651494805 73435187345 299431034145306250 73741525875 7168 303788811688118638 75903543237 checked_small_491520 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 492544 299431034145306250 73741525875 300053703628073544 74048537073 6144 303788811688118638 75903543237 checked_small_492544 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 493568 300053703628073544 74048537073 300676026868191084 74356014791 5120 303788811688118638 75903543237 checked_small_493568 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 494592 300676026868191084 74356014791 301298445342005078 74664176765 4096 303788811688118638 75903543237 checked_small_494592 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 495616 301298445342005078 74664176765 301921166838586813 74973126483 3072 303788811688118638 75903543237 checked_small_495616 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 496640 301921166838586813 74973126483 302543728814496991 75282634695 2048 303788811688118638 75903543237 checked_small_496640 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 497664 302543728814496991 75282634695 303166036352022987 75592653569 1024 303788811688118638 75903543237 checked_small_497664 checked_small_498688)))))))
#print axioms checked_part_491520
private theorem checked_small_499712 : DualFrontier209.checkFrom FactorFullCertificate209.phi 499712 1024 303788811688118638 75903543237 304411031489043560 76214792707 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_500736 : DualFrontier209.checkFrom FactorFullCertificate209.phi 500736 1024 304411031489043560 76214792707 305033582054761951 76526844993 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_501760 : DualFrontier209.checkFrom FactorFullCertificate209.phi 501760 1024 305033582054761951 76526844993 305656408656964928 76839673597 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_502784 : DualFrontier209.checkFrom FactorFullCertificate209.phi 502784 1024 305656408656964928 76839673597 306278748943740571 77152895283 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_503808 : DualFrontier209.checkFrom FactorFullCertificate209.phi 503808 1024 306278748943740571 77152895283 306901212283911096 77466816183 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_504832 : DualFrontier209.checkFrom FactorFullCertificate209.phi 504832 1024 306901212283911096 77466816183 307523765654766422 77781419975 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_505856 : DualFrontier209.checkFrom FactorFullCertificate209.phi 505856 1024 307523765654766422 77781419975 308146229600364841 78096615971 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_506880 : DualFrontier209.checkFrom FactorFullCertificate209.phi 506880 1024 308146229600364841 78096615971 308768823075875770 78412515103 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_499712 : DualFrontier209.checkFrom FactorFullCertificate209.phi 499712 8192 303788811688118638 75903543237 308768823075875770 78412515103 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 499712 303788811688118638 75903543237 304411031489043560 76214792707 7168 308768823075875770 78412515103 checked_small_499712 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 500736 304411031489043560 76214792707 305033582054761951 76526844993 6144 308768823075875770 78412515103 checked_small_500736 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 501760 305033582054761951 76526844993 305656408656964928 76839673597 5120 308768823075875770 78412515103 checked_small_501760 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 502784 305656408656964928 76839673597 306278748943740571 77152895283 4096 308768823075875770 78412515103 checked_small_502784 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 503808 306278748943740571 77152895283 306901212283911096 77466816183 3072 308768823075875770 78412515103 checked_small_503808 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 504832 306901212283911096 77466816183 307523765654766422 77781419975 2048 308768823075875770 78412515103 checked_small_504832 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 505856 307523765654766422 77781419975 308146229600364841 78096615971 1024 308768823075875770 78412515103 checked_small_505856 checked_small_506880)))))))
#print axioms checked_part_499712
private theorem checked_small_507904 : DualFrontier209.checkFrom FactorFullCertificate209.phi 507904 1024 308768823075875770 78412515103 309391378739559314 78729032607 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_508928 : DualFrontier209.checkFrom FactorFullCertificate209.phi 508928 1024 309391378739559314 78729032607 310013741388273108 79046089217 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_509952 : DualFrontier209.checkFrom FactorFullCertificate209.phi 509952 1024 310013741388273108 79046089217 310636324820769070 79363895781 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_510976 : DualFrontier209.checkFrom FactorFullCertificate209.phi 510976 1024 310636324820769070 79363895781 311259044173722788 79682409529 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_512000 : DualFrontier209.checkFrom FactorFullCertificate209.phi 512000 1024 311259044173722788 79682409529 311881351984618770 80001350023 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_513024 : DualFrontier209.checkFrom FactorFullCertificate209.phi 513024 1024 311881351984618770 80001350023 312503778455782478 80320988539 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_514048 : DualFrontier209.checkFrom FactorFullCertificate209.phi 514048 1024 312503778455782478 80320988539 313126632333430884 80641484467 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_515072 : DualFrontier209.checkFrom FactorFullCertificate209.phi 515072 1024 313126632333430884 80641484467 313748910621233874 80962321489 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_507904 : DualFrontier209.checkFrom FactorFullCertificate209.phi 507904 8192 308768823075875770 78412515103 313748910621233874 80962321489 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 507904 308768823075875770 78412515103 309391378739559314 78729032607 7168 313748910621233874 80962321489 checked_small_507904 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 508928 309391378739559314 78729032607 310013741388273108 79046089217 6144 313748910621233874 80962321489 checked_small_508928 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 509952 310013741388273108 79046089217 310636324820769070 79363895781 5120 313748910621233874 80962321489 checked_small_509952 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 510976 310636324820769070 79363895781 311259044173722788 79682409529 4096 313748910621233874 80962321489 checked_small_510976 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 512000 311259044173722788 79682409529 311881351984618770 80001350023 3072 313748910621233874 80962321489 checked_small_512000 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 513024 311881351984618770 80001350023 312503778455782478 80320988539 2048 313748910621233874 80962321489 checked_small_513024 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 514048 312503778455782478 80320988539 313126632333430884 80641484467 1024 313748910621233874 80962321489 checked_small_514048 checked_small_515072)))))))
#print axioms checked_part_507904
private theorem checked_small_516096 : DualFrontier209.checkFrom FactorFullCertificate209.phi 516096 1024 313748910621233874 80962321489 314371424403657809 81283917263 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_517120 : DualFrontier209.checkFrom FactorFullCertificate209.phi 517120 1024 314371424403657809 81283917263 314994118840871592 81606244085 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_518144 : DualFrontier209.checkFrom FactorFullCertificate209.phi 518144 1024 314994118840871592 81606244085 315616490690046127 81929041249 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_519168 : DualFrontier209.checkFrom FactorFullCertificate209.phi 519168 1024 315616490690046127 81929041249 316238992661580852 82252543265 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_520192 : DualFrontier209.checkFrom FactorFullCertificate209.phi 520192 1024 316238992661580852 82252543265 316861533800965568 82576703123 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_521216 : DualFrontier209.checkFrom FactorFullCertificate209.phi 521216 1024 316861533800965568 82576703123 317483972176126225 82901446813 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_522240 : DualFrontier209.checkFrom FactorFullCertificate209.phi 522240 1024 317483972176126225 82901446813 318106566749351281 83226909533 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_523264 : DualFrontier209.checkFrom FactorFullCertificate209.phi 523264 1024 318106566749351281 83226909533 318729258473855633 83553060809 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_516096 : DualFrontier209.checkFrom FactorFullCertificate209.phi 516096 8192 313748910621233874 80962321489 318729258473855633 83553060809 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 516096 313748910621233874 80962321489 314371424403657809 81283917263 7168 318729258473855633 83553060809 checked_small_516096 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 517120 314371424403657809 81283917263 314994118840871592 81606244085 6144 318729258473855633 83553060809 checked_small_517120 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 518144 314994118840871592 81606244085 315616490690046127 81929041249 5120 318729258473855633 83553060809 checked_small_518144 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 519168 315616490690046127 81929041249 316238992661580852 82252543265 4096 318729258473855633 83553060809 checked_small_519168 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 520192 316238992661580852 82252543265 316861533800965568 82576703123 3072 318729258473855633 83553060809 checked_small_520192 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 521216 316861533800965568 82576703123 317483972176126225 82901446813 2048 318729258473855633 83553060809 checked_small_521216 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 522240 317483972176126225 82901446813 318106566749351281 83226909533 1024 318729258473855633 83553060809 checked_small_522240 checked_small_523264)))))))
#print axioms checked_part_516096
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 491520 32768 298808435651494805 73435187345 318729258473855633 83553060809 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 491520 298808435651494805 73435187345 303788811688118638 75903543237 24576 318729258473855633 83553060809 checked_part_491520 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 499712 303788811688118638 75903543237 308768823075875770 78412515103 16384 318729258473855633 83553060809 checked_part_499712 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 507904 308768823075875770 78412515103 313748910621233874 80962321489 8192 318729258473855633 83553060809 checked_part_507904 checked_part_516096)))
theorem block_sound :
    (318729258473855633 = FrontierCheck209.massFloor FactorFullCertificate209.phi 524288 ∧
     83553060809 = FrontierCheck209.triangle FactorFullCertificate209.phi 524288) ∧
    ∀ t, 491520 < t → t ≤ 524288 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 491520 298808435651494805 73435187345 318729258473855633 83553060809 FullPrefix209_014.endpoint.1 FullPrefix209_014.endpoint.2 checked
theorem endpoint :
    318729258473855633 = FrontierCheck209.massFloor FactorFullCertificate209.phi 524288 ∧
    83553060809 = FrontierCheck209.triangle FactorFullCertificate209.phi 524288 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 524288) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 491520
  · exact FullPrefix209_014.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_015
