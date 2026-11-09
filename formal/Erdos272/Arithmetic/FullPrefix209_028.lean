module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_027

@[expose] public section
namespace JSP233.FullPrefix209_028
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_917504 : DualFrontier209.checkFrom FactorFullCertificate209.phi 917504 1024 557775833787990876 255880910551 558398181957511392 256452236335 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_918528 : DualFrontier209.checkFrom FactorFullCertificate209.phi 918528 1024 558398181957511392 256452236335 559020835318291086 257024479867 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_919552 : DualFrontier209.checkFrom FactorFullCertificate209.phi 919552 1024 559020835318291086 257024479867 559643376492464619 257597257857 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_920576 : DualFrontier209.checkFrom FactorFullCertificate209.phi 920576 1024 559643376492464619 257597257857 560265637440500160 258170415103 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_921600 : DualFrontier209.checkFrom FactorFullCertificate209.phi 921600 1024 560265637440500160 258170415103 560888315052505542 258744593707 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_922624 : DualFrontier209.checkFrom FactorFullCertificate209.phi 922624 1024 560888315052505542 258744593707 561510951429012610 259319372007 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_923648 : DualFrontier209.checkFrom FactorFullCertificate209.phi 923648 1024 561510951429012610 259319372007 562133283056411694 259894506217 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_924672 : DualFrontier209.checkFrom FactorFullCertificate209.phi 924672 1024 562133283056411694 259894506217 562755814086551788 260470462087 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_917504 : DualFrontier209.checkFrom FactorFullCertificate209.phi 917504 8192 557775833787990876 255880910551 562755814086551788 260470462087 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 917504 557775833787990876 255880910551 558398181957511392 256452236335 7168 562755814086551788 260470462087 checked_small_917504 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 918528 558398181957511392 256452236335 559020835318291086 257024479867 6144 562755814086551788 260470462087 checked_small_918528 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 919552 559020835318291086 257024479867 559643376492464619 257597257857 5120 562755814086551788 260470462087 checked_small_919552 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 920576 559643376492464619 257597257857 560265637440500160 258170415103 4096 562755814086551788 260470462087 checked_small_920576 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 921600 560265637440500160 258170415103 560888315052505542 258744593707 3072 562755814086551788 260470462087 checked_small_921600 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 922624 560888315052505542 258744593707 561510951429012610 259319372007 2048 562755814086551788 260470462087 checked_small_922624 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 923648 561510951429012610 259319372007 562133283056411694 259894506217 1024 562755814086551788 260470462087 checked_small_923648 checked_small_924672)))))))
#print axioms checked_part_917504
private theorem checked_small_925696 : DualFrontier209.checkFrom FactorFullCertificate209.phi 925696 1024 562755814086551788 260470462087 563378524565607797 261047221741 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_926720 : DualFrontier209.checkFrom FactorFullCertificate209.phi 926720 1024 563378524565607797 261047221741 564001025924676165 261624425239 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_927744 : DualFrontier209.checkFrom FactorFullCertificate209.phi 927744 1024 564001025924676165 261624425239 564623322350965686 262202075831 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_928768 : DualFrontier209.checkFrom FactorFullCertificate209.phi 928768 1024 564623322350965686 262202075831 565246103400457926 262780814021 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_929792 : DualFrontier209.checkFrom FactorFullCertificate209.phi 929792 1024 565246103400457926 262780814021 565868358898625020 263359701017 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_930816 : DualFrontier209.checkFrom FactorFullCertificate209.phi 930816 1024 565868358898625020 263359701017 566490893014226653 263939484565 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_931840 : DualFrontier209.checkFrom FactorFullCertificate209.phi 931840 1024 566490893014226653 263939484565 567113726085539793 264520184487 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_932864 : DualFrontier209.checkFrom FactorFullCertificate209.phi 932864 1024 567113726085539793 264520184487 567736042793562667 265101040297 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_925696 : DualFrontier209.checkFrom FactorFullCertificate209.phi 925696 8192 562755814086551788 260470462087 567736042793562667 265101040297 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 925696 562755814086551788 260470462087 563378524565607797 261047221741 7168 567736042793562667 265101040297 checked_small_925696 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 926720 563378524565607797 261047221741 564001025924676165 261624425239 6144 567736042793562667 265101040297 checked_small_926720 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 927744 564001025924676165 261624425239 564623322350965686 262202075831 5120 567736042793562667 265101040297 checked_small_927744 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 928768 564623322350965686 262202075831 565246103400457926 262780814021 4096 567736042793562667 265101040297 checked_small_928768 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 929792 565246103400457926 262780814021 565868358898625020 263359701017 3072 567736042793562667 265101040297 checked_small_929792 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 930816 565868358898625020 263359701017 566490893014226653 263939484565 2048 567736042793562667 265101040297 checked_small_930816 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 931840 566490893014226653 263939484565 567113726085539793 264520184487 1024 567736042793562667 265101040297 checked_small_931840 checked_small_932864)))))))
#print axioms checked_part_925696
private theorem checked_small_933888 : DualFrontier209.checkFrom FactorFullCertificate209.phi 933888 1024 567736042793562667 265101040297 568358601611934367 265682759503 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_934912 : DualFrontier209.checkFrom FactorFullCertificate209.phi 934912 1024 568358601611934367 265682759503 568981003772282357 266264969623 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_935936 : DualFrontier209.checkFrom FactorFullCertificate209.phi 935936 1024 568981003772282357 266264969623 569603506560430319 266847911255 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_936960 : DualFrontier209.checkFrom FactorFullCertificate209.phi 936960 1024 569603506560430319 266847911255 570226103938399156 267431579037 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_937984 : DualFrontier209.checkFrom FactorFullCertificate209.phi 937984 1024 570226103938399156 267431579037 570848669162504045 268015854249 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_939008 : DualFrontier209.checkFrom FactorFullCertificate209.phi 939008 1024 570848669162504045 268015854249 571471076602444258 268600618693 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_940032 : DualFrontier209.checkFrom FactorFullCertificate209.phi 940032 1024 571471076602444258 268600618693 572093609036289344 269186137999 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_941056 : DualFrontier209.checkFrom FactorFullCertificate209.phi 941056 1024 572093609036289344 269186137999 572716262083460711 269772408421 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_933888 : DualFrontier209.checkFrom FactorFullCertificate209.phi 933888 8192 567736042793562667 265101040297 572716262083460711 269772408421 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 933888 567736042793562667 265101040297 568358601611934367 265682759503 7168 572716262083460711 269772408421 checked_small_933888 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 934912 568358601611934367 265682759503 568981003772282357 266264969623 6144 572716262083460711 269772408421 checked_small_934912 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 935936 568981003772282357 266264969623 569603506560430319 266847911255 5120 572716262083460711 269772408421 checked_small_935936 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 936960 569603506560430319 266847911255 570226103938399156 267431579037 4096 572716262083460711 269772408421 checked_small_936960 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 937984 570226103938399156 267431579037 570848669162504045 268015854249 3072 572716262083460711 269772408421 checked_small_937984 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 939008 570848669162504045 268015854249 571471076602444258 268600618693 2048 572716262083460711 269772408421 checked_small_939008 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 940032 571471076602444258 268600618693 572093609036289344 269186137999 1024 572716262083460711 269772408421 checked_small_940032 checked_small_941056)))))))
#print axioms checked_part_933888
private theorem checked_small_942080 : DualFrontier209.checkFrom FactorFullCertificate209.phi 942080 1024 572716262083460711 269772408421 573338722363421586 270359134773 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_943104 : DualFrontier209.checkFrom FactorFullCertificate209.phi 943104 1024 573338722363421586 270359134773 573961148444432529 270946466177 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_944128 : DualFrontier209.checkFrom FactorFullCertificate209.phi 944128 1024 573961148444432529 270946466177 574583838238972119 271534684103 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_945152 : DualFrontier209.checkFrom FactorFullCertificate209.phi 945152 1024 574583838238972119 271534684103 575206098865290661 272123133777 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_946176 : DualFrontier209.checkFrom FactorFullCertificate209.phi 946176 1024 575206098865290661 272123133777 575828604216251710 272712452187 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_947200 : DualFrontier209.checkFrom FactorFullCertificate209.phi 947200 1024 575828604216251710 272712452187 576451470203684233 273302749995 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_948224 : DualFrontier209.checkFrom FactorFullCertificate209.phi 948224 1024 576451470203684233 273302749995 577073810653183766 273893187105 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_949248 : DualFrontier209.checkFrom FactorFullCertificate209.phi 949248 1024 577073810653183766 273893187105 577696225005780916 274484331541 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_942080 : DualFrontier209.checkFrom FactorFullCertificate209.phi 942080 8192 572716262083460711 269772408421 577696225005780916 274484331541 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 942080 572716262083460711 269772408421 573338722363421586 270359134773 7168 577696225005780916 274484331541 checked_small_942080 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 943104 573338722363421586 270359134773 573961148444432529 270946466177 6144 577696225005780916 274484331541 checked_small_943104 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 944128 573961148444432529 270946466177 574583838238972119 271534684103 5120 577696225005780916 274484331541 checked_small_944128 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 945152 574583838238972119 271534684103 575206098865290661 272123133777 4096 577696225005780916 274484331541 checked_small_945152 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 946176 575206098865290661 272123133777 575828604216251710 272712452187 3072 577696225005780916 274484331541 checked_small_946176 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 947200 575828604216251710 272712452187 576451470203684233 273302749995 2048 577696225005780916 274484331541 checked_small_947200 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 948224 576451470203684233 273302749995 577073810653183766 273893187105 1024 577696225005780916 274484331541 checked_small_948224 checked_small_949248)))))))
#print axioms checked_part_942080
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 917504 32768 557775833787990876 255880910551 577696225005780916 274484331541 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 917504 557775833787990876 255880910551 562755814086551788 260470462087 24576 577696225005780916 274484331541 checked_part_917504 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 925696 562755814086551788 260470462087 567736042793562667 265101040297 16384 577696225005780916 274484331541 checked_part_925696 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 933888 567736042793562667 265101040297 572716262083460711 269772408421 8192 577696225005780916 274484331541 checked_part_933888 checked_part_942080)))
theorem block_sound :
    (577696225005780916 = FrontierCheck209.massFloor FactorFullCertificate209.phi 950272 ∧
     274484331541 = FrontierCheck209.triangle FactorFullCertificate209.phi 950272) ∧
    ∀ t, 917504 < t → t ≤ 950272 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 917504 557775833787990876 255880910551 577696225005780916 274484331541 FullPrefix209_027.endpoint.1 FullPrefix209_027.endpoint.2 checked
theorem endpoint :
    577696225005780916 = FrontierCheck209.massFloor FactorFullCertificate209.phi 950272 ∧
    274484331541 = FrontierCheck209.triangle FactorFullCertificate209.phi 950272 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 950272) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 917504
  · exact FullPrefix209_027.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_028
