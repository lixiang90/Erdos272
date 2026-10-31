import Erdos272.Certificates.ForcedDual209
import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_033
namespace JSP233.FullPrefix209_034
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1114112 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1114112 1024 677299234994878149 377293800811 677921463847893794 377987352243 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1115136 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1115136 1024 677921463847893794 377987352243 678543941962519360 378681818755 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1116160 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1116160 1024 678543941962519360 378681818755 679166778151561826 379377322681 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1117184 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1117184 1024 679166778151561826 379377322681 679789093809080419 380072882653 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1118208 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1118208 1024 679789093809080419 380072882653 680411662192386316 380769362527 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1119232 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1119232 1024 680411662192386316 380769362527 681034241467634229 381466492167 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1120256 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1120256 1024 681034241467634229 381466492167 681656708070151904 382164133057 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1121280 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1121280 1024 681656708070151904 382164133057 682279229087509362 382862472363 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1114112 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1114112 8192 677299234994878149 377293800811 682279229087509362 382862472363 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1114112 677299234994878149 377293800811 677921463847893794 377987352243 7168 682279229087509362 382862472363 checked_small_1114112 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1115136 677921463847893794 377987352243 678543941962519360 378681818755 6144 682279229087509362 382862472363 checked_small_1115136 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1116160 678543941962519360 378681818755 679166778151561826 379377322681 5120 682279229087509362 382862472363 checked_small_1116160 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1117184 679166778151561826 379377322681 679789093809080419 380072882653 4096 682279229087509362 382862472363 checked_small_1117184 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1118208 679789093809080419 380072882653 680411662192386316 380769362527 3072 682279229087509362 382862472363 checked_small_1118208 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1119232 680411662192386316 380769362527 681034241467634229 381466492167 2048 682279229087509362 382862472363 checked_small_1119232 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1120256 681034241467634229 381466492167 681656708070151904 382164133057 1024 682279229087509362 382862472363 checked_small_1120256 checked_small_1121280)))))))
#print axioms checked_part_1114112
private theorem checked_small_1122304 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1122304 1024 682279229087509362 382862472363 682901845145164099 383561555905 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1123328 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1123328 1024 682901845145164099 383561555905 683524252763697831 384261042743 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1124352 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1124352 1024 683524252763697831 384261042743 684146712203946923 384961225133 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1125376 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1125376 1024 684146712203946923 384961225133 684769368424036639 385662266517 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1126400 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1126400 1024 684769368424036639 385662266517 685391812154834685 386363706077 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1127424 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1127424 1024 685391812154834685 386363706077 686014277675184253 387065807535 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1128448 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1128448 1024 686014277675184253 387065807535 686636888738627110 387768710727 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1129472 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1129472 1024 686636888738627110 387768710727 687259220819587832 388471936183 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1122304 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1122304 8192 682279229087509362 382862472363 687259220819587832 388471936183 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1122304 682279229087509362 382862472363 682901845145164099 383561555905 7168 687259220819587832 388471936183 checked_small_1122304 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1123328 682901845145164099 383561555905 683524252763697831 384261042743 6144 687259220819587832 388471936183 checked_small_1123328 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1124352 683524252763697831 384261042743 684146712203946923 384961225133 5120 687259220819587832 388471936183 checked_small_1124352 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1125376 684146712203946923 384961225133 684769368424036639 385662266517 4096 687259220819587832 388471936183 checked_small_1125376 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1126400 684769368424036639 385662266517 685391812154834685 386363706077 3072 687259220819587832 388471936183 checked_small_1126400 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1127424 685391812154834685 386363706077 686014277675184253 387065807535 2048 687259220819587832 388471936183 checked_small_1127424 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1128448 686014277675184253 387065807535 686636888738627110 387768710727 1024 687259220819587832 388471936183 checked_small_1128448 checked_small_1129472)))))))
#print axioms checked_part_1122304
private theorem checked_small_1130496 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1130496 1024 687259220819587832 388471936183 687881757784560679 389176030547 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1131520 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1131520 1024 687881757784560679 389176030547 688504495224485818 389880989455 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1132544 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1132544 1024 688504495224485818 389880989455 689126885426121519 390586192653 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1133568 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1133568 1024 689126885426121519 390586192653 689749484251208149 391292269747 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1134592 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1134592 1024 689749484251208149 391292269747 690372029781056777 391998923945 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1135616 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1135616 1024 690372029781056777 391998923945 690994355483790174 392705965795 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1136640 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1136640 1024 690994355483790174 392705965795 691616937588315719 393413936411 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1137664 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1137664 1024 691616937588315719 393413936411 692239584816341468 394122618773 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1130496 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1130496 8192 687259220819587832 388471936183 692239584816341468 394122618773 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1130496 687259220819587832 388471936183 687881757784560679 389176030547 7168 692239584816341468 394122618773 checked_small_1130496 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1131520 687881757784560679 389176030547 688504495224485818 389880989455 6144 692239584816341468 394122618773 checked_small_1131520 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1132544 688504495224485818 389880989455 689126885426121519 390586192653 5120 692239584816341468 394122618773 checked_small_1132544 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1133568 689126885426121519 390586192653 689749484251208149 391292269747 4096 692239584816341468 394122618773 checked_small_1133568 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1134592 689749484251208149 391292269747 690372029781056777 391998923945 3072 692239584816341468 394122618773 checked_small_1134592 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1135616 690372029781056777 391998923945 690994355483790174 392705965795 2048 692239584816341468 394122618773 checked_small_1135616 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1136640 690994355483790174 392705965795 691616937588315719 393413936411 1024 692239584816341468 394122618773 checked_small_1136640 checked_small_1137664)))))))
#print axioms checked_part_1130496
private theorem checked_small_1138688 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1138688 1024 692239584816341468 394122618773 692861960503312131 394831629381 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1139712 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1139712 1024 692861960503312131 394831629381 693484451490485167 395541408681 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1140736 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1140736 1024 693484451490485167 395541408681 694107178965268120 396252095397 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1141760 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1141760 1024 694107178965268120 396252095397 694729658161341050 396963136275 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1142784 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1142784 1024 694729658161341050 396963136275 695352010403597478 397674669319 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1143808 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1143808 1024 695352010403597478 397674669319 695974613801797421 398387127017 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1144832 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1144832 1024 695974613801797421 398387127017 696597013112949481 399099988491 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1145856 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1145856 1024 696597013112949481 399099988491 697219518584982802 399813608939 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1138688 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1138688 8192 692239584816341468 394122618773 697219518584982802 399813608939 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1138688 692239584816341468 394122618773 692861960503312131 394831629381 7168 697219518584982802 399813608939 checked_small_1138688 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1139712 692861960503312131 394831629381 693484451490485167 395541408681 6144 697219518584982802 399813608939 checked_small_1139712 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1140736 693484451490485167 395541408681 694107178965268120 396252095397 5120 697219518584982802 399813608939 checked_small_1140736 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1141760 694107178965268120 396252095397 694729658161341050 396963136275 4096 697219518584982802 399813608939 checked_small_1141760 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1142784 694729658161341050 396963136275 695352010403597478 397674669319 3072 697219518584982802 399813608939 checked_small_1142784 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1143808 695352010403597478 397674669319 695974613801797421 398387127017 2048 697219518584982802 399813608939 checked_small_1143808 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1144832 695974613801797421 398387127017 696597013112949481 399099988491 1024 697219518584982802 399813608939 checked_small_1144832 checked_small_1145856)))))))
#print axioms checked_part_1138688
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1114112 32768 677299234994878149 377293800811 697219518584982802 399813608939 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1114112 677299234994878149 377293800811 682279229087509362 382862472363 24576 697219518584982802 399813608939 checked_part_1114112 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1122304 682279229087509362 382862472363 687259220819587832 388471936183 16384 697219518584982802 399813608939 checked_part_1122304 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1130496 687259220819587832 388471936183 692239584816341468 394122618773 8192 697219518584982802 399813608939 checked_part_1130496 checked_part_1138688)))
theorem block_sound :
    (697219518584982802 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1146880 ∧
     399813608939 = FrontierCheck209.triangle FactorFullCertificate209.phi 1146880) ∧
    ∀ t, 1114112 < t → t ≤ 1146880 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1114112 677299234994878149 377293800811 697219518584982802 399813608939 FullPrefix209_033.endpoint.1 FullPrefix209_033.endpoint.2 checked
theorem endpoint :
    697219518584982802 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1146880 ∧
    399813608939 = FrontierCheck209.triangle FactorFullCertificate209.phi 1146880 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1146880) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1114112
  · exact FullPrefix209_033.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_034
