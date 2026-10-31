import Erdos272.Certificates.ForcedDual209
import Erdos272.Arithmetic.DualFrontier209
import Erdos272.Arithmetic.FactorFullCertificate209
import Erdos272.Arithmetic.SplitChecks209
import Erdos272.Arithmetic.FullPrefix209_034
namespace JSP233.FullPrefix209_035
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1146880 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1146880 1024 697219518584982802 399813608939 697842358103729923 400528250271 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1147904 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1147904 1024 697842358103729923 400528250271 698464567414367861 401242805661 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1148928 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1148928 1024 698464567414367861 401242805661 699087176087628775 401958457123 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1149952 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1149952 1024 699087176087628775 401958457123 699709758953798812 402674716531 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1150976 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1150976 1024 699709758953798812 402674716531 700332159521574107 403391403519 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1152000 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1152000 1024 700332159521574107 403391403519 700954780350496544 404108981693 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1153024 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1153024 1024 700954780350496544 404108981693 701577299827657698 404827080569 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1154048 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1154048 1024 701577299827657698 404827080569 702199744427509716 405545730423 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1146880 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1146880 8192 697219518584982802 399813608939 702199744427509716 405545730423 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1146880 697219518584982802 399813608939 697842358103729923 400528250271 7168 702199744427509716 405545730423 checked_small_1146880 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1147904 697842358103729923 400528250271 698464567414367861 401242805661 6144 702199744427509716 405545730423 checked_small_1147904 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1148928 698464567414367861 401242805661 699087176087628775 401958457123 5120 702199744427509716 405545730423 checked_small_1148928 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1149952 699087176087628775 401958457123 699709758953798812 402674716531 4096 702199744427509716 405545730423 checked_small_1149952 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1150976 699709758953798812 402674716531 700332159521574107 403391403519 3072 702199744427509716 405545730423 checked_small_1150976 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1152000 700332159521574107 403391403519 700954780350496544 404108981693 2048 702199744427509716 405545730423 checked_small_1152000 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1153024 700954780350496544 404108981693 701577299827657698 404827080569 1024 702199744427509716 405545730423 checked_small_1153024 checked_small_1154048)))))))
#print axioms checked_part_1146880
private theorem checked_small_1155072 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1155072 1024 702199744427509716 405545730423 702822263048522060 406265103161 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1156096 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1156096 1024 702822263048522060 406265103161 703444910727326997 406985262691 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1157120 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1157120 1024 703444910727326997 406985262691 704067288652692694 407705747531 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1158144 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1158144 1024 704067288652692694 407705747531 704689853657369330 408427086399 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1159168 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1159168 1024 704689853657369330 408427086399 705312545337064191 409149209791 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1160192 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1160192 1024 705312545337064191 409149209791 705934721836136039 409871372763 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1161216 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1161216 1024 705934721836136039 409871372763 706557234699568428 410594563433 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1162240 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1162240 1024 706557234699568428 410594563433 707180136071022409 411318843487 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1155072 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1155072 8192 702199744427509716 405545730423 707180136071022409 411318843487 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1155072 702199744427509716 405545730423 702822263048522060 406265103161 7168 707180136071022409 411318843487 checked_small_1155072 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1156096 702822263048522060 406265103161 703444910727326997 406985262691 6144 707180136071022409 411318843487 checked_small_1156096 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1157120 703444910727326997 406985262691 704067288652692694 407705747531 5120 707180136071022409 411318843487 checked_small_1157120 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1158144 704067288652692694 407705747531 704689853657369330 408427086399 4096 707180136071022409 411318843487 checked_small_1158144 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1159168 704689853657369330 408427086399 705312545337064191 409149209791 3072 707180136071022409 411318843487 checked_small_1159168 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1160192 705312545337064191 409149209791 705934721836136039 409871372763 2048 707180136071022409 411318843487 checked_small_1160192 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1161216 705934721836136039 409871372763 706557234699568428 410594563433 1024 707180136071022409 411318843487 checked_small_1161216 checked_small_1162240)))))))
#print axioms checked_part_1155072
private theorem checked_small_1163264 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1163264 1024 707180136071022409 411318843487 707802474569289985 412043106431 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1164288 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1164288 1024 707802474569289985 412043106431 708424882570379238 412768087465 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1165312 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1165312 1024 708424882570379238 412768087465 709047496121474790 413493945471 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1166336 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1166336 1024 709047496121474790 413493945471 709669979932580044 414220289681 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1167360 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1167360 1024 709669979932580044 414220289681 710292543773722507 414947364783 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1168384 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1168384 1024 710292543773722507 414947364783 710915145076970954 415675121251 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1169408 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1169408 1024 710915145076970954 415675121251 711537504924838574 416403232739 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1170432 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1170432 1024 711537504924838574 416403232739 712160017886590499 417132160729 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1163264 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1163264 8192 707180136071022409 411318843487 712160017886590499 417132160729 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1163264 707180136071022409 411318843487 707802474569289985 412043106431 7168 712160017886590499 417132160729 checked_small_1163264 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1164288 707802474569289985 412043106431 708424882570379238 412768087465 6144 712160017886590499 417132160729 checked_small_1164288 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1165312 708424882570379238 412768087465 709047496121474790 413493945471 5120 712160017886590499 417132160729 checked_small_1165312 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1166336 709047496121474790 413493945471 709669979932580044 414220289681 4096 712160017886590499 417132160729 checked_small_1166336 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1167360 709669979932580044 414220289681 710292543773722507 414947364783 3072 712160017886590499 417132160729 checked_small_1167360 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1168384 710292543773722507 414947364783 710915145076970954 415675121251 2048 712160017886590499 417132160729 checked_small_1168384 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1169408 710915145076970954 415675121251 711537504924838574 416403232739 1024 712160017886590499 417132160729 checked_small_1169408 checked_small_1170432)))))))
#print axioms checked_part_1163264
private theorem checked_small_1171456 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1171456 1024 712160017886590499 417132160729 712782594253988821 417861800511 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1172480 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1172480 1024 712782594253988821 417861800511 713405070895099919 418591960841 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1173504 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1173504 1024 713405070895099919 418591960841 714027522022683713 419322728579 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1174528 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1174528 1024 714027522022683713 419322728579 714650142065838268 420054332209 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1175552 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1175552 1024 714650142065838268 420054332209 715272473168191168 420786233545 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1176576 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1176576 1024 715272473168191168 420786233545 715895081499848370 421519098425 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1177600 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1177600 1024 715895081499848370 421519098425 716517902335004662 422252851409 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1178624 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1178624 1024 716517902335004662 422252851409 717140127776494276 422986540117 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1171456 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1171456 8192 712160017886590499 417132160729 717140127776494276 422986540117 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1171456 712160017886590499 417132160729 712782594253988821 417861800511 7168 717140127776494276 422986540117 checked_small_1171456 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1172480 712782594253988821 417861800511 713405070895099919 418591960841 6144 717140127776494276 422986540117 checked_small_1172480 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1173504 713405070895099919 418591960841 714027522022683713 419322728579 5120 717140127776494276 422986540117 checked_small_1173504 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1174528 714027522022683713 419322728579 714650142065838268 420054332209 4096 717140127776494276 422986540117 checked_small_1174528 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1175552 714650142065838268 420054332209 715272473168191168 420786233545 3072 717140127776494276 422986540117 checked_small_1175552 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1176576 715272473168191168 420786233545 715895081499848370 421519098425 2048 717140127776494276 422986540117 checked_small_1176576 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1177600 715895081499848370 421519098425 716517902335004662 422252851409 1024 717140127776494276 422986540117 checked_small_1177600 checked_small_1178624)))))))
#print axioms checked_part_1171456
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1146880 32768 697219518584982802 399813608939 717140127776494276 422986540117 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1146880 697219518584982802 399813608939 702199744427509716 405545730423 24576 717140127776494276 422986540117 checked_part_1146880 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1155072 702199744427509716 405545730423 707180136071022409 411318843487 16384 717140127776494276 422986540117 checked_part_1155072 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1163264 707180136071022409 411318843487 712160017886590499 417132160729 8192 717140127776494276 422986540117 checked_part_1163264 checked_part_1171456)))
theorem block_sound :
    (717140127776494276 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1179648 ∧
     422986540117 = FrontierCheck209.triangle FactorFullCertificate209.phi 1179648) ∧
    ∀ t, 1146880 < t → t ≤ 1179648 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1146880 697219518584982802 399813608939 717140127776494276 422986540117 FullPrefix209_034.endpoint.1 FullPrefix209_034.endpoint.2 checked
theorem endpoint :
    717140127776494276 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1179648 ∧
    422986540117 = FrontierCheck209.triangle FactorFullCertificate209.phi 1179648 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1179648) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1146880
  · exact FullPrefix209_034.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_035
