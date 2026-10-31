import Erdos272.Certificates.CoefficientSum132
import Erdos272.Arithmetic.ScaleLogs132
namespace JSP233.PrimeWindowD132.Blocks
open PrefixState131 PrefixTable131 PrefixTable132 ScaleLogs132 PairWindow131 ScaleWindow132 SimplexMoment57 PrefixLog131
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def uppersBlock_004 : List Coeff := [(upperCut grid ⟨43040648239,43040652741,147348614833,147348614906,373027111888,373027126421,618474595848,332⟩ ⟨42904591724,42904596216,146808074293,146808074365,370700590362,370700604651,613824690296,328⟩ 134 (24489197677/2500000000:ℝ)),(upperCut grid ⟨39120227742,39120231605,127152413664,127152413713,289831943833,289831949702,459827104370,207⟩ ⟨38918200708,38918204505,125952413664,125952413712,285137516504,285137521909,451341822992,201⟩ 201 (10606609287/1000000000:ℝ)),(upperCut grid ⟨34011973800,34011973833,103236662171,103236662200,201767306339,201767306504,308685982152,111⟩ ⟨33672958284,33672958316,100569995505,100569995533,192697446659,192697446815,294080047280,103⟩ 335 (3633831417/312500000:ℝ)),(upperCut grid ⟨30910424521,30910424546,89314641622,89314641643,156156877493,156156877610,236984337414,74⟩ ⟨30445224365,30445224389,87496459804,87496459824,150536800308,150536800419,228456308758,70⟩ 469 (61506025037/5000000000:ℝ)),(upperCut grid ⟨42484949753,42484954211,144585744885,144585744954,361196590859,361196604149,594968168410,312⟩ ⟨42341062386,42341066831,143442887743,143442887811,356341168031,356341180810,585406339530,304⟩ 142 (49558267899/5000000000:ℝ)),(upperCut grid ⟨38501473837,38501477479,123256835434,123256835480,274689767881,274689772276,432622351975,188⟩ ⟨38286411839,38286415391,122831303520,122831303565,273051407293,273051411532,429705052145,186⟩ 213 (2680645949/250000000:ℝ)),(upperCut grid ⟨33322045086,33322045117,99880340333,99880340360,190375173674,190375173827,290366140516,101⟩ ⟨32958368645,32958368675,97737483191,97737483217,183234735442,183234735587,279027206320,95⟩ 355 (58721175217/5000000000:ℝ)),(upperCut grid ⟨29957322724,29957322747,85591697900,85591697919,144737709953,144737710059,219727593146,66⟩ ⟨29444389781,29444389803,82591697900,82591697918,135750513136,135750513234,206311185278,60⟩ 497 (31042948791/2500000000:ℝ)),(upperCut grid ⟨42195074400,42195078831,142863177599,142863177666,353886613690,353886626211,580590905406,300⟩ ⟨42046923551,42046927967,141980824658,141980824724,350163518890,350163531020,573314836650,294⟩ 146 (49836063527/5000000000:ℝ)),(upperCut grid ⟨38286411839,38286415391,122831303520,122831303565,273051407293,273051411532,429705052145,186⟩ ⟨38066622832,38066626284,121961738303,121961738347,269722154090,269722158019,423807373897,182⟩ 219 (3368169663/312500000:ℝ)),(upperCut grid ⟨33322045086,33322045117,99880340333,99880340360,190375173674,190375173827,290366140516,101⟩ ⟨32958368645,32958368675,97737483191,97737483217,183234735442,183234735587,279027206320,95⟩ 365 (11799794169/1000000000:ℝ)),(upperCut grid ⟨29957322724,29957322747,85591697900,85591697919,144737709953,144737710059,219727593146,66⟩ ⟨29444389781,29444389803,82591697900,82591697918,135750513136,135750513234,206311185278,60⟩ 511 (6236369321/500000000:ℝ)),(upperCut grid ⟨41431344664,41431349008,138761061369,138761061431,336712386150,336712396864,547312739098,273⟩ ⟨41271341263,41271345586,137808680417,137808680478,332766543802,332766554101,539753449636,267⟩ 158 (5062594761/500000000:ℝ)),(upperCut grid ⟨37376694343,37376697419,118799652328,118799652369,257736950748,257736953609,402767790241,168⟩ ⟨37135718922,37135721840,116894890424,116894890464,250617580397,250617582672,390423522241,160⟩ 237 (54680598691/5000000000:ℝ)),(upperCut grid ⟨32580965366,32580965395,96256001710,96256001735,178352014162,178352014301,271329202728,91⟩ ⟨32188758235,32188758263,94717540172,94717540196,173339557952,173339558086,263484557320,87⟩ 395 (3736803433/312500000:ℝ)),(upperCut grid ⟨28903717569,28903717590,81539066322,81539066339,132651103686,132651103781,201722870600,58⟩ ⟨28332133431,28332133451,78205732989,78205733005,123016531163,123016531250,187580734976,52⟩ 553 (63153577293/5000000000:ℝ))]

theorem uppersBlock_004_sum : sumCoeff uppersBlock_004 = ⟨(94266555195862067049575891/11063270736126266700000000000:ℝ),(-22177934205290673954088576092102340799/207436326302367500625000000000000000000:ℝ),(21020957795000167141/1800331246875000000:ℝ),(-542478:ℝ)⟩ := by
  norm_num [uppersBlock_004,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_004_bound {N:ℕ} (hlo:97568046≤N) (hhi:N≤97818046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [134,201,335,469,142,213,355,497,146,219,365,511,158,237,395,553] uppersBlock_004 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_004
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=134) hN1 (by decide) state_74 state_73 (by decide) (by decide) (Nat.le_trans (by decide : 73^2*134^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤74^2*134^2)) (by simpa using scale_134.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=201) hN1 (by decide) state_50 state_49 (by decide) (by decide) (Nat.le_trans (by decide : 49^2*201^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤50^2*201^2)) (by simpa using scale_201.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=335) hN1 (by decide) state_30 state_29 (by decide) (by decide) (Nat.le_trans (by decide : 29^2*335^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤30^2*335^2)) (by simpa using scale_335.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=469) hN1 (by decide) state_22 state_21 (by decide) (by decide) (Nat.le_trans (by decide : 21^2*469^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤22^2*469^2)) (by simpa using scale_469.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=142) hN1 (by decide) state_70 state_69 (by decide) (by decide) (Nat.le_trans (by decide : 69^2*142^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤70^2*142^2)) (by simpa using scale_142.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=213) hN1 (by decide) state_47 state_46 (by decide) (by decide) (Nat.le_trans (by decide : 46^2*213^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤47^2*213^2)) (by simpa using scale_213.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=355) hN1 (by decide) state_28 state_27 (by decide) (by decide) (Nat.le_trans (by decide : 27^2*355^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤28^2*355^2)) (by simpa using scale_355.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=497) hN1 (by decide) state_20 state_19 (by decide) (by decide) (Nat.le_trans (by decide : 19^2*497^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤20^2*497^2)) (by simpa using scale_497.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=146) hN1 (by decide) state_68 state_67 (by decide) (by decide) (Nat.le_trans (by decide : 67^2*146^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤68^2*146^2)) (by simpa using scale_146.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=219) hN1 (by decide) state_46 state_45 (by decide) (by decide) (Nat.le_trans (by decide : 45^2*219^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤46^2*219^2)) (by simpa using scale_219.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=365) hN1 (by decide) state_28 state_27 (by decide) (by decide) (Nat.le_trans (by decide : 27^2*365^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤28^2*365^2)) (by simpa using scale_365.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=511) hN1 (by decide) state_20 state_19 (by decide) (by decide) (Nat.le_trans (by decide : 19^2*511^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤20^2*511^2)) (by simpa using scale_511.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=158) hN1 (by decide) state_63 state_62 (by decide) (by decide) (Nat.le_trans (by decide : 62^2*158^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤63^2*158^2)) (by simpa using scale_158.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=237) hN1 (by decide) state_42 state_41 (by decide) (by decide) (Nat.le_trans (by decide : 41^2*237^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤42^2*237^2)) (by simpa using scale_237.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=395) hN1 (by decide) state_26 state_25 (by decide) (by decide) (Nat.le_trans (by decide : 25^2*395^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤26^2*395^2)) (by simpa using scale_395.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=553) hN1 (by decide) state_18 state_17 (by decide) (by decide) (Nat.le_trans (by decide : 17^2*553^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤18^2*553^2)) (by simpa using scale_553.1))
  exact .nil

def uppersBlock_005 : List Coeff := [(upperCut grid ⟨40943443063,40943447338,136835650275,136835650334,328756049212,328756059089,532112706952,261⟩ ⟨40775371896,40775376144,134835650275,134835650333,320567360600,320567369621,516620773564,249⟩ 166 (12779968787/1250000000:ℝ)),(upperCut grid ⟨36888792903,36888795643,116407085546,116407085585,248806081913,248806084045,387300047003,158⟩ ⟨36635614944,36635617482,114407085546,114407085584,241428323333,241428324916,374650936355,150⟩ 249 (55174526229/5000000000:ℝ)),(upperCut grid ⟨31780538290,31780538317,93517540172,93517540195,169476906964,169476907094,257484557320,84⟩ ⟨31354942146,31354942172,90184206839,90184206861,158883394201,158883394321,241154625696,76⟩ 415 (30141391233/2500000000:ℝ)),(upperCut grid ⟨28903717569,28903717590,81539066322,81539066339,132651103686,132651103781,201722870600,58⟩ ⟨28332133431,28332133451,78205732989,78205733005,123016531163,123016531250,187580734976,52⟩ 581 (63647504831/5000000000:ℝ)),(upperCut grid ⟨40253514422,40253518574,133105257668,133105257723,313547610470,313547618760,503466608596,239⟩ ⟨40073329390,40073333504,131676686240,131676686294,307797108410,307797116106,492776158916,231⟩ 178 (51817832749/5000000000:ℝ)),(upperCut grid ⟨36375860217,36375862526,113381444521,113381444558,237670824365,237670825687,368245810199,146⟩ ⟨35835188338,35835190090,111788272403,111788272438,231889938994,231889939961,358468973603,140⟩ 267 (5587248383/500000000:ℝ)),(upperCut grid ⟨31354942146,31354942172,90184206839,90184206861,158883394201,158883394321,241154625696,76⟩ ⟨30910424521,30910424546,89314641622,89314641643,156156877493,156156877610,236984337414,74⟩ 445 (60980740067/5000000000:ℝ)),(upperCut grid ⟨27725887213,27725887232,77029262401,77029262416,119683338995,119683339079,182730022474,50⟩ ⟨27080502002,27080502020,73904262401,73904262415,111018999241,111018999318,170230022474,45⟩ 623 (2010795701/156250000:ℝ)),(upperCut grid ⟨39318253979,39318257902,127936727389,127936727439,292915728458,292915734636,465428224710,211⟩ ⟨39120227742,39120231605,127152413664,127152413713,289831943833,289831949702,459827104370,207⟩ 194 (26339289409/2500000000:ℝ)),(upperCut grid ⟨35263604640,35263605658,108145415261,108145415294,218867887079,218867887445,336707739560,127⟩ ⟨34965075281,34965075844,106968944673,106968944705,214719227710,214719227955,329847796152,123⟩ 291 (56733229899/5000000000:ℝ)),(upperCut grid ⟨30445224365,30445224389,87496459804,87496459824,150536800308,150536800419,228456308758,70⟩ ⟨29957322724,29957322747,85591697900,85591697919,144737709953,144737710059,219727593146,66⟩ 485 (7730185767/625000000:ℝ)),(upperCut grid ⟨27080502002,27080502020,73904262401,73904262415,111018999241,111018999318,170230022474,45⟩ ⟨26390573288,26390573305,71237595735,71237595748,103797532041,103797532112,159902066882,41⟩ 679 (65206208501/5000000000:ℝ)),(upperCut grid ⟨38918200708,38918204505,125952413664,125952413712,285137516504,285137521909,451341822992,201⟩ ⟨38712007880,38712011604,125340168767,125340168814,282754769522,282754774694,447056108705,198⟩ 202 (10616534839/1000000000:ℝ)),(upperCut grid ⟨34965075281,34965075844,106968944673,106968944705,214719227710,214719227955,329847796152,123⟩ ⟨34657359011,34657359046,105756823461,105756823492,210481036767,210481036943,322884689912,119⟩ 303 (14284331319/1250000000:ℝ)),(upperCut grid ⟨29957322724,29957322747,85591697900,85591697919,144737709953,144737710059,219727593146,66⟩ ⟨29444389781,29444389803,82591697900,82591697918,135750513136,135750513234,206311185278,60⟩ 505 (62245581513/5000000000:ℝ)),(upperCut grid ⟨26390573288,26390573305,71237595735,71237595748,103797532041,103797532112,159902066882,41⟩ ⟨25649493567,25649493583,68380452878,68380452890,96257368245,96257368310,149211617202,37⟩ 707 (32805151939/2500000000:ℝ))]

theorem uppersBlock_005_sum : sumCoeff uppersBlock_005 = ⟨(1386521269234300928749497761/288716109313031245125000000000:ℝ),(-178381839096119573951034888505397858939/2887161093130312451250000000000000000000:ℝ),(144634622336173827901/18997240237500000000:ℝ),(-295792:ℝ)⟩ := by
  norm_num [uppersBlock_005,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_005_bound {N:ℕ} (hlo:97568046≤N) (hhi:N≤97818046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [166,249,415,581,178,267,445,623,194,291,485,679,202,303,505,707] uppersBlock_005 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_005
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=166) hN1 (by decide) state_60 state_59 (by decide) (by decide) (Nat.le_trans (by decide : 59^2*166^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤60^2*166^2)) (by simpa using scale_166.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=249) hN1 (by decide) state_40 state_39 (by decide) (by decide) (Nat.le_trans (by decide : 39^2*249^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤40^2*249^2)) (by simpa using scale_249.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=415) hN1 (by decide) state_24 state_23 (by decide) (by decide) (Nat.le_trans (by decide : 23^2*415^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤24^2*415^2)) (by simpa using scale_415.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=581) hN1 (by decide) state_18 state_17 (by decide) (by decide) (Nat.le_trans (by decide : 17^2*581^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤18^2*581^2)) (by simpa using scale_581.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=178) hN1 (by decide) state_56 state_55 (by decide) (by decide) (Nat.le_trans (by decide : 55^2*178^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤56^2*178^2)) (by simpa using scale_178.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=267) hN1 (by decide) state_38 state_36 (by decide) (by decide) (Nat.le_trans (by decide : 36^2*267^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤38^2*267^2)) (by simpa using scale_267.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=445) hN1 (by decide) state_23 state_22 (by decide) (by decide) (Nat.le_trans (by decide : 22^2*445^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤23^2*445^2)) (by simpa using scale_445.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=623) hN1 (by decide) state_16 state_15 (by decide) (by decide) (Nat.le_trans (by decide : 15^2*623^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤16^2*623^2)) (by simpa using scale_623.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=194) hN1 (by decide) state_51 state_50 (by decide) (by decide) (Nat.le_trans (by decide : 50^2*194^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤51^2*194^2)) (by simpa using scale_194.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=291) hN1 (by decide) state_34 state_33 (by decide) (by decide) (Nat.le_trans (by decide : 33^2*291^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤34^2*291^2)) (by simpa using scale_291.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=485) hN1 (by decide) state_21 state_20 (by decide) (by decide) (Nat.le_trans (by decide : 20^2*485^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤21^2*485^2)) (by simpa using scale_485.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=679) hN1 (by decide) state_15 state_14 (by decide) (by decide) (Nat.le_trans (by decide : 14^2*679^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤15^2*679^2)) (by simpa using scale_679.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=202) hN1 (by decide) state_49 state_48 (by decide) (by decide) (Nat.le_trans (by decide : 48^2*202^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤49^2*202^2)) (by simpa using scale_202.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=303) hN1 (by decide) state_33 state_32 (by decide) (by decide) (Nat.le_trans (by decide : 32^2*303^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤33^2*303^2)) (by simpa using scale_303.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=505) hN1 (by decide) state_20 state_19 (by decide) (by decide) (Nat.le_trans (by decide : 19^2*505^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤20^2*505^2)) (by simpa using scale_505.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=707) hN1 (by decide) state_14 state_13 (by decide) (by decide) (Nat.le_trans (by decide : 13^2*707^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤14^2*707^2)) (by simpa using scale_707.1))
  exact .nil

def uppersBlock_006 : List Coeff := [(upperCut grid ⟨38918200708,38918204505,125952413664,125952413712,285137516504,285137521909,451341822992,201⟩ ⟨38501473837,38501477479,123256835434,123256835480,274689767881,274689772276,432622351975,188⟩ 206 (26639379453/2500000000:ℝ)),(upperCut grid ⟨34965075281,34965075844,106968944673,106968944705,214719227710,214719227955,329847796152,123⟩ ⟨34339872028,34339872062,103881823461,103881823491,203982781953,203982782121,312278088194,113⟩ 309 (57333409987/5000000000:ℝ)),(upperCut grid ⟨29957322724,29957322747,85591697900,85591697919,144737709953,144737710059,219727593146,66⟩ ⟨29444389781,29444389803,82591697900,82591697918,135750513136,135750513234,206311185278,60⟩ 515 (3902604139/312500000:ℝ)),(upperCut grid ⟨26390573288,26390573305,71237595735,71237595748,103797532041,103797532112,159902066882,41⟩ ⟨25649493567,25649493583,68380452878,68380452890,96257368245,96257368310,149211617202,37⟩ 721 (65806388589/5000000000:ℝ)),(upperCut grid ⟨38501473837,38501477479,123256835434,123256835480,274689767881,274689772276,432622351975,188⟩ ⟨38286411839,38286415391,122831303520,122831303565,273051407293,273051411532,429705052145,186⟩ 214 (53659757363/5000000000:ℝ)),(upperCut grid ⟨34339872028,34339872062,103881823461,103881823491,203982781953,203982782121,312278088194,113⟩ ⟨34011973800,34011973833,103236662171,103236662200,201767306339,201767306504,308685982152,111⟩ 321 (14428602111/1250000000:ℝ)),(upperCut grid ⟨29444389781,29444389803,82591697900,82591697918,135750513136,135750513234,206311185278,60⟩ ⟨28903717569,28903717590,81539066322,81539066339,132651103686,132651103781,201722870600,58⟩ 535 (62822664681/5000000000:ℝ)),(upperCut grid ⟨26390573288,26390573305,71237595735,71237595748,103797532041,103797532112,159902066882,41⟩ ⟨25649493567,25649493583,68380452878,68380452890,96257368245,96257368310,149211617202,37⟩ 749 (33093693523/2500000000:ℝ)),(upperCut grid ⟨38286411839,38286415391,122831303520,122831303565,273051407293,273051411532,429705052145,186⟩ ⟨38066622832,38066626284,121961738303,121961738347,269722154090,269722158019,423807373897,182⟩ 218 (26922473919/2500000000:ℝ)),(upperCut grid ⟨34339872028,34339872062,103881823461,103881823491,203982781953,203982782121,312278088194,113⟩ ⟨34011973800,34011973833,103236662171,103236662200,201767306339,201767306504,308685982152,111⟩ 327 (57899598919/5000000000:ℝ)),(upperCut grid ⟨29444389781,29444389803,82591697900,82591697918,135750513136,135750513234,206311185278,60⟩ ⟨28903717569,28903717590,81539066322,81539066339,132651103686,132651103781,201722870600,58⟩ 545 (15751963789/1250000000:ℝ)),(upperCut grid ⟨25649493567,25649493583,68380452878,68380452890,96257368245,96257368310,149211617202,37⟩ ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ 763 (66372577521/5000000000:ℝ)),(upperCut grid ⟨37841894340,37841897681,120628404970,120628405013,264646604380,264646607847,414863101987,176⟩ ⟨37611999233,37612002449,119264768607,119264768649,259486346061,259486349072,405817761649,170⟩ 226 (27102673599/2500000000:ℝ)),(upperCut grid ⟨34011973800,34011973833,103236662171,103236662200,201767306339,201767306504,308685982152,111⟩ ⟨33672958284,33672958316,100569995505,100569995533,192697446659,192697446815,294080047280,103⟩ 339 (58259998279/5000000000:ℝ)),(upperCut grid ⟨28903717569,28903717590,81539066322,81539066339,132651103686,132651103781,201722870600,58⟩ ⟨28332133431,28332133451,78205732989,78205733005,123016531163,123016531250,187580734976,52⟩ 565 (15842063629/1250000000:ℝ)),(upperCut grid ⟨25649493567,25649493583,68380452878,68380452890,96257368245,96257368310,149211617202,37⟩ ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ 791 (66732976881/5000000000:ℝ))]

theorem uppersBlock_006_sum : sumCoeff uppersBlock_006 = ⟨(44887010139809476343351233/13820162545771236750000000000:ℝ),(-61715381733020372956310494831594777267/1451117067305979858750000000000000000000:ℝ),(135810754908557197299/23755489975000000000:ℝ),(-198204:ℝ)⟩ := by
  norm_num [uppersBlock_006,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_006_bound {N:ℕ} (hlo:97568046≤N) (hhi:N≤97818046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [206,309,515,721,214,321,535,749,218,327,545,763,226,339,565,791] uppersBlock_006 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_006
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=206) hN1 (by decide) state_49 state_47 (by decide) (by decide) (Nat.le_trans (by decide : 47^2*206^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤49^2*206^2)) (by simpa using scale_206.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=309) hN1 (by decide) state_33 state_31 (by decide) (by decide) (Nat.le_trans (by decide : 31^2*309^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤33^2*309^2)) (by simpa using scale_309.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=515) hN1 (by decide) state_20 state_19 (by decide) (by decide) (Nat.le_trans (by decide : 19^2*515^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤20^2*515^2)) (by simpa using scale_515.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=721) hN1 (by decide) state_14 state_13 (by decide) (by decide) (Nat.le_trans (by decide : 13^2*721^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤14^2*721^2)) (by simpa using scale_721.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=214) hN1 (by decide) state_47 state_46 (by decide) (by decide) (Nat.le_trans (by decide : 46^2*214^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤47^2*214^2)) (by simpa using scale_214.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=321) hN1 (by decide) state_31 state_30 (by decide) (by decide) (Nat.le_trans (by decide : 30^2*321^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤31^2*321^2)) (by simpa using scale_321.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=535) hN1 (by decide) state_19 state_18 (by decide) (by decide) (Nat.le_trans (by decide : 18^2*535^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤19^2*535^2)) (by simpa using scale_535.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=749) hN1 (by decide) state_14 state_13 (by decide) (by decide) (Nat.le_trans (by decide : 13^2*749^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤14^2*749^2)) (by simpa using scale_749.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=218) hN1 (by decide) state_46 state_45 (by decide) (by decide) (Nat.le_trans (by decide : 45^2*218^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤46^2*218^2)) (by simpa using scale_218.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=327) hN1 (by decide) state_31 state_30 (by decide) (by decide) (Nat.le_trans (by decide : 30^2*327^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤31^2*327^2)) (by simpa using scale_327.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=545) hN1 (by decide) state_19 state_18 (by decide) (by decide) (Nat.le_trans (by decide : 18^2*545^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤19^2*545^2)) (by simpa using scale_545.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=763) hN1 (by decide) state_13 state_12 (by decide) (by decide) (Nat.le_trans (by decide : 12^2*763^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤13^2*763^2)) (by simpa using scale_763.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=226) hN1 (by decide) state_44 state_43 (by decide) (by decide) (Nat.le_trans (by decide : 43^2*226^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤44^2*226^2)) (by simpa using scale_226.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=339) hN1 (by decide) state_30 state_29 (by decide) (by decide) (Nat.le_trans (by decide : 29^2*339^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤30^2*339^2)) (by simpa using scale_339.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=565) hN1 (by decide) state_18 state_17 (by decide) (by decide) (Nat.le_trans (by decide : 17^2*565^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤18^2*565^2)) (by simpa using scale_565.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=791) hN1 (by decide) state_13 state_12 (by decide) (by decide) (Nat.le_trans (by decide : 12^2*791^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤13^2*791^2)) (by simpa using scale_791.1))
  exact .nil

def uppersBlock_007 : List Coeff := [(upperCut grid ⟨36635614944,36635617482,114407085546,114407085584,241428323333,241428324916,374650936355,150⟩ ⟨36375860217,36375862526,113381444521,113381444558,237670824365,237670825687,368245810199,146⟩ 254 (55373339861/5000000000:ℝ)),(upperCut grid ⟨32580965366,32580965395,96256001710,96256001735,178352014162,178352014301,271329202728,91⟩ ⟨32188758235,32188758263,94717540172,94717540196,173339557952,173339558086,263484557320,87⟩ 381 (29713995471/2500000000:ℝ)),(upperCut grid ⟨27725887213,27725887232,77029262401,77029262416,119683338995,119683339079,182730022474,50⟩ ⟨27080502002,27080502020,73904262401,73904262415,111018999241,111018999318,170230022474,45⟩ 635 (64536247179/5000000000:ℝ)),(upperCut grid ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ 889 (8487621193/625000000:ℝ)),(upperCut grid ⟨36375860217,36375862526,113381444521,113381444558,237670824365,237670825687,368245810199,146⟩ ⟨36109177902,36109179951,112328812943,112328812979,233841786448,233841787526,361756953351,142⟩ 262 (27841721113/2500000000:ℝ)),(upperCut grid ⟨32580965366,32580965395,96256001710,96256001735,178352014162,178352014301,271329202728,91⟩ ⟨32188758235,32188758263,94717540172,94717540196,173339557952,173339558086,263484557320,87⟩ 393 (59738093307/5000000000:ℝ)),(upperCut grid ⟨27725887213,27725887232,77029262401,77029262416,119683338995,119683339079,182730022474,50⟩ ⟨27080502002,27080502020,73904262401,73904262415,111018999241,111018999318,170230022474,45⟩ 655 (8105793693/625000000:ℝ)),(upperCut grid ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ 917 (68211071909/5000000000:ℝ)),(upperCut grid ⟨36109177902,36109179951,112328812943,112328812979,233841786448,233841787526,361756953351,142⟩ ⟨35835188338,35835190090,111788272403,111788272438,231889938994,231889939961,358468973603,140⟩ 274 (7016409781/625000000:ℝ)),(upperCut grid ⟨32188758235,32188758263,94717540172,94717540196,173339557952,173339558086,263484557320,87⟩ ⟨31780538290,31780538317,93517540172,93517540195,169476906964,169476907094,257484557320,84⟩ 411 (60185929329/5000000000:ℝ)),(upperCut grid ⟨27080502002,27080502020,73904262401,73904262415,111018999241,111018999318,170230022474,45⟩ ⟨26390573288,26390573305,71237595735,71237595748,103797532041,103797532112,159902066882,41⟩ 685 (32647092783/2500000000:ℝ)),(upperCut grid ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ 959 (68658907931/5000000000:ℝ)),(upperCut grid ⟨35835188338,35835190090,111788272403,111788272438,231889938994,231889939961,358468973603,140⟩ ⟨35553479773,35553481184,109288272403,109288272437,222931141910,222931142438,343468973600,131⟩ 278 (175863151/15625000:ℝ)),(upperCut grid ⟨31780538290,31780538317,93517540172,93517540195,169476906964,169476907094,257484557320,84⟩ ⟨31354942146,31354942172,90184206839,90184206861,158883394201,158883394321,241154625696,76⟩ 417 (60330859401/5000000000:ℝ)),(upperCut grid ⟨27080502002,27080502020,73904262401,73904262415,111018999241,111018999318,170230022474,45⟩ ⟨26390573288,26390573305,71237595735,71237595748,103797532041,103797532112,159902066882,41⟩ 695 (32719557819/2500000000:ℝ)),(upperCut grid ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ 973 (68803838003/5000000000:ℝ))]

theorem uppersBlock_007_sum : sumCoeff uppersBlock_007 = ⟨(8608914670776432082223793083/4426488675824053652100000000000:ℝ),(-89993678913050657234000733828996472139/3458194277987541915703125000000000000000:ℝ),(108364111501014890793/27721609212500000000:ℝ),(-116651:ℝ)⟩ := by
  norm_num [uppersBlock_007,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_007_bound {N:ℕ} (hlo:97568046≤N) (hhi:N≤97818046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [254,381,635,889,262,393,655,917,274,411,685,959,278,417,695,973] uppersBlock_007 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_007
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=254) hN1 (by decide) state_39 state_38 (by decide) (by decide) (Nat.le_trans (by decide : 38^2*254^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤39^2*254^2)) (by simpa using scale_254.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=381) hN1 (by decide) state_26 state_25 (by decide) (by decide) (Nat.le_trans (by decide : 25^2*381^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤26^2*381^2)) (by simpa using scale_381.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=635) hN1 (by decide) state_16 state_15 (by decide) (by decide) (Nat.le_trans (by decide : 15^2*635^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤16^2*635^2)) (by simpa using scale_635.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=889) hN1 (by decide) state_12 state_11 (by decide) (by decide) (Nat.le_trans (by decide : 11^2*889^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤12^2*889^2)) (by simpa using scale_889.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=262) hN1 (by decide) state_38 state_37 (by decide) (by decide) (Nat.le_trans (by decide : 37^2*262^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤38^2*262^2)) (by simpa using scale_262.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=393) hN1 (by decide) state_26 state_25 (by decide) (by decide) (Nat.le_trans (by decide : 25^2*393^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤26^2*393^2)) (by simpa using scale_393.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=655) hN1 (by decide) state_16 state_15 (by decide) (by decide) (Nat.le_trans (by decide : 15^2*655^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤16^2*655^2)) (by simpa using scale_655.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=917) hN1 (by decide) state_11 state_10 (by decide) (by decide) (Nat.le_trans (by decide : 10^2*917^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤11^2*917^2)) (by simpa using scale_917.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=274) hN1 (by decide) state_37 state_36 (by decide) (by decide) (Nat.le_trans (by decide : 36^2*274^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤37^2*274^2)) (by simpa using scale_274.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=411) hN1 (by decide) state_25 state_24 (by decide) (by decide) (Nat.le_trans (by decide : 24^2*411^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤25^2*411^2)) (by simpa using scale_411.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=685) hN1 (by decide) state_15 state_14 (by decide) (by decide) (Nat.le_trans (by decide : 14^2*685^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤15^2*685^2)) (by simpa using scale_685.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=959) hN1 (by decide) state_11 state_10 (by decide) (by decide) (Nat.le_trans (by decide : 10^2*959^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤11^2*959^2)) (by simpa using scale_959.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=278) hN1 (by decide) state_36 state_35 (by decide) (by decide) (Nat.le_trans (by decide : 35^2*278^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤36^2*278^2)) (by simpa using scale_278.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=417) hN1 (by decide) state_24 state_23 (by decide) (by decide) (Nat.le_trans (by decide : 23^2*417^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤24^2*417^2)) (by simpa using scale_417.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=695) hN1 (by decide) state_15 state_14 (by decide) (by decide) (Nat.le_trans (by decide : 14^2*695^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤15^2*695^2)) (by simpa using scale_695.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=973) hN1 (by decide) state_11 state_10 (by decide) (by decide) (Nat.le_trans (by decide : 10^2*973^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤11^2*973^2)) (by simpa using scale_973.1))
  exact .nil

end
end JSP233.PrimeWindowD132.Blocks
