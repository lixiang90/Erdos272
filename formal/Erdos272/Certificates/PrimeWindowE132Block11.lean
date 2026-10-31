import Erdos272.Certificates.CoefficientSum132
import Erdos272.Arithmetic.ScaleLogs132
namespace JSP233.PrimeWindowE132.Blocks
open PrefixState131 PrefixTable131 PrefixTable132 ScaleLogs132 PairWindow131 ScaleWindow132 SimplexMoment57 PrefixLog131
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def lowersBlock_000 : List Coeff := [(lowerCut grid ⟨85061317221,85061326760,464767619090,464767624034,2468504039805,2468504247293,10795997672738,42832⟩ 2 (108304247/78125000:ℝ)),(lowerCut grid ⟨81004644512,81004652402,426391902048,426391905343,2149800859546,2149801032125,8351620626252,27209⟩ 3 (1098612289/500000000:ℝ)),(lowerCut grid ⟨75898411395,75898417967,380443978835,380443980812,1789219002836,1789219141100,6020671409572,15320⟩ 5 (16094379129/5000000000:ℝ)),(lowerCut grid ⟨72527620727,72527626733,351584327107,351584328518,1575000115761,1575000235355,4838611062633,10467⟩ 7 (2432387687/625000000:ℝ)),(lowerCut grid ⟨57960574592,57960579514,239672360591,239672360919,842223371456,842223430051,1817223983277,1958⟩ 30 (34011973827/5000000000:ℝ)),(lowerCut grid ⟨54595852273,54595857099,216997966117,216997966351,714559045993,714559093445,1438213658290,1323⟩ 42 (18688348097/2500000000:ℝ)),(lowerCut grid ⟨49487596088,49487600811,184596085791,184596085931,545727810507,545727842401,998474461584,723⟩ 70 (42484952433/5000000000:ℝ)),(lowerCut grid ⟨45432945059,45432949683,160570990491,160570990584,431574608944,431574629542,739553170202,443⟩ 105 (9307920703/1000000000:ℝ)),(lowerCut grid ⟨68012827147,68012832640,314541910632,314541911530,1314624547931,1314624645780,3591285924016,6249⟩ 11 (749342273/156250000:ℝ)),(lowerCut grid ⟨66333181204,66333186558,301528382748,301528383507,1227195514775,1227195605428,3216845037755,5171⟩ 13 (25649493583/5000000000:ℝ)),(lowerCut grid ⟨63647504528,63647509703,280885872830,280885873410,1092991925590,1092992005207,2683712528337,3792⟩ 17 (28332133451/5000000000:ℝ)),(lowerCut grid ⟨62538285107,62538290221,272679352033,272679352552,1041201917385,1041201992717,2491140021309,3340⟩ 19 (29444389803/5000000000:ℝ)),(lowerCut grid ⟨60637849119,60637854143,258682337060,258682337489,954973336299,954973404447,2186395271575,2676⟩ 23 (7838735543/1250000000:ℝ)),(lowerCut grid ⟨58318821850,58318826784,242238035966,242238036306,857141884485,857141944357,1864196507141,2044⟩ 29 (8418239579/1250000000:ℝ)),(lowerCut grid ⟨57651908117,57651913029,237479878910,237479879228,829550406993,829550464500,1777769810693,1887⟩ 31 (17169936031/2500000000:ℝ)),(lowerCut grid ⟨55872483699,55872488558,225478020226,225478020492,761415542257,761415593848,1572588170546,1536⟩ 37 (36109179951/5000000000:ℝ))]

theorem lowersBlock_000_sum : sumCoeff lowersBlock_000 = ⟨(3555572871032600567649582562822267399/91778924109038996222893500000000000:ℝ),(-14244854165237440120726002283651944736955128001/52949379293676343974746250000000000000000000:ℝ),(-27989695295351412920884003/6183948445675000000000:ℝ),(-3035199278:ℝ)⟩ := by
  norm_num [lowersBlock_000,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem lowersBlock_000_bound {N:ℕ} (hlo:97818046≤N) (hhi:N≤97940000) :
    List.Forall₂ (fun r c => eval c N≤(DivCount 3 (N/(r*r)):ℝ)) [2,3,5,7,30,42,70,105,11,13,17,19,23,29,31,37] lowersBlock_000 := by
  have hN1 : 1≤N := by omega
  unfold lowersBlock_000
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=2) hN1 (by decide) state_4945 (by decide) (by simpa using scale_2.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=3) hN1 (by decide) state_3296 (by decide) (by simpa using scale_3.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=5) hN1 (by decide) state_1978 (by decide) (by simpa using scale_5.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=7) hN1 (by decide) state_1412 (by decide) (by simpa using scale_7.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=30) hN1 (by decide) state_329 (by decide) (by simpa using scale_30.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=42) hN1 (by decide) state_235 (by decide) (by simpa using scale_42.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=70) hN1 (by decide) state_141 (by decide) (by simpa using scale_70.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=105) hN1 (by decide) state_94 (by decide) (by simpa using scale_105.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=11) hN1 (by decide) state_899 (by decide) (by simpa using scale_11.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=13) hN1 (by decide) state_760 (by decide) (by simpa using scale_13.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=17) hN1 (by decide) state_581 (by decide) (by simpa using scale_17.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=19) hN1 (by decide) state_520 (by decide) (by simpa using scale_19.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=23) hN1 (by decide) state_430 (by decide) (by simpa using scale_23.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=29) hN1 (by decide) state_341 (by decide) (by simpa using scale_29.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=31) hN1 (by decide) state_319 (by decide) (by simpa using scale_31.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=37) hN1 (by decide) state_267 (by decide) (by simpa using scale_37.2))
  exact .nil

def lowersBlock_001 : List Coeff := [(lowerCut grid ⟨54847966464,54847971296,218757117121,218757117361,724191103770,724191152078,1465395184834,1365⟩ 41 (464196523/62500000:ℝ)),(lowerCut grid ⟨54380790225,54380795045,215537947999,215537948228,706601249108,706601295849,1415933586136,1289⟩ 43 (37612002449/5000000000:ℝ)),(lowerCut grid ⟨53471072454,53471077253,209969393644,209969393853,676545910787,676545954829,1333179190639,1166⟩ 47 (38501477479/5000000000:ℝ)),(lowerCut grid ⟨52257463898,52257468670,201875272917,201875273102,633710182836,633710222977,1219041946890,1005⟩ 53 (39702920753/5000000000:ℝ)),(lowerCut grid ⟨51179935293,51179940046,194676475623,194676475789,596475662831,596475699526,1123438403186,878⟩ 59 (2548461009/312500000:ℝ)),(lowerCut grid ⟨50875960524,50875965272,193342349761,193342349922,589664510792,589664546849,1106306429296,856⟩ 61 (2569296273/312500000:ℝ)),(lowerCut grid ⟨49904323048,49904327778,187157160811,187157160957,558464089550,558464122660,1029257114420,760⟩ 67 (42046927967/5000000000:ℝ)),(lowerCut grid ⟨49344736517,49344741238,183455254991,183455255129,540088213809,540088245162,984964002836,707⟩ 71 (21313400283/2500000000:ℝ)),(lowerCut grid ⟨49052744973,49052749688,181997439260,181997439394,532913796642,532913827303,967888914004,687⟩ 73 (5363074527/625000000:ℝ)),(lowerCut grid ⟨48283134568,48283139269,177083501263,177083501387,508987239150,508987267487,911813130910,623⟩ 79 (43694480351/5000000000:ℝ)),(lowerCut grid ⟨47791232133,47791236822,174045290975,174045291093,494397397131,494397424035,878285947086,586⟩ 83 (11047101979/1250000000:ℝ)),(lowerCut grid ⟨47095299223,47095303896,170220682818,170220682928,476249184446,476249209551,837265733208,542⟩ 89 (11221591387/1250000000:ℝ)),(lowerCut grid ⟨46151202392,46151207039,164764553993,164764554093,450791286729,450791309279,781016441218,484⟩ 97 (914942233/100000000:ℝ)),(lowerCut grid ⟨45747107015,45747111650,162448228689,162448228785,440140704888,440140726359,757935224670,461⟩ 101 (46151207039/5000000000:ℝ)),(lowerCut grid ⟨45643479147,45643483778,162242043122,162242043217,439197465569,439197486943,755904532338,459⟩ 103 (11586822939/1250000000:ℝ)),(lowerCut grid ⟨45217883011,45217887627,159715351051,159715351142,427691787094,427691807295,731279678434,435⟩ 107 (46728290223/5000000000:ℝ))]

theorem lowersBlock_001_sum : sumCoeff lowersBlock_001 = ⟨(46140553303895365103337921768994745016533115804611197772398262793523/299010477300915590655651857836152147480967695800969456209922500000000:ℝ),(-30612011102321367699174075690364833383636205382176456724132055967640200108057/18012679355476842810581437219045310089214921433793340735537500000000000000000:ℝ),(-90252697774440523733971963283625345269121/864595971105746580924066846717500000000:ℝ),(-10930064:ℝ)⟩ := by
  norm_num [lowersBlock_001,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem lowersBlock_001_bound {N:ℕ} (hlo:97818046≤N) (hhi:N≤97940000) :
    List.Forall₂ (fun r c => eval c N≤(DivCount 3 (N/(r*r)):ℝ)) [41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107] lowersBlock_001 := by
  have hN1 : 1≤N := by omega
  unfold lowersBlock_001
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=41) hN1 (by decide) state_241 (by decide) (by simpa using scale_41.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=43) hN1 (by decide) state_230 (by decide) (by simpa using scale_43.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=47) hN1 (by decide) state_210 (by decide) (by simpa using scale_47.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=53) hN1 (by decide) state_186 (by decide) (by simpa using scale_53.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=59) hN1 (by decide) state_167 (by decide) (by simpa using scale_59.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=61) hN1 (by decide) state_162 (by decide) (by simpa using scale_61.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=67) hN1 (by decide) state_147 (by decide) (by simpa using scale_67.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=71) hN1 (by decide) state_139 (by decide) (by simpa using scale_71.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=73) hN1 (by decide) state_135 (by decide) (by simpa using scale_73.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=79) hN1 (by decide) state_125 (by decide) (by simpa using scale_79.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=83) hN1 (by decide) state_119 (by decide) (by simpa using scale_83.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=89) hN1 (by decide) state_111 (by decide) (by simpa using scale_89.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=97) hN1 (by decide) state_101 (by decide) (by simpa using scale_97.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=101) hN1 (by decide) state_97 (by decide) (by simpa using scale_101.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=103) hN1 (by decide) state_96 (by decide) (by simpa using scale_103.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=107) hN1 (by decide) state_92 (by decide) (by simpa using scale_107.2))
  exact .nil

def lowersBlock_002 : List Coeff := [(lowerCut grid ⟨44998093949,44998098556,158623616699,158623616788,422759999458,422760019153,720831106660,425⟩ 109 (46913480703/5000000000:ℝ)),(lowerCut grid ⟨44659078441,44659083034,156156473356,156156473442,411681265386,411681283942,697533971594,403⟩ 113 (5909235009/625000000:ℝ)),(lowerCut grid ⟨43438051510,43438056038,149457569036,149457569112,382156624110,382156639598,636843694162,348⟩ 127 (24220936381/2500000000:ℝ)),(lowerCut grid ⟨43174878437,43174882948,148148614833,148148614907,376481102162,376481117057,625402799082,338⟩ 131 (12187993783/1250000000:ℝ)),(lowerCut grid ⟨42766658509,42766662990,146534101691,146534101762,369525122096,369525136261,611483867352,326⟩ 137 (12299952791/1250000000:ℝ)),(lowerCut grid ⟨42626796096,42626800566,144867435025,144867435095,362397345678,362397359095,597341731728,314⟩ 139 (24672370619/2500000000:ℝ)),(lowerCut grid ⟨41896544787,41896549187,141682317196,141682317261,348908386844,348908398841,570871447762,292⟩ 149 (5003946497/500000000:ℝ)),(lowerCut grid ⟨41743870076,41743874459,140470195984,140470196048,343830017779,343830029242,561024128482,284⟩ 151 (1254320007/125000000:ℝ)),(lowerCut grid ⟨41271341263,41271345586,137808680417,137808680478,332766543802,332766554101,539753449636,267⟩ 157 (5056245997/500000000:ℝ)),(lowerCut grid ⟨40943443063,40943447338,136835650275,136835650334,328756049212,328756059089,532112706952,261⟩ 163 (6367187991/625000000:ℝ)),(lowerCut grid ⟨40775371896,40775376144,134835650275,134835650333,320567360600,320567369621,516620773564,249⟩ 167 (25589970023/2500000000:ℝ)),(lowerCut grid ⟨40430510172,40430514359,133807012053,133807012109,316384839254,316384847838,508764738028,243⟩ 173 (5153291787/500000000:ℝ)),(lowerCut grid ⟨40073329390,40073333504,131676686240,131676686294,307797108410,307797116106,492776158916,231⟩ 179 (12968464997/1250000000:ℝ)),(lowerCut grid ⟨39889838028,39889842101,130949413513,130949413566,304882684455,304882691851,487382560016,227⟩ 181 (51984972243/5000000000:ℝ)),(lowerCut grid ⟨39318253979,39318257902,127936727389,127936727439,292915728458,292915734636,465428224710,211⟩ 191 (6565342027/625000000:ℝ)),(lowerCut grid ⟨39318253979,39318257902,127936727389,127936727439,292915728458,292915734636,465428224710,211⟩ 193 (2105076153/200000000:ℝ))]

theorem lowersBlock_002_sum : sumCoeff lowersBlock_002 = ⟨(639636948949766022830866305278331701794651501270049830663101636270699996270987/30051856959861292712700008538633172820926052076035382528269822942555405000000000:ℝ),(-285637473343359949106411104443878545941127223688706337109298398359299825512617075756293/1096783100724864697543795932066904117552045696205670895192329304472825000000000000000000:ℝ),(-13872536601366256860929038773494529651133329/560163186891969623734786382869521250000000:ℝ),(-1445236:ℝ)⟩ := by
  norm_num [lowersBlock_002,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem lowersBlock_002_bound {N:ℕ} (hlo:97818046≤N) (hhi:N≤97940000) :
    List.Forall₂ (fun r c => eval c N≤(DivCount 3 (N/(r*r)):ℝ)) [109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193] lowersBlock_002 := by
  have hN1 : 1≤N := by omega
  unfold lowersBlock_002
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=109) hN1 (by decide) state_90 (by decide) (by simpa using scale_109.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=113) hN1 (by decide) state_87 (by decide) (by simpa using scale_113.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=127) hN1 (by decide) state_77 (by decide) (by simpa using scale_127.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=131) hN1 (by decide) state_75 (by decide) (by simpa using scale_131.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=137) hN1 (by decide) state_72 (by decide) (by simpa using scale_137.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=139) hN1 (by decide) state_71 (by decide) (by simpa using scale_139.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=149) hN1 (by decide) state_66 (by decide) (by simpa using scale_149.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=151) hN1 (by decide) state_65 (by decide) (by simpa using scale_151.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=157) hN1 (by decide) state_62 (by decide) (by simpa using scale_157.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=163) hN1 (by decide) state_60 (by decide) (by simpa using scale_163.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=167) hN1 (by decide) state_59 (by decide) (by simpa using scale_167.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=173) hN1 (by decide) state_57 (by decide) (by simpa using scale_173.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=179) hN1 (by decide) state_55 (by decide) (by simpa using scale_179.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=181) hN1 (by decide) state_54 (by decide) (by simpa using scale_181.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=191) hN1 (by decide) state_51 (by decide) (by simpa using scale_191.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=193) hN1 (by decide) state_51 (by decide) (by simpa using scale_193.2))
  exact .nil

def lowersBlock_003 : List Coeff := [(lowerCut grid ⟨39120227742,39120231605,127152413664,127152413713,289831943833,289831949702,459827104370,207⟩ 197 (26416019613/2500000000:ℝ)),(lowerCut grid ⟨38918200708,38918204505,125952413664,125952413712,285137516504,285137521909,451341822992,201⟩ 199 (52933050187/5000000000:ℝ))]

theorem lowersBlock_003_sum : sumCoeff lowersBlock_003 = ⟨(31010781110607/24013675140625000:ℝ),(-314923238530244281052417717/19210940112500000000000000000:ℝ),(-90209966449527/49003750000000:ℝ),(-86922:ℝ)⟩ := by
  norm_num [lowersBlock_003,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem lowersBlock_003_bound {N:ℕ} (hlo:97818046≤N) (hhi:N≤97940000) :
    List.Forall₂ (fun r c => eval c N≤(DivCount 3 (N/(r*r)):ℝ)) [197,199] lowersBlock_003 := by
  have hN1 : 1≤N := by omega
  unfold lowersBlock_003
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=197) hN1 (by decide) state_50 (by decide) (by simpa using scale_197.2))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_lower_cut (N:=N) (r:=199) hN1 (by decide) state_49 (by decide) (by simpa using scale_199.2))
  exact .nil

end
end JSP233.PrimeWindowE132.Blocks
