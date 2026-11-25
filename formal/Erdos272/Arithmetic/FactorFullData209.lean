module

public import Erdos272.Arithmetic.FactorPack209
public import Erdos272.Arithmetic.MarkerSieve209
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section
namespace JSP233.FactorFullData209
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def Limit : Nat := 1670000
def PrimeBound : Nat := 1292
def denominator (i : Nat) : Nat :=
  if i < 32 then
    if i < 16 then
      if i < 8 then
        if i < 4 then
          if i < 2 then
            if i < 1 then
              1
            else
              256
          else
            if i < 3 then
              65536
            else
              16777216
        else
          if i < 6 then
            if i < 5 then
              4294967296
            else
              1099511627776
          else
            if i < 7 then
              281474976710656
            else
              72057594037927936
      else
        if i < 12 then
          if i < 10 then
            if i < 9 then
              18446744073709551616
            else
              4722366482869645213696
          else
            if i < 11 then
              1208925819614629174706176
            else
              309485009821345068724781056
        else
          if i < 14 then
            if i < 13 then
              79228162514264337593543950336
            else
              20282409603651670423947251286016
          else
            if i < 15 then
              5192296858534827628530496329220096
            else
              1329227995784915872903807060280344576
    else
      if i < 24 then
        if i < 20 then
          if i < 18 then
            if i < 17 then
              340282366920938463463374607431768211456
            else
              87112285931760246646623899502532662132736
          else
            if i < 19 then
              22300745198530623141535718272648361505980416
            else
              5708990770823839524233143877797980545530986496
        else
          if i < 22 then
            if i < 21 then
              1461501637330902918203684832716283019655932542976
            else
              374144419156711147060143317175368453031918731001856
          else
            if i < 23 then
              95780971304118053647396689196894323976171195136475136
            else
              24519928653854221733733552434404946937899825954937634816
      else
        if i < 28 then
          if i < 26 then
            if i < 25 then
              6277101735386680763835789423207666416102355444464034512896
            else
              1606938044258990275541962092341162602522202993782792835301376
          else
            if i < 27 then
              411376139330301510538742295639337626245683966408394965837152256
            else
              105312291668557186697918027683670432318895095400549111254310977536
        else
          if i < 30 then
            if i < 29 then
              26959946667150639794667015087019630673637144422540572481103610249216
            else
              6901746346790563787434755862277025452451108972170386555162524223799296
          else
            if i < 31 then
              1766847064778384329583297500742918515827483896875618958121606201292619776
            else
              452312848583266388373324160190187140051835877600158453279131187530910662656
  else
    if i < 48 then
      if i < 40 then
        if i < 36 then
          if i < 34 then
            if i < 33 then
              115792089237316195423570985008687907853269984665640564039457584007913129639936
            else
              29642774844752946028434172162224104410437116074403984394101141506025761187823616
          else
            if i < 35 then
              7588550360256754183279148073529370729071901715047420004889892225542594864082845696
            else
              1942668892225729070919461906823518906642406839052139521251812409738904285205208498176
        else
          if i < 38 then
            if i < 37 then
              497323236409786642155382248146820840100456150797347717440463976893159497012533375533056
            else
              127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336
          else
            if i < 39 then
              32592575621351777380295131014550050576823494298654980010178247189670100796213387298934358016
            else
              8343699359066055009355553539724812947666814540455674882605631280555545803830627148527195652096
      else
        if i < 44 then
          if i < 42 then
            if i < 41 then
              2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576
            else
              546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763456
          else
            if i < 43 then
              139984046386112763159840142535527767382602843577165595931249318810236991948760059086304843329475444736
            else
              35835915874844867368919076489095108449946327955754392558399825615420669938882575126094039892345713852416
        else
          if i < 46 then
            if i < 45 then
              9173994463960286046443283581208347763186259956673124494950355357547691504353939232280074212440502746218496
            else
              2348542582773833227889480596789337027375682548908319870707290971532209025114608443463698998384768703031934976
          else
            if i < 47 then
              601226901190101306339707032778070279008174732520529886901066488712245510429339761526706943586500787976175353856
            else
              153914086704665934422965000391185991426092731525255651046673021110334850669910978950836977558144201721900890587136
    else
      if i < 56 then
        if i < 52 then
          if i < 50 then
            if i < 49 then
              39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816
            else
              10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896
          else
            if i < 51 then
              2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376
            else
              661055968790248598951915308032771039828404682964281219284648795274405791236311345825189210439715284847591212025023358304256
        else
          if i < 54 then
            if i < 53 then
              169230328010303641331690318856389386196071598838855992136870091590247882556495704531248437872567112920983350278405979725889536
            else
              43322963970637732180912721627235682866194329302747133987038743447103457934462900359999600095377180907771737671271930809827721216
          else
            if i < 55 then
              11090678776483259438313656736572334813745748301503266300681918322458485231222502492159897624416558312389564843845614287315896631296
            else
              2839213766779714416208296124562517712318911565184836172974571090549372219192960637992933791850638927971728600024477257552869537611776
      else
        if i < 60 then
          if i < 58 then
            if i < 57 then
              726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656
            else
              186070713419675363980626894819329160794532188335953423432061490990243657757029868371504908982723472783555205531204141550984858016925351936
          else
            if i < 59 then
              47634102635436893179040485073748265163400240214004076398607741693502376385799646303105256699577209032590132615988260237052123652332890095616
            else
              12194330274671844653834364178879555881830461494785043558043581873536608354764709453594945715091765512343073949692994620685343654997219864477696
        else
          if i < 62 then
            if i < 61 then
              3121748550315992231381597229793166305748598142664971150859156959625371738819765620120306103063491971159826931121406622895447975679288285306290176
            else
              799167628880894011233688890827050574271641124522232614619944181664095165137859998750798362384253944616915694367080095461234681773897801038410285056
          else
            if i < 63 then
              204586912993508866875824356051724947013540127877691549342705710506008362275292159680204380770369009821930417757972504438076078534117837065833032974336
            else
              52374249726338269920211035149241586435466272736689036631732661889538140742474792878132321477214466514414186946040961136147476104734166288853256441430016

def primeAt (i : Nat) : Nat :=
  if i < 128 then
    if i < 64 then
      if i < 32 then
        if i < 16 then
          if i < 8 then
            if i < 4 then
              if i < 2 then
                if i < 1 then
                  0
                else
                  2
              else
                if i < 3 then
                  3
                else
                  5
            else
              if i < 6 then
                if i < 5 then
                  7
                else
                  11
              else
                if i < 7 then
                  13
                else
                  17
          else
            if i < 12 then
              if i < 10 then
                if i < 9 then
                  19
                else
                  23
              else
                if i < 11 then
                  29
                else
                  31
            else
              if i < 14 then
                if i < 13 then
                  37
                else
                  41
              else
                if i < 15 then
                  43
                else
                  47
        else
          if i < 24 then
            if i < 20 then
              if i < 18 then
                if i < 17 then
                  53
                else
                  59
              else
                if i < 19 then
                  61
                else
                  67
            else
              if i < 22 then
                if i < 21 then
                  71
                else
                  73
              else
                if i < 23 then
                  79
                else
                  83
          else
            if i < 28 then
              if i < 26 then
                if i < 25 then
                  89
                else
                  97
              else
                if i < 27 then
                  101
                else
                  103
            else
              if i < 30 then
                if i < 29 then
                  107
                else
                  109
              else
                if i < 31 then
                  113
                else
                  127
      else
        if i < 48 then
          if i < 40 then
            if i < 36 then
              if i < 34 then
                if i < 33 then
                  131
                else
                  137
              else
                if i < 35 then
                  139
                else
                  149
            else
              if i < 38 then
                if i < 37 then
                  151
                else
                  157
              else
                if i < 39 then
                  163
                else
                  167
          else
            if i < 44 then
              if i < 42 then
                if i < 41 then
                  173
                else
                  179
              else
                if i < 43 then
                  181
                else
                  191
            else
              if i < 46 then
                if i < 45 then
                  193
                else
                  197
              else
                if i < 47 then
                  199
                else
                  211
        else
          if i < 56 then
            if i < 52 then
              if i < 50 then
                if i < 49 then
                  223
                else
                  227
              else
                if i < 51 then
                  229
                else
                  233
            else
              if i < 54 then
                if i < 53 then
                  239
                else
                  241
              else
                if i < 55 then
                  251
                else
                  257
          else
            if i < 60 then
              if i < 58 then
                if i < 57 then
                  263
                else
                  269
              else
                if i < 59 then
                  271
                else
                  277
            else
              if i < 62 then
                if i < 61 then
                  281
                else
                  283
              else
                if i < 63 then
                  293
                else
                  307
    else
      if i < 96 then
        if i < 80 then
          if i < 72 then
            if i < 68 then
              if i < 66 then
                if i < 65 then
                  311
                else
                  313
              else
                if i < 67 then
                  317
                else
                  331
            else
              if i < 70 then
                if i < 69 then
                  337
                else
                  347
              else
                if i < 71 then
                  349
                else
                  353
          else
            if i < 76 then
              if i < 74 then
                if i < 73 then
                  359
                else
                  367
              else
                if i < 75 then
                  373
                else
                  379
            else
              if i < 78 then
                if i < 77 then
                  383
                else
                  389
              else
                if i < 79 then
                  397
                else
                  401
        else
          if i < 88 then
            if i < 84 then
              if i < 82 then
                if i < 81 then
                  409
                else
                  419
              else
                if i < 83 then
                  421
                else
                  431
            else
              if i < 86 then
                if i < 85 then
                  433
                else
                  439
              else
                if i < 87 then
                  443
                else
                  449
          else
            if i < 92 then
              if i < 90 then
                if i < 89 then
                  457
                else
                  461
              else
                if i < 91 then
                  463
                else
                  467
            else
              if i < 94 then
                if i < 93 then
                  479
                else
                  487
              else
                if i < 95 then
                  491
                else
                  499
      else
        if i < 112 then
          if i < 104 then
            if i < 100 then
              if i < 98 then
                if i < 97 then
                  503
                else
                  509
              else
                if i < 99 then
                  521
                else
                  523
            else
              if i < 102 then
                if i < 101 then
                  541
                else
                  547
              else
                if i < 103 then
                  557
                else
                  563
          else
            if i < 108 then
              if i < 106 then
                if i < 105 then
                  569
                else
                  571
              else
                if i < 107 then
                  577
                else
                  587
            else
              if i < 110 then
                if i < 109 then
                  593
                else
                  599
              else
                if i < 111 then
                  601
                else
                  607
        else
          if i < 120 then
            if i < 116 then
              if i < 114 then
                if i < 113 then
                  613
                else
                  617
              else
                if i < 115 then
                  619
                else
                  631
            else
              if i < 118 then
                if i < 117 then
                  641
                else
                  643
              else
                if i < 119 then
                  647
                else
                  653
          else
            if i < 124 then
              if i < 122 then
                if i < 121 then
                  659
                else
                  661
              else
                if i < 123 then
                  673
                else
                  677
            else
              if i < 126 then
                if i < 125 then
                  683
                else
                  691
              else
                if i < 127 then
                  701
                else
                  709
  else
    if i < 192 then
      if i < 160 then
        if i < 144 then
          if i < 136 then
            if i < 132 then
              if i < 130 then
                if i < 129 then
                  719
                else
                  727
              else
                if i < 131 then
                  733
                else
                  739
            else
              if i < 134 then
                if i < 133 then
                  743
                else
                  751
              else
                if i < 135 then
                  757
                else
                  761
          else
            if i < 140 then
              if i < 138 then
                if i < 137 then
                  769
                else
                  773
              else
                if i < 139 then
                  787
                else
                  797
            else
              if i < 142 then
                if i < 141 then
                  809
                else
                  811
              else
                if i < 143 then
                  821
                else
                  823
        else
          if i < 152 then
            if i < 148 then
              if i < 146 then
                if i < 145 then
                  827
                else
                  829
              else
                if i < 147 then
                  839
                else
                  853
            else
              if i < 150 then
                if i < 149 then
                  857
                else
                  859
              else
                if i < 151 then
                  863
                else
                  877
          else
            if i < 156 then
              if i < 154 then
                if i < 153 then
                  881
                else
                  883
              else
                if i < 155 then
                  887
                else
                  907
            else
              if i < 158 then
                if i < 157 then
                  911
                else
                  919
              else
                if i < 159 then
                  929
                else
                  937
      else
        if i < 176 then
          if i < 168 then
            if i < 164 then
              if i < 162 then
                if i < 161 then
                  941
                else
                  947
              else
                if i < 163 then
                  953
                else
                  967
            else
              if i < 166 then
                if i < 165 then
                  971
                else
                  977
              else
                if i < 167 then
                  983
                else
                  991
          else
            if i < 172 then
              if i < 170 then
                if i < 169 then
                  997
                else
                  1009
              else
                if i < 171 then
                  1013
                else
                  1019
            else
              if i < 174 then
                if i < 173 then
                  1021
                else
                  1031
              else
                if i < 175 then
                  1033
                else
                  1039
        else
          if i < 184 then
            if i < 180 then
              if i < 178 then
                if i < 177 then
                  1049
                else
                  1051
              else
                if i < 179 then
                  1061
                else
                  1063
            else
              if i < 182 then
                if i < 181 then
                  1069
                else
                  1087
              else
                if i < 183 then
                  1091
                else
                  1093
          else
            if i < 188 then
              if i < 186 then
                if i < 185 then
                  1097
                else
                  1103
              else
                if i < 187 then
                  1109
                else
                  1117
            else
              if i < 190 then
                if i < 189 then
                  1123
                else
                  1129
              else
                if i < 191 then
                  1151
                else
                  1153
    else
      if i < 224 then
        if i < 208 then
          if i < 200 then
            if i < 196 then
              if i < 194 then
                if i < 193 then
                  1163
                else
                  1171
              else
                if i < 195 then
                  1181
                else
                  1187
            else
              if i < 198 then
                if i < 197 then
                  1193
                else
                  1201
              else
                if i < 199 then
                  1213
                else
                  1217
          else
            if i < 204 then
              if i < 202 then
                if i < 201 then
                  1223
                else
                  1229
              else
                if i < 203 then
                  1231
                else
                  1237
            else
              if i < 206 then
                if i < 205 then
                  1249
                else
                  1259
              else
                if i < 207 then
                  1277
                else
                  1279
        else
          if i < 216 then
            if i < 212 then
              if i < 210 then
                if i < 209 then
                  1283
                else
                  1289
              else
                if i < 211 then
                  1291
                else
                  0
            else
              if i < 214 then
                if i < 213 then
                  0
                else
                  0
              else
                if i < 215 then
                  0
                else
                  0
          else
            if i < 220 then
              if i < 218 then
                if i < 217 then
                  0
                else
                  0
              else
                if i < 219 then
                  0
                else
                  0
            else
              if i < 222 then
                if i < 221 then
                  0
                else
                  0
              else
                if i < 223 then
                  0
                else
                  0
      else
        if i < 240 then
          if i < 232 then
            if i < 228 then
              if i < 226 then
                if i < 225 then
                  0
                else
                  0
              else
                if i < 227 then
                  0
                else
                  0
            else
              if i < 230 then
                if i < 229 then
                  0
                else
                  0
              else
                if i < 231 then
                  0
                else
                  0
          else
            if i < 236 then
              if i < 234 then
                if i < 233 then
                  0
                else
                  0
              else
                if i < 235 then
                  0
                else
                  0
            else
              if i < 238 then
                if i < 237 then
                  0
                else
                  0
              else
                if i < 239 then
                  0
                else
                  0
        else
          if i < 248 then
            if i < 244 then
              if i < 242 then
                if i < 241 then
                  0
                else
                  0
              else
                if i < 243 then
                  0
                else
                  0
            else
              if i < 246 then
                if i < 245 then
                  0
                else
                  0
              else
                if i < 247 then
                  0
                else
                  0
          else
            if i < 252 then
              if i < 250 then
                if i < 249 then
                  0
                else
                  0
              else
                if i < 251 then
                  0
                else
                  0
            else
              if i < 254 then
                if i < 253 then
                  0
                else
                  0
              else
                if i < 255 then
                  0
                else
                  0

theorem primeAt_sound {i : Nat} (hi : i < 256) (hp : primeAt i ≠ 0) : (primeAt i).Prime := by
  interval_cases i <;> norm_num [primeAt] at *
def codePack (i : Nat) : Nat := JSP233.FastFullLookup209.packNode_0 i

def code (n : Nat) : Nat := (codePack (n / 128) / denominator ((n % 128) / 2)) % 256
def tailFactor (n : Nat) : Nat :=
  match code n with
  | 0 => 0
  | i + 1 => primeAt (i + 1)
theorem tailFactor_eq (n : Nat) : tailFactor n = primeAt (code n) := by
  unfold tailFactor
  cases h : code n with
  | zero => rfl
  | succ i => rfl
def factor (n : Nat) : Nat :=
  if n % 2 = 0 then 2 else
  if n % 3 = 0 then 3 else
  if n % 5 = 0 then 5 else
  if n % 7 = 0 then 7 else
  if n % 11 = 0 then 11 else
  if n % 13 = 0 then 13 else tailFactor n
theorem factor_prime {n : Nat} (hp : factor n ≠ 0) : (factor n).Prime := by
  unfold factor at hp ⊢
  split_ifs at hp ⊢ <;> try norm_num
  rw [tailFactor_eq] at hp ⊢
  exact primeAt_sound (Nat.mod_lt _ (by decide)) hp
def marked (n : Nat) : Bool := decide (factor n ≠ 0)
end JSP233.FactorFullData209
