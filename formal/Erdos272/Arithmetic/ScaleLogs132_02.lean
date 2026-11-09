module

public import Erdos272.Arithmetic.PrefixTable132

@[expose] public section
namespace JSP233.ScaleLogs132
open PrefixState131 PrefixTable131 PrefixTable132 PrefixLog131
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem scale_185 : (52203557023/5000000000:ℝ)≤Real.log ((185:ℝ)^2) ∧ Real.log ((185:ℝ)^2)≤(1305088977/125000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((185:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (37:ℝ)) := by
    calc Real.log ((185:ℝ)^2)=2*Real.log (185:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (37:ℝ)) := by
           rw [show (185:ℝ)=(5:ℝ)*(37:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h5.1,h5.2]

theorem scale_187 : (52311086153/5000000000:ℝ)≤Real.log ((187:ℝ)^2) ∧ Real.log ((187:ℝ)^2)≤(52311086187/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((187:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (17:ℝ)) := by
    calc Real.log ((187:ℝ)^2)=2*Real.log (187:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (17:ℝ)) := by
           rw [show (187:ℝ)=(11:ℝ)*(17:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h11.1,h11.2]

theorem scale_191 : (26261365719/2500000000:ℝ)≤Real.log ((191:ℝ)^2) ∧ Real.log ((191:ℝ)^2)≤(6565342027/625000000:ℝ) := by
  have h191 := log_bounds (by decide : 0<grid) state_191
  norm_num [grid] at h191
  have he : Real.log ((191:ℝ)^2)=2*(Real.log (191:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h191.1,h191.2]

theorem scale_193 : (10525379809/1000000000:ℝ)≤Real.log ((193:ℝ)^2) ∧ Real.log ((193:ℝ)^2)≤(2105076153/200000000:ℝ) := by
  have h193 := log_bounds (by decide : 0<grid) state_193
  norm_num [grid] at h193
  have he : Real.log ((193:ℝ)^2)=2*(Real.log (193:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h193.1,h193.2]

theorem scale_194 : (26339289409/2500000000:ℝ)≤Real.log ((194:ℝ)^2) ∧ Real.log ((194:ℝ)^2)≤(26339291729/2500000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have he : Real.log ((194:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((194:ℝ)^2)=2*Real.log (194:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (97:ℝ)) := by
           rw [show (194:ℝ)=(2:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h2.1,h2.2]

theorem scale_197 : (52832034441/5000000000:ℝ)≤Real.log ((197:ℝ)^2) ∧ Real.log ((197:ℝ)^2)≤(26416019613/2500000000:ℝ) := by
  have h197 := log_bounds (by decide : 0<grid) state_197
  norm_num [grid] at h197
  have he : Real.log ((197:ℝ)^2)=2*(Real.log (197:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h197.1,h197.2]

theorem scale_199 : (264665227/25000000:ℝ)≤Real.log ((199:ℝ)^2) ∧ Real.log ((199:ℝ)^2)≤(52933050187/5000000000:ℝ) := by
  have h199 := log_bounds (by decide : 0<grid) state_199
  norm_num [grid] at h199
  have he : Real.log ((199:ℝ)^2)=2*(Real.log (199:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h199.1,h199.2]

theorem scale_201 : (10606609287/1000000000:ℝ)≤Real.log ((201:ℝ)^2) ∧ Real.log ((201:ℝ)^2)≤(53033050857/5000000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((201:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((201:ℝ)^2)=2*Real.log (201:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (67:ℝ)) := by
           rw [show (201:ℝ)=(3:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h3.1,h3.2]

theorem scale_202 : (10616534839/1000000000:ℝ)≤Real.log ((202:ℝ)^2) ∧ Real.log ((202:ℝ)^2)≤(53082678847/5000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have he : Real.log ((202:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((202:ℝ)^2)=2*Real.log (202:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (101:ℝ)) := by
           rw [show (202:ℝ)=(2:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h101.1,h101.2]

theorem scale_203 : (5313205977/500000000:ℝ)≤Real.log ((203:ℝ)^2) ∧ Real.log ((203:ℝ)^2)≤(13283014953/1250000000:ℝ) := by
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((203:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (29:ℝ)) := by
    calc Real.log ((203:ℝ)^2)=2*Real.log (203:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (29:ℝ)) := by
           rw [show (203:ℝ)=(7:ℝ)*(29:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h29.1,h29.2,h7.1,h7.2]

theorem scale_205 : (53230098043/5000000000:ℝ)≤Real.log ((205:ℝ)^2) ∧ Real.log ((205:ℝ)^2)≤(53230100969/5000000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((205:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (41:ℝ)) := by
    calc Real.log ((205:ℝ)^2)=2*Real.log (205:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (41:ℝ)) := by
           rw [show (205:ℝ)=(5:ℝ)*(41:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h5.1,h5.2]

theorem scale_206 : (26639379453/2500000000:ℝ)≤Real.log ((206:ℝ)^2) ∧ Real.log ((206:ℝ)^2)≤(13319690891/1250000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((206:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((206:ℝ)^2)=2*Real.log (206:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (103:ℝ)) := by
           rw [show (206:ℝ)=(2:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h103.1,h103.2]

theorem scale_209 : (53423342503/5000000000:ℝ)≤Real.log ((209:ℝ)^2) ∧ Real.log ((209:ℝ)^2)≤(53423342539/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((209:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (19:ℝ)) := by
    calc Real.log ((209:ℝ)^2)=2*Real.log (209:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (19:ℝ)) := by
           rw [show (209:ℝ)=(11:ℝ)*(19:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h11.1,h11.2]

theorem scale_210 : (26735537647/2500000000:ℝ)≤Real.log ((210:ℝ)^2) ∧ Real.log ((210:ℝ)^2)≤(53471075323/5000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((210:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (3:ℝ)+Real.log (5:ℝ)+Real.log (7:ℝ)) := by
    calc Real.log ((210:ℝ)^2)=2*Real.log (210:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (3:ℝ)+Real.log (5:ℝ)+Real.log (7:ℝ)) := by
           rw [show (210:ℝ)=(2:ℝ)*(3:ℝ)*(5:ℝ)*(7:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num),Real.log_mul (by norm_num) (by norm_num),Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h3.1,h3.2,h5.1,h5.2,h7.1,h7.2]

theorem scale_213 : (2680645949/250000000:ℝ)≤Real.log ((213:ℝ)^2) ∧ Real.log ((213:ℝ)^2)≤(837701929/78125000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((213:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((213:ℝ)^2)=2*Real.log (213:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (71:ℝ)) := by
           rw [show (213:ℝ)=(3:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h71.1,h71.2]

theorem scale_214 : (53659757363/5000000000:ℝ)≤Real.log ((214:ℝ)^2) ∧ Real.log ((214:ℝ)^2)≤(53659762031/5000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have he : Real.log ((214:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((214:ℝ)^2)=2*Real.log (214:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (107:ℝ)) := by
           rw [show (214:ℝ)=(2:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h107.1,h107.2]

theorem scale_215 : (26853189177/2500000000:ℝ)≤Real.log ((215:ℝ)^2) ∧ Real.log ((215:ℝ)^2)≤(26853190789/2500000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((215:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (43:ℝ)) := by
    calc Real.log ((215:ℝ)^2)=2*Real.log (215:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (43:ℝ)) := by
           rw [show (215:ℝ)=(5:ℝ)*(43:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h5.1,h5.2]

theorem scale_217 : (26899486757/2500000000:ℝ)≤Real.log ((217:ℝ)^2) ∧ Real.log ((217:ℝ)^2)≤(26899486779/2500000000:ℝ) := by
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((217:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (31:ℝ)) := by
    calc Real.log ((217:ℝ)^2)=2*Real.log (217:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (31:ℝ)) := by
           rw [show (217:ℝ)=(7:ℝ)*(31:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h31.1,h31.2,h7.1,h7.2]

theorem scale_218 : (26922473919/2500000000:ℝ)≤Real.log ((218:ℝ)^2) ∧ Real.log ((218:ℝ)^2)≤(53844952511/5000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have he : Real.log ((218:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((218:ℝ)^2)=2*Real.log (218:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (109:ℝ)) := by
           rw [show (218:ℝ)=(2:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h109.1,h109.2]

theorem scale_219 : (3368169663/312500000:ℝ)≤Real.log ((219:ℝ)^2) ∧ Real.log ((219:ℝ)^2)≤(26945359553/2500000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((219:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((219:ℝ)^2)=2*Real.log (219:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (73:ℝ)) := by
           rw [show (219:ℝ)=(3:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h3.1,h3.2]

theorem scale_221 : (26990813499/2500000000:ℝ)≤Real.log ((221:ℝ)^2) ∧ Real.log ((221:ℝ)^2)≤(26990813517/2500000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((221:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (17:ℝ)) := by
    calc Real.log ((221:ℝ)^2)=2*Real.log (221:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (17:ℝ)) := by
           rw [show (221:ℝ)=(13:ℝ)*(17:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h13.1,h13.2]

theorem scale_226 : (27102673599/2500000000:ℝ)≤Real.log ((226:ℝ)^2) ∧ Real.log ((226:ℝ)^2)≤(1355133797/125000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have he : Real.log ((226:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((226:ℝ)^2)=2*Real.log (226:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (113:ℝ)) := by
           rw [show (226:ℝ)=(2:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h2.1,h2.2]

theorem scale_235 : (27297926479/2500000000:ℝ)≤Real.log ((235:ℝ)^2) ∧ Real.log ((235:ℝ)^2)≤(1706120519/156250000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((235:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (47:ℝ)) := by
    calc Real.log ((235:ℝ)^2)=2*Real.log (235:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (47:ℝ)) := by
           rw [show (235:ℝ)=(5:ℝ)*(47:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h47.1,h47.2]

theorem scale_237 : (54680598691/5000000000:ℝ)≤Real.log ((237:ℝ)^2) ∧ Real.log ((237:ℝ)^2)≤(54680603241/5000000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((237:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((237:ℝ)^2)=2*Real.log (237:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (79:ℝ)) := by
           rw [show (237:ℝ)=(3:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h79.1,h79.2]

theorem scale_247 : (13773470837/1250000000:ℝ)≤Real.log ((247:ℝ)^2) ∧ Real.log ((247:ℝ)^2)≤(27546941693/2500000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((247:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (19:ℝ)) := by
    calc Real.log ((247:ℝ)^2)=2*Real.log (247:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (19:ℝ)) := by
           rw [show (247:ℝ)=(13:ℝ)*(19:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h13.1,h13.2]

theorem scale_249 : (55174526229/5000000000:ℝ)≤Real.log ((249:ℝ)^2) ∧ Real.log ((249:ℝ)^2)≤(27587265403/2500000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((249:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((249:ℝ)^2)=2*Real.log (249:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (83:ℝ)) := by
           rw [show (249:ℝ)=(3:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h3.1,h3.2]

theorem scale_253 : (13833473717/1250000000:ℝ)≤Real.log ((253:ℝ)^2) ∧ Real.log ((253:ℝ)^2)≤(13833473727/1250000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((253:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (23:ℝ)) := by
    calc Real.log ((253:ℝ)^2)=2*Real.log (253:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (23:ℝ)) := by
           rw [show (253:ℝ)=(11:ℝ)*(23:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h23.1,h23.2]

theorem scale_254 : (55373339861/5000000000:ℝ)≤Real.log ((254:ℝ)^2) ∧ Real.log ((254:ℝ)^2)≤(5537334457/500000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have he : Real.log ((254:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((254:ℝ)^2)=2*Real.log (254:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (127:ℝ)) := by
           rw [show (254:ℝ)=(2:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h127.1,h127.2]

theorem scale_259 : (13892069847/1250000000:ℝ)≤Real.log ((259:ℝ)^2) ∧ Real.log ((259:ℝ)^2)≤(55568281447/5000000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((259:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (37:ℝ)) := by
    calc Real.log ((259:ℝ)^2)=2*Real.log (259:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (37:ℝ)) := by
           rw [show (259:ℝ)=(7:ℝ)*(37:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h7.1,h7.2]

theorem scale_262 : (27841721113/2500000000:ℝ)≤Real.log ((262:ℝ)^2) ∧ Real.log ((262:ℝ)^2)≤(2784172347/250000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have he : Real.log ((262:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((262:ℝ)^2)=2*Real.log (262:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (131:ℝ)) := by
           rw [show (262:ℝ)=(2:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h131.1,h131.2]

theorem scale_265 : (27898647923/2500000000:ℝ)≤Real.log ((265:ℝ)^2) ∧ Real.log ((265:ℝ)^2)≤(27898649941/2500000000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((265:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (53:ℝ)) := by
    calc Real.log ((265:ℝ)^2)=2*Real.log (265:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (53:ℝ)) := by
           rw [show (265:ℝ)=(5:ℝ)*(53:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h5.1,h5.2]

theorem scale_267 : (5587248383/500000000:ℝ)≤Real.log ((267:ℝ)^2) ∧ Real.log ((267:ℝ)^2)≤(27936244219/2500000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((267:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((267:ℝ)^2)=2*Real.log (267:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (89:ℝ)) := by
           rw [show (267:ℝ)=(3:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h3.1,h3.2]

theorem scale_274 : (7016409781/625000000:ℝ)≤Real.log ((274:ℝ)^2) ∧ Real.log ((274:ℝ)^2)≤(14032820743/1250000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have he : Real.log ((274:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((274:ℝ)^2)=2*Real.log (274:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (137:ℝ)) := by
           rw [show (274:ℝ)=(2:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h2.1,h2.2]

theorem scale_278 : (175863151/15625000:ℝ)≤Real.log ((278:ℝ)^2) ∧ Real.log ((278:ℝ)^2)≤(28138106523/2500000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have he : Real.log ((278:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((278:ℝ)^2)=2*Real.log (278:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (139:ℝ)) := by
           rw [show (278:ℝ)=(2:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h139.1,h139.2]

theorem scale_287 : (7074352551/625000000:ℝ)≤Real.log ((287:ℝ)^2) ∧ Real.log ((287:ℝ)^2)≤(7074352917/625000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((287:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (41:ℝ)) := by
    calc Real.log ((287:ℝ)^2)=2*Real.log (287:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (41:ℝ)) := by
           rw [show (287:ℝ)=(7:ℝ)*(41:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h7.1,h7.2]

theorem scale_291 : (56733229899/5000000000:ℝ)≤Real.log ((291:ℝ)^2) ∧ Real.log ((291:ℝ)^2)≤(2836661727/250000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((291:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((291:ℝ)^2)=2*Real.log (291:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (97:ℝ)) := by
           rw [show (291:ℝ)=(3:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h3.1,h3.2]

theorem scale_295 : (56869751017/5000000000:ℝ)≤Real.log ((295:ℝ)^2) ∧ Real.log ((295:ℝ)^2)≤(56869755273/5000000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((295:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((295:ℝ)^2)=2*Real.log (295:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (59:ℝ)) := by
           rw [show (295:ℝ)=(5:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h5.1,h5.2]

theorem scale_298 : (56970932041/5000000000:ℝ)≤Real.log ((298:ℝ)^2) ∧ Real.log ((298:ℝ)^2)≤(28485468389/2500000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have he : Real.log ((298:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((298:ℝ)^2)=2*Real.log (298:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (149:ℝ)) := by
           rw [show (298:ℝ)=(2:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h149.1,h149.2]

theorem scale_299 : (57004435713/5000000000:ℝ)≤Real.log ((299:ℝ)^2) ∧ Real.log ((299:ℝ)^2)≤(11400887151/1000000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((299:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (23:ℝ)) := by
    calc Real.log ((299:ℝ)^2)=2*Real.log (299:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (23:ℝ)) := by
           rw [show (299:ℝ)=(13:ℝ)*(23:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h23.1,h23.2]

theorem scale_301 : (57071100719/5000000000:ℝ)≤Real.log ((301:ℝ)^2) ∧ Real.log ((301:ℝ)^2)≤(11414220789/1000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((301:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (43:ℝ)) := by
    calc Real.log ((301:ℝ)^2)=2*Real.log (301:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (43:ℝ)) := by
           rw [show (301:ℝ)=(7:ℝ)*(43:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h7.1,h7.2]

theorem scale_302 : (57104267349/5000000000:ℝ)≤Real.log ((302:ℝ)^2) ∧ Real.log ((302:ℝ)^2)≤(7138034011/625000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have he : Real.log ((302:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((302:ℝ)^2)=2*Real.log (302:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (151:ℝ)) := by
           rw [show (302:ℝ)=(2:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h151.1,h151.2]

theorem scale_303 : (14284331319/1250000000:ℝ)≤Real.log ((303:ℝ)^2) ∧ Real.log ((303:ℝ)^2)≤(57137329929/5000000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have he : Real.log ((303:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((303:ℝ)^2)=2*Real.log (303:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (101:ℝ)) := by
           rw [show (303:ℝ)=(3:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h101.1,h101.2]

theorem scale_305 : (57203115189/5000000000:ℝ)≤Real.log ((305:ℝ)^2) ∧ Real.log ((305:ℝ)^2)≤(57203119497/5000000000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((305:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((305:ℝ)^2)=2*Real.log (305:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (61:ℝ)) := by
           rw [show (305:ℝ)=(5:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h61.1,h61.2,h5.1,h5.2]

theorem scale_309 : (57333409987/5000000000:ℝ)≤Real.log ((309:ℝ)^2) ∧ Real.log ((309:ℝ)^2)≤(28666707323/2500000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((309:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((309:ℝ)^2)=2*Real.log (309:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (103:ℝ)) := by
           rw [show (309:ℝ)=(3:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h103.1,h103.2]

theorem scale_314 : (57493927031/5000000000:ℝ)≤Real.log ((314:ℝ)^2) ∧ Real.log ((314:ℝ)^2)≤(28746965889/2500000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have he : Real.log ((314:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((314:ℝ)^2)=2*Real.log (314:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (157:ℝ)) := by
           rw [show (314:ℝ)=(2:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h157.1,h157.2]

theorem scale_319 : (28825955503/2500000000:ℝ)≤Real.log ((319:ℝ)^2) ∧ Real.log ((319:ℝ)^2)≤(14412977763/1250000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((319:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (29:ℝ)) := by
    calc Real.log ((319:ℝ)^2)=2*Real.log (319:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (29:ℝ)) := by
           rw [show (319:ℝ)=(11:ℝ)*(29:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h29.1,h29.2]

theorem scale_321 : (14428602111/1250000000:ℝ)≤Real.log ((321:ℝ)^2) ∧ Real.log ((321:ℝ)^2)≤(57714413113/5000000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((321:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((321:ℝ)^2)=2*Real.log (321:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (107:ℝ)) := by
           rw [show (321:ℝ)=(3:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h3.1,h3.2]

theorem scale_323 : (14444130803/1250000000:ℝ)≤Real.log ((323:ℝ)^2) ∧ Real.log ((323:ℝ)^2)≤(28888261627/2500000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have he : Real.log ((323:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (19:ℝ)) := by
    calc Real.log ((323:ℝ)^2)=2*Real.log (323:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (19:ℝ)) := by
           rw [show (323:ℝ)=(17:ℝ)*(19:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h19.1,h19.2]

theorem scale_326 : (28934485491/2500000000:ℝ)≤Real.log ((326:ℝ)^2) ∧ Real.log ((326:ℝ)^2)≤(7233621967/625000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have he : Real.log ((326:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (163:ℝ)) := by
    calc Real.log ((326:ℝ)^2)=2*Real.log (326:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (163:ℝ)) := by
           rw [show (326:ℝ)=(2:ℝ)*(163:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h163.1,h163.2]

theorem scale_327 : (57899598919/5000000000:ℝ)≤Real.log ((327:ℝ)^2) ∧ Real.log ((327:ℝ)^2)≤(57899603593/5000000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have he : Real.log ((327:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((327:ℝ)^2)=2*Real.log (327:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (109:ℝ)) := by
           rw [show (327:ℝ)=(3:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h109.1,h109.2]

#print axioms scale_185
#print axioms scale_187
#print axioms scale_191
#print axioms scale_193
#print axioms scale_194
#print axioms scale_197
#print axioms scale_199
#print axioms scale_201
#print axioms scale_202
#print axioms scale_203
#print axioms scale_205
#print axioms scale_206
#print axioms scale_209
#print axioms scale_210
#print axioms scale_213
#print axioms scale_214
#print axioms scale_215
#print axioms scale_217
#print axioms scale_218
#print axioms scale_219
#print axioms scale_221
#print axioms scale_226
#print axioms scale_235
#print axioms scale_237
#print axioms scale_247
#print axioms scale_249
#print axioms scale_253
#print axioms scale_254
#print axioms scale_259
#print axioms scale_262
#print axioms scale_265
#print axioms scale_267
#print axioms scale_274
#print axioms scale_278
#print axioms scale_287
#print axioms scale_291
#print axioms scale_295
#print axioms scale_298
#print axioms scale_299
#print axioms scale_301
#print axioms scale_302
#print axioms scale_303
#print axioms scale_305
#print axioms scale_309
#print axioms scale_314
#print axioms scale_319
#print axioms scale_321
#print axioms scale_323
#print axioms scale_326
#print axioms scale_327
end
end JSP233.ScaleLogs132
