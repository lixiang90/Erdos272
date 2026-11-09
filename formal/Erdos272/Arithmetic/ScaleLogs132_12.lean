module

public import Erdos272.Arithmetic.PrefixTable132

@[expose] public section
namespace JSP233.ScaleLogs132
open PrefixState131 PrefixTable131 PrefixTable132 PrefixLog131
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem scale_5809 : (8667163313/500000000:ℝ)≤Real.log ((5809:ℝ)^2) ∧ Real.log ((5809:ℝ)^2)≤(86671639921/5000000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have he : Real.log ((5809:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((5809:ℝ)^2)=2*Real.log (5809:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (157:ℝ)) := by
           rw [show (5809:ℝ)=(37:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h157.1,h157.2]

theorem scale_5891 : (43405902839/2500000000:ℝ)≤Real.log ((5891:ℝ)^2) ∧ Real.log ((5891:ℝ)^2)≤(86811813613/5000000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have he : Real.log ((5891:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((5891:ℝ)^2)=2*Real.log (5891:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (137:ℝ)) := by
           rw [show (5891:ℝ)=(43:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h43.1,h43.2]

theorem scale_5893 : (86815199441/5000000000:ℝ)≤Real.log ((5893:ℝ)^2) ∧ Real.log ((5893:ℝ)^2)≤(43407604241/2500000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((5893:ℝ)^2)=2*(Real.log (71:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((5893:ℝ)^2)=2*Real.log (5893:ℝ) := Real.log_pow _ _
         _=2*(Real.log (71:ℝ)+Real.log (83:ℝ)) := by
           rw [show (5893:ℝ)=(71:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h71.1,h71.2]

theorem scale_5917 : (86855843083/5000000000:ℝ)≤Real.log ((5917:ℝ)^2) ∧ Real.log ((5917:ℝ)^2)≤(43427926009/2500000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((5917:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((5917:ℝ)^2)=2*Real.log (5917:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (97:ℝ)) := by
           rw [show (5917:ℝ)=(61:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h61.1,h61.2]

theorem scale_5921 : (43431301733/2500000000:ℝ)≤Real.log ((5921:ℝ)^2) ∧ Real.log ((5921:ℝ)^2)≤(43431304139/2500000000:ℝ) := by
  have h191 := log_bounds (by decide : 0<grid) state_191
  norm_num [grid] at h191
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((5921:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (191:ℝ)) := by
    calc Real.log ((5921:ℝ)^2)=2*Real.log (5921:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (191:ℝ)) := by
           rw [show (5921:ℝ)=(31:ℝ)*(191:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h191.1,h191.2,h31.1,h31.2]

theorem scale_5959 : (5432910893/312500000:ℝ)≤Real.log ((5959:ℝ)^2) ∧ Real.log ((5959:ℝ)^2)≤(86926583183/5000000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have he : Real.log ((5959:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((5959:ℝ)^2)=2*Real.log (5959:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (101:ℝ)) := by
           rw [show (5959:ℝ)=(59:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h101.1,h101.2]

theorem scale_5963 : (86933284497/5000000000:ℝ)≤Real.log ((5963:ℝ)^2) ∧ Real.log ((5963:ℝ)^2)≤(17386658703/1000000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have he : Real.log ((5963:ℝ)^2)=2*(Real.log (67:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((5963:ℝ)^2)=2*Real.log (5963:ℝ) := Real.log_pow _ _
         _=2*(Real.log (67:ℝ)+Real.log (89:ℝ)) := by
           rw [show (5963:ℝ)=(67:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h67.1,h67.2]

theorem scale_5969 : (17388668379/1000000000:ℝ)≤Real.log ((5969:ℝ)^2) ∧ Real.log ((5969:ℝ)^2)≤(86943350241/5000000000:ℝ) := by
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((5969:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((5969:ℝ)^2)=2*Real.log (5969:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (127:ℝ)) := by
           rw [show (5969:ℝ)=(47:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h127.1,h127.2,h47.1,h47.2]

theorem scale_5977 : (347826943/20000000:ℝ)≤Real.log ((5977:ℝ)^2) ∧ Real.log ((5977:ℝ)^2)≤(86956743687/5000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have he : Real.log ((5977:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((5977:ℝ)^2)=2*Real.log (5977:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (139:ℝ)) := by
           rw [show (5977:ℝ)=(43:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h139.1,h139.2]

theorem scale_5983 : (86966771073/5000000000:ℝ)≤Real.log ((5983:ℝ)^2) ∧ Real.log ((5983:ℝ)^2)≤(86966775887/5000000000:ℝ) := by
  have h193 := log_bounds (by decide : 0<grid) state_193
  norm_num [grid] at h193
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((5983:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (193:ℝ)) := by
    calc Real.log ((5983:ℝ)^2)=2*Real.log (5983:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (193:ℝ)) := by
           rw [show (5983:ℝ)=(31:ℝ)*(193:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h193.1,h193.2,h31.1,h31.2]

theorem scale_5989 : (2174419803/125000000:ℝ)≤Real.log ((5989:ℝ)^2) ∧ Real.log ((5989:ℝ)^2)≤(3479072033/200000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((5989:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((5989:ℝ)^2)=2*Real.log (5989:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (113:ℝ)) := by
           rw [show (5989:ℝ)=(53:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h53.1,h53.2]

theorem scale_6031 : (87046677081/5000000000:ℝ)≤Real.log ((6031:ℝ)^2) ∧ Real.log ((6031:ℝ)^2)≤(87046683879/5000000000:ℝ) := by
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((6031:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (163:ℝ)) := by
    calc Real.log ((6031:ℝ)^2)=2*Real.log (6031:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (163:ℝ)) := by
           rw [show (6031:ℝ)=(37:ℝ)*(163:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h163.1,h163.2,h37.1,h37.2]

theorem scale_6059 : (87092995069/5000000000:ℝ)≤Real.log ((6059:ℝ)^2) ∧ Real.log ((6059:ℝ)^2)≤(21773251033/1250000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have he : Real.log ((6059:ℝ)^2)=2*(Real.log (73:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((6059:ℝ)^2)=2*Real.log (6059:ℝ) := Real.log_pow _ _
         _=2*(Real.log (73:ℝ)+Real.log (83:ℝ)) := by
           rw [show (6059:ℝ)=(73:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h83.1,h83.2]

theorem scale_6077 : (87122658999/5000000000:ℝ)≤Real.log ((6077:ℝ)^2) ∧ Real.log ((6077:ℝ)^2)≤(871226679/50000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((6077:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((6077:ℝ)^2)=2*Real.log (6077:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (103:ℝ)) := by
           rw [show (6077:ℝ)=(59:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h103.1,h103.2]

theorem scale_6107 : (87171906469/5000000000:ℝ)≤Real.log ((6107:ℝ)^2) ∧ Real.log ((6107:ℝ)^2)≤(10896488911/625000000:ℝ) := by
  have h197 := log_bounds (by decide : 0<grid) state_197
  norm_num [grid] at h197
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((6107:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (197:ℝ)) := by
    calc Real.log ((6107:ℝ)^2)=2*Real.log (6107:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (197:ℝ)) := by
           rw [show (6107:ℝ)=(31:ℝ)*(197:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h197.1,h197.2,h31.1,h31.2]

theorem scale_6109 : (2179379479/125000000:ℝ)≤Real.log ((6109:ℝ)^2) ∧ Real.log ((6109:ℝ)^2)≤(8717518681/500000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have he : Real.log ((6109:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((6109:ℝ)^2)=2*Real.log (6109:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (149:ℝ)) := by
           rw [show (6109:ℝ)=(41:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h149.1,h149.2]

theorem scale_6157 : (4362672213/250000000:ℝ)≤Real.log ((6157:ℝ)^2) ∧ Real.log ((6157:ℝ)^2)≤(87253452611/5000000000:ℝ) := by
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((6157:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((6157:ℝ)^2)=2*Real.log (6157:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (131:ℝ)) := by
           rw [show (6157:ℝ)=(47:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h131.1,h131.2,h47.1,h47.2]

theorem scale_6161 : (4362996923/250000000:ℝ)≤Real.log ((6161:ℝ)^2) ∧ Real.log ((6161:ℝ)^2)≤(87259947407/5000000000:ℝ) := by
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((6161:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((6161:ℝ)^2)=2*Real.log (6161:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (101:ℝ)) := by
           rw [show (6161:ℝ)=(61:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h101.1,h101.2,h61.1,h61.2]

theorem scale_6169 : (21818229357/1250000000:ℝ)≤Real.log ((6169:ℝ)^2) ∧ Real.log ((6169:ℝ)^2)≤(87272922249/5000000000:ℝ) := by
  have h199 := log_bounds (by decide : 0<grid) state_199
  norm_num [grid] at h199
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((6169:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (199:ℝ)) := by
    calc Real.log ((6169:ℝ)^2)=2*Real.log (6169:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (199:ℝ)) := by
           rw [show (6169:ℝ)=(31:ℝ)*(199:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h199.1,h199.2,h31.1,h31.2]

theorem scale_6179 : (17457822639/1000000000:ℝ)≤Real.log ((6179:ℝ)^2) ∧ Real.log ((6179:ℝ)^2)≤(87289119997/5000000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have he : Real.log ((6179:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (167:ℝ)) := by
    calc Real.log ((6179:ℝ)^2)=2*Real.log (6179:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (167:ℝ)) := by
           rw [show (6179:ℝ)=(37:ℝ)*(167:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h167.1,h167.2]

theorem scale_6191 : (21827128617/1250000000:ℝ)≤Real.log ((6191:ℝ)^2) ∧ Real.log ((6191:ℝ)^2)≤(2182713053/125000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have he : Real.log ((6191:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((6191:ℝ)^2)=2*Real.log (6191:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (151:ℝ)) := by
           rw [show (6191:ℝ)=(41:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h151.1,h151.2]

theorem scale_6283 : (87456023171/5000000000:ℝ)≤Real.log ((6283:ℝ)^2) ∧ Real.log ((6283:ℝ)^2)≤(21864008031/1250000000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((6283:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((6283:ℝ)^2)=2*Real.log (6283:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (103:ℝ)) := by
           rw [show (6283:ℝ)=(61:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h61.1,h61.2,h103.1,h103.2]

theorem scale_6313 : (5468978591/312500000:ℝ)≤Real.log ((6313:ℝ)^2) ∧ Real.log ((6313:ℝ)^2)≤(87503666367/5000000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have he : Real.log ((6313:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((6313:ℝ)^2)=2*Real.log (6313:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (107:ℝ)) := by
           rw [show (6313:ℝ)=(59:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h59.1,h59.2]

theorem scale_6319 : (43756578521/2500000000:ℝ)≤Real.log ((6319:ℝ)^2) ∧ Real.log ((6319:ℝ)^2)≤(43756583057/2500000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((6319:ℝ)^2)=2*(Real.log (71:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((6319:ℝ)^2)=2*Real.log (6319:ℝ) := Real.log_pow _ _
         _=2*(Real.log (71:ℝ)+Real.log (89:ℝ)) := by
           rw [show (6319:ℝ)=(71:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h71.1,h71.2]

theorem scale_6401 : (87642091013/5000000000:ℝ)≤Real.log ((6401:ℝ)^2) ∧ Real.log ((6401:ℝ)^2)≤(87642097821/5000000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h173 := log_bounds (by decide : 0<grid) state_173
  norm_num [grid] at h173
  have he : Real.log ((6401:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (173:ℝ)) := by
    calc Real.log ((6401:ℝ)^2)=2*Real.log (6401:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (173:ℝ)) := by
           rw [show (6401:ℝ)=(37:ℝ)*(173:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h173.1,h173.2]

theorem scale_6407 : (87651459471/5000000000:ℝ)≤Real.log ((6407:ℝ)^2) ∧ Real.log ((6407:ℝ)^2)≤(87651467419/5000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have he : Real.log ((6407:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((6407:ℝ)^2)=2*Real.log (6407:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (149:ℝ)) := by
           rw [show (6407:ℝ)=(43:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h149.1,h149.2]

theorem scale_6431 : (87688847931/5000000000:ℝ)≤Real.log ((6431:ℝ)^2) ∧ Real.log ((6431:ℝ)^2)≤(87688856847/5000000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have he : Real.log ((6431:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((6431:ℝ)^2)=2*Real.log (6431:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (109:ℝ)) := by
           rw [show (6431:ℝ)=(59:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h109.1,h109.2]

theorem scale_6437 : (1753963483/100000000:ℝ)≤Real.log ((6437:ℝ)^2) ∧ Real.log ((6437:ℝ)^2)≤(8769818181/500000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have he : Real.log ((6437:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((6437:ℝ)^2)=2*Real.log (6437:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (157:ℝ)) := by
           rw [show (6437:ℝ)=(41:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h157.1,h157.2]

theorem scale_6439 : (43850640141/2500000000:ℝ)≤Real.log ((6439:ℝ)^2) ∧ Real.log ((6439:ℝ)^2)≤(87701288643/5000000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((6439:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((6439:ℝ)^2)=2*Real.log (6439:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (137:ℝ)) := by
           rw [show (6439:ℝ)=(47:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h47.1,h47.2]

theorem scale_6493 : (87784794779/5000000000:ℝ)≤Real.log ((6493:ℝ)^2) ∧ Real.log ((6493:ℝ)^2)≤(87784802729/5000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have he : Real.log ((6493:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((6493:ℝ)^2)=2*Real.log (6493:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (151:ℝ)) := by
           rw [show (6493:ℝ)=(43:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h151.1,h151.2]

theorem scale_6497 : (8779095267/500000000:ℝ)≤Real.log ((6497:ℝ)^2) ∧ Real.log ((6497:ℝ)^2)≤(21947740441/1250000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have he : Real.log ((6497:ℝ)^2)=2*(Real.log (73:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((6497:ℝ)^2)=2*Real.log (6497:ℝ) := Real.log_pow _ _
         _=2*(Real.log (73:ℝ)+Real.log (89:ℝ)) := by
           rw [show (6497:ℝ)=(73:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h73.1,h73.2]

theorem scale_6499 : (43897015283/2500000000:ℝ)≤Real.log ((6499:ℝ)^2) ∧ Real.log ((6499:ℝ)^2)≤(87794039617/5000000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have he : Real.log ((6499:ℝ)^2)=2*(Real.log (67:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((6499:ℝ)^2)=2*Real.log (6499:ℝ) := Real.log_pow _ _
         _=2*(Real.log (67:ℝ)+Real.log (97:ℝ)) := by
           rw [show (6499:ℝ)=(67:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h67.1,h67.2]

theorem scale_6527 : (21959255407/1250000000:ℝ)≤Real.log ((6527:ℝ)^2) ∧ Real.log ((6527:ℝ)^2)≤(87837030591/5000000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((6527:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((6527:ℝ)^2)=2*Real.log (6527:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (107:ℝ)) := by
           rw [show (6527:ℝ)=(61:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h61.1,h61.2]

theorem scale_6533 : (43923105177/2500000000:ℝ)≤Real.log ((6533:ℝ)^2) ∧ Real.log ((6533:ℝ)^2)≤(87846218717/5000000000:ℝ) := by
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((6533:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((6533:ℝ)^2)=2*Real.log (6533:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (139:ℝ)) := by
           rw [show (6533:ℝ)=(47:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h139.1,h139.2,h47.1,h47.2]

theorem scale_6557 : (5492679947/312500000:ℝ)≤Real.log ((6557:ℝ)^2) ∧ Real.log ((6557:ℝ)^2)≤(87882888267/5000000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((6557:ℝ)^2)=2*(Real.log (79:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((6557:ℝ)^2)=2*Real.log (6557:ℝ) := Real.log_pow _ _
         _=2*(Real.log (79:ℝ)+Real.log (83:ℝ)) := by
           rw [show (6557:ℝ)=(79:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h79.1,h79.2]

theorem scale_6623 : (140772853/8000000:ℝ)≤Real.log ((6623:ℝ)^2) ∧ Real.log ((6623:ℝ)^2)≤(87983039939/5000000000:ℝ) := by
  have h179 := log_bounds (by decide : 0<grid) state_179
  norm_num [grid] at h179
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((6623:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (179:ℝ)) := by
    calc Real.log ((6623:ℝ)^2)=2*Real.log (6623:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (179:ℝ)) := by
           rw [show (6623:ℝ)=(37:ℝ)*(179:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h179.1,h179.2,h37.1,h37.2]

theorem scale_6649 : (88022212103/5000000000:ℝ)≤Real.log ((6649:ℝ)^2) ∧ Real.log ((6649:ℝ)^2)≤(88022221071/5000000000:ℝ) := by
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((6649:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((6649:ℝ)^2)=2*Real.log (6649:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (109:ℝ)) := by
           rw [show (6649:ℝ)=(61:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h109.1,h109.2,h61.1,h61.2]

theorem scale_6667 : (88049247291/5000000000:ℝ)≤Real.log ((6667:ℝ)^2) ∧ Real.log ((6667:ℝ)^2)≤(11006157027/625000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have he : Real.log ((6667:ℝ)^2)=2*(Real.log (59:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((6667:ℝ)^2)=2*Real.log (6667:ℝ) := Real.log_pow _ _
         _=2*(Real.log (59:ℝ)+Real.log (113:ℝ)) := by
           rw [show (6667:ℝ)=(59:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h59.1,h59.2]

theorem scale_6683 : (88073218101/5000000000:ℝ)≤Real.log ((6683:ℝ)^2) ∧ Real.log ((6683:ℝ)^2)≤(11009153221/625000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have he : Real.log ((6683:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (163:ℝ)) := by
    calc Real.log ((6683:ℝ)^2)=2*Real.log (6683:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (163:ℝ)) := by
           rw [show (6683:ℝ)=(41:ℝ)*(163:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h163.1,h163.2]

theorem scale_6697 : (44047072689/2500000000:ℝ)≤Real.log ((6697:ℝ)^2) ∧ Real.log ((6697:ℝ)^2)≤(44047076097/2500000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h181 := log_bounds (by decide : 0<grid) state_181
  norm_num [grid] at h181
  have he : Real.log ((6697:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (181:ℝ)) := by
    calc Real.log ((6697:ℝ)^2)=2*Real.log (6697:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (181:ℝ)) := by
           rw [show (6697:ℝ)=(37:ℝ)*(181:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h181.1,h181.2]

theorem scale_6731 : (88144784783/5000000000:ℝ)≤Real.log ((6731:ℝ)^2) ∧ Real.log ((6731:ℝ)^2)≤(17628958703/1000000000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have he : Real.log ((6731:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((6731:ℝ)^2)=2*Real.log (6731:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (127:ℝ)) := by
           rw [show (6731:ℝ)=(53:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h127.1,h127.2]

theorem scale_6751 : (88174454461/5000000000:ℝ)≤Real.log ((6751:ℝ)^2) ∧ Real.log ((6751:ℝ)^2)≤(88174462419/5000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have he : Real.log ((6751:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((6751:ℝ)^2)=2*Real.log (6751:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (157:ℝ)) := by
           rw [show (6751:ℝ)=(43:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h157.1,h157.2]

theorem scale_6767 : (88198125943/5000000000:ℝ)≤Real.log ((6767:ℝ)^2) ∧ Real.log ((6767:ℝ)^2)≤(44099067503/2500000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have he : Real.log ((6767:ℝ)^2)=2*(Real.log (67:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((6767:ℝ)^2)=2*Real.log (6767:ℝ) := Real.log_pow _ _
         _=2*(Real.log (67:ℝ)+Real.log (101:ℝ)) := by
           rw [show (6767:ℝ)=(67:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h101.1,h101.2]

theorem scale_6847 : (17663130843/1000000000:ℝ)≤Real.log ((6847:ℝ)^2) ∧ Real.log ((6847:ℝ)^2)≤(44157830943/2500000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have he : Real.log ((6847:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (167:ℝ)) := by
    calc Real.log ((6847:ℝ)^2)=2*Real.log (6847:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (167:ℝ)) := by
           rw [show (6847:ℝ)=(41:ℝ)*(167:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h167.1,h167.2]

theorem scale_6887 : (88373903111/5000000000:ℝ)≤Real.log ((6887:ℝ)^2) ∧ Real.log ((6887:ℝ)^2)≤(11046739027/625000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((6887:ℝ)^2)=2*(Real.log (71:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((6887:ℝ)^2)=2*Real.log (6887:ℝ) := Real.log_pow _ _
         _=2*(Real.log (71:ℝ)+Real.log (97:ℝ)) := by
           rw [show (6887:ℝ)=(71:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h71.1,h71.2]

theorem scale_6893 : (88382611463/5000000000:ℝ)≤Real.log ((6893:ℝ)^2) ∧ Real.log ((6893:ℝ)^2)≤(2209565511/125000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((6893:ℝ)^2)=2*(Real.log (61:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((6893:ℝ)^2)=2*Real.log (6893:ℝ) := Real.log_pow _ _
         _=2*(Real.log (61:ℝ)+Real.log (113:ℝ)) := by
           rw [show (6893:ℝ)=(61:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h61.1,h61.2]

theorem scale_6901 : (44197105327/2500000000:ℝ)≤Real.log ((6901:ℝ)^2) ∧ Real.log ((6901:ℝ)^2)≤(88394219723/5000000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((6901:ℝ)^2)=2*(Real.log (67:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((6901:ℝ)^2)=2*Real.log (6901:ℝ) := Real.log_pow _ _
         _=2*(Real.log (67:ℝ)+Real.log (103:ℝ)) := by
           rw [show (6901:ℝ)=(67:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h103.1,h103.2]

theorem scale_6943 : (22113721787/1250000000:ℝ)≤Real.log ((6943:ℝ)^2) ∧ Real.log ((6943:ℝ)^2)≤(17690979177/1000000000:ℝ) := by
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((6943:ℝ)^2)=2*(Real.log (53:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((6943:ℝ)^2)=2*Real.log (6943:ℝ) := Real.log_pow _ _
         _=2*(Real.log (53:ℝ)+Real.log (131:ℝ)) := by
           rw [show (6943:ℝ)=(53:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h131.1,h131.2,h53.1,h53.2]

theorem scale_7003 : (3541637363/200000000:ℝ)≤Real.log ((7003:ℝ)^2) ∧ Real.log ((7003:ℝ)^2)≤(88540942449/5000000000:ℝ) := by
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((7003:ℝ)^2)=2*(Real.log (47:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((7003:ℝ)^2)=2*Real.log (7003:ℝ) := Real.log_pow _ _
         _=2*(Real.log (47:ℝ)+Real.log (149:ℝ)) := by
           rw [show (7003:ℝ)=(47:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h149.1,h149.2,h47.1,h47.2]

theorem scale_7009 : (22137374603/1250000000:ℝ)≤Real.log ((7009:ℝ)^2) ∧ Real.log ((7009:ℝ)^2)≤(88549506377/5000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have he : Real.log ((7009:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (163:ℝ)) := by
    calc Real.log ((7009:ℝ)^2)=2*Real.log (7009:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (163:ℝ)) := by
           rw [show (7009:ℝ)=(43:ℝ)*(163:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h163.1,h163.2]

#print axioms scale_5809
#print axioms scale_5891
#print axioms scale_5893
#print axioms scale_5917
#print axioms scale_5921
#print axioms scale_5959
#print axioms scale_5963
#print axioms scale_5969
#print axioms scale_5977
#print axioms scale_5983
#print axioms scale_5989
#print axioms scale_6031
#print axioms scale_6059
#print axioms scale_6077
#print axioms scale_6107
#print axioms scale_6109
#print axioms scale_6157
#print axioms scale_6161
#print axioms scale_6169
#print axioms scale_6179
#print axioms scale_6191
#print axioms scale_6283
#print axioms scale_6313
#print axioms scale_6319
#print axioms scale_6401
#print axioms scale_6407
#print axioms scale_6431
#print axioms scale_6437
#print axioms scale_6439
#print axioms scale_6493
#print axioms scale_6497
#print axioms scale_6499
#print axioms scale_6527
#print axioms scale_6533
#print axioms scale_6557
#print axioms scale_6623
#print axioms scale_6649
#print axioms scale_6667
#print axioms scale_6683
#print axioms scale_6697
#print axioms scale_6731
#print axioms scale_6751
#print axioms scale_6767
#print axioms scale_6847
#print axioms scale_6887
#print axioms scale_6893
#print axioms scale_6901
#print axioms scale_6943
#print axioms scale_7003
#print axioms scale_7009
end
end JSP233.ScaleLogs132
