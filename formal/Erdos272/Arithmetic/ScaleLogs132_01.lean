module

public import Erdos272.Arithmetic.PrefixTable132

@[expose] public section
namespace JSP233.ScaleLogs132
open PrefixState131 PrefixTable131 PrefixTable132 PrefixLog131
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem scale_85 : (5553314069/625000000:ℝ)≤Real.log ((85:ℝ)^2) ∧ Real.log ((85:ℝ)^2)≤(2221325629/250000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((85:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (17:ℝ)) := by
    calc Real.log ((85:ℝ)^2)=2*Real.log (85:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (17:ℝ)) := by
           rw [show (85:ℝ)=(5:ℝ)*(17:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h5.1,h5.2]

theorem scale_86 : (11135867759/1250000000:ℝ)≤Real.log ((86:ℝ)^2) ∧ Real.log ((86:ℝ)^2)≤(44543474257/5000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have he : Real.log ((86:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (43:ℝ)) := by
    calc Real.log ((86:ℝ)^2)=2*Real.log (86:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (43:ℝ)) := by
           rw [show (86:ℝ)=(2:ℝ)*(43:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h43.1,h43.2]

theorem scale_87 : (2791192573/312500000:ℝ)≤Real.log ((87:ℝ)^2) ∧ Real.log ((87:ℝ)^2)≤(22329540603/2500000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((87:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (29:ℝ)) := by
    calc Real.log ((87:ℝ)^2)=2*Real.log (87:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (29:ℝ)) := by
           rw [show (87:ℝ)=(3:ℝ)*(29:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h29.1,h29.2]

theorem scale_89 : (22443180473/2500000000:ℝ)≤Real.log ((89:ℝ)^2) ∧ Real.log ((89:ℝ)^2)≤(11221591387/1250000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have he : Real.log ((89:ℝ)^2)=2*(Real.log (89:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h89.1,h89.2]

theorem scale_91 : (45108595053/5000000000:ℝ)≤Real.log ((91:ℝ)^2) ∧ Real.log ((91:ℝ)^2)≤(45108595079/5000000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((91:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (13:ℝ)) := by
    calc Real.log ((91:ℝ)^2)=2*Real.log (91:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (13:ℝ)) := by
           rw [show (91:ℝ)=(7:ℝ)*(13:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h7.1,h7.2]

theorem scale_93 : (1416437341/156250000:ℝ)≤Real.log ((93:ℝ)^2) ∧ Real.log ((93:ℝ)^2)≤(5665749369/625000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((93:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (31:ℝ)) := by
    calc Real.log ((93:ℝ)^2)=2*Real.log (93:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (31:ℝ)) := by
           rw [show (93:ℝ)=(3:ℝ)*(31:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h31.1,h31.2]

theorem scale_94 : (1135823641/125000000:ℝ)≤Real.log ((94:ℝ)^2) ∧ Real.log ((94:ℝ)^2)≤(45432949287/5000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((94:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (47:ℝ)) := by
    calc Real.log ((94:ℝ)^2)=2*Real.log (94:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (47:ℝ)) := by
           rw [show (94:ℝ)=(2:ℝ)*(47:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h47.1,h47.2]

theorem scale_95 : (22769384451/2500000000:ℝ)≤Real.log ((95:ℝ)^2) ∧ Real.log ((95:ℝ)^2)≤(11384692233/1250000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((95:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (19:ℝ)) := by
    calc Real.log ((95:ℝ)^2)=2*Real.log (95:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (19:ℝ)) := by
           rw [show (95:ℝ)=(5:ℝ)*(19:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h5.1,h5.2]

theorem scale_97 : (9149421403/1000000000:ℝ)≤Real.log ((97:ℝ)^2) ∧ Real.log ((97:ℝ)^2)≤(914942233/100000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have he : Real.log ((97:ℝ)^2)=2*(Real.log (97:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h97.1,h97.2]

theorem scale_101 : (5768900299/625000000:ℝ)≤Real.log ((101:ℝ)^2) ∧ Real.log ((101:ℝ)^2)≤(46151207039/5000000000:ℝ) := by
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have he : Real.log ((101:ℝ)^2)=2*(Real.log (101:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h101.1,h101.2]

theorem scale_103 : (46347287103/5000000000:ℝ)≤Real.log ((103:ℝ)^2) ∧ Real.log ((103:ℝ)^2)≤(11586822939/1250000000:ℝ) := by
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((103:ℝ)^2)=2*(Real.log (103:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h103.1,h103.2]

theorem scale_105 : (46539603491/5000000000:ℝ)≤Real.log ((105:ℝ)^2) ∧ Real.log ((105:ℝ)^2)≤(9307920703/1000000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((105:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (5:ℝ)+Real.log (7:ℝ)) := by
    calc Real.log ((105:ℝ)^2)=2*Real.log (105:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (5:ℝ)+Real.log (7:ℝ)) := by
           rw [show (105:ℝ)=(3:ℝ)*(5:ℝ)*(7:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num),Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h5.1,h5.2,h7.1,h7.2]

theorem scale_106 : (2914649283/312500000:ℝ)≤Real.log ((106:ℝ)^2) ∧ Real.log ((106:ℝ)^2)≤(46634392561/5000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((106:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (53:ℝ)) := by
    calc Real.log ((106:ℝ)^2)=2*Real.log (106:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (53:ℝ)) := by
           rw [show (106:ℝ)=(2:ℝ)*(53:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h53.1,h53.2]

theorem scale_107 : (1168207139/125000000:ℝ)≤Real.log ((107:ℝ)^2) ∧ Real.log ((107:ℝ)^2)≤(46728290223/5000000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have he : Real.log ((107:ℝ)^2)=2*(Real.log (107:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h107.1,h107.2]

theorem scale_109 : (9382695207/1000000000:ℝ)≤Real.log ((109:ℝ)^2) ∧ Real.log ((109:ℝ)^2)≤(46913480703/5000000000:ℝ) := by
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have he : Real.log ((109:ℝ)^2)=2*(Real.log (109:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h109.1,h109.2]

theorem scale_111 : (23547650393/2500000000:ℝ)≤Real.log ((111:ℝ)^2) ∧ Real.log ((111:ℝ)^2)≤(47095302841/5000000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((111:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (37:ℝ)) := by
    calc Real.log ((111:ℝ)^2)=2*Real.log (111:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (37:ℝ)) := by
           rw [show (111:ℝ)=(3:ℝ)*(37:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h37.1,h37.2]

theorem scale_113 : (9454775079/1000000000:ℝ)≤Real.log ((113:ℝ)^2) ∧ Real.log ((113:ℝ)^2)≤(5909235009/625000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have he : Real.log ((113:ℝ)^2)=2*(Real.log (113:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h113.1,h113.2]

theorem scale_115 : (47449321267/5000000000:ℝ)≤Real.log ((115:ℝ)^2) ∧ Real.log ((115:ℝ)^2)≤(47449321301/5000000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((115:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (23:ℝ)) := by
    calc Real.log ((115:ℝ)^2)=2*Real.log (115:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (23:ℝ)) := by
           rw [show (115:ℝ)=(5:ℝ)*(23:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h23.1,h23.2]

theorem scale_118 : (47706843699/5000000000:ℝ)≤Real.log ((118:ℝ)^2) ∧ Real.log ((118:ℝ)^2)≤(2981677997/312500000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have he : Real.log ((118:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((118:ℝ)^2)=2*Real.log (118:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (59:ℝ)) := by
           rw [show (118:ℝ)=(2:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h59.1,h59.2]

theorem scale_119 : (47791234917/5000000000:ℝ)≤Real.log ((119:ℝ)^2) ∧ Real.log ((119:ℝ)^2)≤(47791234947/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((119:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (17:ℝ)) := by
    calc Real.log ((119:ℝ)^2)=2*Real.log (119:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (17:ℝ)) := by
           rw [show (119:ℝ)=(7:ℝ)*(17:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h7.1,h7.2]

theorem scale_122 : (48040207871/5000000000:ℝ)≤Real.log ((122:ℝ)^2) ∧ Real.log ((122:ℝ)^2)≤(3002513261/312500000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((122:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((122:ℝ)^2)=2*Real.log (122:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (61:ℝ)) := by
           rw [show (122:ℝ)=(2:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h61.1,h61.2]

theorem scale_123 : (24060920903/2500000000:ℝ)≤Real.log ((123:ℝ)^2) ∧ Real.log ((123:ℝ)^2)≤(4812184473/500000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((123:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (41:ℝ)) := by
    calc Real.log ((123:ℝ)^2)=2*Real.log (123:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (41:ℝ)) := by
           rw [show (123:ℝ)=(3:ℝ)*(41:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h3.1,h3.2]

theorem scale_127 : (24220934029/2500000000:ℝ)≤Real.log ((127:ℝ)^2) ∧ Real.log ((127:ℝ)^2)≤(24220936381/2500000000:ℝ) := by
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have he : Real.log ((127:ℝ)^2)=2*(Real.log (127:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h127.1,h127.2]

theorem scale_129 : (48598122117/5000000000:ℝ)≤Real.log ((129:ℝ)^2) ∧ Real.log ((129:ℝ)^2)≤(48598125339/5000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((129:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (43:ℝ)) := by
    calc Real.log ((129:ℝ)^2)=2*Real.log (129:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (43:ℝ)) := by
           rw [show (129:ℝ)=(3:ℝ)*(43:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h3.1,h3.2]

theorem scale_131 : (48751970423/5000000000:ℝ)≤Real.log ((131:ℝ)^2) ∧ Real.log ((131:ℝ)^2)≤(12187993783/1250000000:ℝ) := by
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have he : Real.log ((131:ℝ)^2)=2*(Real.log (131:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h131.1,h131.2]

theorem scale_133 : (48903491267/5000000000:ℝ)≤Real.log ((133:ℝ)^2) ∧ Real.log ((133:ℝ)^2)≤(48903491299/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((133:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (19:ℝ)) := by
    calc Real.log ((133:ℝ)^2)=2*Real.log (133:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (19:ℝ)) := by
           rw [show (133:ℝ)=(7:ℝ)*(19:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h7.1,h7.2]

theorem scale_134 : (24489197677/2500000000:ℝ)≤Real.log ((134:ℝ)^2) ∧ Real.log ((134:ℝ)^2)≤(1959135991/200000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have he : Real.log ((134:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((134:ℝ)^2)=2*Real.log (134:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (67:ℝ)) := by
           rw [show (134:ℝ)=(2:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h67.1,h67.2]

theorem scale_137 : (9839961289/1000000000:ℝ)≤Real.log ((137:ℝ)^2) ∧ Real.log ((137:ℝ)^2)≤(12299952791/1250000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have he : Real.log ((137:ℝ)^2)=2*(Real.log (137:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h137.1,h137.2]

theorem scale_139 : (49344736517/5000000000:ℝ)≤Real.log ((139:ℝ)^2) ∧ Real.log ((139:ℝ)^2)≤(24672370619/2500000000:ℝ) := by
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have he : Real.log ((139:ℝ)^2)=2*(Real.log (139:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h139.1,h139.2]

theorem scale_141 : (49487596721/5000000000:ℝ)≤Real.log ((141:ℝ)^2) ∧ Real.log ((141:ℝ)^2)≤(49487600369/5000000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((141:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (47:ℝ)) := by
    calc Real.log ((141:ℝ)^2)=2*Real.log (141:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (47:ℝ)) := by
           rw [show (141:ℝ)=(3:ℝ)*(47:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h47.1,h47.2]

theorem scale_142 : (49558267899/5000000000:ℝ)≤Real.log ((142:ℝ)^2) ∧ Real.log ((142:ℝ)^2)≤(24779136187/2500000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((142:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((142:ℝ)^2)=2*Real.log (142:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (71:ℝ)) := by
           rw [show (142:ℝ)=(2:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h71.1,h71.2]

theorem scale_143 : (49628446289/5000000000:ℝ)≤Real.log ((143:ℝ)^2) ∧ Real.log ((143:ℝ)^2)≤(49628446319/5000000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((143:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (13:ℝ)) := by
    calc Real.log ((143:ℝ)^2)=2*Real.log (143:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (13:ℝ)) := by
           rw [show (143:ℝ)=(11:ℝ)*(13:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h13.1,h13.2]

theorem scale_145 : (9953467481/1000000000:ℝ)≤Real.log ((145:ℝ)^2) ∧ Real.log ((145:ℝ)^2)≤(9953467489/1000000000:ℝ) := by
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((145:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (29:ℝ)) := by
    calc Real.log ((145:ℝ)^2)=2*Real.log (145:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (29:ℝ)) := by
           rw [show (145:ℝ)=(5:ℝ)*(29:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h29.1,h29.2,h5.1,h5.2]

theorem scale_146 : (49836063527/5000000000:ℝ)≤Real.log ((146:ℝ)^2) ∧ Real.log ((146:ℝ)^2)≤(6229508503/625000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have he : Real.log ((146:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((146:ℝ)^2)=2*Real.log (146:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (73:ℝ)) := by
           rw [show (146:ℝ)=(2:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h2.1,h2.2]

theorem scale_149 : (25019730119/2500000000:ℝ)≤Real.log ((149:ℝ)^2) ∧ Real.log ((149:ℝ)^2)≤(5003946497/500000000:ℝ) := by
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have he : Real.log ((149:ℝ)^2)=2*(Real.log (149:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h149.1,h149.2]

theorem scale_151 : (25086397773/2500000000:ℝ)≤Real.log ((151:ℝ)^2) ∧ Real.log ((151:ℝ)^2)≤(1254320007/125000000:ℝ) := by
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have he : Real.log ((151:ℝ)^2)=2*(Real.log (151:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h151.1,h151.2]

theorem scale_155 : (50434251149/5000000000:ℝ)≤Real.log ((155:ℝ)^2) ∧ Real.log ((155:ℝ)^2)≤(50434251191/5000000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((155:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (31:ℝ)) := by
    calc Real.log ((155:ℝ)^2)=2*Real.log (155:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (31:ℝ)) := by
           rw [show (155:ℝ)=(5:ℝ)*(31:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h31.1,h31.2]

theorem scale_157 : (12640613807/1250000000:ℝ)≤Real.log ((157:ℝ)^2) ∧ Real.log ((157:ℝ)^2)≤(5056245997/500000000:ℝ) := by
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have he : Real.log ((157:ℝ)^2)=2*(Real.log (157:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h157.1,h157.2]

theorem scale_158 : (5062594761/500000000:ℝ)≤Real.log ((158:ℝ)^2) ∧ Real.log ((158:ℝ)^2)≤(50625952159/5000000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((158:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((158:ℝ)^2)=2*Real.log (158:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (79:ℝ)) := by
           rw [show (158:ℝ)=(2:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h79.1,h79.2]

theorem scale_159 : (50689039609/5000000000:ℝ)≤Real.log ((159:ℝ)^2) ∧ Real.log ((159:ℝ)^2)≤(50689043643/5000000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((159:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (53:ℝ)) := by
    calc Real.log ((159:ℝ)^2)=2*Real.log (159:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (53:ℝ)) := by
           rw [show (159:ℝ)=(3:ℝ)*(53:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h53.1,h53.2]

theorem scale_161 : (3175877727/312500000:ℝ)≤Real.log ((161:ℝ)^2) ∧ Real.log ((161:ℝ)^2)≤(12703510917/1250000000:ℝ) := by
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((161:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (23:ℝ)) := by
    calc Real.log ((161:ℝ)^2)=2*Real.log (161:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (23:ℝ)) := by
           rw [show (161:ℝ)=(7:ℝ)*(23:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h23.1,h23.2,h7.1,h7.2]

theorem scale_163 : (50937499179/5000000000:ℝ)≤Real.log ((163:ℝ)^2) ∧ Real.log ((163:ℝ)^2)≤(6367187991/625000000:ℝ) := by
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have he : Real.log ((163:ℝ)^2)=2*(Real.log (163:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h163.1,h163.2]

theorem scale_166 : (12779968787/1250000000:ℝ)≤Real.log ((166:ℝ)^2) ∧ Real.log ((166:ℝ)^2)≤(12779969931/1250000000:ℝ) := by
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have he : Real.log ((166:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((166:ℝ)^2)=2*Real.log (166:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (83:ℝ)) := by
           rw [show (166:ℝ)=(2:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h2.1,h2.2,h83.1,h83.2]

theorem scale_167 : (51179935293/5000000000:ℝ)≤Real.log ((167:ℝ)^2) ∧ Real.log ((167:ℝ)^2)≤(25589970023/2500000000:ℝ) := by
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have he : Real.log ((167:ℝ)^2)=2*(Real.log (167:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h167.1,h167.2]

theorem scale_173 : (51532913111/5000000000:ℝ)≤Real.log ((173:ℝ)^2) ∧ Real.log ((173:ℝ)^2)≤(5153291787/500000000:ℝ) := by
  have h173 := log_bounds (by decide : 0<grid) state_173
  norm_num [grid] at h173
  have he : Real.log ((173:ℝ)^2)=2*(Real.log (173:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h173.1,h173.2]

theorem scale_177 : (2588074739/250000000:ℝ)≤Real.log ((177:ℝ)^2) ∧ Real.log ((177:ℝ)^2)≤(25880749517/2500000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have he : Real.log ((177:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((177:ℝ)^2)=2*Real.log (177:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (59:ℝ)) := by
           rw [show (177:ℝ)=(3:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h3.1,h3.2]

theorem scale_178 : (51817832749/5000000000:ℝ)≤Real.log ((178:ℝ)^2) ∧ Real.log ((178:ℝ)^2)≤(12954459339/1250000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h2 := log_bounds (by decide : 0<grid) state_2
  norm_num [grid] at h2
  have he : Real.log ((178:ℝ)^2)=2*(Real.log (2:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((178:ℝ)^2)=2*Real.log (178:ℝ) := Real.log_pow _ _
         _=2*(Real.log (2:ℝ)+Real.log (89:ℝ)) := by
           rw [show (178:ℝ)=(2:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h2.1,h2.2]

theorem scale_179 : (51873855223/5000000000:ℝ)≤Real.log ((179:ℝ)^2) ∧ Real.log ((179:ℝ)^2)≤(12968464997/1250000000:ℝ) := by
  have h179 := log_bounds (by decide : 0<grid) state_179
  norm_num [grid] at h179
  have he : Real.log ((179:ℝ)^2)=2*(Real.log (179:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h179.1,h179.2]

theorem scale_181 : (12996241869/1250000000:ℝ)≤Real.log ((181:ℝ)^2) ∧ Real.log ((181:ℝ)^2)≤(51984972243/5000000000:ℝ) := by
  have h181 := log_bounds (by decide : 0<grid) state_181
  norm_num [grid] at h181
  have he : Real.log ((181:ℝ)^2)=2*(Real.log (181:ℝ)) := by
    exact Real.log_pow _ _
  rw [he]
  constructor <;> linarith only [h181.1,h181.2]

theorem scale_183 : (6511857369/625000000:ℝ)≤Real.log ((183:ℝ)^2) ∧ Real.log ((183:ℝ)^2)≤(26047431629/2500000000:ℝ) := by
  have h3 := log_bounds (by decide : 0<grid) state_3
  norm_num [grid] at h3
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((183:ℝ)^2)=2*(Real.log (3:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((183:ℝ)^2)=2*Real.log (183:ℝ) := Real.log_pow _ _
         _=2*(Real.log (3:ℝ)+Real.log (61:ℝ)) := by
           rw [show (183:ℝ)=(3:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h3.1,h3.2,h61.1,h61.2]

#print axioms scale_85
#print axioms scale_86
#print axioms scale_87
#print axioms scale_89
#print axioms scale_91
#print axioms scale_93
#print axioms scale_94
#print axioms scale_95
#print axioms scale_97
#print axioms scale_101
#print axioms scale_103
#print axioms scale_105
#print axioms scale_106
#print axioms scale_107
#print axioms scale_109
#print axioms scale_111
#print axioms scale_113
#print axioms scale_115
#print axioms scale_118
#print axioms scale_119
#print axioms scale_122
#print axioms scale_123
#print axioms scale_127
#print axioms scale_129
#print axioms scale_131
#print axioms scale_133
#print axioms scale_134
#print axioms scale_137
#print axioms scale_139
#print axioms scale_141
#print axioms scale_142
#print axioms scale_143
#print axioms scale_145
#print axioms scale_146
#print axioms scale_149
#print axioms scale_151
#print axioms scale_155
#print axioms scale_157
#print axioms scale_158
#print axioms scale_159
#print axioms scale_161
#print axioms scale_163
#print axioms scale_166
#print axioms scale_167
#print axioms scale_173
#print axioms scale_177
#print axioms scale_178
#print axioms scale_179
#print axioms scale_181
#print axioms scale_183
end
end JSP233.ScaleLogs132
