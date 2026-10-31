import Erdos272.Arithmetic.PrefixTable132
namespace JSP233.ScaleLogs132
open PrefixState131 PrefixTable131 PrefixTable132 PrefixLog131
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem scale_871 : (33848208559/2500000000:ℝ)≤Real.log ((871:ℝ)^2) ∧ Real.log ((871:ℝ)^2)≤(1353928431/100000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((871:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((871:ℝ)^2)=2*Real.log (871:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (67:ℝ)) := by
           rw [show (871:ℝ)=(13:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h13.1,h13.2]

theorem scale_889 : (8487621193/625000000:ℝ)≤Real.log ((889:ℝ)^2) ∧ Real.log ((889:ℝ)^2)≤(33950487129/2500000000:ℝ) := by
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((889:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((889:ℝ)^2)=2*Real.log (889:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (127:ℝ)) := by
           rw [show (889:ℝ)=(7:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h127.1,h127.2,h7.1,h7.2]

theorem scale_893 : (33972931809/2500000000:ℝ)≤Real.log ((893:ℝ)^2) ∧ Real.log ((893:ℝ)^2)≤(33972933641/2500000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((893:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (47:ℝ)) := by
    calc Real.log ((893:ℝ)^2)=2*Real.log (893:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (47:ℝ)) := by
           rw [show (893:ℝ)=(19:ℝ)*(47:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h47.1,h47.2]

theorem scale_895 : (8496029293/625000000:ℝ)≤Real.log ((895:ℝ)^2) ∧ Real.log ((895:ℝ)^2)≤(67968239117/5000000000:ℝ) := by
  have h179 := log_bounds (by decide : 0<grid) state_179
  norm_num [grid] at h179
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((895:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (179:ℝ)) := by
    calc Real.log ((895:ℝ)^2)=2*Real.log (895:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (179:ℝ)) := by
           rw [show (895:ℝ)=(5:ℝ)*(179:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h179.1,h179.2,h5.1,h5.2]

theorem scale_899 : (8501603789/625000000:ℝ)≤Real.log ((899:ℝ)^2) ∧ Real.log ((899:ℝ)^2)≤(34006415189/2500000000:ℝ) := by
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((899:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (31:ℝ)) := by
    calc Real.log ((899:ℝ)^2)=2*Real.log (899:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (31:ℝ)) := by
           rw [show (899:ℝ)=(29:ℝ)*(31:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h29.1,h29.2,h31.1,h31.2]

theorem scale_901 : (17008762539/1250000000:ℝ)≤Real.log ((901:ℝ)^2) ∧ Real.log ((901:ℝ)^2)≤(17008763551/1250000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((901:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (53:ℝ)) := by
    calc Real.log ((901:ℝ)^2)=2*Real.log (901:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (53:ℝ)) := by
           rw [show (901:ℝ)=(17:ℝ)*(53:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h53.1,h53.2]

theorem scale_905 : (68079346597/5000000000:ℝ)≤Real.log ((905:ℝ)^2) ∧ Real.log ((905:ℝ)^2)≤(17019837843/1250000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h181 := log_bounds (by decide : 0<grid) state_181
  norm_num [grid] at h181
  have he : Real.log ((905:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (181:ℝ)) := by
    calc Real.log ((905:ℝ)^2)=2*Real.log (905:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (181:ℝ)) := by
           rw [show (905:ℝ)=(5:ℝ)*(181:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h181.1,h181.2]

theorem scale_913 : (68167356067/5000000000:ℝ)≤Real.log ((913:ℝ)^2) ∧ Real.log ((913:ℝ)^2)≤(17041840163/1250000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((913:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((913:ℝ)^2)=2*Real.log (913:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (83:ℝ)) := by
           rw [show (913:ℝ)=(11:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h11.1,h11.2]

theorem scale_917 : (68211071909/5000000000:ℝ)≤Real.log ((917:ℝ)^2) ∧ Real.log ((917:ℝ)^2)≤(17052769157/1250000000:ℝ) := by
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((917:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((917:ℝ)^2)=2*Real.log (917:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (131:ℝ)) := by
           rw [show (917:ℝ)=(7:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h131.1,h131.2,h7.1,h7.2]

theorem scale_923 : (68276289663/5000000000:ℝ)≤Real.log ((923:ℝ)^2) ∧ Real.log ((923:ℝ)^2)≤(68276294149/5000000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((923:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((923:ℝ)^2)=2*Real.log (923:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (71:ℝ)) := by
           rw [show (923:ℝ)=(13:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h71.1,h71.2]

theorem scale_943 : (17122665267/1250000000:ℝ)≤Real.log ((943:ℝ)^2) ∧ Real.log ((943:ℝ)^2)≤(17122666003/1250000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((943:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (41:ℝ)) := by
    calc Real.log ((943:ℝ)^2)=2*Real.log (943:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (41:ℝ)) := by
           rw [show (943:ℝ)=(23:ℝ)*(41:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h23.1,h23.2]

theorem scale_949 : (68554085291/5000000000:ℝ)≤Real.log ((949:ℝ)^2) ∧ Real.log ((949:ℝ)^2)≤(68554089799/5000000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((949:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((949:ℝ)^2)=2*Real.log (949:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (73:ℝ)) := by
           rw [show (949:ℝ)=(13:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h13.1,h13.2]

theorem scale_955 : (68617110559/5000000000:ℝ)≤Real.log ((955:ℝ)^2) ∧ Real.log ((955:ℝ)^2)≤(13723423069/1000000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h191 := log_bounds (by decide : 0<grid) state_191
  norm_num [grid] at h191
  have he : Real.log ((955:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (191:ℝ)) := by
    calc Real.log ((955:ℝ)^2)=2*Real.log (955:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (191:ℝ)) := by
           rw [show (955:ℝ)=(5:ℝ)*(191:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h191.1,h191.2]

theorem scale_959 : (68658907931/5000000000:ℝ)≤Real.log ((959:ℝ)^2) ∧ Real.log ((959:ℝ)^2)≤(3432945633/250000000:ℝ) := by
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((959:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((959:ℝ)^2)=2*Real.log (959:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (137:ℝ)) := by
           rw [show (959:ℝ)=(7:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h137.1,h137.2,h7.1,h7.2]

theorem scale_965 : (34360639083/2500000000:ℝ)≤Real.log ((965:ℝ)^2) ∧ Real.log ((965:ℝ)^2)≤(34360641477/2500000000:ℝ) := by
  have h193 := log_bounds (by decide : 0<grid) state_193
  norm_num [grid] at h193
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((965:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (193:ℝ)) := by
    calc Real.log ((965:ℝ)^2)=2*Real.log (965:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (193:ℝ)) := by
           rw [show (965:ℝ)=(5:ℝ)*(193:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h193.1,h193.2,h5.1,h5.2]

theorem scale_973 : (68803838003/5000000000:ℝ)≤Real.log ((973:ℝ)^2) ∧ Real.log ((973:ℝ)^2)≤(34401921367/2500000000:ℝ) := by
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((973:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((973:ℝ)^2)=2*Real.log (973:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (139:ℝ)) := by
           rw [show (973:ℝ)=(7:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h139.1,h139.2,h7.1,h7.2]

theorem scale_979 : (17216328417/1250000000:ℝ)≤Real.log ((979:ℝ)^2) ∧ Real.log ((979:ℝ)^2)≤(17216329571/1250000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((979:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((979:ℝ)^2)=2*Real.log (979:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (89:ℝ)) := by
           rw [show (979:ℝ)=(11:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h11.1,h11.2]

theorem scale_985 : (34463206781/2500000000:ℝ)≤Real.log ((985:ℝ)^2) ∧ Real.log ((985:ℝ)^2)≤(13785283671/1000000000:ℝ) := by
  have h197 := log_bounds (by decide : 0<grid) state_197
  norm_num [grid] at h197
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have he : Real.log ((985:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (197:ℝ)) := by
    calc Real.log ((985:ℝ)^2)=2*Real.log (985:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (197:ℝ)) := by
           rw [show (985:ℝ)=(5:ℝ)*(197:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h197.1,h197.2,h5.1,h5.2]

theorem scale_989 : (68966941379/5000000000:ℝ)≤Real.log ((989:ℝ)^2) ∧ Real.log ((989:ℝ)^2)≤(68966944621/5000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((989:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (43:ℝ)) := by
    calc Real.log ((989:ℝ)^2)=2*Real.log (989:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (43:ℝ)) := by
           rw [show (989:ℝ)=(23:ℝ)*(43:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h23.1,h23.2]

theorem scale_995 : (69027424521/5000000000:ℝ)≤Real.log ((995:ℝ)^2) ∧ Real.log ((995:ℝ)^2)≤(17256857329/1250000000:ℝ) := by
  have h5 := log_bounds (by decide : 0<grid) state_5
  norm_num [grid] at h5
  have h199 := log_bounds (by decide : 0<grid) state_199
  norm_num [grid] at h199
  have he : Real.log ((995:ℝ)^2)=2*(Real.log (5:ℝ)+Real.log (199:ℝ)) := by
    calc Real.log ((995:ℝ)^2)=2*Real.log (995:ℝ) := Real.log_pow _ _
         _=2*(Real.log (5:ℝ)+Real.log (199:ℝ)) := by
           rw [show (995:ℝ)=(5:ℝ)*(199:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h5.1,h5.2,h199.1,h199.2]

theorem scale_1003 : (69107505327/5000000000:ℝ)≤Real.log ((1003:ℝ)^2) ∧ Real.log ((1003:ℝ)^2)≤(13821501919/1000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have he : Real.log ((1003:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((1003:ℝ)^2)=2*Real.log (1003:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (59:ℝ)) := by
           rw [show (1003:ℝ)=(17:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h59.1,h59.2]

theorem scale_1007 : (34573653253/2500000000:ℝ)≤Real.log ((1007:ℝ)^2) ∧ Real.log ((1007:ℝ)^2)≤(17286827639/1250000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((1007:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (53:ℝ)) := by
    calc Real.log ((1007:ℝ)^2)=2*Real.log (1007:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (53:ℝ)) := by
           rw [show (1007:ℝ)=(19:ℝ)*(53:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h53.1,h53.2]

theorem scale_1027 : (34671984687/2500000000:ℝ)≤Real.log ((1027:ℝ)^2) ∧ Real.log ((1027:ℝ)^2)≤(34671986967/2500000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((1027:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((1027:ℝ)^2)=2*Real.log (1027:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (79:ℝ)) := by
           rw [show (1027:ℝ)=(13:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h79.1,h79.2]

theorem scale_1037 : (69440869499/5000000000:ℝ)≤Real.log ((1037:ℝ)^2) ∧ Real.log ((1037:ℝ)^2)≤(69440873819/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((1037:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((1037:ℝ)^2)=2*Real.log (1037:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (61:ℝ)) := by
           rw [show (1037:ℝ)=(17:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h61.1,h61.2]

theorem scale_1043 : (17374640431/1250000000:ℝ)≤Real.log ((1043:ℝ)^2) ∧ Real.log ((1043:ℝ)^2)≤(34749283233/2500000000:ℝ) := by
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((1043:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((1043:ℝ)^2)=2*Real.log (1043:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (149:ℝ)) := by
           rw [show (1043:ℝ)=(7:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h149.1,h149.2,h7.1,h7.2]

theorem scale_1057 : (8703987129/625000000:ℝ)≤Real.log ((1057:ℝ)^2) ∧ Real.log ((1057:ℝ)^2)≤(4351993861/312500000:ℝ) := by
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((1057:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((1057:ℝ)^2)=2*Real.log (1057:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (151:ℝ)) := by
           rw [show (1057:ℝ)=(7:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h151.1,h151.2,h7.1,h7.2]

theorem scale_1067 : (69726059737/5000000000:ℝ)≤Real.log ((1067:ℝ)^2) ∧ Real.log ((1067:ℝ)^2)≤(34863032193/2500000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((1067:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((1067:ℝ)^2)=2*Real.log (1067:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (97:ℝ)) := by
           rw [show (1067:ℝ)=(11:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h11.1,h11.2]

theorem scale_1073 : (34891068093/2500000000:ℝ)≤Real.log ((1073:ℝ)^2) ∧ Real.log ((1073:ℝ)^2)≤(69782138267/5000000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((1073:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (37:ℝ)) := by
    calc Real.log ((1073:ℝ)^2)=2*Real.log (1073:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (37:ℝ)) := by
           rw [show (1073:ℝ)=(29:ℝ)*(37:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h29.1,h29.2]

theorem scale_1079 : (4364868557/312500000:ℝ)≤Real.log ((1079:ℝ)^2) ∧ Real.log ((1079:ℝ)^2)≤(69837901499/5000000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((1079:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((1079:ℝ)^2)=2*Real.log (1079:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (83:ℝ)) := by
           rw [show (1079:ℝ)=(13:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h13.1,h13.2]

theorem scale_1081 : (69856415983/5000000000:ℝ)≤Real.log ((1081:ℝ)^2) ∧ Real.log ((1081:ℝ)^2)≤(69856419651/5000000000:ℝ) := by
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((1081:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (47:ℝ)) := by
    calc Real.log ((1081:ℝ)^2)=2*Real.log (1081:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (47:ℝ)) := by
           rw [show (1081:ℝ)=(23:ℝ)*(47:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h47.1,h47.2,h23.1,h23.2]

theorem scale_1099 : (35010778357/2500000000:ℝ)≤Real.log ((1099:ℝ)^2) ∧ Real.log ((1099:ℝ)^2)≤(35010780733/2500000000:ℝ) := by
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((1099:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((1099:ℝ)^2)=2*Real.log (1099:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (157:ℝ)) := by
           rw [show (1099:ℝ)=(7:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h157.1,h157.2,h7.1,h7.2]

theorem scale_1111 : (35065077557/2500000000:ℝ)≤Real.log ((1111:ℝ)^2) ∧ Real.log ((1111:ℝ)^2)≤(2805206391/200000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have he : Real.log ((1111:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((1111:ℝ)^2)=2*Real.log (1111:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (101:ℝ)) := by
           rw [show (1111:ℝ)=(11:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h101.1,h101.2]

theorem scale_1121 : (70219761677/5000000000:ℝ)≤Real.log ((1121:ℝ)^2) ∧ Real.log ((1121:ℝ)^2)≤(70219765947/5000000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have he : Real.log ((1121:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((1121:ℝ)^2)=2*Real.log (1121:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (59:ℝ)) := by
           rw [show (1121:ℝ)=(19:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h19.1,h19.2]

theorem scale_1133 : (2813049593/200000000:ℝ)≤Real.log ((1133:ℝ)^2) ∧ Real.log ((1133:ℝ)^2)≤(17581561123/1250000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((1133:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((1133:ℝ)^2)=2*Real.log (1133:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (103:ℝ)) := by
           rw [show (1133:ℝ)=(11:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h103.1,h103.2]

theorem scale_1139 : (35189528491/2500000000:ℝ)≤Real.log ((1139:ℝ)^2) ∧ Real.log ((1139:ℝ)^2)≤(35189530709/2500000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have he : Real.log ((1139:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((1139:ℝ)^2)=2*Real.log (1139:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (67:ℝ)) := by
           rw [show (1139:ℝ)=(17:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h67.1,h67.2]

theorem scale_1141 : (14079320133/1000000000:ℝ)≤Real.log ((1141:ℝ)^2) ∧ Real.log ((1141:ℝ)^2)≤(4399787839/312500000:ℝ) := by
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((1141:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (163:ℝ)) := by
    calc Real.log ((1141:ℝ)^2)=2*Real.log (1141:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (163:ℝ)) := by
           rw [show (1141:ℝ)=(7:ℝ)*(163:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h163.1,h163.2,h7.1,h7.2]

theorem scale_1147 : (7044904993/500000000:ℝ)≤Real.log ((1147:ℝ)^2) ∧ Real.log ((1147:ℝ)^2)≤(70449052013/5000000000:ℝ) := by
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((1147:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (37:ℝ)) := by
    calc Real.log ((1147:ℝ)^2)=2*Real.log (1147:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (37:ℝ)) := by
           rw [show (1147:ℝ)=(31:ℝ)*(37:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h37.1,h37.2,h31.1,h31.2]

theorem scale_1157 : (70535854513/5000000000:ℝ)≤Real.log ((1157:ℝ)^2) ∧ Real.log ((1157:ℝ)^2)≤(70535859131/5000000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((1157:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((1157:ℝ)^2)=2*Real.log (1157:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (89:ℝ)) := by
           rw [show (1157:ℝ)=(13:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h13.1,h13.2]

theorem scale_1159 : (70553125849/5000000000:ℝ)≤Real.log ((1159:ℝ)^2) ∧ Real.log ((1159:ℝ)^2)≤(70553130171/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have he : Real.log ((1159:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((1159:ℝ)^2)=2*Real.log (1159:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (61:ℝ)) := by
           rw [show (1159:ℝ)=(19:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h61.1,h61.2]

theorem scale_1169 : (70639036779/5000000000:ℝ)≤Real.log ((1169:ℝ)^2) ∧ Real.log ((1169:ℝ)^2)≤(35319520771/2500000000:ℝ) := by
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((1169:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (167:ℝ)) := by
    calc Real.log ((1169:ℝ)^2)=2*Real.log (1169:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (167:ℝ)) := by
           rw [show (1169:ℝ)=(7:ℝ)*(167:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h167.1,h167.2,h7.1,h7.2]

theorem scale_1177 : (35353619141/2500000000:ℝ)≤Real.log ((1177:ℝ)^2) ∧ Real.log ((1177:ℝ)^2)≤(70707242959/5000000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((1177:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((1177:ℝ)^2)=2*Real.log (1177:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (107:ℝ)) := by
           rw [show (1177:ℝ)=(11:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h11.1,h11.2]

theorem scale_1189 : (35404338603/2500000000:ℝ)≤Real.log ((1189:ℝ)^2) ∧ Real.log ((1189:ℝ)^2)≤(17702170039/1250000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((1189:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (41:ℝ)) := by
    calc Real.log ((1189:ℝ)^2)=2*Real.log (1189:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (41:ℝ)) := by
           rw [show (1189:ℝ)=(29:ℝ)*(41:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h29.1,h29.2]

theorem scale_1199 : (70892428757/5000000000:ℝ)≤Real.log ((1199:ℝ)^2) ∧ Real.log ((1199:ℝ)^2)≤(70892433439/5000000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have he : Real.log ((1199:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((1199:ℝ)^2)=2*Real.log (1199:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (109:ℝ)) := by
           rw [show (1199:ℝ)=(11:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h109.1,h109.2]

theorem scale_1207 : (70958929527/5000000000:ℝ)≤Real.log ((1207:ℝ)^2) ∧ Real.log ((1207:ℝ)^2)≤(70958934017/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((1207:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((1207:ℝ)^2)=2*Real.log (1207:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (71:ℝ)) := by
           rw [show (1207:ℝ)=(17:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h71.1,h71.2]

theorem scale_1211 : (70992014597/5000000000:ℝ)≤Real.log ((1211:ℝ)^2) ∧ Real.log ((1211:ℝ)^2)≤(35496009683/2500000000:ℝ) := by
  have h173 := log_bounds (by decide : 0<grid) state_173
  norm_num [grid] at h173
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((1211:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (173:ℝ)) := by
    calc Real.log ((1211:ℝ)^2)=2*Real.log (1211:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (173:ℝ)) := by
           rw [show (1211:ℝ)=(7:ℝ)*(173:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h173.1,h173.2,h7.1,h7.2]

theorem scale_1219 : (71057858871/5000000000:ℝ)≤Real.log ((1219:ℝ)^2) ∧ Real.log ((1219:ℝ)^2)≤(2842314517/200000000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((1219:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (53:ℝ)) := by
    calc Real.log ((1219:ℝ)^2)=2*Real.log (1219:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (53:ℝ)) := by
           rw [show (1219:ℝ)=(23:ℝ)*(53:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h23.1,h23.2]

theorem scale_1241 : (14247345031/1000000000:ℝ)≤Real.log ((1241:ℝ)^2) ∧ Real.log ((1241:ℝ)^2)≤(71236729667/5000000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have he : Real.log ((1241:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((1241:ℝ)^2)=2*Real.log (1241:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (73:ℝ)) := by
           rw [show (1241:ℝ)=(17:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h17.1,h17.2]

theorem scale_1243 : (71252828117/5000000000:ℝ)≤Real.log ((1243:ℝ)^2) ∧ Real.log ((1243:ℝ)^2)≤(8906604101/625000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((1243:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((1243:ℝ)^2)=2*Real.log (1243:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (113:ℝ)) := by
           rw [show (1243:ℝ)=(11:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h11.1,h11.2]

theorem scale_1247 : (71284957517/5000000000:ℝ)≤Real.log ((1247:ℝ)^2) ∧ Real.log ((1247:ℝ)^2)≤(14256992153/1000000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((1247:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (43:ℝ)) := by
    calc Real.log ((1247:ℝ)^2)=2*Real.log (1247:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (43:ℝ)) := by
           rw [show (1247:ℝ)=(29:ℝ)*(43:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h29.1,h29.2]

theorem scale_1253 : (71332956709/5000000000:ℝ)≤Real.log ((1253:ℝ)^2) ∧ Real.log ((1253:ℝ)^2)≤(17833240371/1250000000:ℝ) := by
  have h179 := log_bounds (by decide : 0<grid) state_179
  norm_num [grid] at h179
  have h7 := log_bounds (by decide : 0<grid) state_7
  norm_num [grid] at h7
  have he : Real.log ((1253:ℝ)^2)=2*(Real.log (7:ℝ)+Real.log (179:ℝ)) := by
    calc Real.log ((1253:ℝ)^2)=2*Real.log (1253:ℝ) := Real.log_pow _ _
         _=2*(Real.log (7:ℝ)+Real.log (179:ℝ)) := by
           rw [show (1253:ℝ)=(7:ℝ)*(179:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h179.1,h179.2,h7.1,h7.2]

#print axioms scale_871
#print axioms scale_889
#print axioms scale_893
#print axioms scale_895
#print axioms scale_899
#print axioms scale_901
#print axioms scale_905
#print axioms scale_913
#print axioms scale_917
#print axioms scale_923
#print axioms scale_943
#print axioms scale_949
#print axioms scale_955
#print axioms scale_959
#print axioms scale_965
#print axioms scale_973
#print axioms scale_979
#print axioms scale_985
#print axioms scale_989
#print axioms scale_995
#print axioms scale_1003
#print axioms scale_1007
#print axioms scale_1027
#print axioms scale_1037
#print axioms scale_1043
#print axioms scale_1057
#print axioms scale_1067
#print axioms scale_1073
#print axioms scale_1079
#print axioms scale_1081
#print axioms scale_1099
#print axioms scale_1111
#print axioms scale_1121
#print axioms scale_1133
#print axioms scale_1139
#print axioms scale_1141
#print axioms scale_1147
#print axioms scale_1157
#print axioms scale_1159
#print axioms scale_1169
#print axioms scale_1177
#print axioms scale_1189
#print axioms scale_1199
#print axioms scale_1207
#print axioms scale_1211
#print axioms scale_1219
#print axioms scale_1241
#print axioms scale_1243
#print axioms scale_1247
#print axioms scale_1253
end
end JSP233.ScaleLogs132
