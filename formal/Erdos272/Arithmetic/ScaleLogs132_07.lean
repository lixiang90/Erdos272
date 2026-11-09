module

public import Erdos272.Arithmetic.PrefixTable132

@[expose] public section
namespace JSP233.ScaleLogs132
open PrefixState131 PrefixTable131 PrefixTable132 PrefixLog131
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem scale_1793 : (74916451901/5000000000:ℝ)≤Real.log ((1793:ℝ)^2) ∧ Real.log ((1793:ℝ)^2)≤(9364557083/625000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have he : Real.log ((1793:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (163:ℝ)) := by
    calc Real.log ((1793:ℝ)^2)=2*Real.log (1793:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (163:ℝ)) := by
           rw [show (1793:ℝ)=(11:ℝ)*(163:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h163.1,h163.2]

theorem scale_1807 : (18748557521/1250000000:ℝ)≤Real.log ((1807:ℝ)^2) ∧ Real.log ((1807:ℝ)^2)≤(74994234821/5000000000:ℝ) := by
  have h139 := log_bounds (by decide : 0<grid) state_139
  norm_num [grid] at h139
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((1807:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (139:ℝ)) := by
    calc Real.log ((1807:ℝ)^2)=2*Real.log (1807:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (139:ℝ)) := by
           rw [show (1807:ℝ)=(13:ℝ)*(139:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h139.1,h139.2,h13.1,h13.2]

theorem scale_1817 : (75049417953/5000000000:ℝ)≤Real.log ((1817:ℝ)^2) ∧ Real.log ((1817:ℝ)^2)≤(75049422523/5000000000:ℝ) := by
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((1817:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((1817:ℝ)^2)=2*Real.log (1817:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (79:ℝ)) := by
           rw [show (1817:ℝ)=(23:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h79.1,h79.2,h23.1,h23.2]

theorem scale_1819 : (75060418991/5000000000:ℝ)≤Real.log ((1819:ℝ)^2) ∧ Real.log ((1819:ℝ)^2)≤(37530211837/2500000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have he : Real.log ((1819:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((1819:ℝ)^2)=2*Real.log (1819:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (107:ℝ)) := by
           rw [show (1819:ℝ)=(17:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h107.1,h107.2]

theorem scale_1829 : (18778810981/1250000000:ℝ)≤Real.log ((1829:ℝ)^2) ∧ Real.log ((1829:ℝ)^2)≤(37557624103/2500000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((1829:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((1829:ℝ)^2)=2*Real.log (1829:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (59:ℝ)) := by
           rw [show (1829:ℝ)=(31:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h31.1,h31.2]

theorem scale_1837 : (15031777603/1000000000:ℝ)≤Real.log ((1837:ℝ)^2) ∧ Real.log ((1837:ℝ)^2)≤(37579446391/2500000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have he : Real.log ((1837:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (167:ℝ)) := by
    calc Real.log ((1837:ℝ)^2)=2*Real.log (1837:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (167:ℝ)) := by
           rw [show (1837:ℝ)=(11:ℝ)*(167:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h167.1,h167.2]

theorem scale_1843 : (18797874199/1250000000:ℝ)≤Real.log ((1843:ℝ)^2) ∧ Real.log ((1843:ℝ)^2)≤(75191501453/5000000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have he : Real.log ((1843:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((1843:ℝ)^2)=2*Real.log (1843:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (97:ℝ)) := by
           rw [show (1843:ℝ)=(19:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h19.1,h19.2]

theorem scale_1853 : (37622804733/2500000000:ℝ)≤Real.log ((1853:ℝ)^2) ∧ Real.log ((1853:ℝ)^2)≤(37622807077/2500000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have he : Real.log ((1853:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((1853:ℝ)^2)=2*Real.log (1853:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (109:ℝ)) := by
           rw [show (1853:ℝ)=(17:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h109.1,h109.2]

theorem scale_1891 : (2357769003/156250000:ℝ)≤Real.log ((1891:ℝ)^2) ∧ Real.log ((1891:ℝ)^2)≤(7544861243/500000000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((1891:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((1891:ℝ)^2)=2*Real.log (1891:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (61:ℝ)) := by
           rw [show (1891:ℝ)=(31:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h61.1,h61.2,h31.1,h31.2]

theorem scale_1903 : (75511865833/5000000000:ℝ)≤Real.log ((1903:ℝ)^2) ∧ Real.log ((1903:ℝ)^2)≤(37755935303/2500000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h173 := log_bounds (by decide : 0<grid) state_173
  norm_num [grid] at h173
  have he : Real.log ((1903:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (173:ℝ)) := by
    calc Real.log ((1903:ℝ)^2)=2*Real.log (1903:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (173:ℝ)) := by
           rw [show (1903:ℝ)=(11:ℝ)*(173:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h173.1,h173.2]

theorem scale_1909 : (75543345491/5000000000:ℝ)≤Real.log ((1909:ℝ)^2) ∧ Real.log ((1909:ℝ)^2)≤(9442918761/625000000:ℝ) := by
  have h83 := log_bounds (by decide : 0<grid) state_83
  norm_num [grid] at h83
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((1909:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (83:ℝ)) := by
    calc Real.log ((1909:ℝ)^2)=2*Real.log (1909:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (83:ℝ)) := by
           rw [show (1909:ℝ)=(23:ℝ)*(83:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h83.1,h83.2,h23.1,h23.2]

theorem scale_1919 : (75595592173/5000000000:ℝ)≤Real.log ((1919:ℝ)^2) ∧ Real.log ((1919:ℝ)^2)≤(37797798421/2500000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have he : Real.log ((1919:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((1919:ℝ)^2)=2*Real.log (1919:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (101:ℝ)) := by
           rw [show (1919:ℝ)=(19:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h101.1,h101.2]

theorem scale_1921 : (37803004413/2500000000:ℝ)≤Real.log ((1921:ℝ)^2) ∧ Real.log ((1921:ℝ)^2)≤(75606013523/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have he : Real.log ((1921:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((1921:ℝ)^2)=2*Real.log (1921:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (113:ℝ)) := by
           rw [show (1921:ℝ)=(17:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h113.1,h113.2]

theorem scale_1927 : (75637192759/5000000000:ℝ)≤Real.log ((1927:ℝ)^2) ∧ Real.log ((1927:ℝ)^2)≤(75637199319/5000000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((1927:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (47:ℝ)) := by
    calc Real.log ((1927:ℝ)^2)=2*Real.log (1927:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (47:ℝ)) := by
           rw [show (1927:ℝ)=(41:ℝ)*(47:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h47.1,h47.2]

theorem scale_1937 : (15137790761/1000000000:ℝ)≤Real.log ((1937:ℝ)^2) ∧ Real.log ((1937:ℝ)^2)≤(75688958553/5000000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h149 := log_bounds (by decide : 0<grid) state_149
  norm_num [grid] at h149
  have he : Real.log ((1937:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (149:ℝ)) := by
    calc Real.log ((1937:ℝ)^2)=2*Real.log (1937:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (149:ℝ)) := by
           rw [show (1937:ℝ)=(13:ℝ)*(149:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h149.1,h149.2]

theorem scale_1943 : (15143976367/1000000000:ℝ)≤Real.log ((1943:ℝ)^2) ∧ Real.log ((1943:ℝ)^2)≤(75719886283/5000000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((1943:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((1943:ℝ)^2)=2*Real.log (1943:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (67:ℝ)) := by
           rw [show (1943:ℝ)=(29:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h29.1,h29.2]

theorem scale_1957 : (18947919221/1250000000:ℝ)≤Real.log ((1957:ℝ)^2) ∧ Real.log ((1957:ℝ)^2)≤(75791681559/5000000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h103 := log_bounds (by decide : 0<grid) state_103
  norm_num [grid] at h103
  have he : Real.log ((1957:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (103:ℝ)) := by
    calc Real.log ((1957:ℝ)^2)=2*Real.log (1957:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (103:ℝ)) := by
           rw [show (1957:ℝ)=(19:ℝ)*(103:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h103.1,h103.2]

theorem scale_1961 : (75812094627/5000000000:ℝ)≤Real.log ((1961:ℝ)^2) ∧ Real.log ((1961:ℝ)^2)≤(2369128147/156250000:ℝ) := by
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((1961:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (53:ℝ)) := by
    calc Real.log ((1961:ℝ)^2)=2*Real.log (1961:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (53:ℝ)) := by
           rw [show (1961:ℝ)=(37:ℝ)*(53:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h53.1,h53.2,h37.1,h37.2]

theorem scale_1963 : (75822289113/5000000000:ℝ)≤Real.log ((1963:ℝ)^2) ∧ Real.log ((1963:ℝ)^2)≤(75822293863/5000000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h151 := log_bounds (by decide : 0<grid) state_151
  norm_num [grid] at h151
  have he : Real.log ((1963:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (151:ℝ)) := by
    calc Real.log ((1963:ℝ)^2)=2*Real.log (1963:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (151:ℝ)) := by
           rw [show (1963:ℝ)=(13:ℝ)*(151:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h151.1,h151.2]

theorem scale_1969 : (15170561589/1000000000:ℝ)≤Real.log ((1969:ℝ)^2) ∧ Real.log ((1969:ℝ)^2)≤(18963203181/1250000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h179 := log_bounds (by decide : 0<grid) state_179
  norm_num [grid] at h179
  have he : Real.log ((1969:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (179:ℝ)) := by
    calc Real.log ((1969:ℝ)^2)=2*Real.log (1969:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (179:ℝ)) := by
           rw [show (1969:ℝ)=(11:ℝ)*(179:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h179.1,h179.2]

theorem scale_1991 : (37981960099/2500000000:ℝ)≤Real.log ((1991:ℝ)^2) ∧ Real.log ((1991:ℝ)^2)≤(75963924979/5000000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h181 := log_bounds (by decide : 0<grid) state_181
  norm_num [grid] at h181
  have he : Real.log ((1991:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (181:ℝ)) := by
    calc Real.log ((1991:ℝ)^2)=2*Real.log (1991:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (181:ℝ)) := by
           rw [show (1991:ℝ)=(11:ℝ)*(181:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h181.1,h181.2]

theorem scale_2021 : (7611347307/500000000:ℝ)≤Real.log ((2021:ℝ)^2) ∧ Real.log ((2021:ℝ)^2)≤(9514184991/625000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h47 := log_bounds (by decide : 0<grid) state_47
  norm_num [grid] at h47
  have he : Real.log ((2021:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (47:ℝ)) := by
    calc Real.log ((2021:ℝ)^2)=2*Real.log (2021:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (47:ℝ)) := by
           rw [show (2021:ℝ)=(43:ℝ)*(47:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h47.1,h47.2]

theorem scale_2033 : (76172675341/5000000000:ℝ)≤Real.log ((2033:ℝ)^2) ∧ Real.log ((2033:ℝ)^2)≤(38086340013/2500000000:ℝ) := by
  have h107 := log_bounds (by decide : 0<grid) state_107
  norm_num [grid] at h107
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have he : Real.log ((2033:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (107:ℝ)) := by
    calc Real.log ((2033:ℝ)^2)=2*Real.log (2033:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (107:ℝ)) := by
           rw [show (2033:ℝ)=(19:ℝ)*(107:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h107.1,h107.2,h19.1,h19.2]

theorem scale_2041 : (15242389759/1000000000:ℝ)≤Real.log ((2041:ℝ)^2) ∧ Real.log ((2041:ℝ)^2)≤(76211953553/5000000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h157 := log_bounds (by decide : 0<grid) state_157
  norm_num [grid] at h157
  have he : Real.log ((2041:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (157:ℝ)) := by
    calc Real.log ((2041:ℝ)^2)=2*Real.log (2041:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (157:ℝ)) := by
           rw [show (2041:ℝ)=(13:ℝ)*(157:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h157.1,h157.2]

theorem scale_2047 : (19060325773/1250000000:ℝ)≤Real.log ((2047:ℝ)^2) ∧ Real.log ((2047:ℝ)^2)≤(1906032693/125000000:ℝ) := by
  have h89 := log_bounds (by decide : 0<grid) state_89
  norm_num [grid] at h89
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((2047:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (89:ℝ)) := by
    calc Real.log ((2047:ℝ)^2)=2*Real.log (2047:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (89:ℝ)) := by
           rw [show (2047:ℝ)=(23:ℝ)*(89:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h89.1,h89.2,h23.1,h23.2]

theorem scale_2059 : (3814987719/250000000:ℝ)≤Real.log ((2059:ℝ)^2) ∧ Real.log ((2059:ℝ)^2)≤(38149879441/2500000000:ℝ) := by
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have he : Real.log ((2059:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((2059:ℝ)^2)=2*Real.log (2059:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (71:ℝ)) := by
           rw [show (2059:ℝ)=(29:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h29.1,h29.2,h71.1,h71.2]

theorem scale_2071 : (9544733227/625000000:ℝ)≤Real.log ((2071:ℝ)^2) ∧ Real.log ((2071:ℝ)^2)≤(38178935253/2500000000:ℝ) := by
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have h109 := log_bounds (by decide : 0<grid) state_109
  norm_num [grid] at h109
  have he : Real.log ((2071:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (109:ℝ)) := by
    calc Real.log ((2071:ℝ)^2)=2*Real.log (2071:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (109:ℝ)) := by
           rw [show (2071:ℝ)=(19:ℝ)*(109:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h19.1,h19.2,h109.1,h109.2]

theorem scale_2077 : (76386795579/5000000000:ℝ)≤Real.log ((2077:ℝ)^2) ∧ Real.log ((2077:ℝ)^2)≤(76386800029/5000000000:ℝ) := by
  have h67 := log_bounds (by decide : 0<grid) state_67
  norm_num [grid] at h67
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((2077:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (67:ℝ)) := by
    calc Real.log ((2077:ℝ)^2)=2*Real.log (2077:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (67:ℝ)) := by
           rw [show (2077:ℝ)=(31:ℝ)*(67:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h67.1,h67.2,h31.1,h31.2]

theorem scale_2101 : (239067763/15625000:ℝ)≤Real.log ((2101:ℝ)^2) ∧ Real.log ((2101:ℝ)^2)≤(9562711119/625000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h191 := log_bounds (by decide : 0<grid) state_191
  norm_num [grid] at h191
  have he : Real.log ((2101:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (191:ℝ)) := by
    calc Real.log ((2101:ℝ)^2)=2*Real.log (2101:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (191:ℝ)) := by
           rw [show (2101:ℝ)=(11:ℝ)*(191:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h191.1,h191.2]

theorem scale_2117 : (9572193751/625000000:ℝ)≤Real.log ((2117:ℝ)^2) ∧ Real.log ((2117:ℝ)^2)≤(19144388633/1250000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have he : Real.log ((2117:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((2117:ℝ)^2)=2*Real.log (2117:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (73:ℝ)) := by
           rw [show (2117:ℝ)=(29:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h29.1,h29.2]

theorem scale_2119 : (38293496373/2500000000:ℝ)≤Real.log ((2119:ℝ)^2) ∧ Real.log ((2119:ℝ)^2)≤(76586997511/5000000000:ℝ) := by
  have h163 := log_bounds (by decide : 0<grid) state_163
  norm_num [grid] at h163
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((2119:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (163:ℝ)) := by
    calc Real.log ((2119:ℝ)^2)=2*Real.log (2119:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (163:ℝ)) := by
           rw [show (2119:ℝ)=(13:ℝ)*(163:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h163.1,h163.2,h13.1,h13.2]

theorem scale_2123 : (76605851767/5000000000:ℝ)≤Real.log ((2123:ℝ)^2) ∧ Real.log ((2123:ℝ)^2)≤(76605856561/5000000000:ℝ) := by
  have h193 := log_bounds (by decide : 0<grid) state_193
  norm_num [grid] at h193
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have he : Real.log ((2123:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (193:ℝ)) := by
    calc Real.log ((2123:ℝ)^2)=2*Real.log (2123:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (193:ℝ)) := by
           rw [show (2123:ℝ)=(11:ℝ)*(193:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h193.1,h193.2,h11.1,h11.2]

theorem scale_2147 : (9589783147/625000000:ℝ)≤Real.log ((2147:ℝ)^2) ∧ Real.log ((2147:ℝ)^2)≤(613746159/40000000:ℝ) := by
  have h113 := log_bounds (by decide : 0<grid) state_113
  norm_num [grid] at h113
  have h19 := log_bounds (by decide : 0<grid) state_19
  norm_num [grid] at h19
  have he : Real.log ((2147:ℝ)^2)=2*(Real.log (19:ℝ)+Real.log (113:ℝ)) := by
    calc Real.log ((2147:ℝ)^2)=2*Real.log (2147:ℝ) := Real.log_pow _ _
         _=2*(Real.log (19:ℝ)+Real.log (113:ℝ)) := by
           rw [show (2147:ℝ)=(19:ℝ)*(113:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h113.1,h113.2,h19.1,h19.2]

theorem scale_2159 : (76774001489/5000000000:ℝ)≤Real.log ((2159:ℝ)^2) ∧ Real.log ((2159:ℝ)^2)≤(76774006213/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h127 := log_bounds (by decide : 0<grid) state_127
  norm_num [grid] at h127
  have he : Real.log ((2159:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (127:ℝ)) := by
    calc Real.log ((2159:ℝ)^2)=2*Real.log (2159:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (127:ℝ)) := by
           rw [show (2159:ℝ)=(17:ℝ)*(127:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h127.1,h127.2]

theorem scale_2167 : (76810987163/5000000000:ℝ)≤Real.log ((2167:ℝ)^2) ∧ Real.log ((2167:ℝ)^2)≤(38405495981/2500000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h197 := log_bounds (by decide : 0<grid) state_197
  norm_num [grid] at h197
  have he : Real.log ((2167:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (197:ℝ)) := by
    calc Real.log ((2167:ℝ)^2)=2*Real.log (2167:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (197:ℝ)) := by
           rw [show (2167:ℝ)=(11:ℝ)*(197:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h197.1,h197.2]

theorem scale_2171 : (3841471443/250000000:ℝ)≤Real.log ((2171:ℝ)^2) ∧ Real.log ((2171:ℝ)^2)≤(76829433629/5000000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h167 := log_bounds (by decide : 0<grid) state_167
  norm_num [grid] at h167
  have he : Real.log ((2171:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (167:ℝ)) := by
    calc Real.log ((2171:ℝ)^2)=2*Real.log (2171:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (167:ℝ)) := by
           rw [show (2171:ℝ)=(13:ℝ)*(167:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h167.1,h167.2]

theorem scale_2173 : (76838635647/5000000000:ℝ)≤Real.log ((2173:ℝ)^2) ∧ Real.log ((2173:ℝ)^2)≤(76838642593/5000000000:ℝ) := by
  have h41 := log_bounds (by decide : 0<grid) state_41
  norm_num [grid] at h41
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((2173:ℝ)^2)=2*(Real.log (41:ℝ)+Real.log (53:ℝ)) := by
    calc Real.log ((2173:ℝ)^2)=2*Real.log (2173:ℝ) := Real.log_pow _ _
         _=2*(Real.log (41:ℝ)+Real.log (53:ℝ)) := by
           rw [show (2173:ℝ)=(41:ℝ)*(53:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h41.1,h41.2,h53.1,h53.2]

theorem scale_2183 : (38442274899/2500000000:ℝ)≤Real.log ((2183:ℝ)^2) ∧ Real.log ((2183:ℝ)^2)≤(15376911219/1000000000:ℝ) := by
  have h59 := log_bounds (by decide : 0<grid) state_59
  norm_num [grid] at h59
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((2183:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (59:ℝ)) := by
    calc Real.log ((2183:ℝ)^2)=2*Real.log (2183:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (59:ℝ)) := by
           rw [show (2183:ℝ)=(37:ℝ)*(59:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h59.1,h59.2,h37.1,h37.2]

theorem scale_2189 : (38455999061/2500000000:ℝ)≤Real.log ((2189:ℝ)^2) ∧ Real.log ((2189:ℝ)^2)≤(76912002923/5000000000:ℝ) := by
  have h11 := log_bounds (by decide : 0<grid) state_11
  norm_num [grid] at h11
  have h199 := log_bounds (by decide : 0<grid) state_199
  norm_num [grid] at h199
  have he : Real.log ((2189:ℝ)^2)=2*(Real.log (11:ℝ)+Real.log (199:ℝ)) := by
    calc Real.log ((2189:ℝ)^2)=2*Real.log (2189:ℝ) := Real.log_pow _ _
         _=2*(Real.log (11:ℝ)+Real.log (199:ℝ)) := by
           rw [show (2189:ℝ)=(11:ℝ)*(199:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h11.1,h11.2,h199.1,h199.2]

theorem scale_2201 : (19241667031/1250000000:ℝ)≤Real.log ((2201:ℝ)^2) ∧ Real.log ((2201:ℝ)^2)≤(19241668157/1250000000:ℝ) := by
  have h71 := log_bounds (by decide : 0<grid) state_71
  norm_num [grid] at h71
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((2201:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (71:ℝ)) := by
    calc Real.log ((2201:ℝ)^2)=2*Real.log (2201:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (71:ℝ)) := by
           rw [show (2201:ℝ)=(31:ℝ)*(71:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h71.1,h71.2,h31.1,h31.2]

theorem scale_2227 : (38542051927/2500000000:ℝ)≤Real.log ((2227:ℝ)^2) ∧ Real.log ((2227:ℝ)^2)≤(77084108583/5000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h131 := log_bounds (by decide : 0<grid) state_131
  norm_num [grid] at h131
  have he : Real.log ((2227:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (131:ℝ)) := by
    calc Real.log ((2227:ℝ)^2)=2*Real.log (2227:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (131:ℝ)) := by
           rw [show (2227:ℝ)=(17:ℝ)*(131:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h131.1,h131.2]

theorem scale_2231 : (77102049161/5000000000:ℝ)≤Real.log ((2231:ℝ)^2) ∧ Real.log ((2231:ℝ)^2)≤(38551026911/2500000000:ℝ) := by
  have h97 := log_bounds (by decide : 0<grid) state_97
  norm_num [grid] at h97
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((2231:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (97:ℝ)) := by
    calc Real.log ((2231:ℝ)^2)=2*Real.log (2231:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (97:ℝ)) := by
           rw [show (2231:ℝ)=(23:ℝ)*(97:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h97.1,h97.2,h23.1,h23.2]

theorem scale_2249 : (38591203339/2500000000:ℝ)≤Real.log ((2249:ℝ)^2) ∧ Real.log ((2249:ℝ)^2)≤(77182411453/5000000000:ℝ) := by
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have h173 := log_bounds (by decide : 0<grid) state_173
  norm_num [grid] at h173
  have he : Real.log ((2249:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (173:ℝ)) := by
    calc Real.log ((2249:ℝ)^2)=2*Real.log (2249:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (173:ℝ)) := by
           rw [show (2249:ℝ)=(13:ℝ)*(173:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h13.1,h13.2,h173.1,h173.2]

theorem scale_2257 : (7721791397/500000000:ℝ)≤Real.log ((2257:ℝ)^2) ∧ Real.log ((2257:ℝ)^2)≤(77217920319/5000000000:ℝ) := by
  have h61 := log_bounds (by decide : 0<grid) state_61
  norm_num [grid] at h61
  have h37 := log_bounds (by decide : 0<grid) state_37
  norm_num [grid] at h37
  have he : Real.log ((2257:ℝ)^2)=2*(Real.log (37:ℝ)+Real.log (61:ℝ)) := by
    calc Real.log ((2257:ℝ)^2)=2*Real.log (2257:ℝ) := Real.log_pow _ _
         _=2*(Real.log (37:ℝ)+Real.log (61:ℝ)) := by
           rw [show (2257:ℝ)=(37:ℝ)*(61:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h61.1,h61.2,h37.1,h37.2]

theorem scale_2263 : (9655557969/625000000:ℝ)≤Real.log ((2263:ℝ)^2) ∧ Real.log ((2263:ℝ)^2)≤(38622234139/2500000000:ℝ) := by
  have h73 := log_bounds (by decide : 0<grid) state_73
  norm_num [grid] at h73
  have h31 := log_bounds (by decide : 0<grid) state_31
  norm_num [grid] at h31
  have he : Real.log ((2263:ℝ)^2)=2*(Real.log (31:ℝ)+Real.log (73:ℝ)) := by
    calc Real.log ((2263:ℝ)^2)=2*Real.log (2263:ℝ) := Real.log_pow _ _
         _=2*(Real.log (31:ℝ)+Real.log (73:ℝ)) := by
           rw [show (2263:ℝ)=(31:ℝ)*(73:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h73.1,h73.2,h31.1,h31.2]

theorem scale_2279 : (38657457979/2500000000:ℝ)≤Real.log ((2279:ℝ)^2) ∧ Real.log ((2279:ℝ)^2)≤(38657461601/2500000000:ℝ) := by
  have h43 := log_bounds (by decide : 0<grid) state_43
  norm_num [grid] at h43
  have h53 := log_bounds (by decide : 0<grid) state_53
  norm_num [grid] at h53
  have he : Real.log ((2279:ℝ)^2)=2*(Real.log (43:ℝ)+Real.log (53:ℝ)) := by
    calc Real.log ((2279:ℝ)^2)=2*Real.log (2279:ℝ) := Real.log_pow _ _
         _=2*(Real.log (43:ℝ)+Real.log (53:ℝ)) := by
           rw [show (2279:ℝ)=(43:ℝ)*(53:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h43.1,h43.2,h53.1,h53.2]

theorem scale_2291 : (77367434091/5000000000:ℝ)≤Real.log ((2291:ℝ)^2) ∧ Real.log ((2291:ℝ)^2)≤(77367438667/5000000000:ℝ) := by
  have h29 := log_bounds (by decide : 0<grid) state_29
  norm_num [grid] at h29
  have h79 := log_bounds (by decide : 0<grid) state_79
  norm_num [grid] at h79
  have he : Real.log ((2291:ℝ)^2)=2*(Real.log (29:ℝ)+Real.log (79:ℝ)) := by
    calc Real.log ((2291:ℝ)^2)=2*Real.log (2291:ℝ) := Real.log_pow _ _
         _=2*(Real.log (29:ℝ)+Real.log (79:ℝ)) := by
           rw [show (2291:ℝ)=(29:ℝ)*(79:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h29.1,h29.2,h79.1,h79.2]

theorem scale_2323 : (38753072269/2500000000:ℝ)≤Real.log ((2323:ℝ)^2) ∧ Real.log ((2323:ℝ)^2)≤(77506149211/5000000000:ℝ) := by
  have h101 := log_bounds (by decide : 0<grid) state_101
  norm_num [grid] at h101
  have h23 := log_bounds (by decide : 0<grid) state_23
  norm_num [grid] at h23
  have he : Real.log ((2323:ℝ)^2)=2*(Real.log (23:ℝ)+Real.log (101:ℝ)) := by
    calc Real.log ((2323:ℝ)^2)=2*Real.log (2323:ℝ) := Real.log_pow _ _
         _=2*(Real.log (23:ℝ)+Real.log (101:ℝ)) := by
           rw [show (2323:ℝ)=(23:ℝ)*(101:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h101.1,h101.2,h23.1,h23.2]

theorem scale_2327 : (7752334879/500000000:ℝ)≤Real.log ((2327:ℝ)^2) ∧ Real.log ((2327:ℝ)^2)≤(77523353571/5000000000:ℝ) := by
  have h179 := log_bounds (by decide : 0<grid) state_179
  norm_num [grid] at h179
  have h13 := log_bounds (by decide : 0<grid) state_13
  norm_num [grid] at h13
  have he : Real.log ((2327:ℝ)^2)=2*(Real.log (13:ℝ)+Real.log (179:ℝ)) := by
    calc Real.log ((2327:ℝ)^2)=2*Real.log (2327:ℝ) := Real.log_pow _ _
         _=2*(Real.log (13:ℝ)+Real.log (179:ℝ)) := by
           rw [show (2327:ℝ)=(13:ℝ)*(179:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h179.1,h179.2,h13.1,h13.2]

theorem scale_2329 : (19382984969/1250000000:ℝ)≤Real.log ((2329:ℝ)^2) ∧ Real.log ((2329:ℝ)^2)≤(15506388923/1000000000:ℝ) := by
  have h17 := log_bounds (by decide : 0<grid) state_17
  norm_num [grid] at h17
  have h137 := log_bounds (by decide : 0<grid) state_137
  norm_num [grid] at h137
  have he : Real.log ((2329:ℝ)^2)=2*(Real.log (17:ℝ)+Real.log (137:ℝ)) := by
    calc Real.log ((2329:ℝ)^2)=2*Real.log (2329:ℝ) := Real.log_pow _ _
         _=2*(Real.log (17:ℝ)+Real.log (137:ℝ)) := by
           rw [show (2329:ℝ)=(17:ℝ)*(137:ℝ) by norm_num]
           rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [he]
  constructor <;> linarith only [h17.1,h17.2,h137.1,h137.2]

#print axioms scale_1793
#print axioms scale_1807
#print axioms scale_1817
#print axioms scale_1819
#print axioms scale_1829
#print axioms scale_1837
#print axioms scale_1843
#print axioms scale_1853
#print axioms scale_1891
#print axioms scale_1903
#print axioms scale_1909
#print axioms scale_1919
#print axioms scale_1921
#print axioms scale_1927
#print axioms scale_1937
#print axioms scale_1943
#print axioms scale_1957
#print axioms scale_1961
#print axioms scale_1963
#print axioms scale_1969
#print axioms scale_1991
#print axioms scale_2021
#print axioms scale_2033
#print axioms scale_2041
#print axioms scale_2047
#print axioms scale_2059
#print axioms scale_2071
#print axioms scale_2077
#print axioms scale_2101
#print axioms scale_2117
#print axioms scale_2119
#print axioms scale_2123
#print axioms scale_2147
#print axioms scale_2159
#print axioms scale_2167
#print axioms scale_2171
#print axioms scale_2173
#print axioms scale_2183
#print axioms scale_2189
#print axioms scale_2201
#print axioms scale_2227
#print axioms scale_2231
#print axioms scale_2249
#print axioms scale_2257
#print axioms scale_2263
#print axioms scale_2279
#print axioms scale_2291
#print axioms scale_2323
#print axioms scale_2327
#print axioms scale_2329
end
end JSP233.ScaleLogs132
