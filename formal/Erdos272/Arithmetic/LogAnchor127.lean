import Erdos272.Arithmetic.DivisorMoment122

/-! Tight finite logarithmic windows and the exact fixed-anchor certificates.
The near10 library bounds already have ordinary finite Taylor proofs.
No derivative or physical pool bound is assumed in this numerical module. -/
namespace JSP233.LogAnchor127
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Anchor : ℝ := 113246208
def AnchorSlope : ℝ := 53107/200
def AnchorIntercept : ℝ := 4755141098
def TwoLo : ℝ := 69314718045/100000000000
def TwoHi : ℝ := 69314718066/100000000000
def ThreeLo : ℝ := 109861228857/100000000000
def ThreeHi : ℝ := 109861228877/100000000000
def L4Lo : ℝ := 20*TwoLo+3*ThreeLo
def L4Hi : ℝ := 20*TwoHi+3*ThreeHi
def L9Lo : ℝ := 22*TwoLo+ThreeLo
def L9Hi : ℝ := 22*TwoHi+ThreeHi
def L36Lo : ℝ := 20*TwoLo+ThreeLo
def L36Hi : ℝ := 20*TwoHi+ThreeHi
def Qprime (x : ℝ) : ℝ := x^2/2+(91/50)*x+18181/10000
def SlopeExpr : ℝ :=
  (Real.log (Anchor/4))^3/24+(Real.log (Anchor/9))^3/54-
    (DivisorMoment122.Q3 (Real.log (Anchor/36))+Qprime (Real.log (Anchor/36)))/36
def InterceptExpr : ℝ :=
  (Anchor/4)*((Real.log (Anchor/4))^2/2-Real.log (Anchor/4)+1)+
  (Anchor/9)*((Real.log (Anchor/9))^2/2-Real.log (Anchor/9)+1)-
  (Anchor/36)*Qprime (Real.log (Anchor/36))-2

theorem log_two_window : TwoLo≤Real.log 2 ∧ Real.log 2≤TwoHi := by
  have h := abs_le.mp Real.log_two_near_10
  constructor <;> dsimp only [TwoLo,TwoHi] <;> linarith only [h.1,h.2]

theorem log_three_window : ThreeLo≤Real.log 3 ∧ Real.log 3≤ThreeHi := by
  have h := abs_le.mp Real.log_three_near_10
  constructor <;> dsimp only [ThreeLo,ThreeHi] <;> linarith only [h.1,h.2]

theorem anchor_log4 : Real.log (Anchor/4)=20*Real.log 2+3*Real.log 3 := by
  have he : Anchor/4=(2:ℝ)^20*(3:ℝ)^3 := by norm_num [Anchor]
  rw [he,Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
  norm_num

theorem anchor_log9 : Real.log (Anchor/9)=22*Real.log 2+Real.log 3 := by
  have he : Anchor/9=(2:ℝ)^22*3 := by norm_num [Anchor]
  rw [he,Real.log_mul (by positivity) (by norm_num),Real.log_pow]
  norm_num

theorem anchor_log36 : Real.log (Anchor/36)=20*Real.log 2+Real.log 3 := by
  have he : Anchor/36=(2:ℝ)^20*3 := by norm_num [Anchor]
  rw [he,Real.log_mul (by positivity) (by norm_num),Real.log_pow]
  norm_num

theorem anchor_log_windows :
    L4Lo≤Real.log (Anchor/4) ∧ Real.log (Anchor/4)≤L4Hi ∧
    L9Lo≤Real.log (Anchor/9) ∧ Real.log (Anchor/9)≤L9Hi ∧
    L36Lo≤Real.log (Anchor/36) ∧ Real.log (Anchor/36)≤L36Hi := by
  obtain ⟨h2l,h2u⟩ := log_two_window
  obtain ⟨h3l,h3u⟩ := log_three_window
  rw [anchor_log4,anchor_log9,anchor_log36]
  dsimp only [L4Lo,L4Hi,L9Lo,L9Hi,L36Lo,L36Hi]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem anchor_slope_lower : AnchorSlope≤SlopeExpr := by
  obtain ⟨h4l,_h4u,h9l,_h9u,h36l,h36u⟩ := anchor_log_windows
  have h4p : 0≤L4Lo := by norm_num [L4Lo,TwoLo,ThreeLo]
  have h9p : 0≤L9Lo := by norm_num [L9Lo,TwoLo,ThreeLo]
  have h36p : 0≤Real.log (Anchor/36) := by
    have hp : 0≤L36Lo := by norm_num [L36Lo,TwoLo,ThreeLo]
    exact hp.trans h36l
  have h4 : L4Lo^3≤(Real.log (Anchor/4))^3 := by gcongr
  have h9 : L9Lo^3≤(Real.log (Anchor/9))^3 := by gcongr
  have hq := DivisorMoment122.q3_monotone h36p h36u
  have hd : Qprime (Real.log (Anchor/36))≤Qprime L36Hi := by
    dsimp only [Qprime]
    gcongr
  have hr : AnchorSlope≤L4Lo^3/24+L9Lo^3/54-
      (DivisorMoment122.Q3 L36Hi+Qprime L36Hi)/36 := by
    norm_num [AnchorSlope,L4Lo,L9Lo,L36Hi,TwoLo,ThreeLo,TwoHi,ThreeHi,
      DivisorMoment122.Q3,Qprime]
  dsimp only [SlopeExpr]
  linarith only [h4,h9,hq,hd,hr]

theorem anchor_intercept_upper : InterceptExpr≤AnchorIntercept := by
  obtain ⟨h4l,h4u,h9l,h9u,h36l,_h36u⟩ := anchor_log_windows
  have h4p : 0≤Real.log (Anchor/4) := by
    have hp : 0≤L4Lo := by norm_num [L4Lo,TwoLo,ThreeLo]
    exact hp.trans h4l
  have h9p : 0≤Real.log (Anchor/9) := by
    have hp : 0≤L9Lo := by norm_num [L9Lo,TwoLo,ThreeLo]
    exact hp.trans h9l
  have h36p : 0≤L36Lo := by norm_num [L36Lo,TwoLo,ThreeLo]
  have h4sq : (Real.log (Anchor/4))^2≤L4Hi^2 := by gcongr
  have h9sq : (Real.log (Anchor/9))^2≤L9Hi^2 := by gcongr
  have h4 : (Real.log (Anchor/4))^2/2-Real.log (Anchor/4)+1≤L4Hi^2/2-L4Lo+1 := by
    linarith only [h4sq,h4l]
  have h9 : (Real.log (Anchor/9))^2/2-Real.log (Anchor/9)+1≤L9Hi^2/2-L9Lo+1 := by
    linarith only [h9sq,h9l]
  have hd : Qprime L36Lo≤Qprime (Real.log (Anchor/36)) := by
    dsimp only [Qprime]
    gcongr
  have hm4 := mul_le_mul_of_nonneg_left h4 (by norm_num [Anchor] : 0≤Anchor/4)
  have hm9 := mul_le_mul_of_nonneg_left h9 (by norm_num [Anchor] : 0≤Anchor/9)
  have hmd := mul_le_mul_of_nonneg_left hd (by norm_num [Anchor] : 0≤Anchor/36)
  have hr : (Anchor/4)*(L4Hi^2/2-L4Lo+1)+(Anchor/9)*(L9Hi^2/2-L9Lo+1)-
      (Anchor/36)*Qprime L36Lo-2≤AnchorIntercept := by
    norm_num [Anchor,AnchorIntercept,L4Hi,L4Lo,L9Hi,L9Lo,L36Lo,TwoHi,TwoLo,ThreeHi,ThreeLo,Qprime]
  dsimp only [InterceptExpr]
  linarith only [hm4,hm9,hmd,hr]

#print axioms log_two_window
#print axioms log_three_window
#print axioms anchor_log4
#print axioms anchor_log9
#print axioms anchor_log36
#print axioms anchor_log_windows
#print axioms anchor_slope_lower
#print axioms anchor_intercept_upper
end
end JSP233.LogAnchor127
