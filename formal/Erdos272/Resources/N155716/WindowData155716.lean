module

public import Erdos272.Resources.N158375.WindowData158375

@[expose] public section

namespace JSP233.WindowData155716
noncomputable section
set_option autoImplicit false
abbrev Info := WindowData158375.Info

def info (_w : ℕ) : Info := ⟨155716,161056,119⟩
def G (_w : ℕ) : ℝ := 1/779664
def CoeffA (_w : ℕ) : ℝ := 1681293855030143/129944000000000000
def CoeffB (_w : ℕ) : ℝ := 1610416788095236189081/227402000000000000
def CoeffC (_w : ℕ) : ℝ := 58873766029907/129944
def HCommon : ℝ := 5107/400
def Fee (w N : ℕ) : ℝ := CoeffA w*(N:ℝ)^2+CoeffB w*N+CoeffC w
def SmallCount (w : ℕ) : ℕ := ((info w).memberFloor-2)^2+((info w).memberFloor-1)
end
end JSP233.WindowData155716
