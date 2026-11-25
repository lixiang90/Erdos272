module

public import Erdos272.Resources.N158375.WindowData158375

@[expose] public section

namespace JSP233.WindowData153080
noncomputable section
set_option autoImplicit false
abbrev Info := WindowData158375.Info
def info (_w : ℕ) : Info := ⟨153080,155715,118⟩
def G (_w : ℕ) : ℝ := 1/789564
def CoeffA (_w : ℕ) : ℝ := 6722757072253/514039062500000
def CoeffB (_w : ℕ) : ℝ := 6885493563351354370399/921158000000000000
def CoeffC (_w : ℕ) : ℝ := 53903490294533/131594
def HCommon : ℝ := 5107/400
def Fee (w N : ℕ) : ℝ := CoeffA w*(N:ℝ)^2+CoeffB w*N+CoeffC w
def SmallCount (w : ℕ) : ℕ := ((info w).memberFloor-2)^2+((info w).memberFloor-1)
end
end JSP233.WindowData153080
