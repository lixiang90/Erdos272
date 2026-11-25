module

public import Erdos272.Resources.N158375.WindowData158375

@[expose] public section

namespace JSP233.WindowData151879
noncomputable section
set_option autoImplicit false
abbrev Info := WindowData158375.Info
def info (_w : ℕ) : Info := ⟨151879,153079,117⟩
def G (_w : ℕ) : ℝ := 1/763860
def CoeffA (_w : ℕ) : ℝ := 1678530104182899/127310000000000000
def CoeffB (_w : ℕ) : ℝ := 926458564386142790607/127310000000000000
def CoeffC (_w : ℕ) : ℝ := 24149552957277/63655
def HCommon : ℝ := 5107/400
def Fee (w N : ℕ) : ℝ := CoeffA w*(N:ℝ)^2+CoeffB w*N+CoeffC w
def SmallCount (w : ℕ) : ℕ := ((info w).memberFloor-2)^2+((info w).memberFloor-1)
end
end JSP233.WindowData151879
