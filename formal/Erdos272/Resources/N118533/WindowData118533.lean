module

public import Erdos272.Resources.N158375.WindowData158375

@[expose] public section

namespace JSP233.WindowData118533
noncomputable section
set_option autoImplicit false
abbrev Info := WindowData158375.Info

def info (w : ℕ) : Info :=
  match w with
  | 0 => ⟨118533,125563,104⟩
  | 1 => ⟨125564,129999,107⟩
  | _ => ⟨118533,129999,130⟩

def G (w : ℕ) : ℝ :=
  match w with
  | 0 => 1/617196
  | 1 => 1/647652
  | _ => 1/725976

def CoeffA (w : ℕ) : ℝ :=
  match w with
  | 0 => 15368671782749/1028660000000000
  | 1 => 1567440968366383/107942000000000000
  | _ => 234291622649263/20166000000000000

def CoeffB (w : ℕ) : ℝ :=
  match w with
  | 0 => 13891921107561780469/2368625000000000
  | 1 => 4682714212647312122797/755594000000000000
  | _ => 1780901930805756358883/846972000000000000

def CoeffC (w : ℕ) : ℝ :=
  match w with
  | 0 => 13010708825112/51433
  | 1 => 14834228425213/53971
  | _ => 82166993389505/120996

def HCommon : ℝ := 5107/400
def RootK (w : ℕ) : ℕ := if w=2 then 554 else 129
def RootCredit (w : ℕ) : ℕ := RootK w*(RootK w+3)/2
def Fee (w N : ℕ) : ℝ := CoeffA w*(N : ℝ)^2+CoeffB w*N+CoeffC w
def SmallCount (w : ℕ) : ℕ := ((info w).memberFloor-2)^2+((info w).memberFloor-1)
end
end JSP233.WindowData118533
