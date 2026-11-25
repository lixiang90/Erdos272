module

public import Erdos272.Resources.N158375.WindowData158375

@[expose] public section

namespace JSP233.WindowData109474
noncomputable section
set_option autoImplicit false
abbrev Info := WindowData158375.Info

def info (w : ℕ) : Info :=
  match w with
  | 0 => ⟨109474,111704,100⟩
  | 1 => ⟨111705,113957,101⟩
  | 2 => ⟨113958,118532,102⟩
  | _ => ⟨109474,118532,130⟩

def G (w : ℕ) : ℝ :=
  match w with
  | 0 => 1/546432
  | 1 => 1/556356
  | 2 => 1/574212
  | _ => 1/615528

def CoeffA (w : ℕ) : ℝ :=
  match w with
  | 0 => 141386494334863/9107200000000000
  | 1 => 1425154462969453/92726000000000000
  | 2 => 1456397126698671/95702000000000000
  | _ => 196628273424347/17098000000000000

def CoeffB (w : ℕ) : ℝ :=
  match w with
  | 0 => 1671296527258276122927/318752000000000000
  | 1 => 684527690726811914933/129816400000000000
  | 2 => 182058970092364375181/33495700000000000
  | _ => 806978634087929803/598430000000000

def CoeffC (w : ℕ) : ℝ :=
  match w with
  | 0 => 17046673554729/91072
  | 1 => 18283527458935/92726
  | 2 => 10272894075394/47851
  | _ => 23134532141851/102588

def HCommon : ℝ := 5107/400
def RootK (w : ℕ) : ℕ := if w=3 then 554 else 129
def RootCredit (w : ℕ) : ℕ := RootK w*(RootK w+3)/2
def Fee (w N : ℕ) : ℝ := CoeffA w*(N : ℝ)^2+CoeffB w*N+CoeffC w
def SmallCount (w : ℕ) : ℕ := ((info w).memberFloor-2)^2+((info w).memberFloor-1)
end
end JSP233.WindowData109474
