module

public import Erdos272.Resources.N158375.WindowData158375

@[expose] public section

namespace JSP233.WindowData86412
noncomputable section
set_option autoImplicit false
abbrev Info := WindowData158375.Info

def info (w : ℕ) : Info :=
  match w with
  | 0 => ⟨86412,88403,89⟩
  | 1 => ⟨86412,88403,90⟩
  | _ => ⟨86412,88403,130⟩

def G (w : ℕ) : ℝ :=
  match w with
  | 0 => 1/363384
  | 1 => 1/360372
  | _ => 1/547128

def CoeffA (w : ℕ) : ℝ :=
  match w with
  | 0 => 34996476464273/2018800000000000
  | 1 => 257309738105927/15015500000000000
  | _ => 1034372304333739/91188000000000000

def CoeffB (w : ℕ) : ℝ :=
  match w with
  | 0 => 238095860721628004657/60564000000000000
  | 1 => 386458557504947518347/105108500000000000
  | _ => 436287545541755388631/638316000000000000

def CoeffC (w : ℕ) : ℝ :=
  match w with
  | 0 => 94635812654/721
  | 1 => 4206912255580/30031
  | _ => 7094093183573/30396

def HCommon : ℝ := 12

def RootK (w : ℕ) : ℕ := if w=0 then 89 else if w=1 then 129 else 554

def RootCredit (w : ℕ) : ℕ := RootK w*(RootK w+3)/2

def Fee (w N : ℕ) : ℝ := CoeffA w*(N : ℝ)^2+CoeffB w*N+CoeffC w

def SmallCount : ℕ := 7657
end
end JSP233.WindowData86412
