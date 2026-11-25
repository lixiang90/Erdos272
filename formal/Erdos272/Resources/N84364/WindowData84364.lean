module

public import Erdos272.Resources.N158375.WindowData158375

@[expose] public section

namespace JSP233.WindowData84364
noncomputable section
set_option autoImplicit false
abbrev Info := WindowData158375.Info

def info (w : ℕ) : Info :=
  match w with
  | 0 => ⟨84364,86411,88⟩
  | 1 => ⟨84364,86411,89⟩
  | _ => ⟨84364,86411,130⟩

def G (w : ℕ) : ℝ :=
  match w with
  | 0 => 1/355728
  | 1 => 1/363384
  | _ => 1/547128

def CoeffA (w : ℕ) : ℝ :=
  match w with
  | 0 => 260427512453817/14822000000000000
  | 1 => 105157935557833/6056400000000000
  | _ => 1034372304333739/91188000000000000

def CoeffB (w : ℕ) : ℝ :=
  match w with
  | 0 => 118458787644346236997/29644000000000000
  | 1 => 235502685349845938153/60564000000000000
  | _ => 437332485349160970803/638316000000000000

def CoeffC (w : ℕ) : ℝ :=
  match w with
  | 0 => 3305770836817/29644
  | 1 => 2604918057925/20188
  | _ => 7094093183573/30396

def HCommon : ℝ := 12

def RootK (w : ℕ) : ℕ := if w=0 then 88 else if w=1 then 129 else 554

def RootCredit (w : ℕ) : ℕ := RootK w*(RootK w+3)/2

def Fee (w N : ℕ) : ℝ := CoeffA w*(N : ℝ)^2+CoeffB w*N+CoeffC w

def SmallCount : ℕ := 7483

def SmallCredit : ℕ := 654763
end
end JSP233.WindowData84364
