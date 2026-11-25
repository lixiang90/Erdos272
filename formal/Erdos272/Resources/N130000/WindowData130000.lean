module

public import Erdos272.Resources.N158375.WindowData158375

@[expose] public section

namespace JSP233.WindowData130000
noncomputable section
set_option autoImplicit false
abbrev Info := WindowData158375.Info

def info (w : ℕ) : Info :=
  match w with
  | 0 => ⟨130000,132797,108⟩
  | 1 => ⟨132798,137732,110⟩
  | 2 => ⟨137733,145304,112⟩
  | _ => ⟨130000,179999,130⟩

def G (w : ℕ) : ℝ :=
  match w with
  | 0 => 1/651180
  | 1 => 1/659436
  | 2 => 1/706236
  | _ => 1/743904

def CoeffA (w : ℕ) : ℝ :=
  match w with
  | 0 => 1557081289541497/108530000000000000
  | 1 => 386332194157869/27476500000000000
  | 2 => 1628100945877719/117706000000000000
  | _ => 160348169416361/13776000000000000

def CoeffB (w : ℕ) : ℝ :=
  match w with
  | 0 => 5211767415799365010151/759710000000000000
  | 1 => 143741925447997231679/21981200000000000
  | 2 => 5969635051797637487891/823942000000000000
  | _ => 358940009215381782073/123984000000000000

def CoeffC (w : ℕ) : ℝ :=
  match w with
  | 0 => 11362945564876/54265
  | 1 => 13518005571941/54953
  | 2 => 32134367087159/117706
  | _ => 30085007969687/41328

def HCommon : ℝ := 5107/400
def RootK (w : ℕ) : ℕ := if w=3 then 554 else 129
def RootCredit (w : ℕ) : ℕ := RootK w*(RootK w+3)/2
def Fee (w N : ℕ) : ℝ := CoeffA w*(N : ℝ)^2+CoeffB w*N+CoeffC w
def SmallCount (w : ℕ) : ℕ := ((info w).memberFloor-2)^2+((info w).memberFloor-1)
end
end JSP233.WindowData130000
