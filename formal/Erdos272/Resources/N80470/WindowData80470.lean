module

public import Erdos272.Resources.N158375.WindowData158375

@[expose] public section

namespace JSP233.WindowData80470
noncomputable section
set_option autoImplicit false
abbrev Info := WindowData158375.Info

def info (w : ℕ) : Info :=
  match w with
  | 0 => ⟨80470,81426,86⟩
  | 1 => ⟨80470,82425,86⟩
  | 2 => ⟨80470,82425,87⟩
  | _ => ⟨80470,82425,130⟩

def G (w : ℕ) : ℝ :=
  match w with
  | 0 => 1/335652
  | 1 => 1/327132
  | 2 => 1/331572
  | _ => 1/547128

def CoeffA (w : ℕ) : ℝ :=
  match w with
  | 0 => 507867565652907/27971000000000000
  | 1 => 98809351767779/5452200000000000
  | 2 => 981033572311251/55262000000000000
  | _ => 0

def CoeffB (w : ℕ) : ℝ :=
  match w with
  | 0 => 4002921700363946629/39159400000000000
  | 1 => 2466549628005013319/23853375000000000
  | 2 => 34344207140850981057/386834000000000000
  | _ => 0

def CoeffC (w : ℕ) : ℝ :=
  match w with
  | 0 => 10107442655950/27971
  | 1 => 3260659215121/9087
  | 2 => 10339300617779/27631
  | _ => 6687285737295017569366769/17731000000000000

def HCommon : ℝ := 11921/1000

def RootK (w : ℕ) : ℕ :=
  match w with
  | 0 => 86
  | 1 => 0
  | 2 => 129
  | _ => 554

def Witness (w : ℕ) : ℕ :=
  match w with
  | 0 => 85
  | 1 => 86
  | _ => 129

def RootCredit (w : ℕ) : ℕ := RootK w*(RootK w+3)/2
def Fee (w N : ℕ) : ℝ := CoeffA w*(N : ℝ)^2+CoeffB w*N+CoeffC w
def SmallLowCount : ℕ := 7141
def SmallLowCredit : ℕ := 610556
def SmallUpperCount : ℕ := 7226
def SmallUpperCredit : ℕ := 621437
end
end JSP233.WindowData80470
