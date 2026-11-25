module

public import Erdos272.Resources.N158375.WindowData158375

@[expose] public section

namespace JSP233.WindowData142758
noncomputable section
set_option autoImplicit false
abbrev Info := WindowData158375.Info

def info (w : ℕ) : Info :=
  match w with
  | 0 => ⟨142758,145304,114⟩
  | 1 => ⟨145305,150464,115⟩
  | _ => ⟨142758,179999,130⟩

def G (w : ℕ) : ℝ :=
  match w with
  | 0 => 1/718212
  | 1 => 1/742716
  | _ => 1/780216

def CoeffA (w : ℕ) : ℝ :=
  match w with
  | 0 => 810379716823979/59851000000000000
  | 1 => 553919478434963/41262000000000000
  | _ => 379776759518347/32509000000000000

def CoeffB (w : ℕ) : ℝ :=
  match w with
  | 0 => 91301470887540352529/13092406250000000
  | 1 => 24543501399790005703/3438500000000000
  | _ => 128529266594923590343/32509000000000000

def CoeffC (w : ℕ) : ℝ :=
  match w with
  | 0 => 21911968432472/59851
  | 1 => 49475345321437/123786
  | _ => 104215406313889/130036

def HCommon : ℝ := 5107/400
def RootK (w : ℕ) : ℕ := if w=2 then 554 else 129
def RootCredit (w : ℕ) : ℕ := RootK w*(RootK w+3)/2
def Fee (w N : ℕ) : ℝ := CoeffA w*(N : ℝ)^2+CoeffB w*N+CoeffC w
def SmallCount (w : ℕ) : ℕ := ((info w).memberFloor-2)^2+((info w).memberFloor-1)
end
end JSP233.WindowData142758
