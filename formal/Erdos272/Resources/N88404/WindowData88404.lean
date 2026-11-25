module

public import Erdos272.Resources.N158375.WindowData158375

@[expose] public section

namespace JSP233.WindowData88404
noncomputable section
set_option autoImplicit false
abbrev Info := WindowData158375.Info

def info (w : ℕ) : Info :=
  match w with
  | 0 => ⟨88404,90408,90⟩
  | 1 => ⟨90409,92436,91⟩
  | 2 => ⟨92437,94487,92⟩
  | _ => ⟨88404,94487,130⟩

def G (w : ℕ) : ℝ :=
  match w with
  | 0 => 1/375744
  | 1 => 1/384780
  | 2 => 1/389604
  | _ => 1/530808

def CoeffA (w : ℕ) : ℝ :=
  match w with
  | 0 => 67352733246201/3914000000000000
  | 1 => 21853334744159/1282600000000000
  | 2 => 1093515542866207/64934000000000000
  | _ => 1005397837634161/88468000000000000

def CoeffB (w : ℕ) : ℝ :=
  match w with
  | 0 => 178436854500731858181/43836800000000000
  | 1 => 927983384730169140349/224455000000000000
  | 2 => 135120217129399952987/32467000000000000
  | _ => 12508503372048613371/18214000000000000

def CoeffC (w : ℕ) : ℝ :=
  match w with
  | 0 => 4328015245913/31312
  | 1 => 9563077441821/64130
  | 2 => 10223981537939/64934
  | _ => 21231348582921/88468

def HCommon : ℝ := 5107/400

def RootK (w : ℕ) : ℕ := if w=3 then 554 else 129

def RootCredit (w : ℕ) : ℕ := RootK w*(RootK w+3)/2

def Fee (w N : ℕ) : ℝ := CoeffA w*(N : ℝ)^2+CoeffB w*N+CoeffC w

def SmallCount (w : ℕ) : ℕ := ((info w).memberFloor-2)^2+((info w).memberFloor-1)
end
end JSP233.WindowData88404
