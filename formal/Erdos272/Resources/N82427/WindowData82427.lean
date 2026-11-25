module

public import Erdos272.Resources.N158375.WindowData158375

@[expose] public section

namespace JSP233.WindowData82427
noncomputable section
set_option autoImplicit false
abbrev Info := WindowData158375.Info

def info (w : ℕ) : Info :=
  match w with
  | 0 => ⟨82427,83394,87⟩
  | 1 => ⟨83395,84363,87⟩
  | 2 => ⟨82427,84363,88⟩
  | _ => ⟨82427,84363,130⟩

def G (w : ℕ) : ℝ :=
  match w with
  | 0 => 1/339744
  | 1 => 1/349692
  | 2 => 1/347964
  | _ => 1/547128

def CoeffA (w : ℕ) : ℝ :=
  match w with
  | 0 => 31403596145411/1769500000000000
  | 1 => 518259580694791/29141000000000000
  | 2 => 1018591589581187/57994000000000000
  | _ => 0

def CoeffB (w : ℕ) : ℝ :=
  match w with
  | 0 => 1970535155701749007731/396368000000000000
  | 1 => 13554477744950495377/2534000000000000
  | 2 => 2016651931581123652931/405958000000000000
  | _ => 0

def CoeffC (w : ℕ) : ℝ :=
  match w with
  | 0 => 167082864299/56624
  | 1 => -7767831138/1267
  | 2 => 627631078611/57994
  | _ => 6687285737295017569366769/17731000000000000

def HCommon : ℝ := 11921/1000

def RootK (w : ℕ) : ℕ :=
  match w with
  | 0 => 87
  | 1 => 0
  | 2 => 129
  | _ => 554

def RootCredit (w : ℕ) : ℕ := RootK w*(RootK w+3)/2

def Fee (w N : ℕ) : ℝ := CoeffA w*(N : ℝ)^2+CoeffB w*N+CoeffC w

def SmallLowCount : ℕ := 7311
def SmallLowCredit : ℕ := 632402
def SmallUpperCount : ℕ := 7397
def SmallUpperCredit : ℕ := 643540
end
end JSP233.WindowData82427
