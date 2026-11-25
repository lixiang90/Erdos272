module

public import Erdos272.Resources.N65968.WindowData65968

@[expose] public section

namespace JSP233.SmallData65968
noncomputable section
set_option autoImplicit false

structure Policy where
  low : ℕ
  high : ℕ
  L : ℕ
  T : ℕ
  coefficient : ℕ
  credit : ℕ
  base : ℕ
  mid : ℕ

def policy (p : ℕ) : Policy :=
  match p with
  | 0 => ⟨65968,66834,77,77,5853,453608,4,5⟩
  | _ => ⟨66835,67701,78,77,5930,462541,4,5⟩

def HSmall : ℝ := 4759/400
def Leading : ℝ := 1/2-257021/625000
def SmallLoss (count : ℝ) : ℝ := count+HSmall+1/4-2*(257021/625000)-1851/1000
def SmallConstant (credit : ℝ) : ℝ := credit+HSmall-257021/625000-1851/1000-50945/8-1
def SmallMargin (count credit n : ℝ) : ℝ := Leading*n^2-SmallLoss count*n+SmallConstant credit

end
end JSP233.SmallData65968
