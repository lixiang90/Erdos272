module

public import Erdos272.Resources.N67702.WindowData67702

@[expose] public section

namespace JSP233.SmallData67702
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
  | 0 => ⟨67702,68579,78,78,6007,471550,2,6⟩
  | 1 => ⟨68580,69457,79,78,6085,480716,2,6⟩
  | 2 => ⟨69458,71236,79,79,6163,489959,3,6⟩
  | 3 => ⟨71237,73038,80,80,6321,508841,4,6⟩
  | 4 => ⟨73039,74862,81,81,6481,528202,5,6⟩
  | 5 => ⟨74863,76708,82,82,6643,548048,6,6⟩
  | 6 => ⟨76709,78577,83,83,6807,568385,7,7⟩
  | _ => ⟨78578,80469,84,84,6973,589219,8,8⟩

def HSmall : ℝ := 4759/400
def Leading : ℝ := 1/2-257021/625000
def SmallLoss (count : ℝ) : ℝ := count+HSmall+1/4-2*(257021/625000)-1851/1000
def SmallConstant (credit : ℝ) : ℝ := credit+HSmall-257021/625000-1851/1000-50945/8-1
def SmallMargin (count credit n : ℝ) : ℝ := Leading*n^2-SmallLoss count*n+SmallConstant credit

end
end JSP233.SmallData67702
