module

public import Erdos272.Arithmetic.FactorFullData209

@[expose] public section
namespace JSP233.SmallCover209
set_option maxHeartbeats 0
def Small : List Nat := [2,3,5,7,11,13]
theorem marked_of_small_divisor (p n : Nat) (hp : p ∈ Small) (hd : p ∣ n) :
    FactorFullData209.marked n = true := by
  simp only [Small,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have hm := Nat.mod_eq_zero_of_dvd hd
    unfold FactorFullData209.marked FactorFullData209.factor
    split_ifs <;> simp_all
theorem marked_multiple (p q : Nat) (hp : p ∈ Small) :
    FactorFullData209.marked (p*q) = true := by
  exact marked_of_small_divisor p (p*q) hp ⟨q,rfl⟩
#print axioms marked_of_small_divisor
#print axioms marked_multiple
end JSP233.SmallCover209
