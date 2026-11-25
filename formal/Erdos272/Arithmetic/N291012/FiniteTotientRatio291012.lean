module

public import Erdos272.Arithmetic.PrimorialRatio39

@[expose] public section
namespace JSP233.LowResourceBridges3040
open PrimorialRatio39
noncomputable section
set_option autoImplicit false

theorem primorial_seven : Primorial 7 = 510510 := by
  norm_num [Primorial, Finset.prod_range_succ, prime_at_seed_nat, SeedPrime]

theorem ratio_six : Ratio 6 = (1001/192 : ℝ) := by
  norm_num [Ratio, Finset.prod_range_succ, prime_at_seed_nat, SeedPrime]

theorem finite_totient_ratio {N m : ℕ} (hN : N < 510510) (hm : m ≤ N) :
    192*m ≤ 1001*Nat.totient m := by
  have hcut : N < Primorial (6+1) := by
    change N < Primorial 7
    rw [primorial_seven]
    exact hN
  have hr := (uniform_omega_and_ratio N 6 hcut).2 m hm
  rw [ratio_six] at hr
  have hn : 192*(m : ℝ) ≤ 1001*Nat.totient m := by nlinarith only [hr]
  exact_mod_cast hn

#print axioms finite_totient_ratio
end
end JSP233.LowResourceBridges3040
