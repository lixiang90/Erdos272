module

public import Erdos272.Arithmetic.LightAnalytic209
public import Erdos272.Arithmetic.LightOwners209
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.LightOwnerPrice209
open LightAnalytic209 LightOwners209
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem shifted_sum (f : ℕ→ℝ) (n : ℕ) :
    (∑i∈Finset.range n,f (i+1))=∑d∈Finset.Icc 1 n,f d := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,Finset.sum_Icc_succ_top (by omega),ih]

def LinearFactor (mask : ℕ) (lo hi : ℤ) : ℝ :=
  ((Count mask 210:ℝ)+(hi:ℝ)-(lo:ℝ))/210

theorem owner_closed {N T E B V HIGH L mask : ℕ} {lo hi : ℤ}
    (hc : Checks mask lo hi) (hET : E<T) (hTV : T≤V)
    (hB : 0<B) (hNH : N≤HIGH) (hAH : T-E≤HIGH) (hL : 1≤L) :
    (∑d∈Finset.Icc 1 N,if Selected mask d then
      (LightPrice208.Closed N d T E B V:ℝ) else 0)≤
      Rho mask*Alpha (T-E:ℕ) B V E L*(N:ℝ)^2+
        (LinearFactor mask lo hi*(V:ℝ)*LogFactor (T-E:ℕ) B HIGH)*N := by
  have hs := checks_sign hc
  have hl : (lo:ℝ)/210≤0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hs.1) (by norm_num)
  have hu : (0:ℝ)≤(hi:ℝ)/210 := div_nonneg (by exact_mod_cast hs.2) (by norm_num)
  have hh := weighted_closed hET hTV hB hNH hAH hL (Weight mask)
    (Rho mask) ((lo:ℝ)/210) ((hi:ℝ)/210) (rho_nonneg mask) hl hu
    (fun i hi' => weight_nonneg mask i)
    (fun n hn hnN => real_bounds hc n)
  have he : (∑i∈Finset.range N,Weight mask i*(LightPrice208.Closed N (i+1) T E B V:ℝ))=
      ∑d∈Finset.Icc 1 N,if Selected mask d then (LightPrice208.Closed N d T E B V:ℝ) else 0 := by
    simp only [Weight,ite_mul,one_mul,zero_mul]
    exact shifted_sum (fun d => if Selected mask d then (LightPrice208.Closed N d T E B V:ℝ) else 0) N
  rw [he] at hh
  convert hh using 1
  unfold LinearFactor Rho
  ring

theorem owner_partial {N D T E B V HIGH L mask : ℕ} {lo hi : ℤ}
    (hc : Checks mask lo hi) (hET : E<T) (hTV : T≤V)
    (hB : 0<B) (hNH : N≤HIGH) (hAH : T-E≤HIGH) (hL : 1≤L) (hDN : D≤N) :
    (∑d∈Finset.Icc 1 D,if Selected mask d then
      (LightPrice208.Closed N d T E B V:ℝ) else 0)≤
      Rho mask*Alpha (T-E:ℕ) B V E L*(N:ℝ)^2+
        (LinearFactor mask lo hi*(V:ℝ)*LogFactor (T-E:ℕ) B HIGH)*N := by
  apply le_trans ?_ (owner_closed hc hET hTV hB hNH hAH hL)
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (fun d hd => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans hDN⟩)
  intro d hd hn
  split_ifs <;> positivity

theorem closed_cap_mono {N d T E B V W : ℕ} (hd : 0<d) (hB : 0<B)
    (hET : E≤T) (hTV : T≤V) (hVW : V≤W) :
    LightPrice208.Closed N d T E B V≤LightPrice208.Closed N d T E B W := by
  rw [←LightPrice208.price_closed hd hB hET hTV,
    ←LightPrice208.price_closed hd hB hET (hTV.trans hVW)]
  apply Finset.sum_le_sum
  intro r hr
  apply Nat.mul_le_mul_left
  exact min_le_min hVW le_rfl

#print axioms owner_closed
#print axioms owner_partial
#print axioms closed_cap_mono
end
end JSP233.LightOwnerPrice209
