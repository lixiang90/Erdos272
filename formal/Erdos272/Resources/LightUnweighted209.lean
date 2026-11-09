module

public import Erdos272.Resources.ActualLightAnalytic209
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.LightUnweighted209
open LightAnalytic209 LightOwnerPrice209 ActualLightAnalytic209 PrefixAbel208
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem closed_sum {N T E B V HIGH L : ℕ} (hET : E<T) (hTV : T≤V)
    (hB : 0<B) (hNH : N≤HIGH) (hAH : T-E≤HIGH) (hL : 1≤L) :
    (∑d∈Finset.Icc 1 N,(LightPrice208.Closed N d T E B V:ℝ))≤
      Alpha (T-E:ℕ) B V E L*(N:ℝ)^2+
        ((V:ℝ)*LogFactor (T-E:ℕ) B HIGH)*N := by
  have hp (n : ℕ) : Prefix (fun _ : ℕ => (1:ℝ)) n=n := by simp [Prefix]
  have hh := weighted_closed hET hTV hB hNH hAH hL (fun _ : ℕ => (1:ℝ))
    1 0 0 (by norm_num) le_rfl le_rfl (by intros; norm_num)
    (by intros; rw [hp]; simp)
  have hs := shifted_sum (fun d => (LightPrice208.Closed N d T E B V:ℝ)) N
  simpa only [one_mul,add_zero,sub_zero,hs] using hh

theorem closed_partial {N D T E B V HIGH L : ℕ} (hET : E<T) (hTV : T≤V)
    (hB : 0<B) (hNH : N≤HIGH) (hAH : T-E≤HIGH) (hL : 1≤L) (hDN : D≤N) :
    (∑d∈Finset.Icc 1 D,(LightPrice208.Closed N d T E B V:ℝ))≤
      Alpha (T-E:ℕ) B V E L*(N:ℝ)^2+
        ((V:ℝ)*LogFactor (T-E:ℕ) B HIGH)*N := by
  apply le_trans ?_ (closed_sum hET hTV hB hNH hAH hL)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun d hd => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans hDN⟩)
    (by intros; positivity)

theorem actual_band (s : System) (v : Valid s) (b : Band)
    {T E B V HIGH L : ℕ} (hET : E<T) (hTV : T≤V) (hB : 0<B)
    (hNH : s.N≤HIGH) (hAH : T-E≤HIGH) (hL : 1≤L) (hDN : s.D≤s.N)
    (hfields : ∀d∈Finset.Icc 1 s.D,
      s.T d b=T ∧ s.E d b=E ∧ s.B d b=B ∧ s.U d b+s.B d b-3≤V) :
    (∑d∈Finset.Icc 1 s.D,EffectiveLight s d b)≤
      (if E≤1 then 0 else Alpha (T-E:ℕ) B V E L)*(s.N:ℝ)^2+
        (if E≤1 then 0 else (V:ℝ)*LogFactor (T-E:ℕ) B HIGH)*s.N := by
  by_cases he : E≤1
  · simp only [if_pos he,zero_mul,add_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro d hd
    simp only [EffectiveLight,(hfields d hd).2.1,if_pos he]
  · simp only [if_neg he]
    apply le_trans ?_ (closed_partial hET hTV hB hNH hAH hL hDN)
    apply Finset.sum_le_sum
    intro d hd
    obtain ⟨hT,hE,hBB,hV⟩ := hfields d hd
    simp only [EffectiveLight,hE,if_neg he,System.Light]
    have hd0 : 0<d := (Finset.mem_Icc.mp hd).1
    have hTU := v.TU d hd b
    have hB2 := v.B_two d hd b
    have hTV' : T≤s.U d b+B-3 := by rw [hBB] at hB2; rw [hT] at hTU; omega
    rw [hT,hBB]
    have hV' : s.U d b+B-3≤V := by simpa only [hBB] using hV
    exact_mod_cast closed_cap_mono hd0 hB hET.le hTV' hV'

/-- The actual seven-band light bill, with no finite-fee callback. The
frozen menu-zero layouts use one fixed B for every physical owner class. -/
theorem actual_total (s : System) (v : Valid s)
    (T E B V : Band→ℕ) (HIGH L : ℕ)
    (hET : ∀b,E b<T b) (hTV : ∀b,T b≤V b) (hB : ∀b,0<B b)
    (hNH : s.N≤HIGH) (hAH : ∀b,T b-E b≤HIGH) (hL : 1≤L) (hDN : s.D≤s.N)
    (hfields : ∀d∈Finset.Icc 1 s.D,∀b,
      s.T d b=T b ∧ s.E d b=E b ∧ s.B d b=B b ∧ s.U d b+s.B d b-3≤V b) :
    (∑d∈Finset.Icc 1 s.D,∑b : Band,EffectiveLight s d b)≤
      (∑b : Band,if E b≤1 then 0 else Alpha (T b-E b:ℕ) (B b) (V b) (E b) L)*(s.N:ℝ)^2+
        (∑b : Band,if E b≤1 then 0 else (V b:ℝ)*LogFactor (T b-E b:ℕ) (B b) HIGH)*s.N := by
  rw [Finset.sum_comm]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun b hb =>
    actual_band s v b (hET b) (hTV b) (hB b) hNH (hAH b) hL hDN
      (fun d hd => hfields d hd b))
  simpa only [Finset.sum_add_distrib,Finset.sum_mul] using hh

#print axioms closed_sum
#print axioms actual_total
end
end JSP233.LightUnweighted209
