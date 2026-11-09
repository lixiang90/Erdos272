module

public import Erdos272.Arithmetic.LightOwnerPrice209
public import Erdos272.Resources.ActualBandEval208
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.ActualLightAnalytic209
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208
open LightOwnerPrice209 LightOwners209 LightAnalytic209
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def EffectiveLight (s : System) (d : ℕ) (b : Band) : ℝ :=
  if s.E d b≤1 then 0 else s.Light d b

/-- Actual geometry determines each owner's fixed light parameters. The
chosen V may enlarge the physical cap by three; monotonicity justifies this. -/
theorem actual_owner_light (s : System) (v : Valid s) (b : Band)
    {T E B V HIGH L mask : ℕ} {lo hi : ℤ}
    (hc : Checks mask lo hi) (hET : E<T) (hTV : T≤V) (hB : 0<B)
    (hNH : s.N≤HIGH) (hAH : T-E≤HIGH) (hL : 1≤L) (hDN : s.D≤s.N)
    (hfields : ∀d∈Finset.Icc 1 s.D, Selected mask d=true →
      s.T d b=T ∧ s.E d b=E ∧ s.B d b=B ∧ s.U d b+s.B d b-3≤V) :
    (∑d∈Finset.Icc 1 s.D,if Selected mask d then EffectiveLight s d b else 0)≤
      Rho mask*Alpha (T-E:ℕ) B V E L*(s.N:ℝ)^2+
        (LinearFactor mask lo hi*(V:ℝ)*LogFactor (T-E:ℕ) B HIGH)*s.N := by
  apply le_trans ?_ (owner_partial hc hET hTV hB hNH hAH hL hDN)
  apply Finset.sum_le_sum
  intro d hd
  by_cases hs : Selected mask d=true
  · simp only [hs,↓reduceIte]
    obtain ⟨hT,hE,hBB,hV⟩ := hfields d hd hs
    by_cases he1 : s.E d b≤1
    · simp only [EffectiveLight,if_pos he1]
      positivity
    · simp only [EffectiveLight,if_neg he1,System.Light]
      have hd0 : 0<d := (Finset.mem_Icc.mp hd).1
      have hTU := v.TU d hd b
      have hB2 := v.B_two d hd b
      have hTV' : T≤s.U d b+B-3 := by rw [hBB] at hB2; rw [hT] at hTU; omega
      rw [hT,hE,hBB]
      have hV' : s.U d b+B-3≤V := by simpa only [hBB] using hV
      exact_mod_cast closed_cap_mono hd0 hB hET.le hTV' hV'
  · have hs' : Selected mask d=false := Bool.eq_false_iff.mpr hs
    simp only [hs',Bool.false_eq_true,↓reduceIte,le_refl]

theorem actual_owner_effective (s : System) (v : Valid s) (b : Band)
    {T E B V HIGH L mask : ℕ} {lo hi : ℤ}
    (hc : Checks mask lo hi) (hET : E<T) (hTV : T≤V) (hB : 0<B)
    (hNH : s.N≤HIGH) (hAH : T-E≤HIGH) (hL : 1≤L) (hDN : s.D≤s.N)
    (hfields : ∀d∈Finset.Icc 1 s.D, Selected mask d=true →
      s.T d b=T ∧ s.E d b=E ∧ s.B d b=B ∧ s.U d b+s.B d b-3≤V) :
    (∑d∈Finset.Icc 1 s.D,if Selected mask d then EffectiveLight s d b else 0)≤
      if E≤1 then 0 else
        Rho mask*Alpha (T-E:ℕ) B V E L*(s.N:ℝ)^2+
          (LinearFactor mask lo hi*(V:ℝ)*LogFactor (T-E:ℕ) B HIGH)*s.N := by
  by_cases he : E≤1
  · rw [if_pos he]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro d hd
    by_cases hs : Selected mask d=true
    · have hE := (hfields d hd hs).2.1
      simp only [hs,↓reduceIte,EffectiveLight,hE,if_pos he]
    · have hs' : Selected mask d=false := Bool.eq_false_iff.mpr hs
      simp only [hs',Bool.false_eq_true,↓reduceIte]
  · rw [if_neg he]
    exact actual_owner_light s v b hc hET hTV hB hNH hAH hL hDN hfields

#print axioms actual_owner_light
#print axioms actual_owner_effective
end
end JSP233.ActualLightAnalytic209
