module

public import Erdos272.Resources.StarResources30
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

/-! The physical interval and active-step arithmetic of the common-point
bound. The geometric AP-line estimate is explicit until CrossLine30 supplies it. -/
namespace JSP233.StarBudget30
open StarCompletion StarResources30
open scoped Classical
noncomputable section

theorem physical_card (N : ℕ) : (Finset.Icc (1:ℤ) (N:ℤ)).card=N := by
  rw [Int.card_Icc]
  omega

theorem active_steps_card_le (N : ℕ) (c : ℤ) (I : Finset ℤ)
    (hI : ∀ d∈I, 0<d ∧ 1≤c-2*d ∧ c+2*d≤(N:ℤ)) :
    I.card≤(N-1)/4 := by
  have hsub : I⊆Finset.Icc (1:ℤ) (((N-1)/4:ℕ):ℤ) := by
    intro d hd
    obtain ⟨hd0,hL,hR⟩ := hI d hd
    have hN : 1≤N := by omega
    have hfour : 4*d≤((N-1:ℕ):ℤ) := by omega
    have hdn : (d.toNat:ℤ)=d := Int.toNat_of_nonneg (by omega)
    have hnat : d.toNat*4≤N-1 := by omega
    have hdiv : d.toNat≤(N-1)/4 := (Nat.le_div_iff_mul_le (by decide)).mpr hnat
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hc := Finset.card_le_card hsub
  have he : (Finset.Icc (1:ℤ) (((N-1)/4:ℕ):ℤ)).card=(N-1)/4 := by
    rw [Int.card_Icc]
    rw [show (((N-1)/4:ℕ):ℤ)+1-1=(((N-1)/4:ℕ):ℤ) by omega]
    exact Int.toNat_natCast _
  rw [he] at hc
  exact hc

theorem small_budget_identity (N : ℕ) (hN : 1≤N) :
    N+(N-1).choose 2=N.choose 2+1 := by
  cases N with
  | zero => omega
  | succ n =>
    rw [Nat.succ_sub_one]
    have hc := Nat.choose_succ_succ n 1
    norm_num at hc
    omega

theorem physical_rooted_bound_of_APLarge
    (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hc : c∈Finset.Icc (1:ℤ) (N:ℤ))
    (hlegal : Legal (Finset.Icc (1:ℤ) (N:ℤ)) F) (hroot : Rooted F c)
    (a : ℕ) (ha : a≤(N-1)/4)
    (hAP : (APLarge F).card≤(CoveredAPBadPairs c (Finset.Icc (1:ℤ) (N:ℤ)) F).card+a) :
    F.card≤N.choose 2+1+(N-1)/4 := by
  have hN : 1≤N := by have := Finset.mem_Icc.mp hc; omega
  have hb := rooted_card_le_of_APLarge c (Finset.Icc (1:ℤ) (N:ℤ)) F hlegal hroot a hAP
  rw [physical_card,small_budget_identity N hN] at hb
  omega

#print axioms physical_card
#print axioms active_steps_card_le
#print axioms small_budget_identity
#print axioms physical_rooted_bound_of_APLarge
end
end JSP233.StarBudget30
