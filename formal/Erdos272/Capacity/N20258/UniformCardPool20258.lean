module

public import Erdos272.Counting.N84364.UniformBridge84364
public import Erdos272.Counting.N86412.StrictPool86412
public import Erdos272.Counting.N20258.PaddedSource20258
public import Erdos272.Core.N200000.MixedCore200000

@[expose] public section
namespace JSP233.UniformCardPool20258
open StarCompletion PrivatePairExistence IntrinsicTriples208 PaddedSource20258
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

theorem pool_floor {N s h : ℕ} {S : Finset ℤ} (hi : N≤2^18) (inside : S⊆Ground N)
    (bad : ¬IsAP S) (four : 4≤s) (top : s≤549) (size : s≤S.card)
    (val : h≤UniformNumeric84364.value s) : h≤(Pool S).card := by
  have cert : SourceContract86412.Paid ⟨s,1,h⟩ := UniformBridge84364.uniform_paid four top val
    (fun U sz hu => StrictPool86412.actual_U_le_pool U sz hu)
  have two : 2≤S.card := by omega
  exact cert hi inside two size (MixedCore200000.crooked_defect_positive two bad)

theorem mass_mono {A F : Finset (Finset ℤ)} (sub : A⊆F) : mass A≤mass F :=
  Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)

theorem unit_mass {N s h : ℕ} {A F : Finset (Finset ℤ)}
    (hi : N≤2^18) (legal : Legal (Ground N) F) (sub : A⊆CrookedMembers F)
    (four : 4≤s) (top : s≤549) (size : ∀ S∈A,s≤S.card)
    (val : h≤UniformNumeric84364.value s) : (h:ℝ)*(A.card:ℝ)≤mass A := by
  calc
    _ = ∑ _S∈A, (h:ℝ) := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun S hs => by
      obtain ⟨mem,bad⟩ := Finset.mem_filter.mp (sub hs)
      exact_mod_cast pool_floor hi (legal.1 S mem) bad four top (size S hs) val)

#print axioms pool_floor
#print axioms unit_mass
end
end JSP233.UniformCardPool20258
