module

public import Erdos272.Counting.N84364.TwoFirstHitRank84364
public import Erdos272.Counting.N82427.FixedSmallScalars82427

@[expose] public section

namespace JSP233.FixedAnchorNoSingleton82427
open StarCompletion SparseSmall39 SmallKernel112 SharpSmall212 TwoFirstHitRank84364
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_fixed_no_singleton_credit {N L : ℕ} {F : Finset (Finset ℤ)} {A : Finset ℤ}
    (hL : 2≤L) (hN : 2*L+1≤N) (hgap : L+1+(L-1)^2/4≤N)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F, ¬IsAP S)
    (hA : A∈Small F L) (hAN : A.Nonempty)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F L)=∅)
    (hno : ¬∃ B∈Small F L, ∃ c : ℤ, A∩B={c}) :
    (F.card : ℝ)≤(FixedSmallScalars82427.Coefficient (A.card-1) (L-1) : ℝ)*N-
      FixedSmallScalars82427.Credit (A.card-1) (L-1) := by
  obtain ⟨hAF, hAL⟩ := Finset.mem_filter.mp hA
  have hex : ∀ x : ℤ, ∃ T : Finset ℤ,
      x∈A → T∈F ∧ x∉T ∧ T.card≤L ∧ 2≤(T∩A).card := by
    intro x
    by_cases hx : x∈A
    · obtain ⟨T, hTS, hxT⟩ := actual_omitter_of_empty_kernel hkernel x (hlegal.1 A hAF hx)
      obtain ⟨hTF, hTL⟩ := Finset.mem_filter.mp hTS
      have hne : T≠A := by intro he; exact hxT (he.symm ▸ hx)
      have hi : (T∩A).Nonempty := isAP_nonempty (hlegal.2 T hTF A hAF hne)
      have htwo : 2≤(T∩A).card := by
        by_contra hn
        have he : (T∩A).card=1 := by have hp := Finset.card_pos.mpr hi; omega
        obtain ⟨c, hc⟩ := Finset.card_eq_one.mp he
        exact hno ⟨T, hTS, c, by simpa only [Finset.inter_comm] using hc⟩
      exact ⟨T, fun _ => ⟨hTF, hxT, hTL, htwo⟩⟩
    · exact ⟨∅, fun hh => (hx hh).elim⟩
  choose T hT using hex
  have hrank := actual_two_first_hit_rank hL hN hlegal hbad hAF hAN hAL T
    (fun x hx => (hT x hx).1) (fun x hx => (hT x hx).2.1)
    (fun x hx => (hT x hx).2.2.1) (fun x hx => (hT x hx).2.2.2)
  dsimp only at hrank
  have hfloor : (A.card-1)^2/4≤(L-1)^2/4 :=
    Nat.div_le_div_right (Nat.pow_le_pow_left (Nat.sub_le_sub_right hAL 1) 2)
  have hgap' : (L-1)+2+(A.card-1)^2/4≤N := by omega
  have haeq : ((A.card-1 : ℕ) : ℝ)+1=(A.card : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (Finset.card_pos.mpr hAN)
  have hdata : 2*(F.card : ℝ)+(((A.card-1 : ℕ) : ℝ)+1)*((L-1 : ℕ) : ℝ)*
      (((A.card-1 : ℕ) : ℝ)+((L-1 : ℕ) : ℝ)+3)≤
      2*(((A.card-1 : ℕ) : ℝ)+1)*((L-1 : ℕ) : ℝ)*N+
        2*(((A.card-1)^2/4 : ℕ) : ℝ) := by
    rw [←haeq] at hrank
    convert hrank using 1 <;> ring
  exact FixedSmallScalars82427.rank_credit hgap' hdata

#print axioms actual_fixed_no_singleton_credit
end
end JSP233.FixedAnchorNoSingleton82427
