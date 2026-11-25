module

public import Erdos272.Counting.ShortAP208

@[expose] public section

namespace JSP233.RootedShort80470
open StarCompletion APGeometry APCount41 ShortAP208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_rooted_three_count {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hc : c ∈ Ground N) (hsub : ∀ S ∈ F, S ⊆ Ground N)
    (hAP : ∀ S ∈ F, IsAP S) (hthree : ∀ S ∈ F, S.card = 3)
    (hroot : ∀ S ∈ F, c ∈ S) :
    (F.card : ℝ)≤(N : ℝ)/2+(c : ℝ)-3/2 := by
  let r := c.toNat
  have hcN := (mem_ground N c).mp hc
  have hrc : (r : ℤ) = c := Int.toNat_of_nonneg (by omega)
  have hr : 1 ≤ r ∧ r ≤ N := by omega
  let C (i : ℕ) := F.filter (fun S => RootPosition c S = i)
  have hdata := fun S hS => actual_root_position (hsub S hS) (hAP S hS)
    (by rw [hthree S hS]; omega) (hroot S hS)
  have hend : ∀ S ∈ F, (1 : ℤ) ≤ Low S ∧ High S ≤ (N : ℤ) := by
    intro S hS
    have hne := isAP_nonempty (hAP S hS)
    exact ⟨((mem_ground N (Low S)).mp (hsub S hS (low_spec hne).1)).1,
      ((mem_ground N (High S)).mp (hsub S hS (high_spec hne).1)).2⟩
  have hstep : ∀ i ∈ Finset.range 3, ∀ S ∈ C i,
      Step S ≤ if i = 0 then (N - r) / 2 else
        if i = 1 then min (r - 1) (N - r) else (r - 1) / 2 := by
    intro i hi S hS
    obtain ⟨hSF, hSi⟩ := Finset.mem_filter.mp hS
    obtain ⟨_, _, hs, he⟩ := hdata S hSF
    have hl := (hend S hSF).1
    have hh := (hend S hSF).2
    rw [hSi] at hs
    rw [hthree S hSF] at he
    norm_num at he
    have hir : i < 3 := Finset.mem_range.mp hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · simp only [ite_true, Nat.cast_zero, zero_mul, add_zero] at hs ⊢
      have hbound : 2 * Step S ≤ N - r := by omega
      omega
    · simp only [show (1 : ℕ) ≠ 0 by omega, ite_false, ite_true,
        Nat.cast_one, one_mul] at hs ⊢
      have hb1 : Step S ≤ r - 1 := by omega
      have hb2 : Step S ≤ N - r := by omega
      exact le_min hb1 hb2
    · simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
        ite_false, Nat.cast_ofNat] at hs ⊢
      have hbound : 2 * Step S ≤ r - 1 := by omega
      omega
  have hcount : ∀ i ∈ Finset.range 3, (C i).card ≤
      if i = 0 then (N - r) / 2 else
        if i = 1 then min (r - 1) (N - r) else (r - 1) / 2 := by
    intro i hi
    apply actual_rooted_three_position_count
      (fun S hS => hsub S (Finset.mem_filter.mp hS).1)
      (fun S hS => hAP S (Finset.mem_filter.mp hS).1)
      (fun S hS => hthree S (Finset.mem_filter.mp hS).1)
      (fun S hS => hroot S (Finset.mem_filter.mp hS).1)
      (fun S hS => (Finset.mem_filter.mp hS).2)
    exact hstep i hi
  have hpart : F.card = ∑ i ∈ Finset.range 3, (C i).card :=
    Finset.card_eq_sum_card_fiberwise (show Set.MapsTo (RootPosition c)
      (F : Set (Finset ℤ)) (Finset.range 3) from fun S hS =>
        Finset.mem_range.mpr (by have hh := (hdata S hS).2.1; rw [hthree S hS] at hh; omega))
  have h0 := hcount 0 (by simp)
  have h1 := hcount 1 (by simp)
  have h2 := hcount 2 (by simp)
  norm_num at h0 h1 h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hpart
  have hm : min (r - 1) (N - r) ≤ r - 1 := min_le_left _ _
  have hm' : min (r - 1) (N - r) ≤ N - r := min_le_right _ _
  have hb : 2*F.card+3≤N+2*r := by omega
  have hbR : 2*(F.card : ℝ)+3≤(N : ℝ)+2*(r : ℝ) := by exact_mod_cast hb
  have hrcR : (r : ℝ)=(c : ℝ) := by exact_mod_cast hrc
  linarith only [hbR,hrcR]

theorem actual_rooted_small_count {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hc : c∈Ground N) (hsub : ∀ S∈F,S⊆Ground N)
    (hAP : ∀ S∈F,IsAP S) (hcard : ∀ S∈F,S.card≤3)
    (hroot : ∀ S∈F,c∈S) : (F.card : ℝ)≤(3/2 : ℝ)*N+(c : ℝ) := by
  let C (k : ℕ) := F.filter (fun S => S.card=k)
  have h1 : (C 1).card≤1 := by
    apply Finset.card_le_one.mpr
    intro S hS T hT
    obtain ⟨hSF,hSc⟩ := Finset.mem_filter.mp hS
    obtain ⟨hTF,hTc⟩ := Finset.mem_filter.mp hT
    rw [singleton_of_root_card_le_one (hroot S hSF) (by omega),
      singleton_of_root_card_le_one (hroot T hTF) (by omega)]
  have h2 : (C 2).card≤N-1 := actual_rooted_two_count hc
    (fun S hS => hsub S (Finset.mem_filter.mp hS).1)
    (fun S hS => (Finset.mem_filter.mp hS).2)
    (fun S hS => hroot S (Finset.mem_filter.mp hS).1)
  have h3 := actual_rooted_three_count hc
    (F:=C 3) (fun S hS => hsub S (Finset.mem_filter.mp hS).1)
    (fun S hS => hAP S (Finset.mem_filter.mp hS).1)
    (fun S hS => (Finset.mem_filter.mp hS).2)
    (fun S hS => hroot S (Finset.mem_filter.mp hS).1)
  have hcover : F⊆C 1∪C 2∪C 3 := by
    intro S hS
    have hp : 0<S.card := Finset.card_pos.mpr ⟨c,hroot S hS⟩
    have hu := hcard S hS
    simp only [Finset.mem_union,C,Finset.mem_filter,hS,true_and]
    omega
  have hh := (Finset.card_le_card hcover).trans
    ((Finset.card_union_le (C 1∪C 2) (C 3)).trans
      (Nat.add_le_add_right (Finset.card_union_le (C 1) (C 2)) _))
  have hhR : (F.card : ℝ)≤(C 1).card+(C 2).card+(C 3).card := by exact_mod_cast hh
  have h1R : ((C 1).card : ℝ)≤1 := by exact_mod_cast h1
  have h2R : ((C 2).card : ℝ)≤((N-1 : ℕ) : ℝ) := by exact_mod_cast h2
  have hN : 1≤N := by have h:= (mem_ground N c).mp hc; omega
  rw [Nat.cast_sub hN] at h2R
  norm_num only [Nat.cast_one] at h2R
  linarith only [hhR,h1R,h2R,h3]

#print axioms actual_rooted_three_count
#print axioms actual_rooted_small_count
end
end JSP233.RootedShort80470
