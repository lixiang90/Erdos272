import Erdos272.Counting.CrossBand57
import Erdos272.Core.SmallKernel112

/-! Two opposite first-hit covers pay the whole family, including Large. -/
namespace JSP233.SharpSmall212
open StarCompletion SparseSmall39 SparseCross41 SmallKernel112
open SmallSpan48 SmallJoint46
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem actual_small_omitter_whole_count {N L : ℕ} {F : Finset (Finset ℤ)}
    {A B T : Finset ℤ} {c : ℤ} (hlegal : Legal (Ground N) F)
    (hbad : ∀ S ∈ F, ¬ IsAP S) (hA : A ∈ SpanMembers F L) (hB : B ∈ SpanMembers F L)
    (hAB : A ∩ B = {c}) (hT : T ∈ SpanMembers F L) (hTc : c ∉ T) :
    F.card ≤ ((L-1)^2+L)*N := by
  obtain ⟨hAF, hAL⟩ := Finset.mem_filter.mp hA
  obtain ⟨hBF, hBL⟩ := Finset.mem_filter.mp hB
  obtain ⟨hTF, hTL⟩ := Finset.mem_filter.mp hT
  have hcAB : c ∈ A ∩ B := by rw [hAB]; simp
  obtain ⟨hcA, hcB⟩ := Finset.mem_inter.mp hcAB
  have hdegree := (actual_degree_from_omitter hlegal hbad hTF hTc).trans
    ((degreeBudget_mono N hTL).trans (degreeBudget_le_linear N L))
  have hLA : Legal (Ground N) (Avoiders F c) :=
    ⟨fun S hS => hlegal.1 S (Finset.mem_filter.mp hS).1,
     fun S hS U hU hne => hlegal.2 S (Finset.mem_filter.mp hS).1 U (Finset.mem_filter.mp hU).1 hne⟩
  have hc := actual_cross_pool_bound (A.erase c) (B.erase c) hLA
    (fun S hS => hbad S (Finset.mem_filter.mp hS).1)
    (singleton_erases_disjoint hAB) (actual_singleton_cross_hits hlegal hAF hBF hAB)
  have ha := erase_span_card hcA hAL
  have hb := erase_span_card hcB hBL
  have hm := Nat.mul_le_mul_right N (Nat.mul_le_mul ha hb)
  have hp := root_avoider_card_partition F c
  nlinarith only [hdegree, hc, hm, hp]

def Order (upper : Bool) (x y : ℤ) : Prop := if upper then y ≤ x else x ≤ y

def Keys (A T : Finset ℤ) (x : ℤ) (upper : Bool) : Finset ℤ :=
  T.filter (fun y => y ∉ A ∨ Order upper x y)

def Bucket (F : Finset (Finset ℤ)) (A : Finset ℤ) (x : ℤ) (upper : Bool) :
    Finset (Finset ℤ) :=
  F.filter (fun S => x ∈ S ∧ ∀ y ∈ S, y ∈ A → Order upper x y)

theorem keys_identity {A T : Finset ℤ} {x : ℤ} (hx : x ∉ T) :
    (Keys A T x false).card + (Keys A T x true).card + (T ∩ A).card = 2*T.card := by
  have hu : Keys A T x false ∪ Keys A T x true = T := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_union.mp hy with hy | hy <;> exact (Finset.mem_filter.mp hy).1
    · intro hy
      by_cases hya : y ∈ A
      · rcases le_total x y with hxy | hyx
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hy, Or.inr hxy⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hy, Or.inr hyx⟩))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hy, Or.inl hya⟩))
  have hi : Keys A T x false ∩ Keys A T x true = T \ A := by
    ext y
    constructor
    · intro hy
      obtain ⟨hlo, hhi⟩ := Finset.mem_inter.mp hy
      obtain ⟨hyT, hlo⟩ := Finset.mem_filter.mp hlo
      obtain ⟨_, hhi⟩ := Finset.mem_filter.mp hhi
      refine Finset.mem_sdiff.mpr ⟨hyT, ?_⟩
      intro hyA
      have hxy : x ≤ y := by simpa only [Order, Bool.false_eq_true, ↓reduceIte, hyA, not_true_eq_false, false_or] using hlo
      have hyx : y ≤ x := by simpa only [Order, ↓reduceIte, hyA, not_true_eq_false, false_or] using hhi
      have he := le_antisymm hxy hyx
      exact hx (he.symm ▸ hyT)
    · intro hy
      obtain ⟨hyT, hyA⟩ := Finset.mem_sdiff.mp hy
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨hyT, Or.inl hyA⟩, Finset.mem_filter.mpr ⟨hyT, Or.inl hyA⟩⟩
  have hh := Finset.card_union_add_card_inter (Keys A T x false) (Keys A T x true)
  rw [hu, hi] at hh
  have ht := Finset.card_sdiff_add_card_inter T A
  omega

theorem actual_first_hit_count {N : ℕ} {F : Finset (Finset ℤ)} {A : Finset ℤ}
    (hlegal : Legal (Ground N) F) (hbad : ∀ S ∈ F, ¬ IsAP S)
    (hA : A ∈ F) (hAN : A.Nonempty) (T : ℤ → Finset ℤ)
    (hT : ∀ x ∈ A, T x ∈ F) (hxT : ∀ x ∈ A, x ∉ T x) (upper : Bool) :
    F.card ≤ (∑ x ∈ A, (Keys A (T x) x upper).card)*N := by
  have hcover : F ⊆ A.biUnion (fun x => Bucket F A x upper) := by
    intro S hS
    have hSA : (S ∩ A).Nonempty := by
      by_cases he : S = A
      · simpa only [he, Finset.inter_self] using hAN
      · exact isAP_nonempty (hlegal.2 S hS A hA he)
    have hex : ∃ x ∈ S ∩ A, ∀ y ∈ S ∩ A, Order upper x y := by
      cases upper
      · simpa only [Order, Bool.false_eq_true, ↓reduceIte] using
          (Finset.exists_min_image (S ∩ A) (fun z : ℤ => z) hSA)
      · simpa only [Order, ↓reduceIte] using
          (Finset.exists_max_image (S ∩ A) (fun z : ℤ => z) hSA)
    obtain ⟨x, hx, hmin⟩ := hex
    obtain ⟨hxS, hxA⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_biUnion.mpr ⟨x, hxA, Finset.mem_filter.mpr
      ⟨hS, hxS, fun y hyS hyA => hmin y (Finset.mem_inter.mpr ⟨hyS, hyA⟩)⟩⟩
  have hb : ∀ x ∈ A, (Bucket F A x upper).card ≤ (Keys A (T x) x upper).card*N := by
    intro x hxA
    have hBF : Bucket F A x upper ⊆ F := Finset.filter_subset _ _
    have hBL : Legal (Ground N) (Bucket F A x upper) :=
      ⟨fun S hS => hlegal.1 S (hBF hS),
       fun S hS U hU hSU => hlegal.2 S (hBF hS) U (hBF hU) hSU⟩
    have hBB : ∀ S ∈ Bucket F A x upper, ¬ IsAP S := fun S hS => hbad S (hBF hS)
    have hdis : Disjoint ({x} : Finset ℤ) (Keys A (T x) x upper) := by
      apply Finset.disjoint_left.mpr
      intro y hyx hyK
      have he : y = x := Finset.mem_singleton.mp hyx
      subst y
      exact hxT x hxA (Finset.mem_filter.mp hyK).1
    have hhit : ∀ S ∈ Bucket F A x upper, ∃ z ∈ ({x} : Finset ℤ),
        ∃ y ∈ Keys A (T x) x upper, z ∈ S ∧ y ∈ S := by
      intro S hS
      obtain ⟨hSF, hxS, hmin⟩ := Finset.mem_filter.mp hS
      have hne : S ≠ T x := by intro he; exact hxT x hxA (he ▸ hxS)
      obtain ⟨y, hy⟩ := isAP_nonempty (hlegal.2 S hSF (T x) (hT x hxA) hne)
      obtain ⟨hyS, hyT⟩ := Finset.mem_inter.mp hy
      refine ⟨x, by simp, y, Finset.mem_filter.mpr ⟨hyT, ?_⟩, hxS, hyS⟩
      by_cases hyA : y ∈ A
      · exact Or.inr (hmin y hyS hyA)
      · exact Or.inl hyA
    have hh := actual_cross_pool_bound ({x} : Finset ℤ) (Keys A (T x) x upper)
      hBL hBB hdis hhit
    simpa only [Finset.card_singleton, one_mul] using hh
  calc
    F.card ≤ (A.biUnion (fun x => Bucket F A x upper)).card := Finset.card_le_card hcover
    _ ≤ ∑ x ∈ A, (Bucket F A x upper).card := Finset.card_biUnion_le
    _ ≤ ∑ x ∈ A, (Keys A (T x) x upper).card*N := Finset.sum_le_sum hb
    _ = (∑ x ∈ A, (Keys A (T x) x upper).card)*N := (Finset.sum_mul _ _ _).symm

theorem actual_two_first_hit_bound {N L : ℕ} {F : Finset (Finset ℤ)} {A : Finset ℤ}
    (hL : 2 ≤ L) (hlegal : Legal (Ground N) F) (hbad : ∀ S ∈ F, ¬ IsAP S)
    (hA : A ∈ F) (hAN : A.Nonempty) (T : ℤ → Finset ℤ)
    (hT : ∀ x ∈ A, T x ∈ F) (hxT : ∀ x ∈ A, x ∉ T x)
    (hsize : ∀ x ∈ A, (T x).card ≤ L) (htwo : ∀ x ∈ A, 2 ≤ (T x ∩ A).card) :
    F.card ≤ A.card*(L-1)*N := by
  have hlo := actual_first_hit_count hlegal hbad hA hAN T hT hxT false
  have hhi := actual_first_hit_count hlegal hbad hA hAN T hT hxT true
  have hp : ∀ x ∈ A, (Keys A (T x) x false).card + (Keys A (T x) x true).card ≤ 2*(L-1) := by
    intro x hx
    have hid := keys_identity (A := A) (hxT x hx)
    have hs := hsize x hx
    have ht := htwo x hx
    omega
  have hs : (∑ x ∈ A, (Keys A (T x) x false).card) +
      (∑ x ∈ A, (Keys A (T x) x true).card) ≤ 2*A.card*(L-1) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ ≤ ∑ _x ∈ A, 2*(L-1) := Finset.sum_le_sum hp
      _ = _ := by simp; ring
  have hm := Nat.mul_le_mul_right N hs
  have hboth := Nat.add_le_add hlo hhi
  have hh : 2*F.card ≤ 2*(A.card*(L-1)*N) := by nlinarith only [hm, hboth]
  omega

theorem actual_no_small_singleton_whole {N L : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1 ≤ N) (hL : 2 ≤ L) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S ∈ F, ¬ IsAP S) (hsmall : (Small F L).Nonempty)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F L) = ∅)
    (hno : ¬ ∃ A ∈ Small F L, ∃ B ∈ Small F L, ∃ c : ℤ, A ∩ B = {c}) :
    F.card ≤ L*(L-1)*N := by
  by_cases hone : F.card ≤ 1
  · have hLp : 0 < L := by omega
    have hLm : 0 < L-1 := by omega
    have hNp : 0 < N := by omega
    have hp : 0 < L*(L-1)*N := by positivity
    omega
  have htwo : 2 ≤ F.card := by omega
  obtain ⟨A, hAS⟩ := hsmall
  obtain ⟨hAF, hAL⟩ := Finset.mem_filter.mp hAS
  have hAN := actual_member_nonempty_of_two hlegal htwo hAF
  have hex : ∀ x : ℤ, ∃ T : Finset ℤ, x ∈ A → T ∈ F ∧ x ∉ T ∧ T.card ≤ L ∧ 2 ≤ (T ∩ A).card := by
    intro x
    by_cases hx : x ∈ A
    · obtain ⟨T, hTS, hxT⟩ := actual_omitter_of_empty_kernel hkernel x (hlegal.1 A hAF hx)
      obtain ⟨hTF, hTL⟩ := Finset.mem_filter.mp hTS
      have hne : T ≠ A := by intro he; exact hxT (he.symm ▸ hx)
      have hi : (T ∩ A).Nonempty := isAP_nonempty (hlegal.2 T hTF A hAF hne)
      have hcard : 2 ≤ (T ∩ A).card := by
        by_contra hn
        have he : (T ∩ A).card = 1 := by have hp := Finset.card_pos.mpr hi; omega
        obtain ⟨c, hc⟩ := Finset.card_eq_one.mp he
        exact hno ⟨T, hTS, A, hAS, c, hc⟩
      exact ⟨T, fun _ => ⟨hTF, hxT, hTL, hcard⟩⟩
    · exact ⟨∅, fun h => False.elim (hx h)⟩
  choose T hT using hex
  have hb := actual_two_first_hit_bound hL hlegal hbad hAF hAN T
    (fun x hx => (hT x hx).1) (fun x hx => (hT x hx).2.1)
    (fun x hx => (hT x hx).2.2.1) (fun x hx => (hT x hx).2.2.2)
  exact hb.trans (Nat.mul_le_mul_right N (Nat.mul_le_mul_right (L-1) hAL))

theorem actual_small_empty_kernel_whole {N L : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1 ≤ N) (hL : 2 ≤ L) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S ∈ F, ¬ IsAP S) (hsmall : (Small F L).Nonempty)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F L) = ∅) :
    F.card ≤ ((L-1)^2+L)*N := by
  by_cases hsing : ∃ A ∈ Small F L, ∃ B ∈ Small F L, ∃ c : ℤ, A ∩ B = {c}
  · obtain ⟨A, hAS, B, hBS, c, hAB⟩ := hsing
    have hcA : c ∈ A := (Finset.mem_inter.mp (show c ∈ A ∩ B by rw [hAB]; simp)).1
    obtain ⟨T, hTS, hcT⟩ := actual_omitter_of_empty_kernel hkernel c
      (hlegal.1 A (Finset.mem_filter.mp hAS).1 hcA)
    exact actual_small_omitter_whole_count hlegal hbad hAS hBS hAB hTS hcT
  · have hb := actual_no_small_singleton_whole hN hL hlegal hbad hsmall hkernel hsing
    have hLe : L*(L-1) ≤ (L-1)^2+L := by
      have hh : L-1+1 = L := by omega
      have hm := congrArg (fun t : ℕ => t*(L-1)) hh
      nlinarith only [hh, hm]
    exact hb.trans (Nat.mul_le_mul_right N hLe)

theorem actual_small_empty_kernel241 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1 ≤ N) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S ∈ F, ¬ IsAP S) (hsmall : (Small F 241).Nonempty)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F 241) = ∅) :
    F.card ≤ 57841*N := by
  simpa using actual_small_empty_kernel_whole hN (by decide : 2 ≤ 241) hlegal hbad hsmall hkernel

#print axioms keys_identity
#print axioms actual_first_hit_count
#print axioms actual_two_first_hit_bound
#print axioms actual_no_small_singleton_whole
#print axioms actual_small_empty_kernel_whole
#print axioms actual_small_empty_kernel241
end
end JSP233.SharpSmall212
