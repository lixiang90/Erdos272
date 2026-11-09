module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.IntervalCases
public import Lean.Elab.Tactic.Omega
public import Aesop

@[expose] public section

/-!
Actual finite integer-set root completion, independent of the unformalized
Yang star bound.  `StarBound` is an explicit parameter, not an axiom.
-/

namespace JSP233.StarCompletion

def IsAP (S : Finset Int) : Prop :=
  ∃ d p : Int, 0 < d ∧ ∃ lo hi : Int,
    (∀ x, x ∈ S ↔ lo ≤ x ∧ x ≤ hi ∧ d ∣ x - p) ∧ p ∈ S

def Legal (Ω : Finset Int) (F : Finset (Finset Int)) : Prop :=
  (∀ S ∈ F, S ⊆ Ω) ∧
  (∀ S ∈ F, ∀ T ∈ F, S ≠ T → IsAP (S ∩ T))

def Rooted (F : Finset (Finset Int)) (c : Int) : Prop :=
  ∀ S ∈ F, c ∈ S

def RootPart (F : Finset (Finset Int)) (c : Int) : Finset (Finset Int) :=
  F.filter (fun S => c ∈ S)

def Avoiders (F : Finset (Finset Int)) (c : Int) : Finset (Finset Int) :=
  F.filter (fun S => c ∉ S)

def CommonKernel (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) : Finset Int :=
  Ω.filter (fun x => ∀ S ∈ Avoiders F c, x ∈ S)

def StarBound (Ω : Finset Int) (B : Nat) : Prop :=
  ∀ H : Finset (Finset Int), Legal Ω H →
    (∃ c ∈ Ω, Rooted H c) → H.card ≤ B

theorem isAP_nonempty {S : Finset Int} (h : IsAP S) : S.Nonempty := by
  obtain ⟨d, p, hd, lo, hi, hrep, hp⟩ := h
  exact ⟨p, hp⟩

theorem singleton_isAP (a : Int) : IsAP {a} := by
  refine ⟨1, a, by omega, a, a, ?_, by simp⟩
  intro x
  simp only [Finset.mem_singleton]
  constructor
  · intro h; subst x; simp
  · intro h; omega

theorem pair_isAP (a b : Int) : IsAP {a,b} := by
  by_cases he : a = b
  · subst b; simpa using singleton_isAP a
  wlog hab : a < b
  · have hba : b < a := by omega
    simpa [Finset.pair_comm] using this b a (Ne.symm he) hba
  refine ⟨b-a, a, by omega, a, b, ?_, by simp⟩
  intro x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases h with rfl | rfl
    · exact ⟨by omega, by omega, by simp⟩
    · exact ⟨by omega, by omega, dvd_refl _⟩
  · intro h
    by_cases hxb : x = b
    · exact Or.inr hxb
    · have hz : x-a = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt
        (by omega) (by omega) h.2.2
      exact Or.inl (by omega)

theorem nonempty_card_le_two_isAP {S : Finset Int}
    (hne : S.Nonempty) (hc : S.card ≤ 2) : IsAP S := by
  have hpos : 0 < S.card := Finset.card_pos.mpr hne
  have hor : S.card = 1 ∨ S.card = 2 := by omega
  rcases hor with h | h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact singleton_isAP a
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    exact pair_isAP a b

def PairStar (Ω : Finset Int) (c : Int) : Finset (Finset Int) :=
  Ω.image (fun x => ({c,x} : Finset Int))

def Completed (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) :
    Finset (Finset Int) := RootPart F c ∪ PairStar Ω c

theorem root_pair_injective (c : Int) :
    Function.Injective (fun x : Int => ({c,x} : Finset Int)) := by
  intro x y he
  change ({c,x} : Finset Int) = {c,y} at he
  have hx : x ∈ ({c,y} : Finset Int) := by rw [← he]; simp
  have hy : y ∈ ({c,x} : Finset Int) := by rw [he]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  aesop

theorem pairStar_card (Ω : Finset Int) (c : Int) :
    (PairStar Ω c).card = Ω.card := by
  exact Finset.card_image_of_injective Ω (root_pair_injective c)

theorem completed_rooted (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) :
    Rooted (Completed Ω F c) c := by
  intro S hS
  rcases Finset.mem_union.mp hS with h | h
  · exact (Finset.mem_filter.mp h).2
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
    simp

theorem completed_legal (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int)
    (hc : c ∈ Ω) (hF : Legal Ω F) : Legal Ω (Completed Ω F c) := by
  constructor
  · intro S hS x hx
    rcases Finset.mem_union.mp hS with h | h
    · exact hF.1 S (Finset.mem_filter.mp h).1 hx
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hc
      · exact hy
  · intro S hS T hT hne
    have hSc := completed_rooted Ω F c S hS
    have hTc := completed_rooted Ω F c T hT
    have hn : (S ∩ T).Nonempty := ⟨c, Finset.mem_inter.mpr ⟨hSc,hTc⟩⟩
    rcases Finset.mem_union.mp hS with hS | hS
    · rcases Finset.mem_union.mp hT with hT | hT
      · exact hF.2 S (Finset.mem_filter.mp hS).1 T (Finset.mem_filter.mp hT).1 hne
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hT
        exact nonempty_card_le_two_isAP hn
          ((Finset.card_le_card Finset.inter_subset_right).trans Finset.card_le_two)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hS
      exact nonempty_card_le_two_isAP hn
        ((Finset.card_le_card Finset.inter_subset_left).trans Finset.card_le_two)

theorem actual_root_pair_partner_in_kernel
    (Ω : Finset Int) (F : Finset (Finset Int)) (c x : Int)
    (hF : Legal Ω F) (hx : x ∈ Ω) (hpair : ({c,x} : Finset Int) ∈ F) :
    x ∈ CommonKernel Ω F c := by
  apply Finset.mem_filter.mpr
  refine ⟨hx, ?_⟩
  intro T hT
  have hTF : T ∈ F := (Finset.mem_filter.mp hT).1
  have hcT : c ∉ T := (Finset.mem_filter.mp hT).2
  have hne : ({c,x} : Finset Int) ≠ T := by
    intro he
    apply hcT
    rw [← he]
    simp
  obtain ⟨y, hy⟩ := isAP_nonempty (hF.2 _ hpair _ hTF hne)
  have hym := Finset.mem_inter.mp hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hym
  rcases hym.1 with rfl | rfl
  · exact False.elim (hcT hym.2)
  · exact hym.2

theorem actual_small_members_card_le_kernel
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int)
    (hF : Legal Ω F) :
    (RootPart F c ∩ PairStar Ω c).card ≤ (CommonKernel Ω F c).card := by
  have hs : RootPart F c ∩ PairStar Ω c ⊆ PairStar (CommonKernel Ω F c) c := by
    intro S hS
    have hh := Finset.mem_inter.mp hS
    have hSF := (Finset.mem_filter.mp hh.1).1
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hh.2
    apply Finset.mem_image.mpr
    exact ⟨x, actual_root_pair_partner_in_kernel Ω F c x hF hx hSF, rfl⟩
  exact (Finset.card_le_card hs).trans_eq (pairStar_card _ _)

theorem root_avoider_card_partition (F : Finset (Finset Int)) (c : Int) :
    (RootPart F c).card + (Avoiders F c).card = F.card := by
  exact Finset.card_filter_add_card_filter_not (s := F) (fun S => c ∈ S)

theorem kernel_subset_ambient (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) :
    CommonKernel Ω F c ⊆ Ω := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

theorem root_not_in_kernel (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int)
    (hne : (Avoiders F c).Nonempty) : c ∉ CommonKernel Ω F c := by
  intro hc
  obtain ⟨S, hS⟩ := hne
  have hall := (Finset.mem_filter.mp hc).2
  exact (Finset.mem_filter.mp hS).2 (hall S hS)

theorem nonempty_avoiders_kernel_capacity
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int)
    (hc : c ∈ Ω) (hne : (Avoiders F c).Nonempty) :
    (CommonKernel Ω F c).card + 1 ≤ Ω.card := by
  have hs : CommonKernel Ω F c ⊆ Ω.erase c := by
    intro x hx
    apply Finset.mem_erase.mpr
    refine ⟨?_, kernel_subset_ambient Ω F c hx⟩
    intro he
    subst x
    exact root_not_in_kernel Ω F c hne hx
  have hcard := Finset.card_le_card hs
  have hcpos : 1 ≤ Ω.card := Finset.card_pos.mpr ⟨c,hc⟩
  rw [Finset.card_erase_of_mem hc] at hcard
  omega

/-- Genuine completion budget. `StarBound` is the explicit unproved external
input; the addition of missing actual small members and their kernel payment
are proved here from finite-set legality. No AP or cardinality oracle occurs
in these geometric hypotheses. The formula remains valid when D is empty,
in which case the ambient-filter definition makes its kernel equal to Ω. -/
theorem completion_payment
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (B : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B) :
    F.card + Ω.card ≤ B + (Avoiders F c).card + (CommonKernel Ω F c).card := by
  have hcap : (Completed Ω F c).card ≤ B :=
    hstar _ (completed_legal Ω F c hc hF) ⟨c, hc, completed_rooted Ω F c⟩
  have hbudget := Finset.card_union_add_card_inter (RootPart F c) (PairStar Ω c)
  have hkernel := actual_small_members_card_le_kernel Ω F c hF
  have hpartition := root_avoider_card_partition F c
  change (RootPart F c ∪ PairStar Ω c).card ≤ B at hcap
  rw [pairStar_card Ω c] at hbudget
  omega

theorem completion_payment_of_kernel_capacity
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (B : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hcapacity : (Avoiders F c).card + (CommonKernel Ω F c).card ≤ Ω.card) :
    F.card ≤ B := by
  have hpayment := completion_payment Ω F c B hc hF hstar
  omega

theorem at_most_one_avoider_payment
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (B : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hcount : (Avoiders F c).card ≤ 1) : F.card ≤ B := by
  apply completion_payment_of_kernel_capacity Ω F c B hc hF hstar
  by_cases hne : (Avoiders F c).Nonempty
  · have hk := nonempty_avoiders_kernel_capacity Ω F c hc hne
    omega
  · have hz : (Avoiders F c).card = 0 := by
      exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
    have hk := Finset.card_le_card (kernel_subset_ambient Ω F c)
    omega

theorem counterexample_forces_kernel_deficit
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (B : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hover : B < F.card) :
    Ω.card + 1 ≤ (Avoiders F c).card + (CommonKernel Ω F c).card := by
  have hpayment := completion_payment Ω F c B hc hF hstar
  omega

#print axioms singleton_isAP
#print axioms pair_isAP
#print axioms nonempty_card_le_two_isAP
#print axioms pairStar_card
#print axioms completed_legal
#print axioms actual_root_pair_partner_in_kernel
#print axioms actual_small_members_card_le_kernel
#print axioms completion_payment
#print axioms completion_payment_of_kernel_capacity
#print axioms nonempty_avoiders_kernel_capacity
#print axioms at_most_one_avoider_payment
#print axioms counterexample_forces_kernel_deficit

end JSP233.StarCompletion
