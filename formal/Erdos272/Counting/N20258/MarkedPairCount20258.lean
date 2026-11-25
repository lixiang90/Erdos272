module

public import Erdos272.Geometry.N20258.CoreWitnessSweep20258

@[expose] public section
namespace JSP233.MarkedPairCount20258
open scoped Classical BigOperators
set_option autoImplicit false

/-- Count members whose designated part meets a test set. -/
theorem hits {α β : Type*} [DecidableEq α] [DecidableEq β]
    (C : Finset α) (U : Finset β) (part : α → Finset β) {v : ℕ}
    (cap : ∀ x∈U,(C.filter (fun S => x∈part S)).card≤v) :
    (C.filter (fun S => (U∩part S).Nonempty)).card≤U.card*v := by
  classical
  have sub : C.filter (fun S => (U∩part S).Nonempty) ⊆
      U.biUnion (fun x => C.filter (fun S => x∈part S)) := by
    intro S hs
    obtain ⟨mem,x,hx⟩ := Finset.mem_filter.mp hs
    obtain ⟨xu,xp⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_biUnion.mpr ⟨x,xu,Finset.mem_filter.mpr ⟨mem,xp⟩⟩
  have total := Finset.sum_le_sum cap
  exact (Finset.card_le_card sub).trans (Finset.card_biUnion_le.trans (by simpa using total))

/-- Every pair is accounted for in its row or its column. -/
theorem rectangle {α β : Type*} (A : Finset α) (B : Finset β)
    (f : α → β → Prop) (g : β → α → Prop) [DecidableRel f] [DecidableRel g]
    {l r : ℕ} (cover : ∀ a∈A,∀ b∈B,f a b ∨ g b a)
    (row : ∀ a∈A,(B.filter (f a)).card≤l) (col : ∀ b∈B,(A.filter (g b)).card≤r) :
    A.card*B.card≤A.card*l+B.card*r := by
  have count : ∑ a∈A,∑ b∈B, 1 ≤
      ∑ a∈A,∑ b∈B, ((if f a b then 1 else 0)+(if g b a then 1 else 0):ℕ) := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    rcases cover a ha b hb with yes|yes <;> simp [yes]
  simp only [Finset.sum_add_distrib] at count
  rw [Finset.sum_comm (s:=A) (t:=B) (f:=fun a b => if g b a then (1:ℕ) else 0)] at count
  simpa using count.trans (by simpa using Nat.add_le_add (Finset.sum_le_sum row) (Finset.sum_le_sum col) :
    _ ≤ A.card*l+B.card*r)

end JSP233.MarkedPairCount20258
