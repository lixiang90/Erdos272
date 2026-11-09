module

public import Erdos272.Arithmetic.BatchSourceLinear208
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Assemble bounded row batches for the original physical-size checker. -/
namespace JSP233.BatchSource208
set_option maxHeartbeats 0
set_option Elab.async false

def rowBlockCheck (a : ℕ → ℕ) (lo count : ℕ) (targets : List ℕ) : Bool :=
  (List.range count).all (fun r => checkRowFrom a (lo + r) 0 0 targets)

theorem rowBlock_step {a : ℕ → ℕ} {lo count r : ℕ} {targets : List ℕ}
    (hc : rowBlockCheck a lo count targets = true) (hr : r < count) :
    checkRowFrom a (lo + r) 0 0 targets = true :=
  (List.all_eq_true.mp hc) r (List.mem_range.mpr hr)

theorem checkBlock_of_rowBlocks {a : ℕ → ℕ} {T H width chunks : ℕ}
    {targets : List ℕ} (hw : 0 < width) (hspan : H + 1 - T ≤ width * chunks)
    (blocks : ∀ b : Fin chunks,
      rowBlockCheck a (T + b.val * width)
        (min width (H + 1 - T - b.val * width)) targets = true) :
    checkBlock a T H targets = true := by
  apply List.all_eq_true.mpr
  intro j hj
  have hjlt : j < H + 1 - T := List.mem_range.mp hj
  have hb : j / width < chunks := by
    by_contra hn
    have hm := Nat.mul_le_mul_right width (show chunks ≤ j / width by omega)
    have hd := Nat.div_mul_le_self j width
    have hc : H + 1 - T ≤ chunks * width := by
      simpa only [Nat.mul_comm] using hspan
    omega
  let b : Fin chunks := ⟨j / width, hb⟩
  have he : j % width + b.val * width = j := by
    dsimp [b]
    simpa only [Nat.mul_comm] using Nat.mod_add_div j width
  have hr : j % width < min width (H + 1 - T - b.val * width) :=
    lt_min (Nat.mod_lt j hw) (by omega)
  have checked := rowBlock_step (blocks b) hr
  have hs : T + b.val * width + j % width = T + j := by omega
  simpa only [hs] using checked

#print axioms rowBlock_step
#print axioms checkBlock_of_rowBlocks
end JSP233.BatchSource208
