module

public import Erdos272.Arithmetic.BatchSource208

@[expose] public section

/-! Small independently checked source blocks can be joined by proof rather
than by reducing the full rectangle again.  Stronger target rows may be
weakened without recomputing any physical source value. -/
namespace JSP233.BatchSourceBlocks208
open BatchSource208
set_option maxHeartbeats 0

def rowLE : List ℕ → List ℕ → Bool
  | [], [] => true
  | b :: bs, c :: cs => decide (b ≤ c) && rowLE bs cs
  | _, _ => false

theorem rowLE_length {lower upper : List ℕ} (hc : rowLE lower upper = true) :
    lower.length = upper.length := by
  induction lower generalizing upper with
  | nil => cases upper <;> simp_all [rowLE]
  | cons b bs ih =>
    cases upper with
    | nil => simp [rowLE] at hc
    | cons c cs =>
      have hp : decide (b ≤ c) = true ∧ rowLE bs cs = true := by
        simpa only [rowLE, Bool.and_eq_true_iff] using hc
      simpa only [List.length_cons] using congrArg (fun n => n + 1) (ih hp.2)

theorem rowLE_get {lower upper : List ℕ} (hc : rowLE lower upper = true)
    (e : ℕ) (hl : e < lower.length) (hu : e < upper.length) : lower[e] ≤ upper[e] := by
  induction lower generalizing upper e with
  | nil => simp at hl
  | cons b bs ih =>
    cases upper with
    | nil => simp at hu
    | cons c cs =>
      have hp : decide (b ≤ c) = true ∧ rowLE bs cs = true := by
        simpa only [rowLE, Bool.and_eq_true_iff] using hc
      cases e with
      | zero => exact of_decide_eq_true hp.1
      | succ e =>
        exact ih hp.2 e (by simp only [List.length_cons] at hl; omega)
          (by simp only [List.length_cons] at hu; omega)

theorem checkRowFrom_mono_targets {a : ℕ → ℕ} {s e mass : ℕ}
    {lower upper : List ℕ} (hdom : rowLE lower upper = true)
    (hc : checkRowFrom a s e mass upper = true) :
    checkRowFrom a s e mass lower = true := by
  induction lower generalizing upper e mass with
  | nil => rfl
  | cons b bs ih =>
    cases upper with
    | nil => simp [rowLE] at hdom
    | cons c cs =>
      have hd : decide (b ≤ c) = true ∧ rowLE bs cs = true := by
        simpa only [rowLE, Bool.and_eq_true_iff] using hdom
      have hp : decide (c ≤ mass) = true ∧ checkRowFrom a s (e + 1)
          (mass + a (s - (e + 1)) * FastSource208.fastMultiplicity s (s - (e + 1))) cs = true := by
        simpa only [checkRowFrom, Bool.and_eq_true_iff] using hc
      apply Bool.and_eq_true_iff.mpr
      exact ⟨decide_eq_true ((of_decide_eq_true hd.1).trans (of_decide_eq_true hp.1)),
        ih hd.2 hp.2⟩

theorem checkBlock_mono_targets {a : ℕ → ℕ} {T H : ℕ} {lower upper : List ℕ}
    (hdom : rowLE lower upper = true) (hc : checkBlock a T H upper = true) :
    checkBlock a T H lower = true := by
  apply List.all_eq_true.mpr
  intro j hj
  exact checkRowFrom_mono_targets hdom ((List.all_eq_true.mp hc) j hj)

/-- A full Boolean certificate is assembled without evaluating its large
rectangle. Each supplied piece may be a separate kernel-checked declaration. -/
theorem checkBlock_split {a : ℕ → ℕ} {T C H : ℕ} {targets : List ℕ}
    (hTC : T ≤ C) (hCH : C + 1 ≤ H)
    (hleft : checkBlock a T C targets = true)
    (hright : checkBlock a (C + 1) H targets = true) :
    checkBlock a T H targets = true := by
  apply List.all_eq_true.mpr
  intro j hj
  have hjH : j < H + 1 - T := List.mem_range.mp hj
  by_cases hsC : T + j ≤ C
  · exact (List.all_eq_true.mp hleft) j (by simp only [List.mem_range]; omega)
  · let k := T + j - (C + 1)
    have hk : k ∈ List.range (H + 1 - (C + 1)) := by
      simp only [List.mem_range]
      dsimp only [k]
      omega
    have hh := (List.all_eq_true.mp hright) k hk
    have he : C + 1 + k = T + j := by dsimp only [k]; omega
    simpa only [he] using hh

/-- One step of the maximum-active-row strategy: the next threshold's
already checked suffix pays all weaker targets of this threshold. -/
theorem checkBlock_extend_stronger {a : ℕ → ℕ} {T U H : ℕ}
    {lower upper : List ℕ} (hTU : T < U) (hUH : U ≤ H)
    (hdom : rowLE lower upper = true)
    (hleft : checkBlock a T (U - 1) lower = true)
    (hsuffix : checkBlock a U H upper = true) :
    checkBlock a T H lower = true := by
  have hright := checkBlock_mono_targets hdom hsuffix
  have hU : U - 1 + 1 = U := by omega
  have hh := checkBlock_split (by omega : T ≤ U - 1)
    (by omega : U - 1 + 1 ≤ H) hleft (by simpa only [hU] using hright)
  exact hh

def adjacentCheck : List (ℕ × List ℕ) → Bool
  | [] => true
  | [_] => true
  | r :: t :: rs => decide (r.1 ≤ t.1) && (rowLE r.2 t.2 && adjacentCheck (t :: rs))

theorem adjacentCheck_get {rows : List (ℕ × List ℕ)} (hc : adjacentCheck rows = true)
    (i : ℕ) (hi : i + 1 < rows.length) :
    rows[i].1 ≤ rows[i + 1].1 ∧ rowLE rows[i].2 rows[i + 1].2 = true := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons r rows ih =>
    cases rows with
    | nil => simp only [List.length_cons, List.length_nil] at hi; omega
    | cons t rs =>
      have hp : decide (r.1 ≤ t.1) = true ∧
          rowLE r.2 t.2 = true ∧ adjacentCheck (t :: rs) = true := by
        simpa only [adjacentCheck, Bool.and_eq_true_iff] using hc
      cases i with
      | zero => exact ⟨of_decide_eq_true hp.1, hp.2.1⟩
      | succ i =>
        have hi' : i + 1 < (t :: rs).length := by
          simp only [List.length_cons] at hi ⊢
          omega
        exact ih hp.2.2 i hi'

#print axioms rowLE_get
#print axioms checkRowFrom_mono_targets
#print axioms checkBlock_mono_targets
#print axioms checkBlock_split
#print axioms checkBlock_extend_stronger
#print axioms adjacentCheck_get
end JSP233.BatchSourceBlocks208
