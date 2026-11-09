module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Erdos272.Foundation.ProofTactics

@[expose] public section

/-! # Exact finite physical source tables

This module defines the integer source used by the round 207 unit calculation.
`physicalK s e` is an actual finite sum with Euler's totient, rather than a
digest or an externally supplied table.  Its suffix minimum is restricted to
the explicit finite physical window.  The reflection interface below accepts
only a Lean proof of a finite Boolean calculation.

No assertion about a family of sets or about the round 207 numerical costs is
made here: those still need their separate combinatorial bridges.
-/
namespace JSP233.PureSource208
open scoped BigOperators

/-- The number of translates, summed over all positive physical steps.
Natural subtraction is the positive part `(s - d*q)_+`. -/
def intervalMultiplicity (s q : ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 s, (s - d * q)

/-- The exact intrinsic-triple source expression used in the unit tables. -/
def physicalK (s e : ℕ) : ℕ :=
  ∑ q ∈ Finset.Ico (s - e) s, Nat.totient q * intervalMultiplicity s q

@[simp] theorem physicalK_zero (s : ℕ) : physicalK s 0 = 0 := by
  simp [physicalK]

/-- The incremental identity used to build the defect rows of the table. -/
theorem physicalK_succ {s e : ℕ} (he : e < s) :
    physicalK s (e + 1) = physicalK s e +
      Nat.totient (s - (e + 1)) * intervalMultiplicity s (s - (e + 1)) := by
  have hI : Finset.Ico (s - (e + 1)) s =
      insert (s - (e + 1)) (Finset.Ico (s - e) s) := by
    ext q
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  have hn : s - (e + 1) ∉ Finset.Ico (s - e) s := by
    simp only [Finset.mem_Ico]
    omega
  rw [physicalK, hI, Finset.sum_insert hn]
  simp only [physicalK, Nat.add_comm]

theorem physicalK_mono_defect (s : ℕ) : Monotone (physicalK s) := by
  intro e f hef
  apply Finset.sum_le_sum_of_subset
  intro q hq
  simp only [Finset.mem_Ico] at hq ⊢
  omega

theorem intervalMultiplicity_mono_size (q : ℕ) :
    Monotone (fun s => intervalMultiplicity s q) := by
  intro s t hst
  calc
    intervalMultiplicity s q ≤ ∑ d ∈ Finset.Icc 1 s, (t - d * q) := by
      exact Finset.sum_le_sum (fun d _ => Nat.sub_le_sub_right hst _)
    _ ≤ intervalMultiplicity t q := by
      apply Finset.sum_le_sum_of_subset
      intro d hd
      simp only [Finset.mem_Icc] at hd ⊢
      omega

/-- Minimum over every physical integer in the given nonempty window. -/
def finiteMinimum (T H e : ℕ) (hTH : T ≤ H) : ℕ :=
  (Finset.Icc T H).inf' (Finset.nonempty_Icc.mpr hTH) (fun s => physicalK s e)

theorem finiteMinimum_le {T H e s : ℕ} (hTH : T ≤ H)
    (hTs : T ≤ s) (hsH : s ≤ H) :
    finiteMinimum T H e hTH ≤ physicalK s e := by
  exact Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hTs, hsH⟩)

theorem le_finiteMinimum_iff {T H e b : ℕ} (hTH : T ≤ H) :
    b ≤ finiteMinimum T H e hTH ↔
      ∀ s, T ≤ s → s ≤ H → b ≤ physicalK s e := by
  simp only [finiteMinimum, Finset.le_inf'_iff, Finset.mem_Icc]
  constructor
  · intro hb s hTs hsH
    exact hb s ⟨hTs, hsH⟩
  · intro hb s hs
    exact hb s hs.1 hs.2

theorem finiteMinimum_mono_defect {T H : ℕ} (hTH : T ≤ H) :
    Monotone (fun e => finiteMinimum T H e hTH) := by
  intro e f hef
  apply (le_finiteMinimum_iff hTH).mpr
  intro s hTs hsH
  exact (finiteMinimum_le hTH hTs hsH).trans (physicalK_mono_defect s hef)

theorem finiteMinimum_mono_lower {T U H e : ℕ}
    (hTU : T ≤ U) (hUH : U ≤ H) :
    finiteMinimum T H e (hTU.trans hUH) ≤ finiteMinimum U H e hUH := by
  apply (le_finiteMinimum_iff hUH).mpr
  intro s hUs hsH
  exact finiteMinimum_le (hTU.trans hUH) (hTU.trans hUs) hsH

theorem finiteMinimum_antitone_upper {T H J e : ℕ}
    (hTH : T ≤ H) (hHJ : H ≤ J) :
    finiteMinimum T J e (hTH.trans hHJ) ≤ finiteMinimum T H e hTH := by
  apply (le_finiteMinimum_iff hTH).mpr
  intro s hTs hsH
  exact finiteMinimum_le (hTH.trans hHJ) hTs (hsH.trans hHJ)

@[simp] theorem finiteMinimum_zero {T H : ℕ} (hTH : T ≤ H) :
    finiteMinimum T H 0 hTH = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using (finiteMinimum_le (e := 0) hTH le_rfl hTH)

/-- A direct, finite, executable lower-bound check.  The supplied result must
be proved in Lean; the checker never accepts a Python hash or process exit code. -/
def checkFloor (T H e b : ℕ) : Bool :=
  ((List.range (H + 1 - T)).all fun j => decide (b ≤ physicalK (T + j) e))

theorem checkFloor_sound {T H e b : ℕ} (hTH : T ≤ H)
    (hc : checkFloor T H e b = true) : b ≤ finiteMinimum T H e hTH := by
  apply (le_finiteMinimum_iff hTH).mpr
  intro s hTs hsH
  have hj : s - T ∈ List.range (H + 1 - T) := by
    simp only [List.mem_range]
    omega
  have hh := (List.all_eq_true.mp hc) (s - T) hj
  have heq : T + (s - T) = s := by omega
  simpa only [heq, decide_eq_true_eq] using hh

/-- Completeness is useful when generating smaller kernel-checkable chunks. -/
theorem checkFloor_complete {T H e b : ℕ} (hTH : T ≤ H)
    (hb : b ≤ finiteMinimum T H e hTH) : checkFloor T H e b = true := by
  apply List.all_eq_true.mpr
  intro j hj
  have hjH : j < H + 1 - T := List.mem_range.mp hj
  apply decide_eq_true
  exact ((le_finiteMinimum_iff hTH).mp hb) (T + j) (by omega) (by omega)

/-- A checked threshold pays the target for every actual physical size in the
window, including defects larger than the selected threshold. -/
theorem threshold_sound {T H e f b s : ℕ} (hTH : T ≤ H)
    (hc : checkFloor T H e b = true) (hef : e ≤ f)
    (hTs : T ≤ s) (hsH : s ≤ H) : b ≤ physicalK s f := by
  exact ((le_finiteMinimum_iff hTH).mp (checkFloor_sound hTH hc) s hTs hsH).trans
    (physicalK_mono_defect s hef)

/-- Adjacent checked chunks cover the same whole physical interval. -/
theorem lower_bound_of_split {T C H e b : ℕ}
    (hTC : T ≤ C) (hCH : C + 1 ≤ H)
    (hleft : b ≤ finiteMinimum T C e hTC)
    (hright : b ≤ finiteMinimum (C + 1) H e hCH) :
    b ≤ finiteMinimum T H e (by omega) := by
  apply (le_finiteMinimum_iff (by omega)).mpr
  intro s hTs hsH
  by_cases hsC : s ≤ C
  · exact (le_finiteMinimum_iff hTC).mp hleft s hTs hsC
  · exact (le_finiteMinimum_iff hCH).mp hright s (by omega) hsH

#print axioms checkFloor_sound
#print axioms finiteMinimum_mono_defect
#print axioms lower_bound_of_split
end JSP233.PureSource208
