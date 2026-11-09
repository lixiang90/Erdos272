module

public import Erdos272.Arithmetic.PureSource208
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! A periodic totient minorant pays the actual d=1 source.  Every residue
gate is a natural-number inequality, and no finite lookup is assumed here. -/
namespace JSP233.ResidueSource208
open PureSource208
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

def Weight (C : ℕ → ℕ) (r i : ℕ) : ℕ :=
  C ((r + 30 - i % 30) % 30)

def A (C : ℕ → ℕ) (e r : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 e, Weight C r i * i

def B (C : ℕ → ℕ) (e r : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 e, Weight C r i * i^2

theorem sub_mod_thirty {s i : ℕ} (hi : i ≤ s) :
    (s - i) % 30 = (s % 30 + 30 - i % 30) % 30 := by
  omega

theorem reverse_weighted_sum (s e : ℕ) (he : e ≤ s) (f : ℕ → ℕ) :
    (∑ i ∈ Finset.Icc 1 e, f (s - i) * i) =
      ∑ q ∈ Finset.Ico (s - e) s, f q * (s - q) := by
  apply Finset.sum_bij (fun i _hi => s - i)
  · intro i hi
    obtain ⟨hi1, hie⟩ := Finset.mem_Icc.mp hi
    exact Finset.mem_Ico.mpr (by omega)
  · intro i hi j hj heq
    have hie := (Finset.mem_Icc.mp hi).2
    have hje := (Finset.mem_Icc.mp hj).2
    omega
  · intro q hq
    obtain ⟨hql, hqs⟩ := Finset.mem_Ico.mp hq
    refine ⟨s - q, Finset.mem_Icc.mpr (by omega), ?_⟩
    omega
  · intro i hi
    have hie := (Finset.mem_Icc.mp hi).2
    have heq : s - (s - i) = i := by omega
    rw [heq]

theorem actual_d1_source_lower {s e : ℕ} (he : e ≤ s) :
    (∑ i ∈ Finset.Icc 1 e, Nat.totient (s - i) * i) ≤ physicalK s e := by
  by_cases hs : 1 ≤ s
  · rw [reverse_weighted_sum s e he]
    apply Finset.sum_le_sum
    intro q hq
    apply Nat.mul_le_mul_left
    have hmem : 1 ∈ Finset.Icc 1 s := Finset.mem_Icc.mpr ⟨le_rfl, hs⟩
    have h := Finset.single_le_sum (fun d _ => Nat.zero_le (s - d * q)) hmem
    simpa only [intervalMultiplicity, one_mul] using h
  · have hs0 : s = 0 := by omega
    have he0 : e = 0 := by omega
    simp [hs0, he0]

theorem actual_weighted_source_lower {D H s e : ℕ} {C : ℕ → ℕ}
    (hC : ∀ q, q ≤ H → C (q % 30) * q ≤ D * Nat.totient q)
    (he : e ≤ s) (hs : s ≤ H) :
    s * A C e (s % 30) ≤ D * physicalK s e + B C e (s % 30) := by
  have hpoint : ∀ i ∈ Finset.Icc 1 e,
      s * (Weight C (s % 30) i * i) ≤
        D * (Nat.totient (s - i) * i) + Weight C (s % 30) i * i^2 := by
    intro i hi
    have hie := (Finset.mem_Icc.mp hi).2
    have his : i ≤ s := hie.trans he
    have hphi := hC (s - i) ((Nat.sub_le s i).trans hs)
    rw [sub_mod_thirty his] at hphi
    change Weight C (s % 30) i * (s - i) ≤ D * Nat.totient (s - i) at hphi
    have hm := Nat.mul_le_mul_right i hphi
    calc
      s * (Weight C (s % 30) i * i) = Weight C (s % 30) i * s * i := by ring
      _ = Weight C (s % 30) i * ((s - i) + i) * i := by
        rw [Nat.sub_add_cancel his]
      _ = Weight C (s % 30) i * (s - i) * i + Weight C (s % 30) i * i^2 := by ring
      _ ≤ D * (Nat.totient (s - i) * i) + Weight C (s % 30) i * i^2 := by
        nlinarith only [hm]
  have hsum := Finset.sum_le_sum hpoint
  have hbound : s * A C e (s % 30) ≤
      D * (∑ i ∈ Finset.Icc 1 e, Nat.totient (s - i) * i) + B C e (s % 30) := by
    simpa only [A, B, Finset.sum_add_distrib, ← Finset.mul_sum] using hsum
  exact hbound.trans (Nat.add_le_add_right (Nat.mul_le_mul_left D (actual_d1_source_lower he)) _)

theorem residue_tail_floor {D H cutoff s e b : ℕ} {C : ℕ → ℕ}
    (hD : 0 < D)
    (hC : ∀ q, q ≤ H → C (q % 30) * q ≤ D * Nat.totient q)
    (he : e ≤ cutoff) (hcut : cutoff ≤ s) (hs : s ≤ H)
    (hgates : ∀ r, r < 30 → D * b + B C e r ≤ cutoff * A C e r) :
    b ≤ physicalK s e := by
  have hr : s % 30 < 30 := Nat.mod_lt _ (by decide)
  have hgate := hgates (s % 30) hr
  have hmono := Nat.mul_le_mul_right (A C e (s % 30)) hcut
  have hsource := actual_weighted_source_lower hC (he.trans hcut) hs
  have hmul : D * b ≤ D * physicalK s e := by omega
  by_contra hb
  have hbad : physicalK s e + 1 ≤ b := by omega
  have hm := Nat.mul_le_mul_left D hbad
  nlinarith only [hmul, hm, hD]

def CheckResidues (D : ℕ) (C : ℕ → ℕ) (cutoff e b : ℕ) : Bool :=
  (List.range 30).all fun r => decide (D * b + B C e r ≤ cutoff * A C e r)

theorem checkResidues_sound {D H cutoff s e b : ℕ} {C : ℕ → ℕ}
    (hD : 0 < D)
    (hC : ∀ q, q ≤ H → C (q % 30) * q ≤ D * Nat.totient q)
    (he : e ≤ cutoff) (hcut : cutoff ≤ s) (hs : s ≤ H)
    (hcheck : CheckResidues D C cutoff e b = true) : b ≤ physicalK s e := by
  apply residue_tail_floor hD hC he hcut hs
  intro r hr
  have hh := List.all_eq_true.mp hcheck r (List.mem_range.mpr hr)
  exact of_decide_eq_true hh

def CheckRatios (phi C : ℕ → ℕ) (D H : ℕ) : Bool :=
  (List.range (H + 1)).all fun q => decide (C (q % 30) * q ≤ D * phi q)

theorem checkRatios_sound {phi C : ℕ → ℕ} {D H : ℕ}
    (hphi : ∀ q, q ≤ H → phi q = Nat.totient q)
    (hcheck : CheckRatios phi C D H = true) :
    ∀ q, q ≤ H → C (q % 30) * q ≤ D * Nat.totient q := by
  intro q hq
  have hm : q ∈ List.range (H + 1) := List.mem_range.mpr (by omega)
  have hh := of_decide_eq_true (List.all_eq_true.mp hcheck q hm)
  simpa only [hphi q hq] using hh

#print axioms sub_mod_thirty
#print axioms reverse_weighted_sum
#print axioms actual_d1_source_lower
#print axioms actual_weighted_source_lower
#print axioms residue_tail_floor
#print axioms checkResidues_sound
#print axioms checkRatios_sound
end JSP233.ResidueSource208
