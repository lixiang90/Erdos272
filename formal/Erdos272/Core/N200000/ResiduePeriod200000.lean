module

public import Erdos272.Foundation.ProofTactics

@[expose] public section

/-! Physical phases and standard residues are related by an actual
bijection, including negative external-point offsets. -/
namespace JSP233.ResiduePeriod200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def Residue (d : ℕ) (z : ℤ) : ℕ := (z % (d : ℤ)).toNat
def ResidueDenominator (d s : ℕ) : ℕ := d / Nat.gcd d s
def PhaseRep (d : ℕ) (z : ℤ) : ℕ := Residue d (z - 1) + 1

theorem residue_cast {d : ℕ} (hd : 0 < d) (z : ℤ) :
    (Residue d z : ℤ) = z % (d : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (by omega : (d : ℤ) ≠ 0))

theorem residue_lt {d : ℕ} (hd : 0 < d) (z : ℤ) : Residue d z < d := by
  have hh := Int.emod_lt_of_pos z (show 0 < (d : ℤ) by exact_mod_cast hd)
  rw [← residue_cast hd z] at hh
  exact_mod_cast hh

theorem residue_nat {d s : ℕ} (hd : 0 < d) (hs : s < d) : Residue d (s : ℤ) = s := by
  apply Int.ofNat_inj.mp
  rw [residue_cast hd]
  exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hs)

theorem residue_eq_iff {d : ℕ} (hd : 0 < d) {u v : ℤ} :
    Residue d u = Residue d v ↔ (d : ℤ) ∣ u - v := by
  constructor
  · intro h
    have he : u % (d : ℤ) = v % (d : ℤ) := by
      rw [← residue_cast hd u, ← residue_cast hd v, h]
    exact Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp he)
  · intro h
    have he : u % (d : ℤ) = v % (d : ℤ) :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h)
    apply Int.ofNat_inj.mp
    rw [residue_cast hd u, residue_cast hd v, he]

#print axioms residue_cast
#print axioms residue_lt
#print axioms residue_nat
#print axioms residue_eq_iff
end
end JSP233.ResiduePeriod200000
