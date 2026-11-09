module

public import Erdos272.Core.N200000.PairEventCount200000

@[expose] public section

/-! A bad prime has one actual forbidden residue. The inverse is obtained
from Bezout, and the residue count pays the same interval complement. -/
namespace JSP233.PrimePairResidue200000
open StarCompletion APGeometry SourceBridge208 ResiduePeriod200000 CoreNormal200000
open PairEventCount200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def BadEvent (A J : Finset ℕ) (h : ℕ) (ell : ℤ) (q : ℕ) : Finset (Finset ℕ) :=
  (Space A J).filter (PrimePairEvents200000.Bad h ell q)

theorem linear_bad_residue {h q : ℕ} (hq : 0 < q) (hc : Int.gcd (h : ℤ) (q : ℤ) = 1) (ell : ℤ) :
    ∃ u : ℕ, u < q ∧ ∀ i : ℕ, (q : ℤ) ∣ ell - (h : ℤ) * i ↔ (q : ℤ) ∣ (i : ℤ) - u := by
  obtain ⟨inv, other, hbez⟩ := coprime_of_gcd_one hc
  let z := ell * inv
  let u := Residue q z
  have hu : u < q := residue_lt hq z
  have huDiv : (q : ℤ) ∣ (u : ℤ) - z := by
    apply (residue_eq_iff hq).mp
    exact residue_nat hq hu
  have hInv : (q : ℤ) ∣ (h : ℤ) * inv - 1 := by
    refine ⟨-other, ?_⟩
    nlinarith only [hbez]
  refine ⟨u, hu, ?_⟩
  intro i
  constructor
  · intro hi
    have hzmi : (q : ℤ) ∣ z - (i : ℤ) := by
      have hh := dvd_add (dvd_mul_of_dvd_right hi inv) (dvd_mul_of_dvd_left hInv (i : ℤ))
      have he : inv * (ell - (h : ℤ) * i) + ((h : ℤ) * inv - 1) * i = z - (i : ℤ) := by
        dsimp only [z]
        ring
      simpa only [he] using hh
    have hiz : (q : ℤ) ∣ (i : ℤ) - z := by
      rw [show (i : ℤ) - z = -(z - (i : ℤ)) by ring]
      exact dvd_neg.mpr hzmi
    have hh := dvd_sub hiz huDiv
    have he : ((i : ℤ) - z) - ((u : ℤ) - z) = (i : ℤ) - u := by ring
    simpa only [he] using hh
  · intro hi
    have hiz : (q : ℤ) ∣ (i : ℤ) - z := by
      have hh := dvd_add hi huDiv
      have he : ((i : ℤ) - u) + ((u : ℤ) - z) = (i : ℤ) - z := by ring
      simpa only [he] using hh
    have hdiff : (q : ℤ) ∣ (h : ℤ) * i - ell := by
      have hh := dvd_add (dvd_mul_of_dvd_right hiz (h : ℤ)) (dvd_mul_of_dvd_left hInv ell)
      have he : (h : ℤ) * ((i : ℤ) - z) + ((h : ℤ) * inv - 1) * ell = (h : ℤ) * i - ell := by
        dsimp only [z]
        ring
      simpa only [he] using hh
    rw [show ell - (h : ℤ) * i = -((h : ℤ) * i - ell) by ring]
    exact dvd_neg.mpr hdiff

theorem prime_bad_residue {h q : ℕ} (hq : q.Prime) (hn : ¬q ∣ h) (ell : ℤ) :
    ∃ u : ℕ, u < q ∧ ∀ i : ℕ, (q : ℤ) ∣ ell - (h : ℤ) * i ↔ (q : ℤ) ∣ (i : ℤ) - u := by
  have hcop : h.Coprime q := (hq.coprime_iff_not_dvd.mpr hn).symm
  have hgcd : Int.gcd (h : ℤ) (q : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hcop.gcd_eq_one
  exact linear_bad_residue hq.pos hgcd ell

theorem bad_event_interval_bounds {a b l h q : ℕ} (hlen : l + b ≤ a) (hq : q.Prime) (hn : ¬q ∣ h) (ell : ℤ) :
    (a / q).choose 2 - ((b + q - 1) / q).choose 2 ≤
        (BadEvent (Finset.range a) (Finset.Ico l (l + b)) h ell q).card ∧
      (BadEvent (Finset.range a) (Finset.Ico l (l + b)) h ell q).card ≤
        ((a + q - 1) / q).choose 2 - (b / q).choose 2 := by
  obtain ⟨u, _hu, hres⟩ := prime_bad_residue hq hn ell
  have he : BadEvent (Finset.range a) (Finset.Ico l (l + b)) h ell q =
      Event (Finset.range a) (Finset.Ico l (l + b)) q (u : ℤ) := by
    ext Q
    simp only [BadEvent, Event, Finset.mem_filter, PrimePairEvents200000.Bad, hres]
  rw [he]
  exact interval_event_bounds hlen hq.pos (u : ℤ)

#print axioms linear_bad_residue
#print axioms prime_bad_residue
#print axioms bad_event_interval_bounds
end
end JSP233.PrimePairResidue200000
