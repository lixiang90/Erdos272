import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
Kernel-checked local potential certificates for finite decreasing staircase
profiles.  The concrete B=8 instance uses actual primitive-gcd column scores;
it is not an infinite-tail proof and does not supply the separate bridge from
an actual AP family to its staircase and pair-union score.
-/

namespace JSP233.StaircaseCertificate

open scoped BigOperators

/-- Height 0 means absent; height i+1 means actual height i. -/
def ProfileScore (score : Nat → Nat → Int) (p : Nat → Nat) (B : Nat) : Int :=
  ∑ r ∈ Finset.range (B+1), score r (p r)

/-- These are local integer comparisons, not the desired profile bound. -/
structure Certificate (B H : Nat) (cap : Int)
    (score potential : Nat → Nat → Int) : Prop where
  base : ∀ h : Fin (H+1), score 0 h ≤ potential 0 h
  step : ∀ r : Fin B, ∀ h k : Fin (H+1), h.val ≤ k.val →
    score (r+1) h + potential r k ≤ potential (r+1) h
  terminal : ∀ h : Fin (H+1), potential B h ≤ cap

theorem certificate_sound {B H : Nat} {cap : Int}
    {score potential : Nat → Nat → Int}
    (cert : Certificate B H cap score potential)
    (p : Nat → Nat) (hp : ∀ r ≤ B, p r ≤ H)
    (hmono : ∀ r < B, p (r+1) ≤ p r) :
    ProfileScore score p B ≤ cap := by
  have hprefix : ∀ n ≤ B,
      (∑ r ∈ Finset.range (n+1), score r (p r)) ≤ potential n (p n) := by
    intro n
    induction n with
    | zero =>
      intro hn
      simpa using cert.base ⟨p 0, by have := hp 0 hn; omega⟩
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hs := cert.step ⟨n, by omega⟩
        ⟨p (n+1), by have := hp (n+1) hn; omega⟩
        ⟨p n, by have := hp n (by omega); omega⟩ (hmono n (by omega))
      rw [Finset.sum_range_succ]
      have hs' : score (n+1) (p (n+1)) + potential n (p n) ≤
          potential (n+1) (p (n+1)) := hs
      linarith
  exact (hprefix B le_rfl).trans (cert.terminal ⟨p B, by have := hp B le_rfl; omega⟩)

/-- A linear-size form of the certificate. The auxiliary `suffix` bounds all
potentials at larger heights using only adjacent-height comparisons. -/
structure LocalCertificate (B H : Nat) (cap : Int)
    (score potential suffix : Nat → Nat → Int) : Prop where
  base : ∀ h : Fin (H+1), score 0 h ≤ potential 0 h
  majorize : ∀ r : Fin B, ∀ h : Fin (H+1), potential r h ≤ suffix r h
  descending : ∀ r : Fin B, ∀ h : Fin H, suffix r (h+1) ≤ suffix r h
  step : ∀ r : Fin B, ∀ h : Fin (H+1),
    score (r+1) h + suffix r h ≤ potential (r+1) h
  terminal : ∀ h : Fin (H+1), potential B h ≤ cap

theorem local_certificate_to_certificate {B H : Nat} {cap : Int}
    {score potential suffix : Nat → Nat → Int}
    (cert : LocalCertificate B H cap score potential suffix) :
    Certificate B H cap score potential := by
  have hdown (r : Fin B) (h k : Nat) (hk : h ≤ k) :
      k ≤ H → suffix r k ≤ suffix r h := by
    induction k, hk using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ k hk ih =>
      intro hkH
      have ha := cert.descending r ⟨k, by omega⟩
      exact ha.trans (ih (by omega))
  refine ⟨cert.base, ?_, cert.terminal⟩
  intro r h k hhk
  have hs := (cert.majorize r k).trans (hdown r h k hhk (by omega))
  have ht := cert.step r h
  linarith

theorem local_certificate_sound {B H : Nat} {cap : Int}
    {score potential suffix : Nat → Nat → Int}
    (cert : LocalCertificate B H cap score potential suffix)
    (p : Nat → Nat) (hp : ∀ r ≤ B, p r ≤ H)
    (hmono : ∀ r < B, p (r+1) ≤ p r) :
    ProfileScore score p B ≤ cap :=
  certificate_sound (local_certificate_to_certificate cert) p hp hmono

/-- Euler's phi written directly as an actual finite primitive-gcd count. -/
def PrimitivePhi (r : Nat) : Nat :=
  ((Finset.range r).filter (fun a => Nat.gcd a r = 1)).card

def LeftSupply (h : Nat) : Nat :=
  ∑ a ∈ Finset.range (h+1), if 3 ≤ a then PrimitivePhi a else 0

def MixedSupply (h r : Nat) : Nat :=
  ((Finset.range (h+1)).filter
    (fun a => 0 < a ∧ Nat.gcd a r = 1 ∧ a ≠ r)).card

/-- Exact arithmetic formula from the independent staircase audit, including
absent columns.  Counts are cast before subtraction to retain negative scores. -/
def ColumnScore (r i : Nat) : Int :=
  if i = 0 then 0 else
    let h := i-1
    if r = 0 then ((h-2 : Nat) : Int) - (LeftSupply h : Int)
    else ((h+1-(3-r) : Nat) : Int) - (MixedSupply h r : Int) -
      (if 3 ≤ r then (PrimitivePhi r : Int) else 0)

def Potential8 (r h : Nat) : Int :=
  (([[0, 0, 0, 0, -1, -2, -5, -6, -11, -14],
     [0, 0, 0, 0, -1, -2, -5, -6, -11, -14],
     [0, 0, 0, 1, 0, 0, -3, -3, -8, -10],
     [1, 0, 0, 0, 0, 0, -3, -2, -7, -9],
     [1, -1, -1, 0, 0, 1, -1, 0, -5, -6],
     [1, -2, -2, -2, -2, -2, -2, -2, -7, -8],
     [1, -3, -3, -2, -1, 0, 0, 1, -4, -4],
     [1, -4, -4, -4, -4, -4, -4, -4, -8, -8],
     [1, -7, -7, -6, -6, -5, -5, -4, -8, -7]] : List (List Int)).getD r []).getD h 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate_eight : Certificate 8 9 1 ColumnScore Potential8 := by
  constructor <;> decide

/-- All finite decreasing profiles with actual attained extents at most 8.
No assertion about actual-family D-P or the infinite range is hidden here. -/
theorem eight_profiles_score_le_one (p : Nat → Nat)
    (hp : ∀ r ≤ 8, p r ≤ 9) (hmono : ∀ r < 8, p (r+1) ≤ p r) :
    ProfileScore ColumnScore p 8 ≤ 1 :=
  certificate_sound certificate_eight p hp hmono

#print axioms certificate_sound
#print axioms local_certificate_to_certificate
#print axioms local_certificate_sound
#print axioms certificate_eight
#print axioms eight_profiles_score_le_one

end JSP233.StaircaseCertificate
