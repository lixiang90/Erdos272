module

public import Erdos272.Foundation.StaircaseCertificate

@[expose] public section

/-! Verified prefix-count reflection for the finite staircase certificate.
Only ordinary finite comparisons will certify candidate lookup functions. -/

namespace JSP233.Staircase249Counts
open StaircaseCertificate

def MixPred (r a : Nat) : Prop := 0 < a ∧ Nat.gcd a r = 1 ∧ a ≠ r
instance (r a : Nat) : Decidable (MixPred r a) :=
  inferInstanceAs (Decidable (0 < a ∧ Nat.gcd a r = 1 ∧ a ≠ r))

def MixCount (r n : Nat) : Nat := ((Finset.range n).filter (MixPred r)).card

theorem mixCount_zero (r : Nat) : MixCount r 0 = 0 := by simp [MixCount]

theorem mixCount_succ (r n : Nat) :
    MixCount r (n+1) = MixCount r n + if MixPred r n then 1 else 0 := by
  have hn : n ∉ (Finset.range n).filter (MixPred r) := by simp
  by_cases hp : MixPred r n
  · simp [MixCount,Finset.range_add_one,Finset.filter_insert,hp,hn]
  · simp [MixCount,Finset.range_add_one,Finset.filter_insert,hp]

theorem mixedSupply_eq_mixCount (h r : Nat) : MixedSupply h r = MixCount r (h+1) := rfl

theorem primitivePhi_eq_mixCount (r : Nat) :
    PrimitivePhi r = MixCount r r + if r = 1 then 1 else 0 := by
  by_cases hz : r = 0
  · simp [hz,PrimitivePhi,MixCount]
  · by_cases ho : r = 1
    · simp [ho,PrimitivePhi,MixCount,MixPred]
    · have heq : (Finset.range r).filter (fun a => Nat.gcd a r = 1) =
          (Finset.range r).filter (MixPred r) := by
        ext a
        simp only [Finset.mem_filter]
        constructor
        · intro ha
          have har := Finset.mem_range.mp ha.1
          refine ⟨ha.1,?_,ha.2,by omega⟩
          by_contra hn
          have ha0 : a = 0 := by omega
          simp [ha0] at ha
          omega
        · exact fun ha => ⟨ha.1,ha.2.2.1⟩
      simp only [PrimitivePhi,MixCount,ho,if_false,Nat.add_zero,heq]

structure CountCertificate (B H : Nat) (mix : Nat → Nat → Nat) : Prop where
  zero : ∀ r : Fin (B+1), mix r 0 = 0
  step : ∀ r : Fin (B+1), ∀ n : Fin H,
    mix r (n+1) = mix r n + if MixPred r n then 1 else 0

theorem count_certificate_sound {B H : Nat} {mix : Nat → Nat → Nat}
    (cert : CountCertificate B H mix) (r n : Nat) (hr : r ≤ B) (hn : n ≤ H) :
    mix r n = MixCount r n := by
  induction n with
  | zero => simpa [mixCount_zero] using cert.zero ⟨r,by omega⟩
  | succ n ih =>
    have hs := cert.step ⟨r,by omega⟩ ⟨n,by omega⟩
    have hi := ih (by omega)
    simpa only [hi,mixCount_succ] using hs

theorem leftSupply_succ (h : Nat) :
    LeftSupply (h+1) = LeftSupply h + if 3 ≤ h+1 then PrimitivePhi (h+1) else 0 := by
  exact Finset.sum_range_succ _ (h+1)

structure LeftCertificate (H : Nat) (left : Nat → Nat) : Prop where
  zero : left 0 = 0
  step : ∀ h : Fin H,
    left ((h:Nat)+1) = left h + if 3 ≤ (h:Nat)+1 then PrimitivePhi ((h:Nat)+1) else 0

theorem left_certificate_sound {H : Nat} {left : Nat → Nat}
    (cert : LeftCertificate H left) (h : Nat) (hh : h ≤ H) : left h = LeftSupply h := by
  induction h with
  | zero => simpa [LeftSupply] using cert.zero
  | succ h ih =>
    have hs := cert.step ⟨h,by omega⟩
    have hi := ih (by omega)
    simpa only [hi,leftSupply_succ] using hs

def ReflectedScore (mix : Nat → Nat → Nat) (left : Nat → Nat) (r i : Nat) : Int :=
  if i = 0 then 0 else
    let h := i-1
    if r = 0 then ((h-2 : Nat) : Int) - (left h : Int)
    else ((h+1-(3-r) : Nat) : Int) - (mix r i : Int) -
      (if 3 ≤ r then ((mix r r + if r = 1 then 1 else 0 : Nat) : Int) else 0)

theorem reflectedScore_eq_columnScore {B H : Nat} {mix : Nat → Nat → Nat}
    {left : Nat → Nat} (hc : CountCertificate B H mix) (hl : LeftCertificate H left)
    (hBH : B ≤ H) (r i : Nat) (hr : r ≤ B) (hi : i ≤ H) :
    ReflectedScore mix left r i = ColumnScore r i := by
  by_cases hiz : i = 0
  · simp [ReflectedScore,ColumnScore,hiz]
  · have hleft := left_certificate_sound hl (i-1) (by omega)
    have hmix := count_certificate_sound hc r i hr hi
    have hphi : mix r r + (if r = 1 then 1 else 0) = PrimitivePhi r := by
      rw [count_certificate_sound hc r r hr (by omega),primitivePhi_eq_mixCount]
    have hmixed : MixCount r i = MixedSupply (i-1) r := by
      rw [mixedSupply_eq_mixCount,show i-1+1 = i by omega]
    simp only [ReflectedScore,ColumnScore,hiz,if_false,hleft,hmix,hmixed,hphi]

theorem true_localCertificate {B H : Nat} {mix : Nat → Nat → Nat} {left : Nat → Nat}
    {cap : Int} {potential suffix : Nat → Nat → Int}
    (hc : CountCertificate B H mix) (hl : LeftCertificate H left) (hBH : B ≤ H)
    (cert : LocalCertificate B H cap (ReflectedScore mix left) potential suffix) :
    LocalCertificate B H cap ColumnScore potential suffix := by
  refine ⟨?_,cert.majorize,cert.descending,?_,cert.terminal⟩
  · intro h
    rw [← reflectedScore_eq_columnScore hc hl hBH 0 h (by omega) (by omega)]
    exact cert.base h
  · intro r h
    rw [← reflectedScore_eq_columnScore hc hl hBH (r+1) h (by omega) (by omega)]
    exact cert.step r h

#print axioms mixCount_zero
#print axioms mixCount_succ
#print axioms mixedSupply_eq_mixCount
#print axioms primitivePhi_eq_mixCount
#print axioms count_certificate_sound
#print axioms leftSupply_succ
#print axioms left_certificate_sound
#print axioms reflectedScore_eq_columnScore
#print axioms true_localCertificate

end JSP233.Staircase249Counts
