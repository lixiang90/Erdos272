module

public import Erdos272.Counting.N20258.MarkedCoreEnds20258
public import Erdos272.Counting.N20258.MarkedCover20258
public import Erdos272.Resources.FarJoint112
public import Erdos272.Resources.SourceBridge208
public import Erdos272.Arithmetic.StepClass208
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section
namespace JSP233.MarkedPopulation20258
open StarCompletion APGeometry SourceBridge208 FarCapacity112
open scoped Classical BigOperators
set_option autoImplicit false

/-- The unit stride has no proper positive divisor. -/
def factor (d k : ℕ) := if d=1 then k+2 else d.minFac

private theorem factor_two (d k : ℕ) : 2≤factor d k := by
  unfold factor
  split_ifs with h
  · omega
  · exact (Nat.minFac_prime h).two_le

private theorem ratio (d k : ℕ) (δ : ℤ) (pos : 0<δ) (div : δ∣(d:ℤ)) (lt : δ<d) :
    (factor d k:ℤ)*δ≤d := by
  by_cases unit : d=1
  · omega
  apply StepClass208.ratio_of_quotient pos div lt
  intro q two small divides
  lift q to ℕ using (by omega)
  have q2 : 2≤q := by exact_mod_cast two
  have qd : q∣d := by exact_mod_cast divides
  have h := Nat.minFac_le_of_dvd q2 qd
  simp only [factor,ite_eq_right unit] at small
  omega

/-- Number of possible occupants at a fixed core site and a fixed exterior site. -/
def gates (n a k d : ℕ) : ℕ :=
  (if d*a<n then 1 else 0) +
  (if d*ResidualSpan208.Span a (k+1) (factor d k)<n then 1 else 0)

private theorem gates_int (n a k d : ℕ) : gates n a k d =
    (if (d:ℤ)*(a:ℤ)≤(n:ℤ)-1 then 1 else 0) +
    (if (d:ℤ)*(ResidualSpan208.Span a (k+1) (factor d k):ℤ)≤(n:ℤ)-1 then 1 else 0) := by
  unfold gates
  simp only [← Nat.cast_mul (α:=ℤ)]
  split_ifs <;> omega

def strideBound (n a k top d : ℕ) : ℕ :=
  let o := gates n a k d
  let s := min top ((n-1)/d+1+k)
  let u := n*o/(a+1)
  (k+1)*(n*o)+k*min (s*u) (k*(k+1)*(s*o+u))

def budget (n a k top : ℕ) : ℕ :=
  ∑ d∈Finset.Icc 1 ((n-1)/a),strideBound n a k top d

private theorem restrict {n : ℕ} {A F : Finset (Finset ℤ)}
    (legal : Legal (Ground n) F) (sub : A⊆F) : Legal (Ground n) A :=
  ⟨fun S hs => legal.1 S (sub hs),fun S hs T ht ne => legal.2 S (sub hs) T (sub ht) ne⟩

private theorem core_span {n d a : ℕ} {S P : Finset ℤ}
    (inside : S⊆Ground n) (core : MaximumAPCore S P) (step : ∃ p,APAt (d:ℤ) p P)
    (size : a+1≤P.card) : d*a<n := by
  obtain ⟨p,hp⟩ := step
  obtain ⟨z,hz⟩ := isAP_nonempty core.2.1
  have h := ResidualOccupancy208.actual_single_span inside core.1 (apAt_rebase hp hz) hz size
  rw [← Nat.cast_mul] at h
  omega

/-- Actual members of one stride. Double counting the core sites at a single
exterior point gives the bound u, even when the defects are different. -/
theorem stride {n a k top d : ℕ} {A : Finset (Finset ℤ)} {P : Finset ℤ → Finset ℤ}
    (legal : Legal (Ground n) A) (pos : 0<d) (core : ∀ S∈A,MaximumAPCore S (P S))
    (step : ∀ S∈A,∃ p,APAt (d:ℤ) p (P S)) (large : ∀ S∈A,a+1≤(P S).card)
    (small : ∀ S∈A,(S\P S).card≤k) (size : ∀ S∈A,S.card≤top) :
    ∑ S∈A,(S\P S).card≤strideBound n a k top d := by
  classical
  let H (t : ℤ) := A.filter (fun S => t∈P S)
  have sub (t : ℤ) : H t⊆A := Finset.filter_subset _ _
  have hit (t : ℤ) (S : Finset ℤ) (hs : S∈H t) : t∈P S := (Finset.mem_filter.mp hs).2
  have atPivot (t : ℤ) (S : Finset ℤ) (hs : S∈H t) : APAt (d:ℤ) t (P S) := by
    obtain ⟨p,hp⟩ := step S (sub t hs)
    exact apAt_rebase hp (hit t S hs)
  have pivot (t : ℤ) : ∑ S∈H t,(S\P S).card≤n*gates n a k d := by
    rw [gates_int]
    exact MarkedCoreEnds20258.marked_weight (restrict legal (sub t)) (factor_two d k) P
      (fun S hs => maximum_core_is_maximal (core S (sub t hs))) (atPivot t) (hit t)
      (fun S hs => large S (sub t hs)) (fun S hs => small S (sub t hs))
      (fun S hs R ap inc => (core S (sub t hs)).2.2 R inc ap) (ratio d k)
  have pair (t x : ℤ) : ((H t).filter (fun S => x∈S\P S)).card≤gates n a k d := by
    rw [gates_int]
    apply le_trans (Finset.card_le_card ?_) (ResidualOccupancy208.actual_cumulative_occupancy
      (b:=k+1) (restrict legal (sub t)) (factor_two d k) P
      (fun S hs => maximum_core_is_maximal (core S (sub t hs))) (atPivot t) (hit t)
      (fun S hs => large S (sub t hs)) (fun S hs R ap inc => (core S (sub t hs)).2.2 R inc ap)
      (ratio d k) x)
    intro S hs
    obtain ⟨mem,mark⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨mem,mark,Nat.lt_succ_of_le (small S (sub t mem))⟩
  have outer (x : ℤ) : (A.filter (fun S => x∈S\P S)).card≤n*gates n a k d/(a+1) := by
    let G := A.filter (fun S => x∈S\P S)
    have ga : G⊆A := Finset.filter_subset _ _
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos a)).mpr
    calc
      _ = ∑ _S∈G,(a+1) := by simp [G]
      _ ≤ ∑ S∈G,(P S).card := Finset.sum_le_sum (fun S hs => large S (ga hs))
      _ ≤ gates n a k d*(Ground n).card := ResidualPool208.incidence_capacity G (Ground n) P _
        (fun S hs => (core S (ga hs)).1.trans (legal.1 S (ga hs))) (fun t _ => by
          have eq : G.filter (fun S => t∈P S)=(H t).filter (fun S => x∈S\P S) := by
            ext S
            simp [G,H,and_comm,and_left_comm]
          rw [eq]
          exact pair t x)
      _ = _ := by rw [ground_card,Nat.mul_comm]
  apply MarkedCover20258.weight (fun S hs => isAP_nonempty (core S hs).2.1) step ?_ small ?_ pivot pair outer
  · intro S hs T ht
    by_cases eq : S=T
    · subst T
      simpa using (isAP_nonempty (core S hs).2.1).mono (core S hs).1
    · exact isAP_nonempty (legal.2 S hs T ht eq)
  · intro S hs
    apply le_min (size S hs)
    have span := core_span (legal.1 S hs) (core S hs) (step S hs)
      (show (P S).card-1+1≤(P S).card by have := large S hs; omega)
    have bound := (Nat.le_div_iff_mul_le pos).mpr
      (show ((P S).card-1)*d≤n-1 by rw [Nat.mul_comm]; omega)
    have parts := Finset.card_sdiff_add_card_eq_card (core S hs).1
    have few := small S hs
    omega

/-- Sum the defects of the actual family once, according to one chosen
longest core per member. The ground n may pad a smaller original ground. -/
theorem actual {n a k top : ℕ} {A : Finset (Finset ℤ)}
    (legal : Legal (Ground n) A) (len : 0<a) (large : ∀ S∈A,a+1+k≤S.card)
    (size : ∀ S∈A,S.card≤top) (few : ∀ S∈A,Defect S≤k) :
    ∑ S∈A,Defect S≤budget n a k top := by
  classical
  obtain ⟨P,step,chosen⟩ := FarJoint112.exists_maximum_core_selection
    (F:=A) (fun S hs => Finset.card_pos.mp (by have := large S hs; omega))
  have card (S : Finset ℤ) (hs : S∈A) : (P S).card=MaxAPSize S := by
    have h := (chosen S hs).1
    refine le_antisymm (AP_card_le_max h.2.1 h.1) (Finset.sup_le ?_)
    intro R hr
    exact h.2.2 R (Finset.mem_powerset.mp (Finset.mem_filter.mp hr).1) (Finset.mem_filter.mp hr).2
  have remnant (S : Finset ℤ) (hs : S∈A) : (S\P S).card=Defect S := by
    rw [Finset.card_sdiff_of_subset (chosen S hs).1.1,card S hs]
    rfl
  have length (S : Finset ℤ) (hs : S∈A) : a+1≤(P S).card := by
    have defc := few S hs
    unfold Defect at defc
    rw [card S hs]
    have := large S hs
    omega
  let D := Finset.Icc 1 ((n-1)/a)
  have maps (S : Finset ℤ) (hs : S∈A) : step S∈D := by
    obtain ⟨p,hp⟩ := (chosen S hs).2
    have pos := hp.1
    have span := core_span (legal.1 S hs) (chosen S hs).1 (chosen S hs).2 (length S hs)
    exact Finset.mem_Icc.mpr ⟨by omega,(Nat.le_div_iff_mul_le len).mpr (by omega)⟩
  change _≤∑ d∈D,strideBound n a k top d
  rw [← Finset.sum_fiberwise_of_maps_to maps Defect]
  apply Finset.sum_le_sum
  intro d hd
  let B := A.filter (fun S => step S=d)
  have sub : B⊆A := Finset.filter_subset _ _
  change ∑ S∈B,Defect S≤_
  calc
    _ = ∑ S∈B,(S\P S).card := Finset.sum_congr rfl (fun S hs => (remnant S (sub hs)).symm)
    _ ≤ _ := stride (restrict legal sub) (Finset.mem_Icc.mp hd).1
      (fun S hs => (chosen S (sub hs)).1) (fun S hs => by
        rw [←(Finset.mem_filter.mp hs).2]
        exact (chosen S (sub hs)).2) (fun S hs => length S (sub hs))
      (fun S hs => (remnant S (sub hs)).le.trans (few S (sub hs))) (fun S hs => size S (sub hs))

#print axioms stride
#print axioms actual
end JSP233.MarkedPopulation20258
