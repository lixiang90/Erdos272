module

public import Erdos272.Arithmetic.N20258.ProgressionLengths20258
public import Erdos272.Counting.N88404.APClassFrame88404
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! An actual same-step family is an interval family on a single residue
class with a common site. Within each length the left endpoint determines
the whole member, and has at most two different elementary bounds. -/
namespace JSP233.ProgressionTail20258

open StarCompletion APCount41 AffineLine30 APClasses88404 APClassFrame88404
open ProgressionLengths20258
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

private theorem interval_of_length {S : Finset ℤ} {z : ℤ} {l : ℕ}
    (hz : z ∈ S) (hi : ∃ a b : ℤ, S = Finset.Icc a b) (hc : S.card = l) :
    S = Finset.Icc (Low S) (Low S+(l : ℤ)-1) := by
  obtain ⟨a,b,rfl⟩ := hi
  have hab : a ≤ b := (Finset.mem_Icc.mp hz).1.trans (Finset.mem_Icc.mp hz).2
  have hspec := low_spec (show (Finset.Icc a b).Nonempty from ⟨z,hz⟩)
  have ha : Low (Finset.Icc a b) = a :=
    le_antisymm (hspec.2 a (Finset.mem_Icc.mpr ⟨le_rfl,hab⟩)) (Finset.mem_Icc.mp hspec.1).1
  have hl := Int.card_Icc_of_le (a := a) (b := b) (by omega)
  rw [hc] at hl
  rw [ha, show a+(l : ℤ)-1 = b by omega]

private theorem length_fiber {M l : ℕ} {z : ℤ} {V : Finset (Finset ℤ)}
    (hground : ∀ S ∈ V, S ⊆ Ground M) (hroot : ∀ S ∈ V, z ∈ S)
    (hI : ∀ S ∈ V, ∃ a b : ℤ, S = Finset.Icc a b) (hsize : ∀ S ∈ V, S.card = l) :
    V.card ≤ min l (M+1-l) := by
  have rep (S : Finset ℤ) (hS : S ∈ V) := interval_of_length (hroot S hS) (hI S hS) (hsize S hS)
  have inj : Set.InjOn Low (V : Set (Finset ℤ)) := by
    intro S hS T hT he
    calc
      S = Finset.Icc (Low S) (Low S+(l : ℤ)-1) := rep S hS
      _ = Finset.Icc (Low T) (Low T+(l : ℤ)-1) := by rw [he]
      _ = T := (rep T hT).symm
  have ends (S : Finset ℤ) (hS : S ∈ V) :
      1 ≤ Low S ∧ Low S ≤ z ∧ z ≤ Low S+(l : ℤ)-1 ∧ Low S+(l : ℤ)-1 ≤ M := by
    have hz := hroot S hS
    have hpair := Finset.mem_Icc.mp (show z ∈ Finset.Icc (Low S) (Low S+(l : ℤ)-1) by
      simpa only [← rep S hS] using hz)
    have hleft := (mem_ground M _).mp (hground S hS ((low_spec ⟨z,hz⟩).1))
    have he : Low S+(l : ℤ)-1 ∈ S := by
      apply (Finset.ext_iff.mp (rep S hS) _).mpr
      exact Finset.mem_Icc.mpr ⟨hpair.1.trans hpair.2,le_rfl⟩
    exact ⟨hleft.1,hpair.1,hpair.2,((mem_ground M _).mp (hground S hS he)).2⟩
  apply le_min
  · have bound : V.card ≤ (Finset.Icc (z-(l : ℤ)+1) z).card :=
      Finset.card_le_card_of_injOn Low (fun S hS => Finset.mem_Icc.mpr (by have := ends S hS; omega)) inj
    rw [Int.card_Icc] at bound
    omega
  · have bound : V.card ≤ (Finset.Icc (1 : ℤ) (M-(l : ℤ)+1)).card :=
      Finset.card_le_card_of_injOn Low (fun S hS => Finset.mem_Icc.mpr (by have := ends S hS; omega)) inj
    rw [Int.card_Icc] at bound
    omega

/-- Length-`l` progressions of step `d` in the original legal family. -/
theorem actual_length {N d l : ℕ} {F : Finset (Finset ℤ)} (hN : 1 ≤ N) (hd : 0 < d)
    (hF : Legal (Ground N) F) :
    ((StepAP F d).filter (fun S => S.card = l)).card ≤ starts ((N-1)/d) l := by
  obtain ⟨f⟩ := frame_nonempty hN hd hF
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  let V := f.family.filter (fun S => S.card = l)
  have hv : ∀ S ∈ V, S ∈ f.family := fun _ h => (Finset.mem_filter.mp h).1
  have count := length_fiber (fun S h => f.ground S (hv S h))
    (fun S h => f.common_root S (hv S h)) (fun S h => f.intervals S (hv S h))
    (fun _ h => (Finset.mem_filter.mp h).2)
  have he : mapFamily f.offset (d : ℤ) V = (StepAP F d).filter (fun S => S.card = l) := by
    ext T
    have member (X : Finset ℤ) := Finset.ext_iff.mp f.mapped X
    constructor
    · intro hT
      obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hT
      exact Finset.mem_filter.mpr ⟨(member _).mp (Finset.mem_image.mpr ⟨S,hv S hS,rfl⟩),
        (mapSet_card f.offset (d : ℤ) hdZ S).trans (Finset.mem_filter.mp hS).2⟩
    · intro hT
      obtain ⟨hT,hcard⟩ := Finset.mem_filter.mp hT
      obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp ((member _).mpr hT)
      exact Finset.mem_image.mpr ⟨S,Finset.mem_filter.mpr ⟨hS,
        (mapSet_card f.offset (d : ℤ) hdZ S).symm.trans hcard⟩,rfl⟩
  have hspan : (f.size-1)*d ≤ N-1 := by
    have hm := f.span
    have hcast : (((f.size-1)*d : ℕ) : ℝ) ≤ ((N-1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub f.size_positive, Nat.cast_sub hN]
      linarith only [hm, mul_comm (d : ℝ) ((f.size : ℝ)-1)]
    exact_mod_cast hcast
  have hgrid := (Nat.le_div_iff_mul_le hd).mpr hspan
  have hpos := f.size_positive
  rw [← he,mapFamily_card f.offset (d : ℤ) hdZ]
  exact count.trans (min_le_min_left l (by omega))

theorem sum_lengths {q k n : ℕ} (h : k ≤ n) :
    (∑ l ∈ Finset.Ioc k n, starts q l) + tail q n = tail q k := by
  refine Nat.le_induction ?_ ?_ n h
  · simp
  · intro m hm ih
    rw [Finset.sum_Ioc_succ_top hm, Nat.add_assoc, ← tail_step q m]
    exact ih

/-- The tail is a bound on actual members, including the empty class. -/
theorem actual_step_tail {N d k : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1 ≤ N) (hd : 0 < d) (hF : Legal (Ground N) F)
    (hmin : ∀ S ∈ StepAP F d, k < S.card) :
    (StepAP F d).card ≤ tail ((N-1)/d) k := by
  let n := max N k
  have lengths : ∀ S ∈ StepAP F d, S.card ∈ Finset.Ioc k n := by
    intro S hS
    have hle := Finset.card_le_card (hF.1 S (APClasses88404.subset F d hS))
    rw [ground_card] at hle
    exact Finset.mem_Ioc.mpr ⟨hmin S hS,hle.trans (le_max_left _ _)⟩
  have hsum := sum_lengths (q := (N-1)/d) (k := k) (n := n) (le_max_right _ _)
  calc
    (StepAP F d).card = ∑ l ∈ Finset.Ioc k n, ((StepAP F d).filter (fun S => S.card = l)).card :=
      Finset.card_eq_sum_card_fiberwise lengths
    _ ≤ ∑ l ∈ Finset.Ioc k n, starts ((N-1)/d) l :=
      Finset.sum_le_sum (fun l _ => actual_length hN hd hF)
    _ ≤ tail ((N-1)/d) k := by omega

end
end JSP233.ProgressionTail20258
