module

public import Erdos272.Foundation.StarCompletion
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Native finite-set geometry of the published centered lower construction.
No abstract three-term predicate or supplied AP classification is used. -/
namespace JSP233.ConstructionGeometry45
open StarCompletion
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

def Window (m d : ℤ) : Finset ℤ := {m-2*d,m-d,m,m+d,m+2*d}
def BadLeft (m d : ℤ) : Finset ℤ := {m-2*d,m,m+d}
def BadRight (m d : ℤ) : Finset ℤ := {m-d,m,m+2*d}
def LeftFour (m d : ℤ) : Finset ℤ := {m-2*d,m-d,m,m+d}
def RightFour (m d : ℤ) : Finset ℤ := {m-d,m,m+d,m+2*d}

theorem affine_interval_isAP (m d lo hi : ℤ) (hd : 0<d) (hlo : lo≤hi) :
    IsAP ((Finset.Icc lo hi).image (fun i => m+d*i)) := by
  refine ⟨d,m+d*lo,hd,m+d*lo,m+d*hi,?_,?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨i,hiI,rfl⟩ := Finset.mem_image.mp hx
      have hb := Finset.mem_Icc.mp hiI
      refine ⟨by nlinarith,by nlinarith,⟨i-lo,by ring⟩⟩
    · rintro ⟨hxl,hxh,q,hq⟩
      have hx : x=m+d*(lo+q) := by nlinarith only [hq]
      refine Finset.mem_image.mpr ⟨lo+q,Finset.mem_Icc.mpr ⟨?_,?_⟩,hx.symm⟩ <;>
        nlinarith only [hxl,hxh,hd,hx]
  · exact Finset.mem_image.mpr ⟨lo,Finset.mem_Icc.mpr ⟨le_rfl,hlo⟩,rfl⟩

theorem linear_three_isAP (a d : ℤ) (hd : 0<d) : IsAP {a,a+d,a+2*d} := by
  have he : ({a,a+d,a+2*d}:Finset ℤ)=
      (Finset.Icc (0:ℤ) 2).image (fun i=>a+d*i) := by
    ext x
    constructor
    · intro hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl
      · exact Finset.mem_image.mpr ⟨0,by decide,by ring⟩
      · exact Finset.mem_image.mpr ⟨1,by decide,by ring⟩
      · exact Finset.mem_image.mpr ⟨2,by decide,by ring⟩
    · intro hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hil,hiu⟩ := Finset.mem_Icc.mp hi
      interval_cases i <;> simp_all [mul_comm]
  rw [he]
  exact affine_interval_isAP a d 0 2 hd (by decide)

theorem window_isAP (m d : ℤ) (hd : 0<d) : IsAP (Window m d) := by
  have he : Window m d=(Finset.Icc (-2:ℤ) 2).image (fun i=>m+d*i) := by
    ext x
    constructor
    · intro hx
      simp only [Window,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl
      · exact Finset.mem_image.mpr ⟨-2,by decide,by ring⟩
      · exact Finset.mem_image.mpr ⟨-1,by decide,by ring⟩
      · exact Finset.mem_image.mpr ⟨0,by decide,by ring⟩
      · exact Finset.mem_image.mpr ⟨1,by decide,by ring⟩
      · exact Finset.mem_image.mpr ⟨2,by decide,by ring⟩
    · intro hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hil,hiu⟩ := Finset.mem_Icc.mp hi
      interval_cases i <;> simp [Window] <;> omega
  rw [he]
  exact affine_interval_isAP m d (-2) 2 hd (by decide)

theorem left_four_isAP (m d : ℤ) (hd : 0<d) : IsAP (LeftFour m d) := by
  have he : LeftFour m d=(Finset.Icc (-2:ℤ) 1).image (fun i=>m+d*i) := by
    ext x
    constructor
    · intro hx
      simp only [LeftFour,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl|rfl
      · exact Finset.mem_image.mpr ⟨-2,by decide,by ring⟩
      · exact Finset.mem_image.mpr ⟨-1,by decide,by ring⟩
      · exact Finset.mem_image.mpr ⟨0,by decide,by ring⟩
      · exact Finset.mem_image.mpr ⟨1,by decide,by ring⟩
    · intro hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hil,hiu⟩ := Finset.mem_Icc.mp hi
      interval_cases i <;> simp [LeftFour] <;> omega
  rw [he]
  exact affine_interval_isAP m d (-2) 1 hd (by decide)

theorem right_four_isAP (m d : ℤ) (hd : 0<d) : IsAP (RightFour m d) := by
  have he : RightFour m d=(Finset.Icc (-1:ℤ) 2).image (fun i=>m+d*i) := by
    ext x
    constructor
    · intro hx
      simp only [RightFour,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl|rfl
      · exact Finset.mem_image.mpr ⟨-1,by decide,by ring⟩
      · exact Finset.mem_image.mpr ⟨0,by decide,by ring⟩
      · exact Finset.mem_image.mpr ⟨1,by decide,by ring⟩
      · exact Finset.mem_image.mpr ⟨2,by decide,by ring⟩
    · intro hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hil,hiu⟩ := Finset.mem_Icc.mp hi
      interval_cases i <;> simp [RightFour] <;> omega
  rw [he]
  exact affine_interval_isAP m d (-1) 2 hd (by decide)

theorem left_four_subset_window (m d : ℤ) : LeftFour m d⊆Window m d := by
  intro x hx
  simp only [LeftFour,Window,Finset.mem_insert,Finset.mem_singleton] at hx ⊢
  aesop

theorem right_four_subset_window (m d : ℤ) : RightFour m d⊆Window m d := by
  intro x hx
  simp only [RightFour,Window,Finset.mem_insert,Finset.mem_singleton] at hx ⊢
  aesop

theorem centered_triple_six_shapes (m d : ℤ) (T : Finset ℤ)
    (hm : m∈T) (hcard : T.card=3) (hsub : T⊆Window m d) :
    T={m-2*d,m-d,m} ∨ T=BadLeft m d ∨ T={m-2*d,m,m+2*d} ∨
      T={m-d,m,m+d} ∨ T=BadRight m d ∨ T={m,m+d,m+2*d} := by
  have he : (T.erase m).card=2 := by rw [Finset.card_erase_of_mem hm,hcard]
  obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp he
  have ha : a≠m ∧ a∈T := Finset.mem_erase.mp (he ▸ (by simp : a∈({a,b}:Finset ℤ)))
  have hb : b≠m ∧ b∈T := Finset.mem_erase.mp (he ▸ (by simp : b∈({a,b}:Finset ℤ)))
  have hT : T={m,a,b} := by rw [←Finset.insert_erase hm,he]
  have haW : a=m-2*d ∨ a=m-d ∨ a=m+d ∨ a=m+2*d := by
    have hh := hsub ha.2
    simp only [Window,Finset.mem_insert,Finset.mem_singleton] at hh
    omega
  have hbW : b=m-2*d ∨ b=m-d ∨ b=m+d ∨ b=m+2*d := by
    have hh := hsub hb.2
    simp only [Window,Finset.mem_insert,Finset.mem_singleton] at hh
    omega
  rcases haW with rfl|rfl|rfl|rfl <;> rcases hbW with rfl|rfl|rfl|rfl
  all_goals first
  | exact (hab rfl).elim
  | apply Or.inl
    rw [hT]
    all_goals ext x
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton]
    all_goals tauto
  | apply Or.inr; apply Or.inl
    rw [hT]
    all_goals ext x
    all_goals simp only [BadLeft,Finset.mem_insert,Finset.mem_singleton]
    all_goals tauto
  | apply Or.inr; apply Or.inr; apply Or.inl
    rw [hT]
    all_goals ext x
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton]
    all_goals tauto
  | apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    rw [hT]
    all_goals ext x
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton]
    all_goals tauto
  | apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    rw [hT]
    all_goals ext x
    all_goals simp only [BadRight,Finset.mem_insert,Finset.mem_singleton]
    all_goals tauto
  | apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
    rw [hT]
    all_goals ext x
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton]
    all_goals tauto

theorem actual_centered_triple_isAP (m d : ℤ) (hd : 0<d) (T : Finset ℤ)
    (hm : m∈T) (hcard : T.card=3) (hsub : T⊆Window m d)
    (hL : T≠BadLeft m d) (hR : T≠BadRight m d) : IsAP T := by
  rcases centered_triple_six_shapes m d T hm hcard hsub with h|h|h|h|h|h
  · rw [h]
    convert linear_three_isAP (m-2*d) d hd using 1
    ext x
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  · exact False.elim (hL h)
  · rw [h]
    convert linear_three_isAP (m-2*d) (2*d) (by omega) using 1
    ext x
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  · rw [h]
    convert linear_three_isAP (m-d) d hd using 1
    ext x
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  · exact False.elim (hR h)
  · rw [h]
    exact linear_three_isAP m d hd

#print axioms affine_interval_isAP
#print axioms linear_three_isAP
#print axioms window_isAP
#print axioms left_four_isAP
#print axioms right_four_isAP
#print axioms left_four_subset_window
#print axioms right_four_subset_window
#print axioms centered_triple_six_shapes
#print axioms actual_centered_triple_isAP
end
end JSP233.ConstructionGeometry45
