module

public import Erdos272.Counting.N86412.GapShape86412

@[expose] public section

namespace JSP233.EndTemplate86412
open OrderedFinite86412 GapShape86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem adjacent_choice {S : Finset ℤ} {d : ℤ} {i : ℕ}
    (hshape : GapShape S d) (hi : i+1<S.card) :
    ∃ b : ℕ, b≤1 ∧ point S (i+1)-point S i=((1+b : ℕ) : ℤ)*d := by
  have hg := hshape (point S i) (FarShort112.point_mem (by omega))
    (point S (i+1)) (FarShort112.point_mem hi)
    (FarShort112.point_strict (by omega) hi) (consecutive_no_between hi)
  rcases hg with hg | ⟨hg, _⟩
  · exact ⟨0, by omega, by simpa using hg⟩
  · exact ⟨1, by omega, by simpa using hg⟩

theorem interior_gap {S : Finset ℤ} {d : ℤ} {i : ℕ}
    (hshape : GapShape S d) (hleft : 1 ≤ i) (hright : i + 2 < S.card) :
    point S (i+1)-point S i=d := by
  rcases hshape (point S i) (FarShort112.point_mem (by omega))
    (point S (i+1)) (FarShort112.point_mem (by omega))
    (FarShort112.point_strict (by omega) (by omega))
    (consecutive_no_between (by omega)) with hh | ⟨_, hedge⟩
  · exact hh
  · rcases hedge with hmin | hmax
    · have hbefore : point S 0 < point S i :=
        FarShort112.point_strict (S := S) (by omega : 0 < i)
        (by omega : i < S.card)
      have hh := hmin (point S 0) (FarShort112.point_mem (by omega))
      omega
    · have hafter : point S (i+1) < point S (i+2) :=
        FarShort112.point_strict (S := S) (by omega : i + 1 < i + 2) hright
      have hh := hmax (point S (i+2)) (FarShort112.point_mem hright)
      omega

theorem interior_points {S : Finset ℤ} {d : ℤ} {l : ℕ}
    (hshape : GapShape S d)
    (hfirst : point S 1-point S 0=((1+l : ℕ) : ℤ)*d) :
    ∀ i : ℕ, i<S.card-2 →
      point S (i+1)=point S 0+((i+1+l : ℕ) : ℤ)*d := by
  intro i
  induction i with
  | zero =>
    intro hi
    simpa only [Nat.zero_add] using (sub_eq_iff_eq_add.mp hfirst).trans (by ring)
  | succ i ih =>
    intro hi
    have hp := ih (by omega)
    have hg := interior_gap hshape (by omega : 1 ≤ i + 1) (by omega : i + 1 + 2 < S.card)
    norm_num only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at hp hg ⊢
    nlinarith only [hp, hg]

theorem last_point {S : Finset ℤ} {d : ℤ} {l r : ℕ}
    (hS : 4≤S.card) (hshape : GapShape S d)
    (hfirst : point S 1-point S 0=((1+l : ℕ) : ℤ)*d)
    (hlast : point S (S.card-1)-point S (S.card-2)=((1+r : ℕ) : ℤ)*d) :
    point S (S.card-1)=point S 0+((S.card-1+l+r : ℕ) : ℤ)*d := by
  have hp := interior_points hshape hfirst (S.card-3) (by omega)
  have he : S.card-3+1=S.card-2 := by omega
  rw [he] at hp
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : 2≤S.card),
    Nat.cast_sub (by omega : 1≤S.card)] at hp hlast ⊢
  nlinarith only [hp, hlast]

theorem gap_shape_template {S : Finset ℤ} {d : ℤ}
    (hd : 0<d) (hshape : GapShape S d) (hS : 4≤S.card) :
    ∃ a : ℤ, ∃ l r : ℕ, l≤1 ∧ r≤1 ∧
      S=insert a (insert (a+((S.card-1+l+r : ℕ) : ℤ)*d)
        (Grid (a+((1+l : ℕ) : ℤ)*d) d (S.card-2))) := by
  obtain ⟨l, hl, hfirst⟩ := adjacent_choice hshape (by omega : 0+1<S.card)
  obtain ⟨r, hr, hlast⟩ := adjacent_choice hshape (by omega : S.card-2+1<S.card)
  have he : S.card-2+1=S.card-1 := by omega
  rw [he] at hlast
  have hlast' := last_point hS hshape hfirst hlast
  refine ⟨point S 0, l, r, hl, hr, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := point_surjective hx
    by_cases hzero : i=0
    · subst i
      exact Finset.mem_insert_self _ _
    by_cases hend : i=S.card-1
    · subst i
      rw [hlast']
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    apply mem_grid.mpr
    refine ⟨i-1, by omega, ?_⟩
    have hp := interior_points hshape hfirst (i-1) (by omega)
    have hei : i-1+1=i := by omega
    rw [hei] at hp
    rw [hp]
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : 1 ≤ i)]
    ring
  · intro hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]
      exact FarShort112.point_mem (by omega)
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [← hlast'] at hx
      rw [hx]
      exact FarShort112.point_mem (by omega)
    obtain ⟨i, hi, hx⟩ := mem_grid.mp hx
    have hp := interior_points hshape hfirst i hi
    have heq : point S 0+((1+l : ℕ) : ℤ)*d+(i : ℤ)*d=point S (i+1) := by
      rw [hp]
      push_cast
      ring
    rw [heq] at hx
    rw [hx]
    exact FarShort112.point_mem (by omega)

#print axioms adjacent_choice
#print axioms interior_gap
#print axioms interior_points
#print axioms last_point
#print axioms gap_shape_template
end
end JSP233.EndTemplate86412
