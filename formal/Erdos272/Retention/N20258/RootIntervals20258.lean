module

public import Erdos272.Retention.N20258.RootProgressions20258
public import Erdos272.Retention.LongTerminal35

@[expose] public section
namespace JSP233.RootIntervals20258
open StarCompletion APGeometry APCount41 DenseDeletion40 LongTerminal35
open scoped Classical
noncomputable section
set_option autoImplicit false

theorem actual_intervals {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : RootModel291012.Start N c L R F P T)
    (unit : ∀ S ∈ F, IsAP S → (c : ℤ) ∉ S → Step S=1) :
    ∀ S ∈ Avoiders (Retained N 12 F) (c : ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b) := by
  intro S hs
  obtain ⟨ret,miss⟩ := Finset.mem_filter.mp hs
  have hF := (Finset.mem_sdiff.mp ret).1
  have ap : IsAP S := by by_contra h; exact miss (g.root S ret h)
  obtain ⟨_,p,hp⟩ := actual_step ap
  rw [unit S hF ap miss,Nat.cast_one] at hp
  have ne := isAP_nonempty ap
  have low := low_spec ne
  have high := high_spec ne
  have lowN := (mem_ground N _).mp (g.legal.1 S hF low.1)
  have highN := (mem_ground N _).mp (g.legal.1 S hF high.1)
  obtain ⟨⟨u,hu,ul⟩,v,hv,rv⟩ := g.outside S ret miss
  have ll := (low.2 _ hu).trans ul
  have rh := rv.trans (high.2 _ hv)
  have cr := g.root_left.le.trans g.left_right
  have ca : (c : ℤ) < Low S := by
    by_contra h
    exact miss (apAt_fill hp low.1 high.1 (by omega) (by omega) (one_dvd _))
  have a : ((Low S).toNat : ℤ)=Low S := Int.toNat_of_nonneg (by omega)
  have b : ((High S).toNat : ℤ)=High S := Int.toNat_of_nonneg (by omega)
  refine ⟨(Low S).toNat,(High S).toNat,by omega,by omega,by omega,by omega,?_⟩
  ext x
  simp only [Interval,a,b,Finset.mem_Icc]
  exact ⟨fun hx => ⟨low.2 _ hx,high.2 _ hx⟩,
    fun h => apAt_fill hp low.1 high.1 h.1 h.2 (one_dvd _)⟩

theorem actual_core {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : RootModel291012.Start N c L R F P T)
    (iv : ∀ S ∈ Avoiders (Retained N 12 F) (c : ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) :
    ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H := by
  obtain ⟨a,b,_,aL,Rb,_,eq⟩ := iv P (Finset.mem_filter.mpr ⟨g.right_member,g.right_avoids⟩)
  refine ⟨P,(Finset.mem_sdiff.mp g.right_member).1,?_,?_⟩
  · by_contra h
    exact g.right_avoids (g.root P g.right_member h)
  · intro x hx
    rw [eq]
    obtain ⟨lx,xr⟩ := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨(by exact_mod_cast aL : (a : ℤ) ≤ L).trans lx,
      xr.trans (by exact_mod_cast Rb : (R : ℤ) ≤ b)⟩

#print axioms actual_intervals
#print axioms actual_core
end
end JSP233.RootIntervals20258
