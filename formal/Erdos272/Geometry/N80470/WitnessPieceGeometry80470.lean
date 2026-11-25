module

public import Erdos272.Resources.N80470.WitnessCredit80470
public import Erdos272.Geometry.N82427.PhaseCleanup82427

@[expose] public section

namespace JSP233.WitnessPieceGeometry80470
open StarCompletion APGeometry NearAP36 SourceBridge208 ShiftedBlocks208
open CrossBandCredit208 CrossBandCleanup208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Fiber (s : System) (d : ℕ) (b : Band) (q : ℕ × ℕ) : Finset (Finset ℤ) :=
  BandSystem208.Fiber (s.Piece d b) d (s.B d b) s.start q

def Window (s : System) (d : ℕ) (b : Band) (q : ℕ × ℕ) : Finset ℤ :=
  ClippedWindows208.Window s.N d (s.B d b) (s.U d b+s.B d b-3) q

def Hits (s : System) (d : ℕ) (b : Band) (A₀ : Finset ℤ) (q : ℕ × ℕ) : Prop :=
  ((Window s d b q) ∩ A₀).Nonempty

theorem actual_fiber_cap {s : System} (v : Valid s) {d W : ℕ}
    (hd : d ∈ Finset.Icc 1 s.D) (b : Band)
    {F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (hlegal : Legal (Ground s.N) F) (hsub : s.F ⊆ F)
    (hA : A₀ ∈ F) (hW : A₀.card ≤ W) (q : ℕ × ℕ)
    (hmiss : ¬Hits s d b A₀ q) : (Fiber s d b q).card ≤ W := by
  have hd0 : 0 < d := by have := (Finset.mem_Icc.mp hd).1; omega
  have heM := v.eM
  have he2 := v.e_two
  have hM := v.M_le d hd b
  have hET := v.ET d hd b
  have hB := v.B_two d hd b
  have hT : 2 ≤ s.T d b := by omega
  have hmem : ∀ S ∈ Fiber s d b q,
      S ∈ s.Piece d b ∧ Code d (s.B d b) (s.start S)=q := by
    intro S hS
    exact Finset.mem_filter.mp hS
  have hw := BandGeometry208.actual_band_windows (s.piece_legal v.legal d b)
    hd0 hT hET.le hB s.start
    (fun S hS => v.crooked S (s.piece_subset d b hS))
    (v.low d hd b) (v.high d hd b) (v.small d hd b)
    (fun S hS => v.piece_sub hS)
  have hr := BandGeometry208.actual_band_disjoint (s.piece_legal v.legal d b)
    hd0 hT hET.le (by omega : 0 < s.B d b) (v.BA d hd b) s.start
    (fun S hS => v.crooked S (s.piece_subset d b hS))
    (v.low d hd b) (v.high d hd b) (v.small d hd b)
    (fun S hS => v.piece_sub hS) (v.gate d hd b)
  let core : Finset ℤ → Finset ℤ := fun S => Grid (s.start S) d (MaxAPSize S)
  have hHF : Fiber s d b q ⊆ F := by
    intro S hS
    exact hsub (s.piece_subset d b (hmem S hS).1)
  have hcore : ∀ S ∈ Fiber s d b q, core S ⊆ S := by
    intro S hS
    exact v.piece_sub (hmem S hS).1
  have hne : ∀ S ∈ Fiber s d b q, (core S).Nonempty := by
    intro S hS
    apply Finset.card_pos.mp
    dsimp only [core]
    rw [grid_card _ _ _ hd0]
    have hs := v.low d hd b S (hmem S hS).1
    have hm := two_le_maxAPSize (show 2 ≤ S.card by omega)
    omega
  have hwindow : ∀ S ∈ Fiber s d b q, core S ⊆ Window s d b q := by
    intro S hS
    have hh := (hw S (hmem S hS).1).1
    simpa only [Window, (hmem S hS).2] using hh
  have havoid : Disjoint (Window s d b q) A₀ := by
    apply Finset.disjoint_left.mpr
    intro x hxW hxA
    exact hmiss ⟨x, Finset.mem_inter.mpr ⟨hxW,hxA⟩⟩
  have hdisjoint : ∀ S ∈ Fiber s d b q, ∀ T ∈ Fiber s d b q, S≠T →
      Disjoint (S\core S) (T\core T) := by
    intro S hS T hT hST
    exact hr S (hmem S hS).1 T (hmem T hT).1 hST
      ((hmem S hS).2.trans (hmem T hT).2.symm)
  exact (WitnessCredit80470.actual_disjoint_core_fiber_cap core hlegal hHF hA
    hcore hne hwindow havoid hdisjoint).trans hW

#print axioms actual_fiber_cap
end
end JSP233.WitnessPieceGeometry80470
