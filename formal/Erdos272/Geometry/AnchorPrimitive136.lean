module

public import Erdos272.Resources.FarCapacity112
public import Erdos272.Resources.FarJoint112

@[expose] public section
namespace JSP233.AnchorPrimitive136
open StarCompletion APGeometry FarSlot112 FarCapacity112 LongTerminal35
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Piece (g d x a:ℤ) : Finset ℤ := Segment g x (min a x) (max (a+d) x)
def Coverable (S:Finset ℤ) (d x a:ℤ) : Prop :=
  ∃R:Finset ℤ,IsAP R ∧ insert a {a+d,x}⊆R ∧ R⊆S

theorem gcd_anchor_invariant {d x a p:ℤ} (hda:d∣a-p) :
    Int.gcd d (x-a)=Int.gcd d (x-p) := by
  apply Int.gcd_right_eq_iff.mpr
  intro c hcd
  have hcap:c∣a-p:=dvd_trans hcd hda
  constructor
  · intro hc
    rw [show x-p=(x-a)+(a-p) by ring]
    exact dvd_add hc hcap
  · intro hc
    rw [show x-a=(x-p)-(a-p) by ring]
    exact dvd_sub hc hcap

theorem piece_APAt {g d x a:ℤ} (hg:0<g) : APAt g x (Piece g d x a) :=
  segment_APAt hg

theorem piece_contains_shell (g d x a:ℤ) : x∈Piece g d x a := by
  exact mem_segment.mpr ⟨min_le_right _ _,le_max_right _ _,by simp⟩

theorem piece_contains_edge {g d x a:ℤ} (hd:0<d) (hga:g∣a-x) (hgd:g∣d) :
    a∈Piece g d x a ∧ a+d∈Piece g d x a := by
  constructor
  · exact mem_segment.mpr ⟨min_le_left _ _,(by omega:a≤a+d).trans (le_max_left _ _),hga⟩
  · exact mem_segment.mpr ⟨(min_le_left _ _).trans (by omega:a≤a+d),le_max_left _ _,by
      rw [show a+d-x=(a-x)+d by ring]
      exact dvd_add hga hgd⟩

theorem piece_subset_of_coverable {S:Finset ℤ} {d p x a:ℤ}
    (hda:d∣a-p) (hcover:Coverable S d x a) :
    Piece (Int.gcd d (x-p):ℤ) d x a⊆S := by
  obtain ⟨R,hR,hpoints,hRS⟩:=hcover
  have ha:a∈R:=hpoints (by simp)
  have hb:a+d∈R:=hpoints (by simp)
  have hx:x∈R:=hpoints (by simp)
  have hh:=primitive_segment_subset hR ha hb ha hb hx
  rw [gcd_anchor_invariant hda] at hh
  intro y hy
  apply hRS
  apply hh
  obtain ⟨hyl,hyr,hyg⟩:=mem_segment.mp hy
  have hgA:(Int.gcd d (x-p):ℤ)∣a-p:=dvd_trans (Int.gcd_dvd_left d (x-p)) hda
  have hgX:(Int.gcd d (x-p):ℤ)∣x-a:=by
    rw [show x-a=(x-p)-(a-p) by ring]
    exact dvd_sub (Int.gcd_dvd_right d (x-p)) hgA
  exact mem_segment.mpr ⟨hyl,hyr,by
    rw [show y-a=(y-x)+(x-a) by ring]
    exact dvd_add hyg hgX⟩

theorem two_pieces_APAt {g d x a b:ℤ} (hg:0<g) :
    APAt g x (Piece g d x a∪Piece g d x b) := by
  simpa only [APAt,Finset.mem_union] using
    PrivateUnion.union_APAt g x (fun y=>y∈Piece g d x a) (fun y=>y∈Piece g d x b)
      (piece_APAt hg) (piece_APAt hg) (piece_contains_shell g d x a) (piece_contains_shell g d x b)

theorem two_coverable_pieces {S:Finset ℤ} {d p x a b:ℤ} (hd:0<d)
    (hda:d∣a-p) (hdb:d∣b-p) (ha:Coverable S d x a) (hb:Coverable S d x b) :
    let g:ℤ:=Int.gcd d (x-p)
    (Piece g d x a∪Piece g d x b)⊆S ∧ IsAP (Piece g d x a∪Piece g d x b) := by
  dsimp only
  have hg:0<(Int.gcd d (x-p):ℤ):=by
    exact_mod_cast Int.gcd_pos_of_ne_zero_left (x-p) hd.ne'
  refine ⟨Finset.union_subset (piece_subset_of_coverable hda ha) (piece_subset_of_coverable hdb hb),?_⟩
  exact (isAP_iff_exists_APAt _).mpr ⟨_,x,two_pieces_APAt hg,
    Finset.mem_union_left _ (piece_contains_shell _ d x a)⟩

#print axioms gcd_anchor_invariant
#print axioms piece_APAt
#print axioms piece_contains_shell
#print axioms piece_contains_edge
#print axioms piece_subset_of_coverable
#print axioms two_pieces_APAt
#print axioms two_coverable_pieces
end
end JSP233.AnchorPrimitive136
