import Erdos272.Resources.CrossBandCleanup208

namespace JSP233.CrossBandMenu208
open StarCompletion CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def SourceA (s : System) (d : ℕ) (b : Band) : ℕ := s.T d b-s.E d b
def SizeV (s : System) (d : ℕ) (b : Band) : ℕ := s.U d b+s.B d b-3
def Low (s : System) (d : ℕ) (b : Band) : ℕ :=
  (s.N/d-(SizeV s d b-s.E d b-1)+s.B d b-1)/s.B d b
def High (s : System) (d : ℕ) (b : Band) : ℕ := (s.N/d-SourceA s d b)/s.B d b

def CountBound (s : System) (d : ℕ) (b : Band) : ℕ :=
  if SourceA s d b≤s.N/d then
    HeavyMenu208.OrdinaryCount (s.N/d) (s.B d b) (SizeV s d b) (SizeV s d b-s.E d b)+
      (High s d b+1-Low s d b) else 0

def UnionBound (s : System) (d : ℕ) (b : Band) : ℕ :=
  if SourceA s d b≤s.N/d then
    HeavyMenu208.OrdinaryUnion (s.N/d) (s.B d b) (SizeV s d b) (SizeV s d b-s.E d b)+
      ∑r∈Finset.Icc (Low s d b) (High s d b),min (SizeV s d b) (s.N/d-r*s.B d b+1) else 0

theorem actual_menu_bounds (s : System) (v : Valid s) {d : ℕ}
    (hd : d∈Finset.Icc 1 s.D) (b : Band) :
    (s.Heavy d b).card≤CountBound s d b ∧
      ((s.Heavy d b).biUnion (ClippedWindows208.Window s.N d (s.B d b) (SizeV s d b))).card≤UnionBound s d b := by
  by_cases hE0 : s.E d b=0
  · have hp : s.Piece d b=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      have hh := v.small d hd b S hS
      omega
    have hh : s.Heavy d b=∅ := by simp only [System.Heavy,BandSystem208.Heavy,hp,Finset.image_empty,Finset.filter_empty]
    simp only [hh,Finset.card_empty,Finset.biUnion_empty,Nat.zero_le,and_self]
  · have hE : 1≤s.E d b := by omega
    have heM := v.eM
    have he2 := v.e_two
    have hM := v.M_le d hd b
    have hET := v.ET d hd b
    have hTU := v.TU d hd b
    have hB := v.B_two d hd b
    have hd0 : 0<d := by have := (Finset.mem_Icc.mp hd).1;omega
    have hp := BandSystem208.actual_properties (s.piece_legal v.legal d b) hd0
      (by omega : 2≤s.T d b) hET.le hE hTU hB (v.BA d hd b) s.start
      (fun S hS=>v.crooked S (s.piece_subset d b hS))
      (v.low d hd b) (v.high d hd b) (v.small d hd b) (fun S hS=>v.piece_sub hS) (v.gate d hd b)
    by_cases hAq : SourceA s d b≤s.N/d
    · have hm := HeavyMenu208.actual_menu hd0 (by omega : 0<s.B d b)
        (by dsimp only [SizeV];omega : 0<SizeV s d b)
        (by dsimp only [SizeV];omega : s.E d b<SizeV s d b) hAq
        hp.residue hp.feasible hp.injective hp.ordinary_pair
      simp only [CountBound,UnionBound,if_pos hAq]
      simpa only [Low,High,SourceA,SizeV,System.Heavy] using hm
    · have hh : s.Heavy d b=∅ := HeavyMenu208.actual_extinction hp.feasible (by
        change s.N/d<s.T d b-s.E d b
        exact Nat.lt_of_not_ge hAq)
      simp only [hh,Finset.card_empty,Finset.biUnion_empty,CountBound,UnionBound,if_neg hAq,le_refl,and_self]

theorem actual_closed_near_payment (s : System) (v : Valid s) :
    (s.F.card : ℝ)+(∑d∈Finset.Icc 1 s.D,∑b : Band,(s.T d b : ℝ)*(s.Heavy d b).card)≤
      (∑d∈Finset.Icc 1 s.D,∑b : Band,s.Light d b)+
      (s.N : ℝ)^2*ResidualAggregate208.Price s.e (ResidualTwoCensus208.H s.M)+
      (253/35 : ℝ)*s.N+
      ((∑d∈Finset.Icc 1 s.D,(∑b : Band,(s.Heavy d b).card)*
        (min s.N (∑b : Band,UnionBound s d b)+(s.e-1)) : ℕ) : ℝ) := by
  exact actual_near_payment_with_credit s v (UnionBound s)
    (fun d hd b=>(actual_menu_bounds s v hd b).2)

#print axioms actual_menu_bounds
#print axioms actual_closed_near_payment
end
end JSP233.CrossBandMenu208
