import Erdos272.Resources.BandCredit208
import Erdos272.Resources.NearResidual208
import Erdos272.Resources.BandSystem208

namespace JSP233.CrossBandCredit208
open StarCompletion APGeometry NearAP36 SourceBridge208 ShiftedBlocks208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

abbrev Band := Fin 7

structure System where
  N : ℕ
  D : ℕ
  M : ℕ
  e : ℕ
  F : Finset (Finset ℤ)
  step : Finset ℤ→ℕ
  band : Finset ℤ→Band
  start : Finset ℤ→ℕ
  T : ℕ→Band→ℕ
  E : ℕ→Band→ℕ
  B : ℕ→Band→ℕ
  U : ℕ→Band→ℕ

namespace System
def Piece (s : System) (d : ℕ) (b : Band) : Finset (Finset ℤ) :=
  s.F.filter fun S=>s.step S=d ∧ s.band S=b

def Heavy (s : System) (d : ℕ) (b : Band) : Finset (ℕ×ℕ) :=
  BandSystem208.Heavy s.N d (s.B d b) (s.U d b) (s.E d b) (s.Piece d b) s.start

def HeavyPiece (s : System) (d : ℕ) (b : Band) : Finset (Finset ℤ) :=
  (s.Piece d b).filter fun S=>Code d (s.B d b) (s.start S)∈s.Heavy d b

def G (s : System) : Finset (Finset ℤ) :=
  s.F.filter fun S=>Code (s.step S) (s.B (s.step S) (s.band S)) (s.start S)∈s.Heavy (s.step S) (s.band S)

def Labels (s : System) (d : ℕ) : Finset (Band×(ℕ×ℕ)) :=
  Finset.univ.biUnion fun b=>(s.Heavy d b).image (fun q=>(b,q))

def Label (s : System) (S : Finset ℤ) : Band×(ℕ×ℕ) :=
  (s.band S,Code (s.step S) (s.B (s.step S) (s.band S)) (s.start S))

def Windows (s : System) (d : ℕ) : Finset ℤ :=
  Finset.univ.biUnion fun b=>(s.Heavy d b).biUnion
    (ClippedWindows208.Window s.N d (s.B d b) (s.U d b+s.B d b-3))

def Light (s : System) (d : ℕ) (b : Band) : ℝ :=
  LightPrice208.Closed s.N d (s.T d b) (s.E d b) (s.B d b) (s.U d b+s.B d b-3)

def Core (s : System) (S : Finset ℤ) : Finset ℤ :=
  Grid (s.start S) (s.step S) (MaxAPSize S)

theorem piece_subset (s : System) (d : ℕ) (b : Band) : s.Piece d b⊆s.F :=
  Finset.filter_subset _ _

theorem g_subset (s : System) : s.G⊆s.F := Finset.filter_subset _ _

theorem piece_legal (s : System) (hF : Legal (Ground s.N) s.F) (d : ℕ) (b : Band) :
    Legal (Ground s.N) (s.Piece d b) :=
  ⟨fun S hS=>hF.1 S (s.piece_subset d b hS),
    fun S hS T hT hST=>hF.2 S (s.piece_subset d b hS) T (s.piece_subset d b hT) hST⟩

theorem heavy_piece_eq (s : System) (d : ℕ) (b : Band) :
    s.G.filter (fun S=>s.step S=d ∧ s.band S=b)=s.HeavyPiece d b := by
  ext S
  by_cases hd : s.step S=d <;> by_cases hb : s.band S=b <;>
    simp [G,HeavyPiece,Piece,Finset.mem_filter,hd,hb]

theorem card_partition (s : System)
    (hstep : ∀S∈s.F,s.step S∈Finset.Icc 1 s.D) :
    s.F.card=∑d∈Finset.Icc 1 s.D,∑b : Band,(s.Piece d b).card := by
  rw [Finset.card_eq_sum_card_fiberwise hstep]
  apply Finset.sum_congr rfl
  intro d hd
  have hb := Finset.card_eq_sum_card_fiberwise
    (s := s.F.filter fun S=>s.step S=d) (t := (Finset.univ : Finset Band))
    (f := s.band) (fun S hS=>Finset.mem_univ _)
  simpa only [Piece,Finset.filter_filter,and_assoc] using hb

theorem g_card_partition (s : System)
    (hstep : ∀S∈s.F,s.step S∈Finset.Icc 1 s.D) :
    s.G.card=∑d∈Finset.Icc 1 s.D,∑b : Band,(s.HeavyPiece d b).card := by
  have hp := s.card_partition hstep
  have hgstep : ∀S∈s.G,s.step S∈Finset.Icc 1 s.D := fun S hS=>hstep S (s.g_subset hS)
  rw [Finset.card_eq_sum_card_fiberwise hgstep]
  apply Finset.sum_congr rfl
  intro d hd
  have hb := Finset.card_eq_sum_card_fiberwise
    (s := s.G.filter fun S=>s.step S=d) (t := (Finset.univ : Finset Band))
    (f := s.band) (fun S hS=>Finset.mem_univ _)
  rw [hb]
  apply Finset.sum_congr rfl
  intro b hb
  have he : (s.G.filter fun S=>s.step S=d).filter (fun S=>s.band S=b)=s.HeavyPiece d b := by
    rw [Finset.filter_filter]
    exact s.heavy_piece_eq d b
  rw [he]

theorem labels_card (s : System) (d : ℕ) :
    (s.Labels d).card=∑b : Band,(s.Heavy d b).card := by
  unfold Labels
  rw [Finset.card_biUnion (by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro q hq hqc
    obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hq
    obtain ⟨v,hv,he'⟩ := Finset.mem_image.mp hqc
    exact hbc (congrArg Prod.fst (he.trans he'.symm)))]
  apply Finset.sum_congr rfl
  intro b hb
  exact Finset.card_image_of_injective _ (fun u v he=>congrArg Prod.snd he)

theorem label_mem (s : System) {S : Finset ℤ} (hS : S∈s.G) :
    s.Label S∈s.Labels (s.step S) := by
  obtain ⟨hSF,hH⟩ := Finset.mem_filter.mp hS
  exact Finset.mem_biUnion.mpr ⟨s.band S,Finset.mem_univ _,Finset.mem_image.mpr ⟨_,hH,rfl⟩⟩

theorem windows_card (s : System) (d : ℕ) (Z : Band→ℕ)
    (hZ : ∀b : Band,((s.Heavy d b).biUnion
      (ClippedWindows208.Window s.N d (s.B d b) (s.U d b+s.B d b-3))).card≤Z b) :
    (s.Windows d).card≤min s.N (∑b : Band,Z b) := by
  apply le_min
  · have hsub : s.Windows d⊆Ground s.N := by
      intro x hx
      obtain ⟨b,hb,hxb⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨q,hq,hxq⟩ := Finset.mem_biUnion.mp hxb
      exact (Finset.mem_inter.mp hxq).2
    simpa only [ground_card] using Finset.card_le_card hsub
  · exact (Finset.card_biUnion_le).trans (Finset.sum_le_sum (fun b hb=>hZ b))

/-- The credit and the remaining heavy family refer to the identical pieces. -/
theorem actual_credit_sum (s : System)
    (hstep : ∀S∈s.F,s.step S∈Finset.Icc 1 s.D)
    (hcredit : ∀d∈Finset.Icc 1 s.D,∀b : Band,
      ((s.Piece d b).card : ℝ)+(s.T d b : ℝ)*(s.Heavy d b).card≤
        s.Light d b+(s.HeavyPiece d b).card) :
    (s.F.card : ℝ)+∑d∈Finset.Icc 1 s.D,∑b : Band,(s.T d b : ℝ)*(s.Heavy d b).card≤
      (∑d∈Finset.Icc 1 s.D,∑b : Band,s.Light d b)+(s.G.card : ℝ) := by
  have hp := s.card_partition hstep
  have hg := s.g_card_partition hstep
  have hh := Finset.sum_le_sum (fun d (hd : d∈Finset.Icc 1 s.D)=>
    Finset.sum_le_sum (s := (Finset.univ : Finset Band)) (fun b hb=>hcredit d hd b))
  have hpR : (s.F.card : ℝ)=∑d∈Finset.Icc 1 s.D,∑b : Band,((s.Piece d b).card : ℝ) := by exact_mod_cast hp
  have hgR : (s.G.card : ℝ)=∑d∈Finset.Icc 1 s.D,∑b : Band,((s.HeavyPiece d b).card : ℝ) := by exact_mod_cast hg
  simp only [Finset.sum_add_distrib] at hh
  rw [←hpR,←hgR] at hh
  exact hh
end System

#print axioms System.card_partition
#print axioms System.g_card_partition
#print axioms System.labels_card
#print axioms System.windows_card
#print axioms System.actual_credit_sum
end
end JSP233.CrossBandCredit208
