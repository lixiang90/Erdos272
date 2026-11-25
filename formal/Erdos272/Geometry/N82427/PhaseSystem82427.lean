module

public import Erdos272.Geometry.N82427.PhaseDefs82427
public import Erdos272.Resources.CrossBandCleanup208

@[expose] public section

namespace JSP233.PhaseSystem82427
open StarCompletion APGeometry NearAP36 SourceBridge208 ShiftedBlocks208
open CrossBandCredit208 CrossBandCleanup208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Refined (s : System) (d : ℕ) (b : Band) : Prop := 2 ≤ s.E d b ∧ 3 ≤ s.B d b

def Heavy (s : System) (d : ℕ) (b : Band) : Finset (ℕ × ℕ) :=
  if Refined s d b then
    PhaseDefs82427.Heavy s.N d (s.B d b) (s.U d b) (s.E d b) (s.Piece d b) s.start
  else CrossBandCredit208.System.Heavy s d b

def HeavyPiece (s : System) (d : ℕ) (b : Band) : Finset (Finset ℤ) :=
  (s.Piece d b).filter fun S => Code d (s.B d b) (s.start S) ∈ Heavy s d b

def G (s : System) : Finset (Finset ℤ) :=
  s.F.filter fun S => Code (s.step S) (s.B (s.step S) (s.band S)) (s.start S) ∈
    Heavy s (s.step S) (s.band S)

def Labels (s : System) (d : ℕ) : Finset (Band × (ℕ × ℕ)) :=
  Finset.univ.biUnion fun b => (Heavy s d b).image (fun q => (b, q))

def Windows (s : System) (d : ℕ) : Finset ℤ :=
  Finset.univ.biUnion fun b => (Heavy s d b).biUnion
    (ClippedWindows208.Window s.N d (s.B d b) (s.U d b+s.B d b-3))

def Light (s : System) (d : ℕ) (b : Band) : ℝ :=
  if s.E d b ≤ 1 then 0 else if Refined s d b then
    PhaseDefs82427.Price s.N d (s.T d b) (s.E d b) (s.B d b) (s.U d b+s.B d b-3)
  else CrossBandCredit208.System.Light s d b

theorem g_subset (s : System) : G s ⊆ s.F := Finset.filter_subset _ _

theorem heavy_piece_eq (s : System) (d : ℕ) (b : Band) :
    (G s).filter (fun S => s.step S=d ∧ s.band S=b)=HeavyPiece s d b := by
  ext S
  by_cases hd : s.step S=d <;> by_cases hb : s.band S=b <;>
    simp [G, HeavyPiece, System.Piece, Finset.mem_filter, hd, hb]

theorem g_card_partition (s : System)
    (hstep : ∀ S ∈ s.F, s.step S ∈ Finset.Icc 1 s.D) :
    (G s).card=∑ d ∈ Finset.Icc 1 s.D, ∑ b : Band, (HeavyPiece s d b).card := by
  have hgstep : ∀ S ∈ G s, s.step S ∈ Finset.Icc 1 s.D :=
    fun S hS => hstep S (g_subset s hS)
  rw [Finset.card_eq_sum_card_fiberwise hgstep]
  apply Finset.sum_congr rfl
  intro d hd
  have hb := Finset.card_eq_sum_card_fiberwise
    (s := (G s).filter fun S => s.step S=d) (t := (Finset.univ : Finset Band))
    (f := s.band) (fun S hS => Finset.mem_univ _)
  rw [hb]
  apply Finset.sum_congr rfl
  intro b hb
  have he : ((G s).filter fun S => s.step S=d).filter (fun S => s.band S=b)=HeavyPiece s d b := by
    rw [Finset.filter_filter]
    exact heavy_piece_eq s d b
  rw [he]

theorem labels_card (s : System) (d : ℕ) :
    (Labels s d).card=∑ b : Band, (Heavy s d b).card := by
  unfold Labels
  rw [Finset.card_biUnion (by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro q hq hqc
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hq
    obtain ⟨v, hv, he'⟩ := Finset.mem_image.mp hqc
    exact hbc (congrArg Prod.fst (he.trans he'.symm)))]
  apply Finset.sum_congr rfl
  intro b hb
  exact Finset.card_image_of_injective _ (fun u v he => congrArg Prod.snd he)

theorem label_mem (s : System) {S : Finset ℤ} (hS : S ∈ G s) :
    s.Label S ∈ Labels s (s.step S) := by
  obtain ⟨hSF, hH⟩ := Finset.mem_filter.mp hS
  exact Finset.mem_biUnion.mpr ⟨s.band S, Finset.mem_univ _,
    Finset.mem_image.mpr ⟨_, hH, rfl⟩⟩

theorem windows_card (s : System) (d : ℕ) (Z : Band → ℕ)
    (hZ : ∀ b : Band, ((Heavy s d b).biUnion
      (ClippedWindows208.Window s.N d (s.B d b) (s.U d b+s.B d b-3))).card ≤ Z b) :
    (Windows s d).card ≤ min s.N (∑ b : Band, Z b) := by
  apply le_min
  · have hsub : Windows s d ⊆ Ground s.N := by
      intro x hx
      obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨q, hq, hxq⟩ := Finset.mem_biUnion.mp hxb
      exact (Finset.mem_inter.mp hxq).2
    simpa only [ground_card] using Finset.card_le_card hsub
  · exact (Finset.card_biUnion_le).trans (Finset.sum_le_sum (fun b hb => hZ b))

theorem credit_sum (s : System)
    (hstep : ∀ S ∈ s.F, s.step S ∈ Finset.Icc 1 s.D)
    (hcredit : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : Band,
      ((s.Piece d b).card : ℝ)+(s.T d b : ℝ)*(Heavy s d b).card ≤
        Light s d b+(HeavyPiece s d b).card) :
    (s.F.card : ℝ)+(∑ d ∈ Finset.Icc 1 s.D, ∑ b : Band, (s.T d b : ℝ)*(Heavy s d b).card) ≤
      (∑ d ∈ Finset.Icc 1 s.D, ∑ b : Band, Light s d b)+(G s).card := by
  have hp := s.card_partition hstep
  have hg := g_card_partition s hstep
  have hh := Finset.sum_le_sum (fun d (hd : d ∈ Finset.Icc 1 s.D) =>
    Finset.sum_le_sum (s := (Finset.univ : Finset Band)) (fun b hb => hcredit d hd b))
  have hpR : (s.F.card : ℝ)=∑ d ∈ Finset.Icc 1 s.D, ∑ b : Band, ((s.Piece d b).card : ℝ) := by exact_mod_cast hp
  have hgR : ((G s).card : ℝ)=∑ d ∈ Finset.Icc 1 s.D, ∑ b : Band, ((HeavyPiece s d b).card : ℝ) := by exact_mod_cast hg
  simp only [Finset.sum_add_distrib] at hh
  rw [←hpR, ←hgR] at hh
  exact hh

#print axioms g_subset
#print axioms heavy_piece_eq
#print axioms g_card_partition
#print axioms labels_card
#print axioms label_mem
#print axioms windows_card
#print axioms credit_sum
end
end JSP233.PhaseSystem82427
