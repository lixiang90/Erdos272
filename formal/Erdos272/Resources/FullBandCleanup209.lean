import Erdos272.Resources.FullBandCredit209
import Erdos272.Resources.NearCapped209

namespace JSP233.FullBandCleanup209
open StarCompletion APGeometry NearAP36 SourceBridge208 ShiftedBlocks208
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208 CrossBandMenu208
open FullBandGeometry209 FullBandCredit209
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 200000

def Labels (s : System) (d : ℕ) : Finset (Band×(ℕ×ℕ)) :=
  Finset.univ.biUnion fun b=>(Full s d b).image (fun q=>(b,q))
def Windows (s : System) (d : ℕ) : Finset ℤ :=
  Finset.univ.biUnion fun b=>(Full s d b).biUnion
    (ClippedWindows208.Window s.N d (s.B d b) (SizeV s d b))
def Raw (s : System) (d : ℕ) (b : Band) : ℕ :=
  ((Full s d b).biUnion (ClippedWindows208.Window s.N d (s.B d b) (SizeV s d b))).card
def LightTotal (s : System) : ℝ := ∑d∈Finset.Icc 1 s.D,∑b : Band,EffectiveLight s d b
def CleanupTotal (s : System) : ℝ :=
  ((∑d∈Finset.Icc 1 s.D,(∑b : Band,(Full s d b).card)*
    ((∑b : Band,Raw s d b)+(s.e-1)) : ℕ) : ℝ)
def MiddleTotal (s : System) : ℝ := ∑d∈Finset.Icc 1 s.D,∑b : Band,(MiddleFee s d b : ℝ)

theorem family_subset (s : System) : FullFamily s⊆s.F := Finset.filter_subset _ _
theorem old_family_subset (s : System) : FullFamily s⊆s.G := by
  intro S hS
  obtain ⟨hSF,hfull⟩:=Finset.mem_filter.mp hS
  exact Finset.mem_filter.mpr ⟨hSF,full_subset s (s.step S) (s.band S) hfull⟩

theorem full_piece_eq (s : System) (d : ℕ) (b : Band) :
    (FullFamily s).filter (fun S=>s.step S=d ∧ s.band S=b)=FullPiece s d b := by
  ext S
  by_cases hd : s.step S=d <;> by_cases hb : s.band S=b <;>
    simp [FullFamily,FullPiece,System.Piece,hd,hb]

theorem family_card (s : System) (v : Valid s) :
    (FullFamily s).card=∑d∈Finset.Icc 1 s.D,∑b : Band,(FullPiece s d b).card := by
  have hstep : ∀S∈FullFamily s,s.step S∈Finset.Icc 1 s.D := fun S hS=>v.step_range S (family_subset s hS)
  rw [Finset.card_eq_sum_card_fiberwise hstep]
  apply Finset.sum_congr rfl
  intro d hd
  have hb:=Finset.card_eq_sum_card_fiberwise
    (s := (FullFamily s).filter fun S=>s.step S=d) (t := (Finset.univ : Finset Band))
    (f := s.band) (fun S hS=>Finset.mem_univ _)
  rw [hb]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.filter_filter,full_piece_eq]

theorem labels_card (s : System) (d : ℕ) : (Labels s d).card=∑b : Band,(Full s d b).card := by
  unfold Labels
  rw [Finset.card_biUnion (by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro q hq hqc
    obtain ⟨u,hu,he⟩:=Finset.mem_image.mp hq
    obtain ⟨v,hv,he'⟩:=Finset.mem_image.mp hqc
    exact hbc (congrArg Prod.fst (he.trans he'.symm)))]
  apply Finset.sum_congr rfl
  intro b hb
  exact Finset.card_image_of_injective _ (fun u v he=>congrArg Prod.snd he)

theorem label_mem (s : System) {S : Finset ℤ} (hS : S∈FullFamily s) : s.Label S∈Labels s (s.step S) := by
  have hh:=(Finset.mem_filter.mp hS).2
  exact Finset.mem_biUnion.mpr ⟨s.band S,Finset.mem_univ _,Finset.mem_image.mpr ⟨_,hh,rfl⟩⟩

theorem core_in_windows (s : System) (v : Valid s) {S : Finset ℤ} (hS : S∈FullFamily s) :
    s.Core S⊆Windows s (s.step S) := by
  have hSF:=family_subset s hS
  let d:=s.step S
  let b:=s.band S
  have hd:=v.step_range S hSF
  have hd0 : 0<d := by have := (Finset.mem_Icc.mp hd).1;dsimp only [d];omega
  have hM:=v.M_le d hd b
  have heM:=v.eM
  have he2:=v.e_two
  have hw:=BandGeometry208.actual_band_windows (s.piece_legal v.legal d b) hd0
    (by omega : 2≤s.T d b) (v.ET d hd b).le (v.B_two d hd b) s.start
    (fun R hR=>v.crooked R (s.piece_subset d b hR)) (v.low d hd b) (v.high d hd b)
    (v.small d hd b) (fun R hR=>v.piece_sub hR) S (v.self_piece hSF)
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,Finset.mem_biUnion.mpr
    ⟨Code d (s.B d b) (s.start S),(Finset.mem_filter.mp hS).2,hw.1 hx⟩⟩

/-- The capped residual is paid once on the union of the genuine full-heavy
pieces, with `(band,Code)` labels and their actual windows. -/
theorem actual_heavy_cleanup (s : System) (v : Valid s) {c : ℕ}
    (hc : 1≤c) (hce : c<s.e) (hshort : 3*c<2*s.M) :
    ((FullFamily s).card : ℝ)≤(s.N : ℝ)^2*NearCapped209.Price s.M s.e c+CleanupTotal s := by
  have hG : Legal (Ground s.N) (FullFamily s) :=
    ⟨fun S hS=>v.legal.1 S (family_subset s hS),
      fun S hS T hT hST=>v.legal.2 S (family_subset s hS) T (family_subset s hT) hST⟩
  have hstep : ∀S∈FullFamily s,s.step S∈Finset.Icc 1 s.D := fun S hS=>v.step_range S (family_subset s hS)
  have heM:=v.eM
  have he2:=v.e_two
  have hAP : ∀S∈FullFamily s,∃a : ℤ,APAt (s.step S : ℤ) a (s.Core S) := by
    intro S hS
    exact ⟨s.start S,grid_APAt _ _ _ (by have := (Finset.mem_Icc.mp (hstep S hS)).1;omega)⟩
  have hne : ∀S∈FullFamily s,(s.Core S).Nonempty := by
    intro S hS
    apply Finset.card_pos.mp
    rw [v.core_card (family_subset s hS)]
    have hs:=v.size (family_subset s hS)
    have hm:=two_le_maxAPSize (show 2≤S.card by omega)
    omega
  have hmax : ∀S∈FullFamily s,∀R : Finset ℤ,IsAP R→R⊆S→R.card≤(s.Core S).card := by
    intro S hS R hR hRS
    rw [v.core_card (family_subset s hS)]
    exact AP_card_le_max hR hRS
  have hsmall : ∀S∈FullFamily s,(S\s.Core S).card<s.e := by
    intro S hS
    have hSF:=family_subset s hS
    rw [v.remainder hSF]
    exact (v.small _ (v.step_range S hSF) _ S (v.self_piece hSF)).trans_le (v.E_le _ (v.step_range S hSF) _)
  have hp:=NearCapped209.actual_near_payment hG v.e_two v.eM hc hce hshort s.Core s.step hstep
    (fun S hS=>v.sub S (family_subset s hS)) hAP hne hmax
    (fun S hS=>v.size (family_subset s hS)) (fun S hS=>v.crooked S (family_subset s hS)) hsmall
    (Windows s) (fun S hS=>core_in_windows s v hS) s.Label (Labels s) (fun S hS=>label_mem s hS)
    (fun S hS T hT hST hstep hlabel=>v.equal_label_disjoint (old_family_subset s hS) (old_family_subset s hT) hST hstep hlabel)
  have hb : (∑d∈Finset.Icc 1 s.D,(Labels s d).card*((Windows s d).card+(s.e-1)))≤
      ∑d∈Finset.Icc 1 s.D,(∑b : Band,(Full s d b).card)*((∑b : Band,Raw s d b)+(s.e-1)) := by
    apply Finset.sum_le_sum
    intro d hd
    rw [labels_card]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right Finset.card_biUnion_le (s.e-1))
  have hbR : ((∑d∈Finset.Icc 1 s.D,(Labels s d).card*((Windows s d).card+(s.e-1)) : ℕ) : ℝ)≤CleanupTotal s := by
    unfold CleanupTotal
    exact_mod_cast hb
  linarith only [hp,hbR]

theorem actual_credit_sum (s : System) (v : Valid s) :
    (s.F.card : ℝ)+(∑d∈Finset.Icc 1 s.D,∑b : Band,(s.T d b : ℝ)*(Full s d b).card)≤
      LightTotal s+((FullFamily s).card : ℝ)+MiddleTotal s := by
  have hh:=Finset.sum_le_sum (fun d (hd : d∈Finset.Icc 1 s.D)=>
    Finset.sum_le_sum (s := (Finset.univ : Finset Band)) (fun b hb=>actual_full_credit s v hd b))
  have hF : (s.F.card : ℝ)=∑d∈Finset.Icc 1 s.D,∑b : Band,((s.Piece d b).card : ℝ) := by exact_mod_cast s.card_partition v.step_range
  have hG : ((FullFamily s).card : ℝ)=∑d∈Finset.Icc 1 s.D,∑b : Band,((FullPiece s d b).card : ℝ) := by exact_mod_cast family_card s v
  simp only [Finset.sum_add_distrib] at hh
  rw [←hF,←hG] at hh
  exact hh

theorem actual_full_near_bound (s : System) (v : Valid s) {c : ℕ}
    (hc : 1≤c) (hce : c<s.e) (hshort : 3*c<2*s.M) :
    (s.F.card : ℝ)≤LightTotal s+(s.N : ℝ)^2*NearCapped209.Price s.M s.e c+CleanupTotal s+MiddleTotal s := by
  have hcredit:=actual_credit_sum s v
  have hheavy:=actual_heavy_cleanup s v hc hce hshort
  have hnonneg : (0 : ℝ)≤∑d∈Finset.Icc 1 s.D,∑b : Band,(s.T d b : ℝ)*(Full s d b).card := by positivity
  linarith only [hcredit,hheavy,hnonneg]

#print axioms actual_heavy_cleanup
#print axioms actual_credit_sum
#print axioms actual_full_near_bound
end
end JSP233.FullBandCleanup209
