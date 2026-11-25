module

public import Erdos272.Counting.N20258.ProgressionPartition20258
public import Erdos272.Counting.N20258.PaddedSource20258
public import Erdos272.Capacity.N88404.SieveCapacity88404
public import Erdos272.Capacity.N88404.SieveClassBounds88404

@[expose] public section
/-! Price the progressions and intrinsic triples of the very same family.
The six selected nonunit strides and the unit class pay their shadows, and
the remaining strides pay the exact tail above the shortest allowed length. -/
namespace JSP233.ProgressionJoint20258
open StarCompletion IntrinsicTriples208 APShadowCapacity16858 APClasses88404
open SieveConstants88404 SieveClassBounds88404 ProgressionPartition20258
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

def error (n : ℝ) : ℝ :=
  606450017/1803601800*n^2 + 13565611/18036018*n + 2403389/5010005

def reciprocal : ℝ := ∑ p ∈ Selected, (1 : ℝ)/(p : ℝ)
def squares : ℝ := ∑ p ∈ Selected, (1 : ℝ)/(4*(p : ℝ)^2)

def response (n g : ℝ) : ℝ := 1+(1+reciprocal)*n+squares*n^2+
  g*(Alpha 1*n^3+6*error n+n*reciprocal)+1/(432*(g*Alpha 1)^2)

theorem actual_joint {N k : ℕ} {F : Finset (Finset ℤ)} {g : ℝ}
    (hN : 14 ≤ N) (hg : 0 < g) (hcap : 3*g*((N : ℝ)-1) ≤ 1) (hF : Legal (Ground N) F)
    (hmin : ∀ d ∈ Finset.Icc 1 (N-1) \ Steps, ∀ S ∈ StepAP F d, k < S.card) :
    ((F.filter IsAP).card : ℝ)+6*g*(∑ S ∈ F, ((Pool S).card : ℝ)) ≤
      (offTail (N-1) k Steps : ℕ)+response ((N : ℝ)-1) g := by
  let n : ℝ := (N : ℝ)-1
  let c := fun p => ((StepAP F p).card : ℝ)
  let s := fun p => ((APShadow (StepAP F p)).card : ℝ)
  have h1 : 1 ≤ N := by omega
  have hsteps : Steps ⊆ Finset.Icc 1 (N-1) := by
    intro p hp
    have hlo := steps_positive hp
    rcases Finset.mem_insert.mp hp with rfl | hsel
    · exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    · have hhi := (selected_range hsel).2
      exact Finset.mem_Icc.mpr ⟨hlo,by omega⟩
  have part := actual_AP_partition h1 hF Steps hsteps hmin
  have ha : ((F.filter IsAP).card : ℝ) ≤
      1+(∑ p ∈ Steps, ((StepAP F p).card : ℝ))+(offTail (N-1) k Steps : ℕ) := by exact_mod_cast part
  have hu := unit_bound h1 hg hF
  change c 1-6*g*Alpha 1*s 1 ≤ (1+g)*n+1/(432*(g*Alpha 1)^2) at hu
  have hs := selected_sum h1 hg hcap hF
  change (∑ p ∈ Selected, c p)-6*g*(∑ p ∈ Selected, Alpha p*s p) ≤
    (1+g)*n*reciprocal+n^2*squares-g*n^3*(1-Alpha 1) at hs
  have hc := mul_le_mul_of_nonneg_left (SieveCapacity88404.actual_capacity_at_span h1 hF) hg.le
  have hnot : 1 ∉ Selected := by norm_num [Selected]
  rw [Steps, Finset.sum_insert hnot] at ha hc
  change ((F.filter IsAP).card : ℝ) ≤ 1+(c 1+∑ p ∈ Selected, c p)+(offTail (N-1) k Steps : ℕ) at ha
  change g*(6*(∑ S ∈ F, ((Pool S).card : ℝ))+
    6*(Alpha 1*s 1+∑ p ∈ Selected, Alpha p*s p)) ≤ g*(n^3-n+6*error n) at hc
  change _ ≤ (offTail (N-1) k Steps : ℕ)+response n g
  unfold response
  linarith only [hu,hs,ha,hc]

/-- Consume a source bound proved on an actual translated family with cutoff
U and combine it with the progression and pool counts on the original N. -/
theorem actual_source_bound {N k U r j : ℕ} {F : Finset (Finset ℤ)} {x h Z : ℝ}
    (hN : 14 ≤ N) (hx : 0 < x) (hspan : (N : ℝ)-1 ≤ 2*x) (hF : Legal (Ground N) F)
    (hmin : ∀ d ∈ Finset.Icc 1 (N-1) \ Steps, ∀ S ∈ StepAP F d, k < S.card)
    (paid : h*((Density41.SparseCrooked U r (AffineLine30.mapFamily j 1 F)).card : ℝ) ≤
      PaddedSource20258.mass (Density41.SparseCrooked U r (AffineLine30.mapFamily j 1 F))+Z)
    (dense : ∀ S ∈ F, ¬IsAP S → U < r*S.card → x ≤ ((Pool S).card : ℝ)) :
    (F.card : ℝ) ≤ (offTail (N-1) k Steps : ℕ)+response ((N : ℝ)-1) (1/(6*x))+
      (1-h/x)*((Density41.SparseCrooked U r F).card : ℝ)+Z/x := by
  let g : ℝ := 1/(6*x)
  have hg : 0 < g := by dsimp only [g]; positivity
  have hscale : 6*g*x = 1 := by dsimp only [g]; field_simp
  have hcap : 3*g*((N : ℝ)-1) ≤ 1 := calc
    _ ≤ 3*g*(2*x) := mul_le_mul_of_nonneg_left hspan (by positivity)
    _ = 1 := by linarith only [hscale]
  have hb := PaddedSource20258.crooked_payment (PaddedSource20258.source_pullback
    (by decide : (0 : ℤ) < 1) paid) dense
  let J : ℝ := (offTail (N-1) k Steps : ℕ)+response ((N : ℝ)-1) g
  have hj := actual_joint hN hg hcap hF hmin
  change ((F.filter IsAP).card : ℝ)+6*g*PaddedSource20258.mass F ≤ J at hj
  have hs := mul_le_mul_of_nonneg_left hj hx.le
  rw [mul_add, show x*(6*g*PaddedSource20258.mass F) = PaddedSource20258.mass F from calc
    _ = (6*g*x)*PaddedSource20258.mass F := by ring
    _ = _ := by rw [hscale,one_mul]] at hs
  have counts : (F.filter IsAP).card + (PrivatePairExistence.CrookedMembers F).card = F.card :=
    Finset.card_filter_add_card_filter_not _
  have hcounts : ((F.filter IsAP).card : ℝ)+(PrivatePairExistence.CrookedMembers F).card = F.card :=
    by exact_mod_cast counts
  change (F.card : ℝ) ≤ J+(1-h/x)*((Density41.SparseCrooked U r F).card : ℝ)+Z/x
  calc
    _ ≤ (x*J+(x-h)*((Density41.SparseCrooked U r F).card : ℝ)+Z)/x := by
      apply (le_div_iff₀ hx).mpr
      rw [← hcounts]
      linarith only [hs,hb]
    _ = _ := by field_simp

end
end JSP233.ProgressionJoint20258
