import Erdos272.Retention.Relative13Fringe116

/-! All traces through a common off-residue point avoid its period class.
The holes are actual points of the physical interval, shared across steps. -/
namespace JSP233.PeriodOff117
open StarCompletion APGeometry
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem interval_period_holes (D h : ℕ) (L R y : ℤ)
    (hD : 0<D) (hsize : (D:ℤ)*h≤R-L+1) :
    ∃H : Finset ℤ,H⊆Finset.Icc L R ∧ H.card=h ∧ ∀z∈H,(D:ℤ)∣z-y := by
  let f : ℕ→ℤ := fun i=>L+(y-L)%(D:ℤ)+(D:ℤ)*i
  have hdZ : (0:ℤ)<D := by exact_mod_cast hD
  have hr0 := Int.emod_nonneg (y-L) (by omega : (D:ℤ)≠0)
  have hrlt := Int.emod_lt_of_pos (y-L) hdZ
  have he := Int.emod_add_mul_ediv (y-L) (D:ℤ)
  refine ⟨(Finset.range h).image f,?_,?_,?_⟩
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have hiZ : (i:ℤ)+1≤h := by exact_mod_cast (show i+1≤h from Finset.mem_range.mp hi)
    have hm := mul_le_mul_of_nonneg_left hiZ hdZ.le
    dsimp only [f]
    have hm0 : (0:ℤ)≤(D:ℤ)*(i:ℤ) := mul_nonneg hdZ.le (Int.natCast_nonneg i)
    exact Finset.mem_Icc.mpr ⟨by omega,by nlinarith only [hm,hsize,hrlt]⟩
  · have hinj : Function.Injective f := by
      intro i j hij
      dsimp only [f] at hij
      have hi : (i:ℤ)=(j:ℤ) := by nlinarith only [hij,hdZ]
      exact_mod_cast hi
    rw [Finset.card_image_of_injective _ hinj,Finset.card_range]
  · intro z hz
    obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hz
    refine ⟨(i:ℤ)-(y-L)/(D:ℤ),?_⟩
    dsimp only [f]
    nlinarith only [he]

theorem actual_off_point_capacity_pred {N L R p D h : ℕ} {F : Finset (Finset ℤ)}
    (d a : Finset ℤ→ℤ) (y : ℤ)
    (hLR : L≤R) (hp : 0<p) (hD : 0<D)
    (hbudget : h+p=p.choose 2) (hsize : D*h≤R-L+1)
    (hlegal : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S) (a S) (S∩Finset.Icc (L:ℤ) (R:ℤ)))
    (hsteps : ∀S∈F,d S∣(D:ℤ))
    (hlong : ∀S∈F,(R-L+1)/p+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    (OffResidue44.OffPoint F d a y).card≤p-1 := by
  by_contra hn
  obtain ⟨C,hCE,hCc⟩ := Finset.exists_subset_card_eq
    (show p≤(OffResidue44.OffPoint F d a y).card by omega)
  let I := Finset.Icc (L:ℤ) (R:ℤ)
  let T := fun S : Finset ℤ=>S∩I
  have hsizeZ : (D:ℤ)*h≤(R:ℤ)-L+1 := by
    have he : ((R-L+1:ℕ):ℤ)=(R:ℤ)-L+1 := by omega
    rw [←he]
    exact_mod_cast hsize
  obtain ⟨H,hHI,hHc,hmod⟩ := interval_period_holes D h (L:ℤ) (R:ℤ) y hD hsizeZ
  have hpair : ∀S∈C,∀U∈C,S≠U→((T S)∩(T U)).card≤1 := by
    intro S hS U hU hne
    obtain ⟨hSF,hyS,hoff⟩ := Finset.mem_filter.mp (hCE hS)
    obtain ⟨hUF,hyU,_hoffU⟩ := Finset.mem_filter.mp (hCE hU)
    exact OffResidue44.off_point_trace_inter_card (htrace S hSF)
      (hlegal.2 S hSF U hUF hne) hyS hyU hoff
  have hs := TracePacking43.trace_sum_bound C T hpair
  have hsub : C.biUnion T⊆I\H := by
    intro z hz
    obtain ⟨S,hSC,hzS⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hSF,_hyS,hoff⟩ := Finset.mem_filter.mp (hCE hSC)
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hzS).2,?_⟩
    intro hzH
    have hzy : d S∣z-y := dvd_trans (hsteps S hSF) (hmod z hzH)
    have hza : d S∣z-a S := OffResidue44.origin_dvd (htrace S hSF) hzS
    have hh := Int.dvd_sub hza hzy
    apply hoff
    convert hh using 1
    ring
  have hu := Finset.card_le_card hsub
  have hIc : I.card=R-L+1 := Relative13Fringe116.interval_card hLR
  have hdiff : (I\H).card+h=R-L+1 := by
    have hh : (I\H).card+H.card=I.card := Finset.card_sdiff_add_card_eq_card hHI
    simpa only [hHc,hIc] using hh
  have hl : ∑S∈C,((R-L+1)/p+2)≤∑S∈C,(T S).card :=
    Finset.sum_le_sum (by
      intro S hS
      have hh := hlong S (Finset.mem_filter.mp (hCE hS)).1
      dsimp only [T,I]
      omega)
  simp only [Finset.sum_const,nsmul_eq_mul,hCc] at hl
  rw [hCc] at hs
  have hd := Nat.lt_mul_div_succ (R-L+1) hp
  nlinarith only [hl,hs,hu,hdiff,hbudget,hd]

theorem actual_off_residue_count_pred {N L R p D h : ℕ} {F : Finset (Finset ℤ)}
    (d a : Finset ℤ→ℤ)
    (hLR : L≤R) (hp : 0<p) (hD : 0<D)
    (hbudget : h+p=p.choose 2) (hsize : D*h≤R-L+1)
    (hlegal : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S) (a S) (S∩Finset.Icc (L:ℤ) (R:ℤ)))
    (hsteps : ∀S∈F,d S∣(D:ℤ))
    (hlong : ∀S∈F,(R-L+1)/p+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    (OffResidue44.OffMembers F d a).card≤(p-1)*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  have hcover : OffResidue44.OffMembers F d a⊆
      (Ground N\Finset.Icc (L:ℤ) (R:ℤ)).biUnion (OffResidue44.OffPoint F d a) := by
    intro S hS
    obtain ⟨hSF,y,hyS,hoff⟩ := Finset.mem_filter.mp hS
    have hyI : y∉Finset.Icc (L:ℤ) (R:ℤ) := by
      intro hyI
      exact hoff (OffResidue44.origin_dvd (htrace S hSF) (Finset.mem_inter.mpr ⟨hyS,hyI⟩))
    exact Finset.mem_biUnion.mpr ⟨y,Finset.mem_sdiff.mpr ⟨hlegal.1 S hSF hyS,hyI⟩,
      Finset.mem_filter.mpr ⟨hSF,hyS,hoff⟩⟩
  calc
    _≤((Ground N\Finset.Icc (L:ℤ) (R:ℤ)).biUnion (OffResidue44.OffPoint F d a)).card := Finset.card_le_card hcover
    _≤∑y∈Ground N\Finset.Icc (L:ℤ) (R:ℤ),(OffResidue44.OffPoint F d a y).card := Finset.card_biUnion_le
    _≤∑_y∈Ground N\Finset.Icc (L:ℤ) (R:ℤ),(p-1) := Finset.sum_le_sum (by
      intro y _hy
      exact actual_off_point_capacity_pred d a y hLR hp hD hbudget hsize hlegal htrace hsteps hlong)
    _=(p-1)*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by simp [Nat.mul_comm]

theorem actual_off_residue_count12 {N L R : ℕ} {F : Finset (Finset ℤ)}
    (d a : Finset ℤ→ℤ)
    (hLR : L≤R) (hsize : 1801800≤R-L+1)
    (hlegal : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S) (a S) (S∩Finset.Icc (L:ℤ) (R:ℤ)))
    (hsteps : ∀S∈F,d S≤12)
    (hlong : ∀S∈F,(R-L+1)/13+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    (OffResidue44.OffMembers F d a).card≤12*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  apply actual_off_residue_count_pred (p:=13) (D:=27720) (h:=65) d a
    hLR (by decide) (by decide) (by decide) (by norm_num; omega) hlegal htrace ?_ hlong
  intro S hS
  have hpos := (htrace S hS).1
  have hu := hsteps S hS
  have hh : ∀e:ℤ,1≤e→e≤12→e∣27720 := by
    intro e he heu
    interval_cases e <;> norm_num
  exact hh (d S) (by omega) hu

theorem actual_off_residue_count13 {N L R : ℕ} {F : Finset (Finset ℤ)}
    (d a : Finset ℤ→ℤ)
    (hLR : L≤R) (hsize : 27747720≤R-L+1)
    (hlegal : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S) (a S) (S∩Finset.Icc (L:ℤ) (R:ℤ)))
    (hsteps : ∀S∈F,d S≤13)
    (hlong : ∀S∈F,(R-L+1)/14+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    (OffResidue44.OffMembers F d a).card≤13*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  apply actual_off_residue_count_pred (p:=14) (D:=360360) (h:=77) d a
    hLR (by decide) (by decide) (by decide) (by norm_num; omega) hlegal htrace ?_ hlong
  intro S hS
  have hpos := (htrace S hS).1
  have hu := hsteps S hS
  have hh : ∀e:ℤ,1≤e→e≤13→e∣360360 := by
    intro e he heu
    interval_cases e <;> norm_num
  exact hh (d S) (by omega) hu

#print axioms interval_period_holes
#print axioms actual_off_point_capacity_pred
#print axioms actual_off_residue_count_pred
#print axioms actual_off_residue_count12
#print axioms actual_off_residue_count13
end
end JSP233.PeriodOff117
