module

public import Erdos272.Resources.CrossBandMenu208
public import Erdos272.Resources.CleanupNet208
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.CrossBandNormalize208
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208 CrossBandMenu208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

section
variable {ι : Type*} [DecidableEq ι] (bands : Finset ι) (T E rawZ z H actual : ι→ℕ)
variable {N grid low high i e : ℕ}

theorem actual_coefficient_normalization (hgrid : 0<grid) (hlow : 0<low)
    (hlN : low≤N) (hNh : N≤high) (hei : e ≤ i)
    (hwindow : ∀b∈bands,(rawZ b : ℝ)/N≤(z b : ℝ)/grid) :
    ∀b∈bands,
      (((min N (∑a∈bands,rawZ a)+(e-1) : ℕ) : ℝ)/N-(T b : ℝ)/N)≤
      (((min grid (∑a∈bands,z a)+CleanupNet208.Ceil (i*grid) low : ℕ) : ℝ)/grid-(T b : ℝ)/high) := by
  have hN : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hG : (0 : ℝ)<grid := by exact_mod_cast hgrid
  have hhigh : (0 : ℝ)<high := by exact_mod_cast (show 0<high by omega)
  have hNhR : (N : ℝ)≤high := by exact_mod_cast hNh
  have hsum : ((∑a∈bands,rawZ a : ℕ) : ℝ)/N≤((∑a∈bands,z a : ℕ) : ℝ)/grid := by
    rw [Nat.cast_sum,Nat.cast_sum,Finset.sum_div,Finset.sum_div]
    exact Finset.sum_le_sum hwindow
  have hmin : ((min N (∑a∈bands,rawZ a) : ℕ) : ℝ)/N≤
      ((min grid (∑a∈bands,z a) : ℕ) : ℝ)/grid := by
    by_cases hz : (∑a∈bands,z a)≤grid
    · rw [min_eq_right hz]
      apply le_trans _ hsum
      exact div_le_div_of_nonneg_right (by exact_mod_cast (min_le_right N (∑a∈bands,rawZ a))) hN.le
    · rw [min_eq_left (by omega : grid≤∑a∈bands,z a),div_self hG.ne']
      apply (div_le_one hN).mpr
      exact_mod_cast min_le_left N (∑a∈bands,rawZ a)
  have hceil := CleanupNet208.le_ceil_mul (a := i*grid) hlow
  have hrem : (((e-1 : ℕ) : ℝ)/N)≤(CleanupNet208.Ceil (i*grid) low : ℝ)/grid := by
    apply (div_le_div_iff₀ hN hG).mpr
    have hnat : (e-1)*grid≤CleanupNet208.Ceil (i*grid) low*N :=
      (Nat.mul_le_mul_right grid (by omega : e-1 ≤ i)).trans
        (hceil.trans (Nat.mul_le_mul_left _ hlN))
    exact_mod_cast hnat
  intro b hb
  have ht : (T b : ℝ)/high≤(T b : ℝ)/N :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hN hNhR
  simp only [Nat.cast_add,add_div]
  linarith only [hmin,hrem,ht]

theorem actual_normalized_net (hgrid : 0<grid) (hlow : 0<low)
    (hlN : low≤N) (hNh : N≤high) (hei : e ≤ i)
    (hET : ∀b∈bands,E b≤T b) (hEi : ∀b∈bands,E b ≤ i)
    (hwindow : ∀b∈bands,(rawZ b : ℝ)/N≤(z b : ℝ)/grid)
    (hown : ∀b∈bands,0<H b→(T b-E b+1)*grid≤min grid (z b)*high)
    (ha : ∀b∈bands,actual b≤H b) :
    (∑b∈bands,(actual b : ℝ)*
      (((min N (∑a∈bands,rawZ a)+(e-1) : ℕ) : ℝ)/N-(T b : ℝ)/N))≤
      (((∑b∈bands,H b)*(min grid (∑b∈bands,z b)+CleanupNet208.Ceil (i*grid) low)-
        (∑b∈bands,H b*(T b*grid/high)) : ℕ) : ℝ)/grid := by
  have hcoef := actual_coefficient_normalization bands T rawZ z hgrid hlow hlN hNh hei hwindow
  have hh := Finset.sum_le_sum (fun b (hb : b∈bands)=>
    mul_le_mul_of_nonneg_left (hcoef b hb) (Nat.cast_nonneg (actual b)))
  exact hh.trans (CleanupNet208.actual_count_substitution bands T E z H hgrid hlow (hlN.trans hNh)
    hET hEi hown actual ha)
end

def RawWindows (s : System) (d : ℕ) (b : Band) : ℕ :=
  ((s.Heavy d b).biUnion
    (ClippedWindows208.Window s.N d (s.B d b) (SizeV s d b))).card

def IntegerNet (grid low high i : ℕ) (T z H : Band→ℕ) : ℕ :=
  (∑b : Band,H b)*(min grid (∑b : Band,z b)+CleanupNet208.Ceil (i*grid) low)-
    (∑b : Band,H b*(T b*grid/high))

theorem actual_step_normalized (s : System) (v : Valid s) {d grid low high i : ℕ}
    (hd : d∈Finset.Icc 1 s.D) (hgrid : 0<grid) (hlow : 0<low)
    (hlN : low≤s.N) (hNh : s.N≤high) (hei : s.e ≤ i)
    (z H : Band→ℕ)
    (hwindow : ∀b : Band,(RawWindows s d b : ℝ)/s.N≤(z b : ℝ)/grid)
    (hown : ∀b : Band,0<H b→(s.T d b-s.E d b+1)*grid≤min grid (z b)*high)
    (ha : ∀b : Band,(s.Heavy d b).card≤H b) :
    (∑b : Band,((s.Heavy d b).card : ℝ)*
      (((min s.N (∑a : Band,RawWindows s d a)+(s.e-1) : ℕ) : ℝ)/s.N-(s.T d b : ℝ)/s.N))≤
      (IntegerNet grid low high i (s.T d) z H : ℝ)/grid := by
  exact actual_normalized_net Finset.univ (s.T d) (s.E d) (RawWindows s d) z H
    (fun b=>(s.Heavy d b).card) hgrid hlow hlN hNh hei
    (fun b hb=>(v.ET d hd b).le) (fun b hb=>(v.E_le d hd b).trans hei)
    (fun b hb=>hwindow b) (fun b hb=>hown b) (fun b hb=>ha b)

#print axioms actual_coefficient_normalization
#print axioms actual_normalized_net
#print axioms actual_step_normalized
end
end JSP233.CrossBandNormalize208
