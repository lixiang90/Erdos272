module

public import Erdos272.Capacity.N20258.PopulationPrice20258

@[expose] public section
namespace JSP233.PopulationChecks20258
open PopulationPrice20258 PopulationTariff20258 IndividualPrice20258
set_option autoImplicit false

/-- Try the constant and quadratic prices first. The physical and strict
run sums are reduced by the kernel only for a cell that still needs them. -/
def paid (p : Plan) (s e : ℕ) :=
  let due := p.scale*p.head-grant p.table s e
  decide (due≤p.scale*UniformNumeric84364.value s) ||
    (decide (2≤e) && (decide (due≤p.scale*analytic s e) ||
      decide (due≤p.scale*physical s e) ||
      (decide ((s+1)/2<s-e) && decide (due≤p.scale*middle s e))))

def Cell (p : Plan) (s e : ℕ) : Prop :=
  p.scale*p.head≤p.scale*value s e+grant p.table s e

theorem paid_sound {p : Plan} {s e : ℕ} (pay : paid p s e=true) : Cell p s e := by
  simp only [paid,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at pay
  have lift (z : ℕ) (test : p.scale*p.head-grant p.table s e≤p.scale*z) (ok : z≤value s e) : Cell p s e := by
    have := test.trans (Nat.mul_le_mul_left p.scale ok)
    unfold Cell; omega
  rcases pay with cheap|⟨two,rest⟩
  · apply lift _ cheap
    unfold value; split <;> first | exact le_rfl | exact le_max_left ..
  have ne : ¬ e<2 := by omega
  rcases rest with (simple|phys)|⟨room,mid⟩
  · apply lift _ simple
    simp only [value,ite_eq_right ne]
    exact (le_max_left ..).trans (le_max_right ..)
  · apply lift _ phys
    simp only [value,ite_eq_right ne]
    exact (le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))
  · apply lift _ mid
    simp only [value,ite_eq_right ne,ite_eq_left room]
    exact (le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))

def check (p : Plan) (a b : ℕ) := (List.range (b+1-a)).all (fun i =>
  (List.range (p.stop-1)).all (fun j => paid p (a+i) (j+1)))

def Window (p : Plan) (a b : ℕ) : Prop :=
  ∀ s : ℕ,a≤s → s≤b → ∀ j : Fin (p.stop-1),Cell p s (j.val+1)

theorem window {p : Plan} {a b : ℕ} (h : check p a b=true) : Window p a b := by
  intro s low high j
  have first := (List.all_eq_true.mp h) (s-a) (List.mem_range.mpr (by omega))
  have second := (List.all_eq_true.mp first) j.val (List.mem_range.mpr j.isLt)
  simpa only [show a+(s-a)=s by omega] using paid_sound second

theorem join {p : Plan} {a m b : ℕ} (left : Window p a m) (right : Window p (m+1) b) : Window p a b := by
  intro s lo hi j
  by_cases h : s≤m
  · exact left s lo h j
  · exact right s (by omega) hi j

def Shape (p : Plan) : Prop :=
  4≤p.minimum ∧ p.minimum≤p.top ∧ p.top≤256 ∧ 1≤p.stop ∧ 0<p.scale ∧
  p.head≤UniformNumeric84364.value (p.top+1) ∧
  ∀ i : Fin (p.top+1-p.minimum),p.head≤physical (p.minimum+i.val) p.stop

instance (p : Plan) : Decidable (Shape p) := by unfold Shape; infer_instance

theorem certify {p : Plan} (shape : Shape p) (cells : Window p p.minimum p.top) : p.Valid := by
  obtain ⟨a,b,c,d,e,f,g⟩ := shape
  refine ⟨a,b,c,d,e,f,g,?_⟩
  intro i j
  exact cells _ (Nat.le_add_right ..) (by have h:=i.isLt; omega) j

#print axioms certify
end JSP233.PopulationChecks20258
