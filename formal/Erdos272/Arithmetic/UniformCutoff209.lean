import Erdos272.Arithmetic.UniformPotential208

namespace JSP233.UniformCutoff209
open UniformQuery208 UniformDecision208 UniformRat208 UniformEnvelope208 UniformScale208
open UniformSourceQueries208 UniformPotential208
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

def BoundedQuery (a : Query) : Prop :=
  a.q≤RB a.T a.z a.M ∨ 0<(a.z : ℚ) ∧ REnd a.M a.z a.q≤9900

instance (a : Query) : Decidable (BoundedQuery a) := by unfold BoundedQuery; infer_instance

def check (a : Query) : Bool := decide (BoundedQuery a)

theorem checked : UniformSourceQueries208.queries.all check=true := by decide +kernel

theorem query_cap {a : Query} (ha : a∈UniformSourceQueries208.queries) :
    (a.q : ℝ)≤Baseline a.T a.z a.M ∨ HeightEnd a.M a.z a.q≤9900 := by
  have hh : BoundedQuery a := of_decide_eq_true (List.all_eq_true.mp checked a ha)
  rcases hh with hb | ⟨_hz,hY⟩
  · left
    have he := B_cast (a.T : ℚ) a.z a.M
    simp only [Rat.cast_natCast] at he
    rw [←he]
    exact_mod_cast hb
  · right
    have he := end_cast (a.M : ℚ) a.z a.q
    simp only [Rat.cast_natCast] at he
    rw [←he]
    exact_mod_cast hY

theorem row_cap242 (i : Fin 183) (j : Fin 7) :
    (heights242[i.val+1]! : ℝ)≤Baseline ((edges242[i.val]!)[j.val]!) ((cuts242[i.val]!)[j.val]!) 242 ∨
      HeightEnd 242 ((cuts242[i.val]!)[j.val]!) (heights242[i.val+1]!)≤9900 := by
  have hm : rowQuery242 i.val j.val∈UniformSourceQueries208.queries := by
    unfold rowQuery242
    have hn : 0+7*i.val+j.val<UniformSourceQueries208.queries.length := by rw [queries_length]; omega
    rw [getElem!_pos UniformSourceQueries208.queries (0+7*i.val+j.val) hn]
    exact List.getElem_mem hn
  have hh := query_cap hm
  rw [table242 i j] at hh
  exact hh

theorem row_cap243 (i : Fin 184) (j : Fin 7) :
    (heights243[i.val+1]! : ℝ)≤Baseline ((edges243[i.val]!)[j.val]!) ((cuts243[i.val]!)[j.val]!) 243 ∨
      HeightEnd 243 ((cuts243[i.val]!)[j.val]!) (heights243[i.val+1]!)≤9900 := by
  have hm : rowQuery243 i.val j.val∈UniformSourceQueries208.queries := by
    unfold rowQuery243
    have hn : 1281+7*i.val+j.val<UniformSourceQueries208.queries.length := by rw [queries_length]; omega
    rw [getElem!_pos UniformSourceQueries208.queries (1281+7*i.val+j.val) hn]
    exact List.getElem_mem hn
  have hh := query_cap hm
  rw [table243 i j] at hh
  exact hh

#print axioms checked
#print axioms query_cap
#print axioms row_cap242
#print axioms row_cap243
end JSP233.UniformCutoff209
