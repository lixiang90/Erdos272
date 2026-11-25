module

public import Erdos272.Global.N20258.ConcentratedBlocks20258

@[expose] public section
namespace JSP233.ConcentratedBands20258
open StarCompletion FirstSparseCut20258 ConcentratedBlocks20258 EndpointCover20258
set_option autoImplicit false

structure Run where
  first : ℕ
  ends : List ℕ
  percent : ℕ
  source : Source
  deriving DecidableEq

def Run.last (r : Run) := r.ends.getLastD (r.first-1)
def Run.route (r : Run) (l u : ℕ) : Route := ⟨l,u,r.percent,r.source⟩

def Run.Valid (r : Run) (l u : ℕ) : Prop :=
  r.source.Valid ∧ increasing r.first r.last r.ends=true ∧
    ∀ p∈rows r.first r.ends,(r.route l u).Good p.1 p.2

instance (r : Run) (l u : ℕ) : Decidable (r.Valid l u) := by unfold Run.Valid; infer_instance

def Run.chunk (r : Run) (i : ℕ) := ((rows r.first r.ends).drop (3*i)).take 3

theorem Run.validate {r : Run} {l u z : ℕ} (pay : r.source.Valid)
    (asc : increasing r.first r.last r.ends=true)
    (indices : ∀ p∈rows r.first r.ends,∃ i : Fin z,p∈r.chunk i)
    (checked : ∀ i : Fin z, ∀ p∈r.chunk i,(r.route l u).Good p.1 p.2) : r.Valid l u := by
  refine ⟨pay,asc,?_⟩
  intro p hp
  obtain ⟨i,h⟩ := indices p hp
  exact checked i p h

structure Band where
  lower : ℕ
  upper : ℕ
  runs : List Run
  deriving DecidableEq

def Band.stop (b : Band) (start : ℕ) := (b.runs.map Run.last).getLastD (start-1)

def Band.Layout (b : Band) (start Z : ℕ) : Prop :=
  let z := b.stop start
  (z=Z ∨ 5000*((b.upper-1)*b.upper+17)≤443*(z+1)) ∧
    increasing start z (b.runs.map Run.last)=true ∧
    ∀ p∈rows start (b.runs.map Run.last),∃ r∈b.runs,r.first=p.1 ∧ r.last=p.2

instance (b : Band) (start Z : ℕ) : Decidable (b.Layout start Z) := by unfold Band.Layout; infer_instance

theorem upper {N m start Z : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    {b : Band} (lo : start≤N) (hi : N≤Z) (low : b.lower≤m) (high : m≤b.upper)
    (legal : Legal (Ground N) F) (cut : Cut N F m c T) (layout : b.Layout start Z)
    (paid : ∀ r∈b.runs,r.Valid b.lower b.upper) (ground : 2≤N) : F.card≤B N := by
  obtain ⟨stop,asc,matchRun⟩ := layout
  by_cases within : N≤b.stop start
  · obtain ⟨p,hp,l,u,_⟩ := locate _ asc lo within
    obtain ⟨r,hr,first,last⟩ := matchRun p hp
    obtain ⟨valid,ordered,checked⟩ := paid r hr
    obtain ⟨q,hq,left,right,_⟩ := locate r.ends ordered (first ▸ l) (last ▸ u)
    exact ConcentratedBlocks20258.upper (r:=r.route b.lower b.upper) left right low high legal cut
      valid (checked q hq)
  · have sparse := cut.sparse
    have tops : (m-1)*m≤(b.upper-1)*b.upper :=
      Nat.mul_le_mul (Nat.sub_le_sub_right high 1) high
    apply FortyFourFamily20258.of_member ground (by omega) legal
      (Density41.actual_sparse_membership.mp cut.omitter).1 cut.crooked
    rw [cut.size]
    rcases stop with eq|enough <;> omega

#print axioms upper
end JSP233.ConcentratedBands20258
