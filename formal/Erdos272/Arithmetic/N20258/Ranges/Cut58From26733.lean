module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source096
public import Erdos272.Arithmetic.N20258.Sources.Source097
public import Erdos272.Arithmetic.N20258.Sources.Source098
public import Erdos272.Arithmetic.N20258.Sources.Source099

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests58_098_0 : ∀ z∈source098.plan.table,z.1.Valid 58 0 := by decide +kernel
private theorem fee58_098_27540 :
    PopulationFees20258.bill (n:=27540) (PopulationFees20258.tabulate (27540-1) 256) source098.plan.table+
      4*27540*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*304119813594 := by decide +kernel
private theorem range58From26733To2934 : Segment 58 26733 27540 0 2934 :=
  paid (pc:=76) (v:=304119813594) (by decide) source098_valid tests58_098_0 fee58_098_27540 (by decide +kernel)

private theorem tests58_099_2934 : ∀ z∈source099.plan.table,z.1.Valid 58 2934 := by decide +kernel
private theorem fee58_099_27540 :
    PopulationFees20258.bill (n:=27540) (PopulationFees20258.tabulate (27540-1) 256) source099.plan.table+
      4*27540*NaturalPopulation20258.weights source099.extras≤source099.plan.scale*409245563601 := by decide +kernel
private theorem range58From26733To3146 : Segment 58 26733 27540 2934 3146 :=
  paid (pc:=75) (v:=409245563601) (by decide) source099_valid tests58_099_2934 fee58_099_27540 (by decide +kernel)

private theorem tests58_096_3146 : ∀ z∈source096.plan.table,z.1.Valid 58 3146 := by decide +kernel
private theorem fee58_096_27540 :
    PopulationFees20258.bill (n:=27540) (PopulationFees20258.tabulate (27540-1) 256) source096.plan.table+
      4*27540*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*369241309944 := by decide +kernel
private theorem range58From26733To3304 : Segment 58 26733 27540 3146 3304 :=
  paid (pc:=74) (v:=369241309944) (by decide) source096_valid tests58_096_3146 fee58_096_27540 (by decide +kernel)

private theorem tests58_096_3304 : ∀ z∈source096.plan.table,z.1.Valid 58 3304 := by decide +kernel
private theorem range58From26733To3307 : Segment 58 26733 27540 3304 3307 :=
  paid (pc:=74) (v:=369241309944) (by decide) source096_valid tests58_096_3304 fee58_096_27540 (by decide +kernel)

private theorem range58From26733 : Win 58 26733 27540 :=
  complete (by decide) (by decide) (join_population (join_population range58From26733To2934 range58From26733To3146) (join_population range58From26733To3304 range58From26733To3307))

private theorem fee58_098_28458 :
    PopulationFees20258.bill (n:=28458) (PopulationFees20258.tabulate (28458-1) 256) source098.plan.table+
      4*28458*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*323301623007 := by decide +kernel
private theorem range58From27541To2963 : Segment 58 27541 28458 0 2963 :=
  paid (pc:=76) (v:=323301623007) (by decide) source098_valid tests58_098_0 fee58_098_28458 (by decide +kernel)

private theorem tests58_099_2963 : ∀ z∈source099.plan.table,z.1.Valid 58 2963 := by decide +kernel
private theorem fee58_099_28458 :
    PopulationFees20258.bill (n:=28458) (PopulationFees20258.tabulate (28458-1) 256) source099.plan.table+
      4*28458*NaturalPopulation20258.weights source099.extras≤source099.plan.scale*434859526937 := by decide +kernel
private theorem range58From27541To3154 : Segment 58 27541 28458 2963 3154 :=
  paid (pc:=75) (v:=434859526937) (by decide) source099_valid tests58_099_2963 fee58_099_28458 (by decide +kernel)

private theorem tests58_096_3154 : ∀ z∈source096.plan.table,z.1.Valid 58 3154 := by decide +kernel
private theorem fee58_096_28458 :
    PopulationFees20258.bill (n:=28458) (PopulationFees20258.tabulate (28458-1) 256) source096.plan.table+
      4*28458*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*392595137289 := by decide +kernel
private theorem range58From27541To3305 : Segment 58 27541 28458 3154 3305 :=
  paid (pc:=74) (v:=392595137289) (by decide) source096_valid tests58_096_3154 fee58_096_28458 (by decide +kernel)

private theorem tests58_096_3305 : ∀ z∈source096.plan.table,z.1.Valid 58 3305 := by decide +kernel
private theorem range58From27541To3307 : Segment 58 27541 28458 3305 3307 :=
  paid (pc:=74) (v:=392595137289) (by decide) source096_valid tests58_096_3305 fee58_096_28458 (by decide +kernel)

private theorem range58From27541 : Win 58 27541 28458 :=
  complete (by decide) (by decide) (join_population (join_population range58From27541To2963 range58From27541To3154) (join_population range58From27541To3305 range58From27541To3307))

private theorem fee58_098_29526 :
    PopulationFees20258.bill (n:=29526) (PopulationFees20258.tabulate (29526-1) 256) source098.plan.table+
      4*29526*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*346148493869 := by decide +kernel
private theorem range58From28459To2991 : Segment 58 28459 29526 0 2991 :=
  paid (pc:=76) (v:=346148493869) (by decide) source098_valid tests58_098_0 fee58_098_29526 (by decide +kernel)

private theorem tests58_097_2991 : ∀ z∈source097.plan.table,z.1.Valid 58 2991 := by decide +kernel
private theorem fee58_097_29526 :
    PopulationFees20258.bill (n:=29526) (PopulationFees20258.tabulate (29526-1) 256) source097.plan.table+
      4*29526*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*451530016960 := by decide +kernel
private theorem range58From28459To3206 : Segment 58 28459 29526 2991 3206 :=
  paid (pc:=75) (v:=451530016960) (by decide) source097_valid tests58_097_2991 fee58_097_29526 (by decide +kernel)

private theorem tests58_096_3206 : ∀ z∈source096.plan.table,z.1.Valid 58 3206 := by decide +kernel
private theorem fee58_096_29526 :
    PopulationFees20258.bill (n:=29526) (PopulationFees20258.tabulate (29526-1) 256) source096.plan.table+
      4*29526*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*420308290375 := by decide +kernel
private theorem range58From28459To3306 : Segment 58 28459 29526 3206 3306 :=
  paid (pc:=74) (v:=420308290375) (by decide) source096_valid tests58_096_3206 fee58_096_29526 (by decide +kernel)

private theorem tests58_096_3306 : ∀ z∈source096.plan.table,z.1.Valid 58 3306 := by decide +kernel
private theorem range58From28459To3307 : Segment 58 28459 29526 3306 3307 :=
  paid (pc:=74) (v:=420308290375) (by decide) source096_valid tests58_096_3306 fee58_096_29526 (by decide +kernel)

private theorem range58From28459 : Win 58 28459 29526 :=
  complete (by decide) (by decide) (join_population (join_population range58From28459To2991 range58From28459To3206) (join_population range58From28459To3306 range58From28459To3307))

private theorem fee58_098_30797 :
    PopulationFees20258.bill (n:=30797) (PopulationFees20258.tabulate (30797-1) 256) source098.plan.table+
      4*30797*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*374383790819 := by decide +kernel
private theorem range58From29527To3020 : Segment 58 29527 30797 0 3020 :=
  paid (pc:=76) (v:=374383790819) (by decide) source098_valid tests58_098_0 fee58_098_30797 (by decide +kernel)

private theorem tests58_097_3020 : ∀ z∈source097.plan.table,z.1.Valid 58 3020 := by decide +kernel
private theorem fee58_097_30797 :
    PopulationFees20258.bill (n:=30797) (PopulationFees20258.tabulate (30797-1) 256) source097.plan.table+
      4*30797*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*488266041059 := by decide +kernel
private theorem range58From29527To3210 : Segment 58 29527 30797 3020 3210 :=
  paid (pc:=75) (v:=488266041059) (by decide) source097_valid tests58_097_3020 fee58_097_30797 (by decide +kernel)

private theorem tests58_096_3210 : ∀ z∈source096.plan.table,z.1.Valid 58 3210 := by decide +kernel
private theorem fee58_096_30797 :
    PopulationFees20258.bill (n:=30797) (PopulationFees20258.tabulate (30797-1) 256) source096.plan.table+
      4*30797*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*454649679287 := by decide +kernel
private theorem range58From29527To3305 : Segment 58 29527 30797 3210 3305 :=
  paid (pc:=75) (v:=454649679287) (by decide) source096_valid tests58_096_3210 fee58_096_30797 (by decide +kernel)

private theorem range58From29527To3307 : Segment 58 29527 30797 3305 3307 :=
  paid (pc:=75) (v:=454649679287) (by decide) source096_valid tests58_096_3305 fee58_096_30797 (by decide +kernel)

private theorem range58From29527 : Win 58 29527 30797 :=
  complete (by decide) (by decide) (join_population (join_population range58From29527To3020 range58From29527To3210) (join_population range58From29527To3305 range58From29527To3307))

private theorem fee58_098_32340 :
    PopulationFees20258.bill (n:=32340) (PopulationFees20258.tabulate (32340-1) 256) source098.plan.table+
      4*32340*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*410258699711 := by decide +kernel
private theorem range58From30798To3050 : Segment 58 30798 32340 0 3050 :=
  paid (pc:=76) (v:=410258699711) (by decide) source098_valid tests58_098_0 fee58_098_32340 (by decide +kernel)

private theorem tests58_097_3050 : ∀ z∈source097.plan.table,z.1.Valid 58 3050 := by decide +kernel
private theorem fee58_097_32340 :
    PopulationFees20258.bill (n:=32340) (PopulationFees20258.tabulate (32340-1) 256) source097.plan.table+
      4*32340*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*534882991556 := by decide +kernel
private theorem range58From30798To3216 : Segment 58 30798 32340 3050 3216 :=
  paid (pc:=75) (v:=534882991556) (by decide) source097_valid tests58_097_3050 fee58_097_32340 (by decide +kernel)

private theorem tests58_096_3216 : ∀ z∈source096.plan.table,z.1.Valid 58 3216 := by decide +kernel
private theorem fee58_096_32340 :
    PopulationFees20258.bill (n:=32340) (PopulationFees20258.tabulate (32340-1) 256) source096.plan.table+
      4*32340*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*498170517084 := by decide +kernel
private theorem range58From30798To3305 : Segment 58 30798 32340 3216 3305 :=
  paid (pc:=75) (v:=498170517084) (by decide) source096_valid tests58_096_3216 fee58_096_32340 (by decide +kernel)

private theorem range58From30798To3307 : Segment 58 30798 32340 3305 3307 :=
  paid (pc:=75) (v:=498170517084) (by decide) source096_valid tests58_096_3305 fee58_096_32340 (by decide +kernel)

private theorem range58From30798 : Win 58 30798 32340 :=
  complete (by decide) (by decide) (join_population (join_population range58From30798To3050 range58From30798To3216) (join_population range58From30798To3305 range58From30798To3307))

private theorem fee58_098_34252 :
    PopulationFees20258.bill (n:=34252) (PopulationFees20258.tabulate (34252-1) 256) source098.plan.table+
      4*34252*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*456886598695 := by decide +kernel
private theorem range58From32341To3082 : Segment 58 32341 34252 0 3082 :=
  paid (pc:=76) (v:=456886598695) (by decide) source098_valid tests58_098_0 fee58_098_34252 (by decide +kernel)

private theorem tests58_096_3082 : ∀ z∈source096.plan.table,z.1.Valid 58 3082 := by decide +kernel
private theorem fee58_096_34252 :
    PopulationFees20258.bill (n:=34252) (PopulationFees20258.tabulate (34252-1) 256) source096.plan.table+
      4*34252*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*555017607262 := by decide +kernel
private theorem range58From32341To3303 : Segment 58 32341 34252 3082 3303 :=
  paid (pc:=75) (v:=555017607262) (by decide) source096_valid tests58_096_3082 fee58_096_34252 (by decide +kernel)

private theorem tests58_096_3303 : ∀ z∈source096.plan.table,z.1.Valid 58 3303 := by decide +kernel
private theorem range58From32341To3307 : Segment 58 32341 34252 3303 3307 :=
  paid (pc:=75) (v:=555017607262) (by decide) source096_valid tests58_096_3303 fee58_096_34252 (by decide +kernel)

private theorem range58From32341 : Win 58 32341 34252 :=
  complete (by decide) (by decide) (join_population range58From32341To3082 (join_population range58From32341To3303 range58From32341To3307))

theorem cut58From26733 : Win 58 26733 34252 :=
  (join_ground (join_ground range58From26733 (join_ground range58From27541 range58From28459)) (join_ground range58From29527 (join_ground range58From30798 range58From32341)))

end JSP233.FiniteCutRanges20258
