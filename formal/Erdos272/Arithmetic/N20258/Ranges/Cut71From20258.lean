module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source119
public import Erdos272.Arithmetic.N20258.Sources.Source121
public import Erdos272.Arithmetic.N20258.Sources.Source122

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests71_121_0 : ∀ z∈source121.plan.table,z.1.Valid 71 0 := by decide +kernel
private theorem fee71_121_24304 :
    PopulationFees20258.bill (n:=24304) (PopulationFees20258.tabulate (24304-1) 256) source121.plan.table+
      4*24304*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*259902667121 := by decide +kernel
private theorem range71From20258To2543 : Segment 71 20258 24304 0 2543 :=
  paid (pc:=57) (v:=259902667121) (by decide) source121_valid tests71_121_0 fee71_121_24304 (by decide +kernel)

private theorem tests71_121_2543 : ∀ z∈source121.plan.table,z.1.Valid 71 2543 := by decide +kernel
private theorem range71From20258To2725 : Segment 71 20258 24304 2543 2725 :=
  paid (pc:=55) (v:=259902667121) (by decide) source121_valid tests71_121_2543 fee71_121_24304 (by decide +kernel)

private theorem tests71_121_2725 : ∀ z∈source121.plan.table,z.1.Valid 71 2725 := by decide +kernel
private theorem range71From20258To2783 : Segment 71 20258 24304 2725 2783 :=
  paid (pc:=54) (v:=259902667121) (by decide) source121_valid tests71_121_2725 fee71_121_24304 (by decide +kernel)

private theorem tests71_121_2783 : ∀ z∈source121.plan.table,z.1.Valid 71 2783 := by decide +kernel
private theorem range71From20258To4971 : Segment 71 20258 24304 2783 4971 :=
  paid (pc:=53) (v:=259902667121) (by decide) source121_valid tests71_121_2783 fee71_121_24304 (by decide +kernel)

private theorem range71From20258 : Win 71 20258 24304 :=
  complete (by decide) (by decide) (join_population (join_population range71From20258To2543 range71From20258To2725) (join_population range71From20258To2783 range71From20258To4971))

private theorem fee71_121_26636 :
    PopulationFees20258.bill (n:=26636) (PopulationFees20258.tabulate (26636-1) 256) source121.plan.table+
      4*26636*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*307228291197 := by decide +kernel
private theorem range71From24305To3755 : Segment 71 24305 26636 0 3755 :=
  paid (pc:=61) (v:=307228291197) (by decide) source121_valid tests71_121_0 fee71_121_26636 (by decide +kernel)

private theorem tests71_121_3755 : ∀ z∈source121.plan.table,z.1.Valid 71 3755 := by decide +kernel
private theorem range71From24305To3836 : Segment 71 24305 26636 3755 3836 :=
  paid (pc:=60) (v:=307228291197) (by decide) source121_valid tests71_121_3755 fee71_121_26636 (by decide +kernel)

private theorem tests71_121_3836 : ∀ z∈source121.plan.table,z.1.Valid 71 3836 := by decide +kernel
private theorem range71From24305To3840 : Segment 71 24305 26636 3836 3840 :=
  paid (pc:=60) (v:=307228291197) (by decide) source121_valid tests71_121_3836 fee71_121_26636 (by decide +kernel)

private theorem tests71_119_3840 : ∀ z∈source119.plan.table,z.1.Valid 71 3840 := by decide +kernel
private theorem fee71_119_26636 :
    PopulationFees20258.bill (n:=26636) (PopulationFees20258.tabulate (26636-1) 256) source119.plan.table+
      4*26636*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*782556706116 := by decide +kernel
private theorem range71From24305To4971 : Segment 71 24305 26636 3840 4971 :=
  paid (pc:=71) (v:=782556706116) (by decide) source119_valid tests71_119_3840 fee71_119_26636 (by decide +kernel)

private theorem range71From24305 : Win 71 24305 26636 :=
  complete (by decide) (by decide) (join_population (join_population range71From24305To3755 range71From24305To3836) (join_population range71From24305To3840 range71From24305To4971))

private theorem fee71_121_28620 :
    PopulationFees20258.bill (n:=28620) (PopulationFees20258.tabulate (28620-1) 256) source121.plan.table+
      4*28620*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*350670838043 := by decide +kernel
private theorem range71From26637To3794 : Segment 71 26637 28620 0 3794 :=
  paid (pc:=65) (v:=350670838043) (by decide) source121_valid tests71_121_0 fee71_121_28620 (by decide +kernel)

private theorem tests71_121_3794 : ∀ z∈source121.plan.table,z.1.Valid 71 3794 := by decide +kernel
private theorem range71From26637To3841 : Segment 71 26637 28620 3794 3841 :=
  paid (pc:=65) (v:=350670838043) (by decide) source121_valid tests71_121_3794 fee71_121_28620 (by decide +kernel)

private theorem tests71_119_3841 : ∀ z∈source119.plan.table,z.1.Valid 71 3841 := by decide +kernel
private theorem fee71_119_28620 :
    PopulationFees20258.bill (n:=28620) (PopulationFees20258.tabulate (28620-1) 256) source119.plan.table+
      4*28620*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*888985492986 := by decide +kernel
private theorem range71From26637To4971 : Segment 71 26637 28620 3841 4971 :=
  paid (pc:=66) (v:=888985492986) (by decide) source119_valid tests71_119_3841 fee71_119_28620 (by decide +kernel)

private theorem range71From26637 : Win 71 26637 28620 :=
  complete (by decide) (by decide) (join_population range71From26637To3794 (join_population range71From26637To3841 range71From26637To4971))

private theorem fee71_121_30579 :
    PopulationFees20258.bill (n:=30579) (PopulationFees20258.tabulate (30579-1) 256) source121.plan.table+
      4*30579*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*395949451416 := by decide +kernel
private theorem range71From28621To3805 : Segment 71 28621 30579 0 3805 :=
  paid (pc:=68) (v:=395949451416) (by decide) source121_valid tests71_121_0 fee71_121_30579 (by decide +kernel)

private theorem tests71_121_3805 : ∀ z∈source121.plan.table,z.1.Valid 71 3805 := by decide +kernel
private theorem range71From28621To3840 : Segment 71 28621 30579 3805 3840 :=
  paid (pc:=68) (v:=395949451416) (by decide) source121_valid tests71_121_3805 fee71_121_30579 (by decide +kernel)

private theorem fee71_119_30579 :
    PopulationFees20258.bill (n:=30579) (PopulationFees20258.tabulate (30579-1) 256) source119.plan.table+
      4*30579*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1000516680692 := by decide +kernel
private theorem range71From28621To4971 : Segment 71 28621 30579 3840 4971 :=
  paid (pc:=62) (v:=1000516680692) (by decide) source119_valid tests71_119_3840 fee71_119_30579 (by decide +kernel)

private theorem range71From28621 : Win 71 28621 30579 :=
  complete (by decide) (by decide) (join_population range71From28621To3805 (join_population range71From28621To3840 range71From28621To4971))

private theorem fee71_121_32670 :
    PopulationFees20258.bill (n:=32670) (PopulationFees20258.tabulate (32670-1) 256) source121.plan.table+
      4*32670*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*447463243440 := by decide +kernel
private theorem range71From30580To3814 : Segment 71 30580 32670 0 3814 :=
  paid (pc:=70) (v:=447463243440) (by decide) source121_valid tests71_121_0 fee71_121_32670 (by decide +kernel)

private theorem tests71_121_3814 : ∀ z∈source121.plan.table,z.1.Valid 71 3814 := by decide +kernel
private theorem range71From30580To3840 : Segment 71 30580 32670 3814 3840 :=
  paid (pc:=69) (v:=447463243440) (by decide) source121_valid tests71_121_3814 fee71_121_32670 (by decide +kernel)

private theorem fee71_119_32670 :
    PopulationFees20258.bill (n:=32670) (PopulationFees20258.tabulate (32670-1) 256) source119.plan.table+
      4*32670*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1126358088918 := by decide +kernel
private theorem range71From30580To4436 : Segment 71 30580 32670 3840 4436 :=
  paid (pc:=66) (v:=1126358088918) (by decide) source119_valid tests71_119_3840 fee71_119_32670 (by decide +kernel)

private theorem tests71_122_4436 : ∀ z∈source122.plan.table,z.1.Valid 71 4436 := by decide +kernel
private theorem fee71_122_32670 :
    PopulationFees20258.bill (n:=32670) (PopulationFees20258.tabulate (32670-1) 256) source122.plan.table+
      4*32670*NaturalPopulation20258.weights source122.extras≤source122.plan.scale*864233731440 := by decide +kernel
private theorem range71From30580To4971 : Segment 71 30580 32670 4436 4971 :=
  paid (pc:=60) (v:=864233731440) (by decide) source122_valid tests71_122_4436 fee71_122_32670 (by decide +kernel)

private theorem range71From30580 : Win 71 30580 32670 :=
  complete (by decide) (by decide) (join_population (join_population range71From30580To3814 range71From30580To3840) (join_population range71From30580To4436 range71From30580To4971))

private theorem fee71_121_34864 :
    PopulationFees20258.bill (n:=34864) (PopulationFees20258.tabulate (34864-1) 256) source121.plan.table+
      4*34864*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*505216089139 := by decide +kernel
private theorem range71From32671To3886 : Segment 71 32671 34864 0 3886 :=
  paid (pc:=71) (v:=505216089139) (by decide) source121_valid tests71_121_0 fee71_121_34864 (by decide +kernel)

private theorem tests71_119_3886 : ∀ z∈source119.plan.table,z.1.Valid 71 3886 := by decide +kernel
private theorem fee71_119_34864 :
    PopulationFees20258.bill (n:=34864) (PopulationFees20258.tabulate (34864-1) 256) source119.plan.table+
      4*34864*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1266683417014 := by decide +kernel
private theorem range71From32671To4121 : Segment 71 32671 34864 3886 4121 :=
  paid (pc:=69) (v:=1266683417014) (by decide) source119_valid tests71_119_3886 fee71_119_34864 (by decide +kernel)

private theorem tests71_119_4121 : ∀ z∈source119.plan.table,z.1.Valid 71 4121 := by decide +kernel
private theorem range71From32671To4130 : Segment 71 32671 34864 4121 4130 :=
  paid (pc:=69) (v:=1266683417014) (by decide) source119_valid tests71_119_4121 fee71_119_34864 (by decide +kernel)

private theorem tests71_122_4130 : ∀ z∈source122.plan.table,z.1.Valid 71 4130 := by decide +kernel
private theorem fee71_122_34864 :
    PopulationFees20258.bill (n:=34864) (PopulationFees20258.tabulate (34864-1) 256) source122.plan.table+
      4*34864*NaturalPopulation20258.weights source122.extras≤source122.plan.scale*972123402284 := by decide +kernel
private theorem range71From32671To4971 : Segment 71 32671 34864 4130 4971 :=
  paid (pc:=63) (v:=972123402284) (by decide) source122_valid tests71_122_4130 fee71_122_34864 (by decide +kernel)

private theorem range71From32671 : Win 71 32671 34864 :=
  complete (by decide) (by decide) (join_population (join_population range71From32671To3886 range71From32671To4121) (join_population range71From32671To4130 range71From32671To4971))

theorem cut71From20258 : Win 71 20258 34864 :=
  (join_ground (join_ground range71From20258 (join_ground range71From24305 range71From26637)) (join_ground range71From28621 (join_ground range71From30580 range71From32671)))

end JSP233.FiniteCutRanges20258
